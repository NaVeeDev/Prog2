(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-26-27"]

open Type
open Minimir
open Active_borrows

(* This function computes the set of alive lifetimes at every program point. *)
let compute_lft_sets prog mir : lifetime -> PpSet.t =

  (* The [outlives] variable contains all the outlives relations between the
    lifetime variables of the function. *)
  let outlives = ref LMap.empty in

  (* Helper functions to add outlives constraints. *)
  let add_outlives (l1, l2) = outlives := add_outlives_edge l1 l2 !outlives in
  let unify_lft l1 l2 =
    add_outlives (l1, l2);
    add_outlives (l2, l1)
  in

  (* First, we add in [outlives] the constraints implied by the type of locals. *)
  Hashtbl.iter
    (fun _ typ -> outlives := outlives_union !outlives (implied_outlives prog typ))
    mir.mlocals;

  (* Then, we add the outlives relations needed for the instructions to be safe. *)

  (* TODO: generate these constraints by
       - unifying types that need be equal (note that MiniRust does not support subtyping, that is,
         if a variable x: &'a i32 is used as type &'b i32, then this requires that lifetimes 'a and
         'b are equal),
       - adding constraints required by function calls,
       - generating constraints corresponding to reborrows. More precisely, if we create a borrow
         of a place that dereferences  borrows, then the lifetime of the borrow we
         create should be shorter than the lifetimes of the borrows the place dereference.
         For example, if x: &'a &'b i32, and we create a borrow y = &**x of type &'c i32,
         then 'c should be shorter than 'a and 'b.

    SUGGESTION: use functions [typ_of_place], [fields_types_fresh] and [fn_prototype_fresh].
  *)

  let rec unify_lft_types ty1 ty2 =
    match ty1, ty2 with
    | Tborrow (lft1, _, ty1'), Tborrow (lft2, _, ty2') ->
        unify_lft lft1 lft2;
        unify_lft_types ty1' ty2'
    | Tstruct (n1, args1), Tstruct (n2, args2) when n1 = n2 ->
        List.iter2 unify_lft args1 args2
    | _ -> ()
  in

  Array.iter
    (fun (instr, _) ->
      match instr with
      | Iassign (pl, rv, _) -> (
          let ty_pl = typ_of_place prog mir pl in
          let ty_rv =
            match rv with
            | RVplace pl2 | RVunop (_, pl2) | RVborrow (_, pl2) -> typ_of_place prog mir pl2
            | RVbinop (_, pl1, pl2) ->
                unify_lft_types ty_pl (typ_of_place prog mir pl1);
                unify_lft_types ty_pl (typ_of_place prog mir pl2);
                ty_pl
            | RVmake (_, _) -> ty_pl
            | RVunit -> Tunit
            | RVconst _ -> Ti32
          in
          unify_lft_types ty_pl ty_rv;
          match rv with
          | RVborrow (_, pl2) ->
              let rec add_reborrow_constraints lft ty =
                match ty with
                | Tborrow (lft2, _, ty') ->
                    add_outlives (lft2, lft);
                    add_reborrow_constraints lft ty'
                | _ -> ()
              in
              (match typ_of_place prog mir pl with
              | Tborrow (lft, _, _) ->
                  add_reborrow_constraints lft (typ_of_place prog mir pl2)
              | _ -> ())
          | _ -> ()
        )
      | Icall (fname, args, dest, _) ->
          let (fn_args, fn_ret, _) = fn_prototype_fresh prog fname in
          List.iter2 unify_lft_types fn_args (List.map (typ_of_place prog mir) args);
          unify_lft_types (typ_of_place prog mir dest) fn_ret
      | _ -> ()
    )
    mir.minstrs;

  (* Now, we compute the set of living lifetimes at every program point. *)

  (* The [living] variable contains constraints of the form "lifetime 'a should be
    alive at program point p". *)
  let living : PpSet.t LMap.t ref = ref LMap.empty in

  (* Helper function to add living constraint. *)
  let add_living pp l =
    living :=
      LMap.update l
        (fun s -> Some (PpSet.add pp (Option.value s ~default:PpSet.empty)))
        !living
  in

  (* Run the live local analysis. See module Live_locals for documentation. *)
  let live_locals = Live_locals.go mir in

  (* TODO: generate living constraints:
     - Add living constraints corresponding to the fact that liftimes appearing free
       in the type of live locals at some program point should be alive at that
       program point.
     - Add living constraints corresponding to the fact that generic lifetime variables
       (those in [mir.mgeneric_lfts]) should be alive during the whole execution of the
       function.
  *)

  let rec free_lfts_of_type ty =
    match ty with
    | Tborrow (lft, _, ty') -> LSet.add lft (free_lfts_of_type ty')
    | Tstruct (_, args) -> List.fold_left (fun acc lft -> LSet.add lft acc) LSet.empty args
    | _ -> LSet.empty
  in
  

  Array.iteri (fun lbl _ ->
    let live = live_locals lbl in
    List.iter (fun l ->
      let ty = Hashtbl.find mir.mlocals l in
      let lfts = free_lfts_of_type ty in
      LSet.iter (fun lft -> add_living (PpLocal lbl) lft) lfts
    ) (LocSet.elements live)
  ) mir.minstrs;

  List.iter (fun lft ->
    Array.iteri (fun lbl _ -> add_living (PpLocal lbl) lft) mir.minstrs
  ) mir.mgeneric_lfts;


  (* If [lft] is a generic lifetime, [lft] is always alive at [PpInCaller lft]. *)
  List.iter (fun lft -> add_living (PpInCaller lft) lft) mir.mgeneric_lfts;

  (* Now, we compute lifetime sets by finding the smallest solution of the constraints, using the
    Fix library. *)
  let module Fix = Fix.Fix.ForType (struct type t = lifetime end) (Fix.Prop.Set (PpSet))
  in
  Fix.lfp (fun lft lft_sets ->
      LSet.fold
        (fun lft acc -> PpSet.union (lft_sets lft) acc)
        (Option.value ~default:LSet.empty (LMap.find_opt lft !outlives))
        (Option.value ~default:PpSet.empty (LMap.find_opt lft !living)))

let borrowck prog mir =
  (* We check initializedness requirements for every instruction. *)
  let uninitialized_places = Uninitialized_places.go prog mir in
  Array.iteri
    (fun lbl (instr, loc) ->
      let uninit : PlaceSet.t = uninitialized_places lbl in

      let check_initialized pl =
        if PlaceSet.exists (fun pluninit -> is_subplace pluninit pl) uninit then
          Error.error loc "Use of a place which is not fully initialized at this point."
      in

      (match instr with
      | Iassign (pl, _, _) | Icall (_, _, pl, _) -> (
          match pl with
          | PlDeref pl0 ->
              if PlaceSet.mem pl0 uninit then
                Error.error loc "Writing into an uninitialized borrow."
          | PlField (pl0, _) ->
              if PlaceSet.mem pl0 uninit then
                Error.error loc "Writing into a field of an uninitialized struct."
          | _ -> ())
      | _ -> ());

      match instr with
      | Iassign (_, RVplace pl, _) | Iassign (_, RVborrow (_, pl), _) ->
          check_initialized pl
      | Iassign (_, RVbinop (_, pl1, pl2), _) ->
          check_initialized pl1;
          check_initialized pl2
      | Iassign (_, RVunop (_, pl), _) | Iif (pl, _, _) -> check_initialized pl
      | Iassign (_, RVmake (_, pls), _) | Icall (_, pls, _, _) ->
          List.iter check_initialized pls
      | Ireturn -> check_initialized (PlLocal Lret)
      | Iassign (_, (RVunit | RVconst _), _) | Ideinit _ | Igoto _ -> ())
    mir.minstrs;

  (* We check the code honors the non-mutability of shared borrows. *)
  Array.iter
    (fun (instr, loc) ->
      (* TODO: check that we never write to shared borrows, and that we never create mutable borrows
        below shared borrows. Function [place_mut] can be used to determine if a place is mutable, i.e., if it
        does not dereference a shared borrow. *)
      (
        let is_mut = place_mut prog mir in
         match instr with
         | Iassign (pl, rv, next) -> 
              if (is_mut pl) = NotMut then 
                Error.error loc "Writing to a shared borrow."
              else
                (match rv with
                | RVplace pl1 -> if (is_mut pl1) = NotMut then
                    Error.error loc "Writing to a shared borrow."
                | RVborrow (mut, pl') -> if mut = Mut then
                    Error.error loc "Creating a mutable borrow below a shared borrow."
                | _ -> ()
                )
         | Ideinit (l, rv) -> 
                let pl = PlLocal l in
                if (is_mut pl) = NotMut then
                  Error.error loc "Writing to a shared borrow." (* pas sure?? *)
         | Icall (s, pll, pl, next) ->                          (* pas sure?? *)
              if (is_mut pl) = NotMut then
                Error.error loc "Writing to a shared borrow."
      
         | _ -> ()

    )
    )
    mir.minstrs;

  let lft_sets = compute_lft_sets prog mir in

  (* TODO: check that outlives constraints declared in the prototype of the function are
    enough to ensure safety. I.e., if [lft_sets lft] contains program point [PpInCaller lft'], this
    means that we need that [lft] be alive when [lft'] dies, i.e., [lft'] outlives [lft]. This relation
    has to be declared in [mir.outlives_graph]. *)
  
  let ghost_loc : Lexing.position * Lexing.position = Lexing.dummy_pos, Lexing.dummy_pos in

  let is_generic lft = List.mem lft mir.mgeneric_lfts in

  LSet.iter (fun l1 ->
    let l1_pts = lft_sets l1 in
    PpSet.iter (function
      | PpInCaller l2  -> if is_generic l1 && is_generic l2 then (
          let declared =
            match LMap.find_opt l2 mir.moutlives_graph with
            | Some s -> LSet.mem l1 s
            | None -> false
          in
          if not declared then
            Error.error ghost_loc
              "Missing outlives constraint: lifetime %s must outlive lifetime %s."
              (string_of_lft l2) (string_of_lft l1) )
          else ()
      | _ -> ())
      l1_pts
  ) (LSet.of_list mir.mgeneric_lfts);

  (* We check that we never perform any operation which would conflict with an existing
    borrows. *)
  let bor_active_at = Active_borrows.go prog lft_sets mir in
  Array.iteri
    (fun lbl (instr, loc) ->
      (* The list of bor_info for borrows active at this instruction. *)
      let active_borrows_info : bor_info list =
        List.map (get_bor_info prog mir) (BSet.to_list (bor_active_at lbl))
      in

      (* Does there exist a borrow of a place pl', which is active at program point [lbl],
        such that a *write* to [pl] conflicts with this borrow?

         If [pl] is a subplace of pl', then writing to [pl] is always conflicting, because
        it is aliasing with the borrow of pl'.

         If pl' is a subplace of [pl], the situation is more complex:
           - if pl' involves as many dereferences as [pl] (e.g., writing to [x.f1] while
            [x.f1.f2] is borrowed), then the write to [pl] will overwrite pl', hence this is
            conflicting.
           - BUT, if pl' involves more dereferences than [pl] (e.g., writing to [x.f1] while
            [*x.f1.f2] is borrowed), then writing to [pl] will *not* modify values accessible
            from pl'. Hence, subtlely, this is not a conflict. *)
      let conflicting_borrow_no_deref pl =
        List.exists
          (fun bi -> is_subplace pl bi.bplace || is_subplace_no_deref bi.bplace pl)
          active_borrows_info
      in

      (match instr with
      | Iassign (pl, _, _) | Icall (_, _, pl, _) ->
          if conflicting_borrow_no_deref pl then
            Error.error loc "Assigning a borrowed place."
      | Ideinit (l, _) ->
          if conflicting_borrow_no_deref (PlLocal l) then
            Error.error loc
              "A local declared here leaves its scope while still being borrowed."
      | Ireturn ->
          Hashtbl.iter
            (fun l _ ->
              match l with
              | Lparam p ->
                  if conflicting_borrow_no_deref (PlLocal l) then
                    Error.error loc
                      "When returning from this function, parameter `%s` is still \
                       borrowed."
                      p
              | _ -> ())
            mir.mlocals
      | _ -> ());

      (* Variant of [conflicting_borrow_no_deref]: does there exist a borrow of a place pl',
        which is active at program point [lbl], such that a *read* to [pl] conflicts with this
        borrow? In addition, if parameter [write] is true, we consider an operation which is
        both a read and a write. *)
      let conflicting_borrow write pl =
        List.exists
          (fun bi ->
            (bi.bmut = Mut || write)
            && (is_subplace pl bi.bplace || is_subplace bi.bplace pl))
          active_borrows_info
      in

      (* Check a "use" (copy or move) of place [pl]. *)
      let check_use pl =
        let consumes = not (typ_is_copy prog (typ_of_place prog mir pl)) in
        if conflicting_borrow consumes pl then
          Error.error loc "A borrow conflicts with the use of this place.";
        if consumes && contains_deref_borrow pl then
          Error.error loc "Moving a value out of a borrow."
      in

      match instr with
      | Iassign (_, RVunop (_, pl), _) -> check_use pl
      | Iassign (_, RVborrow (mut, pl), _) ->
          if conflicting_borrow (mut = Mut) pl then
            Error.error loc "There is a borrow conflicting this borrow."
      | Iassign (_, RVbinop (_, pl1, pl2), _) ->
          check_use pl1;
          check_use pl2
      | Iassign (_, RVmake (_, pls), _) ->
          List.iter check_use pls
      | Icall (_, pls, _, _) ->
          List.iter check_use pls
      | Iif (pl, _, _) -> check_use pl
      | _ -> ()
    )
    mir.minstrs
