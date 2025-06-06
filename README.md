# PROGRAMMATION AVANCEE : PROJET DE PROGRAMMATION 
---
##### Laura LY
###### LDD3 Magistère Informatique (Paris-Saclay)

---
## Travail réalisé
- La tâche 1 consistait à compléter le fichier `uninitialized_places.ml`. En particulier, pour la fonction `move_or_copy`, il s'agissait d'agir sur une place en fonction de si elle correspondait à un type *copy* ou un type *move*. Dans le dernier cas seulement, on désinitialise la place. Les autres fonctions à compléter ont été faite avec inspiration par le fichier `active_borrows.ml` comme conseillé.
- La tâche 2 a été complétée dans le fichier `borrowck.ml` où les conditions d'écriture et de modifications d'emprunts ont été établies, des erreurs étant levées si ces conditions n'étaient pas respectées.
- La tâche 3 a implémenté les contraintes de survie et les contraintes de vie
- La tâche 4 imposait la déclaration explicite qu'une durée de vie était plus longue qu'une autre quand nécessaire
- La tâche 5 consistait à compléter l'analyseur d'emprunts


## Difficultés rencontrées
N'ayant pu compléter le projet que de justesse et avec un nombre de tests validés très peu satisfaisant, il parait évident que le coeur des difficultés rencontrées se place dans l'organisation du temps, la compréhension du fonctionnement du borrow checker de Rust, la compréhension du sujet ainsi que la compréhension du code fourni, malgré les commentaires mis à disposition.
Des facteurs extérieurs liés à l'organisation du magistère comme le déplacement de dates d'examens et de rendus de projets, ainsi que le jonglement entre les heures de cours et le stage, ont entravé la répartition du travail sur la durée.
Une difficulté s'est aussi posée dans la manipulation d'un code qui n'est pas mien, par la lecture, la compréhension, les commentaires et la division du code en nombreux modules.
Le temps passé sur ce projet a été essentiellement dépensé sur la lecture et les nombreuses tentatives de compréhension du sujet. La tâche 3, couplée à la manipulation non-triviale des *lifetimes*, est celle qui a posé le plus confusion et qui a demandé le plus de relectures du sujet, et cela peut être notamment observé par la différence entre le nombre de tests passés après la tâche 2 et celle après la tâche 3 (cette différence valant 1). Par ailleurs, cette observation peut être prolongée aux tâches suivantes puisqu'aucune amélioration en termes de nombre de tests passés sera perçue après terminaison de ces dernières.

## Conclusion
Pour conclure, malgré le travail fourni peu frructueux, il a été très intéressant de travailler sur ce projet et cela a représenté une occasion de mieux comprendre le fonctionnement d'un borrow checker et par extension du langage de programmation qu'est Rust en général.