/* ****************************************************************************
                              MATRICE SYMÉTRIQUE

   L'énoncé est introduit sous la forme de commentaires C. Les différents
   morceaux de programme et de spécification à considérer sont mentionnés en
   programmation littéraire :

              https://en.wikipedia.org/wiki/Literate_programming

   ************************************************************************* */

/* ---------------------------------------------------------------------------
   Petits rappels de mathématiques élémentaires à toutes fins utiles :

   - Une matrice carrée de taille N (N, entier naturel) est une matrice
   possédant N lignes et N colonnes.

   - Une matrice carrée A est dite symétrique si et seulement si A_{ij} =
   A_{ji} pour toute ligne [i] et colonne [j].
   ------------------------------------------------------------------------- */

#include <stdbool.h>

/* ---------------------------------------------------------------------------
   La fonction [is_symmetric] ci-dessous retourne [true] si et seulement si
   [matrix] est une matrice symétrique de taille [len]. Elle retourne [false]
   sinon.

   Question 1 : spécifier cette fonction en utilisant des comportements ACSL.

   Question 2 : prouver cette fonction, y compris sa terminaison et l'absence
   d'erreurs à l'exécution.
   ------------------------------------------------------------------------- */


/*@ requires \valid(matrix[0..len-1]+(0..len-1));
  @ requires \valid(matrix+(0..len-1));
  @ requires len >= 0;
  @ assigns \nothing;
  @ behavior symm:
  @    assumes \forall integer i,j; 0 <= i < len ==> 0 <= j < len ==> matrix[i][j] == matrix[j][i];
  @    ensures \result == true;
  @ behavior nosymm:
  @    assumes \exists integer i,j; 0 <= i < len && 0 <= j < len && matrix[i][j] != matrix[j][i];
  @    ensures \result == false;
  @ complete behaviors;
  @ disjoint behaviors;
  @ */
_Bool is_symmetric(int **matrix, int len) {
  /*@loop invariant 0 <= i <= len;
    @loop invariant \forall integer k, l; 0 <= k < i ==> 0 <= l < k ==> matrix[k][l] == matrix[l][k];
    @loop assigns i;
    @loop variant len - i;
    @ */
  for (int i = 0; i < len; i++)
    /*@loop invariant 0 <= j <= i;
    @loop invariant \forall integer k; 0 <= k < j ==> matrix[i][k] == matrix[k][i];
    @loop assigns j;
    @loop variant i - j;
    @ */
    for (int j = 0; j < i; j++)
      if (matrix[i][j] != matrix[j][i])
        return false;
  return true;
}
