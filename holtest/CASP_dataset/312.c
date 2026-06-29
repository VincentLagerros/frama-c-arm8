/*@
  requires \valid(t+(0..taille-1)) && taille>0;

  behavior increasing:
    assumes \forall integer i; 1 <= i < taille ==> t[i] >= t[i - 1];
    ensures \result == 1;

  behavior decreasing:
    assumes \exists integer i; 1 <= i < taille && t[i] < t[i - 1];
    ensures \result == 0;

  assigns \nothing;
  complete behaviors increasing, decreasing;
  disjoint behaviors increasing, decreasing;
*/
int monotonic(int t[], int taille) {
    int i;

  /*@
    loop invariant 1 <= i <= taille;
    loop invariant \forall integer j; 1 <= j < i ==> t[j] >= t[j - 1];
    loop assigns i;
    loop variant taille - i;
  */
        for (i = 1; i < taille; i++) {
            if (t[i] < t[i - 1])
                return 0;
        }
        return 1;
}
