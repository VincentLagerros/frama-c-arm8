/*@
  @ requires n > 1;
  @ requires \valid(a+(0..n - 1));
  @
  @ ensures 0 <= \result < n; 
  @ ensures \exists int i; 0 <= i < n &&  a[\result] == a[i];
  @ ensures \forall int j; 0 <= j < n ==> a[\result] <= a[j];
  @ assigns \nothing;
*/

int argmin(int a[], int n) {
    int index_min = 0;

    /*@
      @ loop invariant 1 <= i <= n;
      @ loop invariant 0 <= index_min < i;
      @ loop invariant \forall int j; 0 <= j < i ==> a[index_min] <= a[j];
      @ loop assigns index_min, i;
      @ loop variant n - i;
    */
    for (int i = 1; i < n; ++i) {
        if (a[i] < a[index_min])
            index_min = i;
    }

    /*@ assert \forall int j; 0 <= j < n ==> a[index_min] <= a[j]; */

    return index_min;
}