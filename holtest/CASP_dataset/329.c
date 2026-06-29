/*@
  @ requires n > 0;
  @ requires \valid(a+(0..n-1));
  @ requires \valid(b+(0..n-1));
  @ assigns \nothing;
  @ behavior true_:
  @   assumes \forall int i; 0 <= i < n ==> a[i] == b[i];
  @   ensures \result == n;
  @ behavior false_:
  @   assumes \exists int i; 0 <= i < n && a[i] != b[i];
  @   ensures 0 <= \result < n && a[\result] != b[\result];
  @   ensures \forall int i; 0 <= i < \result ==> a[i] == b[i];
  @ complete behaviors true_, false_;
  @ disjoint behaviors true_, false_;
*/
int compare_arrays(int a[], int b[], int n) {
    /*@
      @ loop invariant 0 <= i <= n;
      @ loop invariant \forall integer j; 0 <= j < i ==> a[j] == b[j];
      @ loop assigns i;
      @ loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        if (a[i] != b[i]) return i;
    }
    return n;
}