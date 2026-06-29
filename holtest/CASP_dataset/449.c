/*@
  @ requires n > 0;
  @ requires \valid(a+(0..n - 1));
  @ 
  @ assigns \nothing;
  @ behavior okay_:
  @   assumes \exists int i; 0 <= i < n && a[i] == val;
  @   ensures 0 <= \result < n;
  @   ensures \forall int i; 0 <= i < \result ==> a[i] != val;
  @   ensures a[\result] == val;
  @ behavior not_okay_:
  @   assumes \forall int i; 0 <= i < n &&  a[i] != val;
  @   ensures \result == n;
*/
int find(int a[], int n, int val) {
    /*@
      @ loop invariant  0 <= i <= n;
      @ loop invariant \forall int j; 0 <= j < i ==> a[j] != val;
      @ loop   variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        if (a[i] == val) return i;
    }
    return n;
}