/*@
  @ requires 0 <= n <= 1000;
  @ ensures 2 * \result == n * (n + 1);
  @ assigns \nothing;
*/
int sum_n(int n) {
    int res = 0;

    /*@
      @ loop invariant 0 <= i <= n + 1;
      @ loop invariant 2 * res == i * (i - 1);
      @ loop   variant n - i + 1;
    */
    for (int i = 0; i <= n; ++i) {
        res += i;
    }
    return res;
}