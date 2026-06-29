/*@ axiomatic Count {
    logic integer count{L}(int *a, integer m, integer n, integer p);

    axiom count_base:
      \forall int *a, integer m, integer n, integer p; m >= n ==> count(a, m, n, p) == 0;

    axiom count_split:
      \forall int *a, integer m, integer n, integer k, integer p; m <= n <= k ==> count(a, m, k, p) == count(a, m, n, p) + count(a, n, k, p);

    axiom count_one:
      \forall int *a, integer m, integer p; count(a, m, m + 1, p) == (a[m] == p ? 1 : 0);
  }

  axiomatic Ordered {
    predicate ordered{L}(int *a, integer m, integer n);

    axiom ordered_base:
      \forall int *a, integer m, integer n; m >= n ==> ordered(a, m, n);

    axiom ordered_split:
      \forall int *a, integer m, integer k, integer n; m <= n <= k ==> ordered(a, m, k) <==> ordered(a, m, n) && ordered(a, n, k);

    axiom ordered_two:
      \forall int *a, integer m, integer n; m < n ==> ordered(a, m, n) <==> a[m] <= a[n-1];
  }

  predicate minimum(int *a, integer m, integer n, integer k) = 
    \forall integer i; m <= i < n ==> a[k] <= a[i];
*/

/*@
  requires n >= 0;
  requires \valid(a + (0 .. n-1));
  ensures ordered(a, 0, n);
  ensures \forall integer p; count{Here}(a, 0, n, p) == count{Pre}(a, 0, n, p);
  assigns a[0 .. n-1];
*/
void sort(int *a, int n)
{
    /*@
        loop invariant ordered(a, 0, i);
        loop invariant 0 <= i <= n;
        loop assigns i, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        int min_pos = i;
        /*@
            loop invariant minimum(a, i, j, min_pos);
            loop invariant i <= min_pos < n;
            loop invariant i <= j <= n;
            loop assigns j, min_pos;
            loop variant n - j;
        */
        for (int j = i + 1; j < n; ++j) {
            if (a[j] < a[min_pos]) {
                min_pos = j;
            }
        }
        if (min_pos != i) {
            int tmp = a[min_pos];
            a[min_pos] = a[i];
            a[i] = tmp;
        }
    }
}
