/*@ requires n > 0;
    requires \valid_read(a + (0..n-1));
    assigns \nothing;

    behavior present:
        assumes \exists integer k; 0 <= k < n && x == a[k];
        ensures \result == 1;
        assigns \nothing;

    behavior not_present:
        assumes \forall integer k; 0 <= k < n ==> x != a[k];
        ensures \result == 0;
        assigns \nothing;

    complete behaviors present, not_present;
    disjoint behaviors present, not_present;
*/
int arraysearch(int* a, int x, int n) {
  /*@ loop invariant 0 <= p <= n;
      loop invariant \forall integer k; 0 <= k < p ==> x != a[k];
      loop assigns p;
      loop variant n - p;
  */
  for (int p = 0; p < n; p++) {
    if (x == a[p])
       return 1;
  }
  return 0;
}