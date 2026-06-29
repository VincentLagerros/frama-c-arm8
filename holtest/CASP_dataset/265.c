/*@ requires \valid(a+(0..n-1));
    requires 0 <= i < n;
    requires 0 <= j < n;
    assigns a[i], a[j];
    ensures a[i] == \old(a[j]);
    ensures a[j] == \old(a[i]);
 */
static inline void swap(int a[], int i, int j, int n)
{
  int tmp = a[i];
  a[i] = a[j];
  a[j] = tmp;
}