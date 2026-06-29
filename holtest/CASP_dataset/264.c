/*@
  requires n > 0;
  requires \valid(a + (0..n-1));
  ensures \forall integer i;
      0 <= i < n ==> a[i]==0;
*/
void Zero_array(int a[], int n)
{
/*@
  loop invariant \forall integer i;
      0 <= i < j ==> a[i]==0;
  loop invariant 0 <= j <= n;
  loop assigns j,a[0..n-1];
  loop variant n - j;
*/
    for (int j = 0; j < n; j++)
    {
        a[j] = 0;
    }
}