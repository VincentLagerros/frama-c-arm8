/*@
  requires n > 0;
  requires \valid_read(arr + (0..n-1));
  ensures \forall integer i;
      0 <= i < n ==> \result <= arr[i];
*/
int arraymin(int arr[], int n) {
int min = arr[0];
/*@
  loop invariant \forall integer i; 0 <= i < n ==> min <= arr[i] || i >= j;
  loop invariant 1 <= j <= n;
  loop assigns j, min;
  loop variant n - j;
*/
for (int j=1; j<n; j++)
{
   if (arr[j] < min)
      min = arr[j];
}

return min;

}