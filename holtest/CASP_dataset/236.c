/*@
  requires n > 0;
  requires \valid_read(a + (0..n-1));
  ensures \forall integer j; 0 <= j < n ==> \result >= a[j];
  assigns \nothing;
*/
int Max_element(int a[], int n)
{
    int max = a[0];
    int i = 0;
    /*@
  loop invariant \forall integer j; 0 <= j < i ==> max >= a[j];
  loop invariant 1 <= i <= n;
  loop assigns i, max;
  loop variant n - i;
*/
    for (int i = 1; i < n; i++)
    {
        if (a[i] > max)
        {
            max = a[i];
        }
    }

    return max;
}