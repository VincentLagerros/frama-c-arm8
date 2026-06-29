/*@ requires n >= 0 && 0 <= n1 < n && 0 <= n2 < n;
    requires \valid(a+(0..n-1));
    ensures (a[n1] == \old(a[n2]) && a[n2] == \old(a[n1]));
*/
void array_swap(int n, int a[], int n1, int n2)
{
  int tmp;
  tmp = a[n1]; a[n1] = a[n2]; a[n2] = tmp;
}

