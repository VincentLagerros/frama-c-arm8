/*@ requires n>=0 && \valid(t+(0..n-1));
    ensures \result != 0 <==> (\forall integer j; 0 <= j < n ==> t[j] == 0);
*/
int all_zeros(int t[], int n) {
  int k;
  /*@ loop invariant 0 <= k <= n;
      loop invariant \forall integer j; 0 <= j < k ==> t[j] == 0;
      loop assigns k;
      loop variant n-k; 
  */
  for(k = 0; k < n; k++) 
    if (t[k] != 0) 
      return 0;
  return 1;
}