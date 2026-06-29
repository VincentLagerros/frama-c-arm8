/*@ requires \valid(t+(0..n-1)) && 0 <= k < n;
  @ ensures \forall integer i; k <= i < n ==> \result <= t[i];
  @ assigns \nothing;
*/

int getMinSubarray(int t[], int n, int k) { 
  int res = t[k];
  /*@ loop invariant k+1 <= i <= n;
      @ loop invariant \forall integer j; k <= j < i ==> res <= t[j];
      @ loop assigns i, res;
      @ loop variant n - i;
    */	
  for (int i = k+1; i < n; i++) 
    if (t[i] < res) 
      res = t[i];
  return res;
}