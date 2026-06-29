/*@ requires \valid(t+(0..n-1)) && n > 0;
  @ ensures  (\forall integer i; 0 <= i < n ==> \result <= t[i]) &&
  @   (\exists integer i; 0 <= i < n && \result == t[i]); 
  @ assigns \nothing;
*/

int getMin(int t[], int n) { 
  int res = t[0]; 
  /*@ loop invariant 1 <= i <= n &&
    @   (\forall integer j; 0 <= j < i ==> res <= t[j]) &&
    @   (\exists integer j; 0 <= j < i && res == t[j]); 
    @ loop assigns i, res;
    @ loop variant n - i;
    @*/
  for (int i = 1; i < n; i++) 
  {
    if (t[i] < res) 
      res = t[i];
  }
  return res;
}

