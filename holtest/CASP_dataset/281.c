/*@ requires 0 <= n <= 1000;
    ensures \result == n*(n-1)/2;
*/
int sum(int n){
  int res=0;

  /*@ loop invariant 0<=i<=n;
      loop invariant res == i*(i-1)/2;
      loop assigns res, i;
      loop variant n-i;
  */
  for(int i=0;i<n;i++) {
    res+=i;
  }
  return res;
}