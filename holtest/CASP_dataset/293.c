/*@ requires 0 <= n <= 1000;
    ensures \result == n*n;
    assigns \nothing;
*/

int oddsum(int n) {
      int sum=0;
/*@ loop invariant 0<=i<=n;
    loop invariant sum==i*i;
    loop assigns i, sum;
    loop variant n-i;
*/
    for(int i=0;i<n;i++) {
          sum += i*2 + 1;
    }
     return sum;
}