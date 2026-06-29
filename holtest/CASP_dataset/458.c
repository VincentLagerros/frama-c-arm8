/*@ requires n>0 && \valid(t+(0..n-1));
    ensures \forall integer i; 0<=i<n ==> t[i] == val;
*/

void fill(int t[],int val,int n) {
/*@ loop invariant 0<=i<=n;
    loop invariant \forall integer j; 0<=j<i ==> t[j] == val;
    loop variant n-i;
*/
      for(int i=0;i<n;i++) {
            t[i]=val;
      }
}