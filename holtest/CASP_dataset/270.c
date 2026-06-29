/*@ requires n>0;
    requires \valid(t+(0..n-1));
    assigns t[0..n-1];
    ensures \forall integer i; 0<=i<n ==> t[i] == i ;
    ensures \forall integer i; 0<=i<n-1 ==> t[i] <= t[i+1];
*/
 
int doubleint(int t[],int n) {
/*@ loop invariant 0<=i<=n;
    loop invariant \forall integer j; 0<=j<i ==> t[j] == j ;
    loop assigns i, t[0..n-1];
    loop variant n-i;
*/
       for(int i=0;i<n;i++) {
          t[i]=i;
       }
       return 0; 
 }