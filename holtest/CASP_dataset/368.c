/*@ requires \valid(t+(0..n-1)) && n>0;
    ensures 0<=\result<n;
    ensures \forall integer i; 0<=i<n ==> t[\result] <= t[i];
*/
int minIndex(int t[], int n){
  int index=0;

  /*@ loop invariant 0<=i<=n;
      loop invariant 0<=index<n;
      loop invariant \forall integer j; 0<=j<i ==> t[index] <= t[j];
      loop assigns index,i;
      loop variant n-i;
  */
  for(int i=0;i<n;i++){
    if(t[i]<t[index]) {
      index=i;
    }
  }
  return index;
}