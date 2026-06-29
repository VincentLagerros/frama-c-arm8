/*@
 requires 0 < n;
 requires \valid(a+(0..n-1));
 assigns a[0..n-1];
 ensures  \forall integer i; 0 <= i < n ==> a[i] == 0;
*/
void array_zero(int* a, int n){
 /*@ loop invariant 0 <= i <= n && (\forall integer k; 0 <= k < i ==> a[k] == 0);
     loop assigns a[0..n-1], i;
     loop variant n-i;
 */
 for(int i = 0;i< n;i++){
  a[i]=0;
 }
}