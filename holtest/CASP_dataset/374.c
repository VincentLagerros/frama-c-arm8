/* run.config
   OPT: -rpp
*/

/*@ requires \valid(t+(0..n-1));
  @ requires n >= 1;
  @ requires \forall integer k; 0 <= k < n ==> 0 <= t[k];
  @ ensures \forall integer k; 0 <= k < n ==> \result >= t[k];
  @ ensures \exists integer k; 0 <= k < n && \result == t[k];
  @ assigns \nothing;
*/
int f(int t[], int n){
  int max = t[0];
  int i = 0;
  /*@ loop assigns i,max;
    @ loop invariant 0 <= i <= n;
    @ loop invariant \forall integer k; 0 <= k < i ==> max >= t[k];
    @ loop invariant \exists integer k; 0 <= k < n && max == t[k];
    @ loop variant n-i;
  */
  while(i < n){
    if(t[i] > max){
      max = t[i];
    }
    i++;
  }
 return max;
}
