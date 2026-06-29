#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
int A, B, C;
#pragma GCC diagnostic pop

/*@ requires A==100 && B==100;
    assigns A,B;
    ensures C==0 ==> A==100 && B==100;
    ensures C!=0 ==> A==C && B==C;*/
void bidon(){
  if ( C != 0 ){
    A = C;
    B = C;
  }
}

/*@ requires \valid ( t +(0.. n -1)) && n >= 0;
  @ assigns \nothing;
  @ ensures \result == 1 <==> ( \forall integer i ; 0 <= i < n ==> t [ i ] == 0);
  @ ensures \result == 0 <==> ( \exists integer i ; 0 <= i < n && t [ i ] != 0);
  @*/
int all_zeros(int t[], int n) {
  int k;
  /*@ loop invariant 0 <= k <= n;
      @ loop invariant \forall integer i ; 0 <= i < k ==> t [ i ] == 0;
      @ loop assigns k;
      @ loop variant n-k;
   */
  for(k = 0; k < n; k++) {
    //@ assert 0 <= k < n;
    if (t[k] != 0)
      return 0;
  }
    //@ assert k == n;
  return 1;
}
