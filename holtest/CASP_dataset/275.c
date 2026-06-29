/*@ requires \valid_read(t+(0..tt-1)) && tt>0;
    requires \valid_read(s+(0..ts-1)) && ts>0;
    requires \valid(r+(0..tt+ts-1));
    requires 0<tt<100;
    requires 0<ts<100;
    requires \separated(t+(0..tt-1), s+(0..ts-1), r+(0..tt+ts-1));
    ensures \forall integer i; 0<=i<tt ==> r[i]==t[i];
    ensures \forall integer j; 0<=j<ts ==> r[j+tt]==s[j];
    assigns r[0..tt+ts-1];
*/
void concat(int t[], int tt, int s[], int ts, int r[]){
  /*@ loop invariant 0<=i<=tt;
      loop invariant \forall integer j; 0<=j<i ==> r[j]==t[j];
      loop assigns i, r[0..tt+ts-1];
      loop variant tt-i;
  */
  for(int i=0;i<tt;i++){
    /*@ assert \forall integer j; 0<=j<i ==> r[j]==t[j]; */
    r[i]=t[i];
  }
  /*@ loop invariant 0<=i<=ts;
      loop invariant \forall integer j; 0<=j<tt ==> r[j]==t[j];
      loop invariant \forall integer j; 0<=j<i ==> r[j+tt]==s[j];
      loop assigns i, r[0..tt+ts-1];
      loop variant ts-i;
  */
  for(int i=0;i<ts;i++){
    /*@ assert \forall integer j; 0<=j<tt ==> r[j]==t[j]; */
    r[i+tt]=s[i];
  }
}