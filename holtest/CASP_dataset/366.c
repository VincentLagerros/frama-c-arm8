int x;


//@ predicate p(integer n) = n > 0 ;

//@ predicate p_array(int t[]) = t[0];

/*@ axiomatic Q {
  @   predicate q(int t[]);
  @   
  @   axiom q_ax: \forall int t[]; t[0] == 0 ==> q(t);
  @ }  @*/

/*@ assigns x; */
void f() {
  /*@ ghost */ int i = 0;

  /*@ loop assigns i; 
      loop invariant i >= 0;
      loop variant 100 - i;
   */
  for (;;) {
    if(i > 99) break;
    i++;
  }

  /*@ ghost */ i = 0;

  /*@ loop assigns x, i; 
      loop invariant i >= 0;
      loop variant 100 - i;
   */
  for(;;) {
    L2: x = 0;
    if(i > 99) break;
    i++;
  }

 L1: x = 0;
}