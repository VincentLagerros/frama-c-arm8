/* run.config
   EXECNOW: make tests/aorai/Aorai_test.cmxs
   OPT: -aorai-ltl tests/aorai/test_boucle1.ltl -aorai-test 1 -aorai-acceptance -load-module tests/aorai/Aorai_test.cmxs -aorai-test-number @PTEST_NUMBER@
*/

int cpt=3;
//@ global invariant inv_cpt : 0<=cpt<=3;

int status=0;
//@ global invariant inv_status : 0<=status<=1;


/*@ requires \true;
  @ ensures 0<=\result<=1;
  @ assigns \nothing;
*/
int commit_trans() {
  return 1;
}

/*@ requires \true;
  @ ensures 0<=\result<=1;
  @ assigns \nothing;
*/
int init_trans() {
  return 1;
}

/*@ requires \true;
  @ assigns cpt, status;
  @ ensures \result == 0 || \result == 1;
*/
int main(){
  cpt=3;
  status=0;
  /*@ loop assigns status, cpt;
      loop invariant i :
    @      0<=status<=1
    @   && 0<=cpt<=3
    @   && (cpt==0 ==> status==0);
    @ loop variant cpt;
   */
  while (cpt>0) {
    status=init_trans();
    if (status && (status=commit_trans())) goto label_ok;
    cpt--;
  }
  return 0;

 label_ok:
  return 1;
}
