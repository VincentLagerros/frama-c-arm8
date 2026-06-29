#include <limits.h>
/* run.config
   EXECNOW: make -s tests/aorai/Aorai_test.cmxs
   OPT: -aorai-automata tests/aorai/test_acces_params.ya -aorai-test 1 -load-module tests/aorai/Aorai_test.cmxs -aorai-test-number @PTEST_NUMBER@
*/

int status=0;
int rr=1;
//@ global invariant inv : 0<=rr<=5000;

/*@ requires rr<5000 && i >= INT_MIN - j && i <= INT_MAX - j;
  @ assigns rr;
  @ ensures rr == i + j;
  @*/
void opa(int i, int j) {
  rr=i+j;
}


/*@ assigns status, \result;
  @ ensures \result == 3;
 */
int opb () {
  status=1;
  return status*3;
}

/*@ assigns rr, status;
 */
int main(){

  //@ assert rr < 5000;
  if (rr<5000) opa(rr,300);
  rr=opb();

  return 0;
}