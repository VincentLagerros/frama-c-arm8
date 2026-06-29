/* run.config
   EXECNOW: make tests/aorai/Aorai_test.cmxs
   OPT: -aorai-ltl tests/aorai/test_boucle.ltl -aorai-test 1 -aorai-acceptance -load-module tests/aorai/Aorai_test.cmxs -aorai-test-number @PTEST_NUMBER@
*/

/*@ requires \true;
  @ ensures 0<=\result<=1;
  @ assigns \nothing;
*/
int a() {
  return 1;
}

/*@ requires \true;
  @ ensures 1<=\result<=2;
  @ assigns \nothing;
*/
int b() {
  //call_to_an_undefined_function(); 
  return 2;
}

/*@ requires \true;
  @ ensures 0<=\result<=1;
  @ assigns \nothing;
*/
int main(){
  int x=a();
  /*@ loop invariant 0<=x<=12;
      loop assigns x;
      loop variant 10-x;
   */
  while (x<10) {
    x+=b();
  }
  return a();
}
