/* run.config
   COMMENT: test option -e-acsl-functions
   LOG: gen_@PTEST_NAME@.c
   OPT: -machdep gcc_x86_64 -e-acsl-functions f -e-acsl -then-last -load-script tests/print.cmxs -print -ocode tests/special/result/gen_@PTEST_NAME@.c -kernel-verbose 0 -eva-verbose 0 -eva -wp-rte
*/

/*@ requires \valid(p);
  @ requires *p == 0;
  @ ensures \result == 0;
  @ assigns \nothing; */
int f(int *p) {
  /*@ loop invariant 0 <= i <= 1;
      loop assigns i;
      loop variant 1 - i; */
  for(int i = 0; i < 1; i++) ;
  return 0;
}

/*@ requires \valid(p);
  @ requires *p == 1;
  @ ensures \result == 0;
  @ assigns \nothing; */
int g(int *p) {
  /*@ loop invariant 0 <= i <= 1;
      loop assigns i;
      loop variant 1 - i; */
  for(int i = 0; i < 1; i++) ;
  return 0;
}

/*@ assigns \nothing; */
int main(void) {
  int x = 0;
  int y = 1;
  f(&x);
  g(&y);
}