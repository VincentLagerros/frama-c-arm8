/* run.config
   OPT: -load-module lib/plugins/Report -rte -rte-precond -then -val -then -report -report-print-properties
   OPT: -load-module lib/plugins/Report -val -then -rte -rte-precond -then -report -report-print-properties
*/

// Fuse with precond.c when bts #1208 is solved
int x = 0;

/*@ requires i >= -1;
  assigns x;
  ensures x == i;
 */
void f (int i) {
  x = i;
}

/*@ requires x <= 8;
  assigns x;
  ensures x == \old(x) + 1 || x == \old(x);
 */
void g();

void g() {
  if (x < 8) {
    x++;
  }
}

/*@ requires -1 <= 8; // Ensure x <= 8 after the calls to f in the if(c) blocks.
    requires x <= 8;
    assigns x;
*/
void main (int c) {
  if (c) {
    f(1);
    if(c) f(-1);
  }
  //@ assert x <= 8;
  g ();
  //@ assert x <= 8;
  g ();
}