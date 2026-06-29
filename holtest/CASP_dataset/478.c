/*@ axiomatic abs {
  @   logic int abs(int x);
  @   axiom pos: \forall int x; x >= 0 ==> abs(x) == x;
  @   axiom neg: \forall int x; x <= 0 ==>  abs(x) == -x;
  @ }
*/

/*@ ensures \result == abs(x); 
  @ assigns \nothing;
*/
int abs(int x);

/*@ ensures (\result == x || \result == y)
  @       && \result >= x && \result >= y; 
  @ assigns \nothing;
*/
int max(int x, int y);

/*@ ensures \result >= 0;
  @ assigns \nothing;
*/
int max_abs(int x, int y) {
  x = abs(x);
  y = abs(y);
  return max(x, y);
}
