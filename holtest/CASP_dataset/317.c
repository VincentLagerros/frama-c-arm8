/*@
  requires x >= 0 && x <= __INT_MAX__ - 1;
  ensures \result == x + 1;
  assigns \nothing;
*/
int foo(int x) {
  return x+1;
}