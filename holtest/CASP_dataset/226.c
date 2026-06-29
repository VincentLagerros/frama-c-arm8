/*@
  requires x >= 0;
  ensures \result == x;
  assigns \nothing;
*/
int foo(int x) {
  return x;
}