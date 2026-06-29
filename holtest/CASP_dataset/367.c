/*@ axiomatic GCD {
  logic integer GCD(integer x, integer y);
  axiom gcd_pos:
    \forall integer x, y; x > 0 && y > 0 ==> GCD(x, y) > 0;
  axiom gcd_recursive:
    \forall integer x, y; x > 0 && y > 0 ==> GCD(x, y) == (x == y ? x : (x > y ? GCD(x - y, y) : GCD(x, y - x)));
}*/

/*@ requires x > 0 && y > 0;
  @ ensures \result == GCD(x,y);
  @ assigns \nothing;
*/
int gcd(int x, int y){
  int a = x;
  int b = y;
  /*@ loop assigns a,b;
    @ loop invariant a > 0;
    @ loop invariant b > 0;
    @ loop invariant GCD(a,b) == GCD(x,y);
    @ loop variant a*b;
*/
  while(a != b){
    if(a > b){
      a = a - b;
    }
    else{
      b = b - a;
    }
  }
  return a;
}