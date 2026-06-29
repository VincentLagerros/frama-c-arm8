/*@ requires x > -2147483648; 
  @ ensures \result >= 0;
  @ ensures \result == x || \result == -x; 
  @ assigns \nothing; 
  @*/
int abs(int x) {
  if (x >= 0) return x;
  return -x;
}