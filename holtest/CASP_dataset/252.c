/*@ requires \true;
  @ behavior x_ge_y:
  @   assumes x >= y;
  @   ensures \result == x;
  @ behavior x_lt_y:
  @   assumes x < y;
  @   ensures \result == y;
  @ complete behaviors x_ge_y, x_lt_y;
  @ disjoint behaviors x_ge_y, x_lt_y;
  @*/
int max (int x, int y) {
  if (x >= y) {
    return x;
  } else {
    return y;
  }
}