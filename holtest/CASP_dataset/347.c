/*@ requires \valid(p + (0..4));
  @ ensures \valid(p + (0..4));
  @*/
void validPointers(int * p) {
  *p = 1;
  return;
}