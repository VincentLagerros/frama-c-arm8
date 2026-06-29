/*@ requires \valid(a) && \valid(b);
  @ ensures *a == \old(*b);
  @ ensures *b == \old(*a);
  @*/
void swap(int* a, int* b) {
  int temp = *a;
  *a = *b;
  *b = temp;
}