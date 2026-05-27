/*@
  @ requires \valid(a) && \valid(b); // Precondition: Pointers must be valid and readable/writable
  @ requires \separated(a, b);       // Precondition: The memory locations must not overlap
  @ 
  @ assigns *a, *b;                  // Side effects: Specifies exactly which memory locations change
  @
  @ ensures *a == \old(*b);          // Postcondition: *a now holds the original value of *b
  @ ensures *b == \old(*a);          // Postcondition: *b now holds the original value of *a
  @*/
void swap(int *a, int *b) {
    int temp = *a;
    *a = *b;
    *b = temp;
}