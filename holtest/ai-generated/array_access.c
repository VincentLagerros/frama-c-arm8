/*@
  @ requires \valid_read(array + index); // Precondition: The specific element must be readable
  @ requires index >= 0 && index < 4;   // Precondition: Explicit bounds check for a size-4 array
  @
  @ assigns \nothing;
  @
  @ ensures \result == array[index];    // Postcondition: Returns the exact value at that index
  @*/
int get_element_4(const int *array, int index) {
    return array[index];
}