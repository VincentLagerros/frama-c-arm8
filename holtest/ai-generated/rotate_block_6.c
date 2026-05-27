/*@
  @ // Precondition: Array must be fully valid and hold at least 6 elements
  @ requires \valid(arr+(0..5));
  @
  @ assigns arr[0 .. 5];
  @
  @ // Postconditions: Complete validation of structural 3-block rotation matching
  @ ensures arr[0] == \old(arr[3]) && arr[1] == \old(arr[4]) && arr[2] == \old(arr[5]);
  @ ensures arr[3] == \old(arr[0]) && arr[4] == \old(arr[1]) && arr[5] == \old(arr[2]);
  @*/
void rotate_block_6(int *arr) {
    // Step 1: Swap Element 0 and Element 3
    int temp0 = arr[0];
    arr[0] = arr[3];
    arr[3] = temp0;

    // Step 2: Swap Element 1 and Element 4
    int temp1 = arr[1];
    arr[1] = arr[4];
    arr[4] = temp1;

    // Step 3: Swap Element 2 and Element 5
    int temp2 = arr[2];
    arr[2] = arr[5];
    arr[5] = temp2;
}