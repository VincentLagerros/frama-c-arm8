/*@
  @ // Precondition: Ensure both 2x2 blocks are fully readable and writable
  @ requires \valid(matrix + offset_a) && \valid(matrix + offset_a + 1);
  @ requires \valid(matrix + offset_a + 4) && \valid(matrix + offset_a + 5);
  @ requires \valid(matrix + offset_b) && \valid(matrix + offset_b + 1);
  @ requires \valid(matrix + offset_b + 4) && \valid(matrix + offset_b + 5);
  @
  @ // Postconditions: Verify cross-swapping of all four individual discrete cells
  @ ensures matrix[offset_a]     == \old(matrix[offset_b])     && matrix[offset_b]     == \old(matrix[offset_a]);
  @ ensures matrix[offset_a + 1] == \old(matrix[offset_b + 1]) && matrix[offset_b + 1] == \old(matrix[offset_a + 1]);
  @ ensures matrix[offset_a + 4] == \old(matrix[offset_b + 4]) && matrix[offset_b + 4] == \old(matrix[offset_a + 4]);
  @ ensures matrix[offset_a + 5] == \old(matrix[offset_b + 5]) && matrix[offset_b + 5] == \old(matrix[offset_a + 5]);
  @*/
void swap_sub_blocks_2x2(int *matrix, int offset_a, int offset_b) {
    int temp;
    
    // Swap Row 1 elements
    temp = matrix[offset_a]; matrix[offset_a] = matrix[offset_b]; matrix[offset_b] = temp;
    temp = matrix[offset_a + 1]; matrix[offset_a + 1] = matrix[offset_b + 1]; matrix[offset_b + 1] = temp;
    
    // Swap Row 2 elements (assuming a row stride of 4 elements)
    temp = matrix[offset_a + 4]; matrix[offset_a + 4] = matrix[offset_b + 4]; matrix[offset_b + 4] = temp;
    temp = matrix[offset_a + 5]; matrix[offset_a + 5] = matrix[offset_b + 5]; matrix[offset_b + 5] = temp;
}