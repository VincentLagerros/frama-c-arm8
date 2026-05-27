/*@
  @ requires \valid(left) && \valid(right);
  @ requires \separated(left, right);
  @ 
  @ // Precondition: Ensure key inputs don't lead to undefined behavior when shifting
  @ requires shift_amount >= 0 && shift_amount < 32;
  @
  @ assigns *left, *right;
  @
  @ // Postcondition: Left becomes the old right unmodified
  @ ensures *left == \old(*right);
  @
  @ // Postcondition: Right is mixed with the Feistel function output
  @ ensures *right == (\old(*left) ^ 
  @                    (((\old(*right) << shift_amount) | (\old(*right) >> (32 - shift_amount))) ^ 
  @                     (~(\old(*right) & secret_key))));
  @*/
void feistel_round(unsigned int *left, unsigned int *right, unsigned int secret_key, int shift_amount) {
    unsigned int old_left = *left;
    unsigned int old_right = *right;

    // F-Function: A combination of bitwise rotation, masking, and inversion
    unsigned int f_output = ((old_right << shift_amount) | (old_right >> (32 - shift_amount))) ^ (~(old_right & secret_key));

    // Feistel state transformation matrix
    *left = old_right;
    *right = old_left ^ f_output;
}