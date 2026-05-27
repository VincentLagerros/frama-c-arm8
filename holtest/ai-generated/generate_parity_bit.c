/*@ 
  @ // Predicate calculating if the total number of set bits is even
  @ predicate has_even_parity(integer b0, integer b1, integer b2, integer b3) = 
  @   ((b0 + b1 + b2 + b3) % 2 == 0);
  @*/

/*@
  @ // Precondition: Each input argument must strictly represent a individual binary bit
  @ requires (bit0 == 0 || bit0 == 1) && 
  @          (bit1 == 0 || bit1 == 1) && 
  @          (bit2 == 0 || bit2 == 1) && 
  @          (bit3 == 0 || bit3 == 1);
  @
  @ assigns \nothing;
  @
  @ // Postcondition: The resulting verification bit creates perfect even parity across the block
  @ ensures has_even_parity(bit0, bit1, bit2, bit3) ==> \result == 0;
  @ ensures !has_even_parity(bit0, bit1, bit2, bit3) ==> \result == 1;
  @*/
int generate_parity_bit(int bit0, int bit1, int bit2, int bit3) {
    // Branchless XOR sequence computing parity flag
    return bit0 ^ bit1 ^ bit2 ^ bit3;
}