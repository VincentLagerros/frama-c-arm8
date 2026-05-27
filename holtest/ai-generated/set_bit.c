/*@
  @ requires index >= 0 && index < 32; // Precondition: Prevent undefined behavior from over-shifting
  @
  @ assigns \nothing;
  @
  @ ensures \result == (value | (1U << index)); // Postcondition: Ensures the target bit is set to 1
  @*/
unsigned int set_bit(unsigned int value, int index) {
    return value | (1U << index);
}