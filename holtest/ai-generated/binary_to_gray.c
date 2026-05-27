/*@ 
  @ // Define an abstract logic predicate that checks if the Gray code mapping rule holds true
  @ predicate is_gray_encoded(integer binary, integer gray) = 
  @   gray == (binary ^ (binary >> 1));
  @*/

/*@
  @ requires n >= 0 && n <= 2147483647; // Precondition: Within positive signed 32-bit integer limits
  @
  @ assigns \nothing;
  @
  @ // Postcondition: Evaluates the functional output directly against our abstract predicate
  @ ensures is_gray_encoded(n, \result);
  @*/
unsigned int binary_to_gray(unsigned int n) {
    return n ^ (n >> 1);
}