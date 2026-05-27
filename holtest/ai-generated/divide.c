/*@
  @ requires denominator != 0;                // Precondition: Math safety (No division by zero)
  @ requires \valid(quotient) && \valid(rem); // Precondition: Output targets must be valid memory
  @ requires \separated(quotient, rem);       // Precondition: Output targets must not overlap
  @
  @ assigns *quotient, *rem;                  // Side effects: Modifies both pointed-to values
  @
  @ ensures *quotient == numerator / denominator;
  @ ensures *rem == numerator % denominator;
  @*/
void divide(int numerator, int denominator, int *quotient, int *rem) {
    *quotient = numerator / denominator;
    *rem = numerator % denominator;
}