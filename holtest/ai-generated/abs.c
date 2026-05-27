/*@
  @ requires val > -2147483648; // Precondition: Prevent overflow when negating INT_MIN
  @ assigns \nothing;           // Side effects: This function does not modify any global state
  @
  @ behavior positive:
  @   assumes val >= 0;
  @   ensures \result == val;
  @
  @ behavior negative:
  @   assumes val < 0;
  @   ensures \result == -val;
  @
  @ complete behaviors;         // Evaluates all possible inputs
  @ disjoint behaviors;         // Behaviors do not overlap
  @*/
int absolute_value(int val) {
    if (val < 0) {
        return -val;
    }
    return val;
}