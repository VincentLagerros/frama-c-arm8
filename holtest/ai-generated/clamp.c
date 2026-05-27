/*@
  @ requires low <= high;          // Precondition: The range must be mathematically valid
  @
  @ assigns \nothing;
  @
  @ behavior below_range:
  @   assumes val < low;
  @   ensures \result == low;
  @
  @ behavior above_range:
  @   assumes val > high;
  @   ensures \result == high;
  @
  @ behavior within_range:
  @   assumes val >= low && val <= high;
  @   ensures \result == val;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int clamp(int val, int low, int high) {
    if (val < low)  return low;
    if (val > high) return high;
    return val;
}