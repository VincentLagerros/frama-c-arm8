/*@
  @ requires current_state == 0 || current_state == 1; // Precondition: State must be valid (0 or 1)
  @
  @ assigns \nothing;
  @
  @ behavior turn_off:
  @   assumes current_state == 1;
  @   ensures \result == 0;
  @
  @ behavior turn_on:
  @   assumes current_state == 0;
  @   ensures \result == 1;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int toggle_state(int current_state) {
    if (current_state == 1) {
        return 0;
    }
    return 1;
}