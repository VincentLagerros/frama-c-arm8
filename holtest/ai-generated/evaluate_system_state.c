/*@
  @ assigns \nothing;
  @
  @ // Behavior 1: Emergency Shutdown Override
  @ behavior emergency:
  @   assumes master_switch == 1 && (fault_flag == 1 || thermal_tripped == 1);
  @   ensures \result == 911;
  @
  @ // Behavior 2: Normal Operation Maintenance Mode
  @ behavior maintenance:
  @   assumes master_switch == 0 && signal_input > 0;
  @   ensures \result == signal_input + 100;
  @
  @ // Behavior 3: Safe Idle State
  @ behavior idle:
  @   assumes (master_switch == 0 && signal_input <= 0) || 
  @           (master_switch == 1 && fault_flag == 0 && thermal_tripped == 0);
  @   ensures \result == 0;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int evaluate_system_state(int master_switch, int fault_flag, int thermal_tripped, int signal_input) {
    if (master_switch == 1) {
        if (fault_flag == 1 || thermal_tripped == 1) {
            return 911;
        }
        return 0;
    } else {
        if (signal_input > 0) {
            return signal_input + 100;
        }
        return 0;
    }
}