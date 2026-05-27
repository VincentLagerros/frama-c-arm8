/*@
  @ requires \valid(reg_a) && \valid(reg_b) && \valid(reg_c);
  @ requires \separated(reg_a, reg_b, reg_c);
  @
  @ assigns *reg_a, *reg_b, *reg_c;
  @
  @ // Behavior 1: Complete Pipeline Success
  @ behavior pipeline_success:
  @   assumes fault_mask == 0x00;
  @   ensures *reg_a == \old(*reg_a) + 1;
  @   ensures *reg_b == \old(*reg_b) + 2;
  @   ensures *reg_c == \old(*reg_c) + 3;
  @   ensures \result == 0;
  @
  @ // Behavior 2: Stage B Fault (Rollback Stage A to its pristine state)
  @ behavior stage_b_fault:
  @   assumes fault_mask == 0x02;
  @   ensures *reg_a == \old(*reg_a); // Strict rollback identity
  @   ensures *reg_b == -1;            // Error flag injected
  @   ensures *reg_c == \old(*reg_c); // Left untouched
  @   ensures \result == -2;
  @
  @ // Behavior 3: Stage C Fault (Rollback Stage A and Stage B to pristine states)
  @ behavior stage_c_fault:
  @   assumes fault_mask == 0x04;
  @   ensures *reg_a == \old(*reg_a);
  @   ensures *reg_b == \old(*reg_b); // Cascading rollback
  @   ensures *reg_c == -1;
  @   ensures \result == -3;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int execute_fault_pipeline(int *reg_a, int *reg_b, int *reg_c, unsigned char fault_mask) {
    int orig_a = *reg_a;
    int orig_b = *reg_b;

    // Execute Stage A
    *reg_a = *reg_a + 1;

    // Check for Stage B fault
    if (fault_mask & 0x02) {
        *reg_a = orig_a; // Rollback
        *reg_b = -1;
        return -2;
    }

    // Execute Stage B
    *reg_b = *reg_b + 2;

    // Check for Stage C fault
    if (fault_mask & 0x04) {
        *reg_a = orig_a; // Cascading Rollback
        *reg_b = orig_b; // Cascading Rollback
        *reg_c = -1;
        return -3;
    }

    // Execute Stage C
    *reg_c = *reg_c + 3;
    return 0;
}