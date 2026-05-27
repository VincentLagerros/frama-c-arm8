/*@
  @ requires \valid(instruction_reg) && \valid(payload_reg);
  @ requires \separated(instruction_reg, payload_reg);
  @
  @ assigns *instruction_reg, *payload_reg;
  @
  @ // Behavior 1: Unverified state triggers aggressive sanitization overrides
  @ behavior untrusted_sandbox:
  @   assumes security_level == 0;
  @   ensures *instruction_reg == 0x00; // Forcefully map execution to a Safe NOP instruction
  @   ensures *payload_reg     == 0;    // Completely purge potentially hostile payload data
  @   ensures \result          == -1;   // Return error alert status
  @
  @ // Behavior 2: Verified state allows controlled processing based on instruction thresholds
  @ behavior trusted_execution_normal:
  @   assumes security_level != 0 && *instruction_reg < 128;
  @   ensures *instruction_reg == \old(*instruction_reg); // Retain the instruction safely
  @   ensures *payload_reg     == \old(*payload_reg) * 2;  // Perform standard trusted shift calculation
  @   ensures \result          == 0;
  @
  @ // Behavior 3: Over-threshold instructions are safely clamped even when trusted
  @ behavior trusted_execution_clamp:
  @   assumes security_level != 0 && *instruction_reg >= 128;
  @   ensures *instruction_reg == 127;                    // Clamp instructions inside bounds
  @   ensures *payload_reg     == \old(*payload_reg);
  @   ensures \result          == 1;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int enforce_sandbox_policy(int *instruction_reg, int *payload_reg, int security_level) {
    if (security_level == 0) {
        *instruction_reg = 0x00;
        *payload_reg = 0;
        return -1;
    }
    
    if (*instruction_reg >= 128) {
        *instruction_reg = 127;
        return 1;
    }
    
    *payload_reg = *payload_reg * 2;
    return 0;
}