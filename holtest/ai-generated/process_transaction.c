/*@
  @ requires \valid(live_buffer) && \valid(scratchpad) && \valid(old_state);
  @ requires \separated(live_buffer, scratchpad, old_state);
  @
  @ assigns *live_buffer, *scratchpad, *old_state;
  @
  @ // Behavior 1: The transaction succeeds, staging data and altering the live buffer
  @ behavior transaction_commit:
  @   assumes status_flag == 1;
  @   ensures *live_buffer == \old(*scratchpad) + 5;
  @   ensures *old_state   == \old(*live_buffer);
  @   ensures *scratchpad  == 0;
  @
  @ // Behavior 2: The transaction fails, triggering a strict restoration fallback
  @ behavior transaction_abort:
  @   assumes status_flag != 1;
  @   ensures *live_buffer == \old(*live_buffer); // Explicit isolation guarantee
  @   ensures *scratchpad  == \old(*scratchpad);
  @   ensures *old_state   == \old(*old_state);
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void process_transaction(int *live_buffer, int *scratchpad, int *old_state, int status_flag) {
    if (status_flag == 1) {
        // Back up original live state
        *old_state = *live_buffer;
        
        // Commit scratchpad data with transformation logic
        *live_buffer = *scratchpad + 5;
        
        // Clear scratchpad
        *scratchpad = 0;
    } else {
        // Explicit Abort/Rollback: Ensure memory states are physically preserved
        // (Even though nothing changes, the code matches the contract's identity guarantee)
        return;
    }
}