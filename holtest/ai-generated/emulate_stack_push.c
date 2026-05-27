/*@
  @ // Precondition: The frame tracking pointers must be fully valid layers
  @ requires \valid(stack_ptr) && \valid(*stack_ptr);
  @ 
  @ // Precondition: The stack must have room to grow forward safely
  @ requires \valid(*stack_ptr + 1);
  @ 
  @ // Precondition: Establish strict limits on the memory boundaries to prevent wrapping
  @ requires limit >= *stack_ptr;
  @
  @ assigns *stack_ptr, **stack_ptr, *(*stack_ptr + 1);
  @
  @ behavior stack_overflow:
  @   assumes *stack_ptr >= limit;
  @   assigns \nothing;
  @   ensures \result == 0;
  @
  @ behavior push_success:
  @   assumes *stack_ptr < limit;
  @   ensures *stack_ptr == \old(*stack_ptr) + 1; // Double dereference check
  @   ensures **stack_ptr == value;
  @   ensures \result == 1;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int emulate_stack_push(int **stack_ptr, int *limit, int value) {
    if (*stack_ptr >= limit) {
        return 0; // Guard against stack overflow
    }
    
    // Advance the stack pointer reference forward by one slot
    *stack_ptr = *stack_ptr + 1;
    
    // Assign the value to the brand new top of the stack
    **stack_ptr = value;
    
    return 1;
}