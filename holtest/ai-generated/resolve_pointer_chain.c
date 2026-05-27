#define NULL ((void*)0)

/*@
  @ // Precondition: Level 1 and Level 2 references must always be valid
  @ requires \valid(ptr_level1) && \valid(ptr_level2);
  @ 
  @ // Precondition: The ultimate target can be valid or invalid (NULL-safe evaluation)
  @ requires val_target != \null ==> \valid(val_target);
  @ 
  @ // Precondition: Complete separation across all layers of the validation chain
  @ requires \separated(ptr_level1, ptr_level2, val_target);
  @
  @ assigns *ptr_level1, *ptr_level2;
  @
  @ behavior chain_uninitialized:
  @   assumes val_target == \null;
  @   ensures *ptr_level1 == 0 && *ptr_level2 == 0;
  @   ensures \result == -1;
  @
  @ behavior chain_fully_resolved:
  @   assumes val_target != \null;
  @   ensures *ptr_level1 == 1 && *ptr_level2 == 1;
  @   ensures \result == *val_target;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int resolve_pointer_chain(int *ptr_level1, int *ptr_level2, const int *val_target) {
    if (val_target == NULL) {
        *ptr_level1 = 0;
        *ptr_level2 = 0;
        return -1;
    } else {
        *ptr_level1 = 1;
        *ptr_level2 = 1;
        return *val_target;
    }
}