#include <stdint.h>
#include <stddef.h>

#define NUM_ELEMS (8)

/*@ requires expected != test;
  @ requires \let n = NUM_ELEMS;
  @          \valid_read(expected + (0.. n-1)) && \valid_read(test + (0.. n-1));
  @ assigns \nothing;
  @ behavior matches:
  @   assumes \let n = NUM_ELEMS;
  @           \forall integer i; 0 <= i < n ==> expected[i] == test[i];
  @   ensures \result == 1;
  @ behavior not_matches:
  @   assumes \let n = NUM_ELEMS;
  @           \exists integer i; 0 <= i < n && expected[i] != test[i];
  @   ensures \result == 0;
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int array_equals(const uint32_t expected[static NUM_ELEMS], const uint32_t test[static NUM_ELEMS]) {

	/*@ loop invariant \let n = NUM_ELEMS; 0 <= i <= n;
	  @ loop invariant \forall integer k; 0 <= k < i ==> expected[k] == test[k];
	  @ loop assigns i;
	  @ loop variant \let n = NUM_ELEMS; n-i;
	  @*/
	for (size_t i = 0; i < NUM_ELEMS; i++) {
		      if (expected[i] != test[i]) {
				        return 0;
						    }
			    }
	    return 1;
}
