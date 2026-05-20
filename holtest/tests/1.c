#include <stdint.h>

// Stack check, can we use 7+ args

/*@ 
    requires \true;
    ensures \result == x9;
*/ 
uint64_t swap(uint64_t x0,uint64_t x1,uint64_t x2,uint64_t x3,uint64_t x4,uint64_t x5,uint64_t x6,uint64_t x7,uint64_t x8,uint64_t x9) {
  return x9;
}