#include <stdint.h>
#include <limits.h>
#include <string.h>
/*@ 
    requires \valid(x+(10..20));
*/ 
uint64_t s(uint64_t * x) {
    return x[10];
}