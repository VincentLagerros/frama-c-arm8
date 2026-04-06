#include <stdint.h>
#include <limits.h>
#include <string.h>
/*@ 
    ensures \result == x || \result == y; 
    ensures \result >= x;
    ensures \result >= y; 
    assigns \nothing;
*/ 
int max2(int x, int y) {
    if (x > y) {
        return x; 
    } else {
        return y;
    }
}

/*@ logic integer my_max(integer a, integer b) = a >= b ? a : b; */
/*@ 
    ensures \result == my_max(x, w); 
*/ 
int bitneg(int x, int w) {
    if (x > w) {
        return x;
    } else {
        return w;
    }
}

// /*@
//     requires \valid(p);
//     requires \valid(q);
// 
//     assigns \nothing;
//     
//     ensures (\result == *p) || (\result == *q);
//     
//     ensures \result >= *p;
//     ensures \result >= *q;
// */
// int max_ptr(int* p, int* q) {
//     if (*p >= *q) {
//         return *p;
//     } else {
//         return *q;
//     }
// }