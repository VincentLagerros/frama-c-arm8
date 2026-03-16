#include <stdint.h>

/*@ 
    ensures \result == x || \result == y; 
    ensures \result >= x;
    ensures \result >= y; 
    assigns \nothing;
*/ 
int64_t max(int64_t x, int64_t y) {
    if (x > y) {
        return x; 
    } else {
        return y;
    }
}

/*@
    requires x < INT64_MAX;
    ensures \result == x + 1; 
*/
int64_t inc(int64_t x) {
    return x + 1;
}

/*@
    ensures \result == x + 1; 
*/
int64_t incorrect_inc(int64_t x) {
    return x + 1;
}


/*@
    ensures x + 1 <= INT64_MAX; 
*/
int64_t test_invalid(int64_t x) {
    return x + 1;
}

/*@ 
    assigns \nothing;
*/
int main() {
	return max(1,2);
}
