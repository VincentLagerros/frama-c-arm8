#include <limits.h>

/*@
  @ assigns \nothing;
  @
  @ // Behavior where multiplication is perfectly safe within standard 32-bit limits
  @ behavior safe_zone:
  @   assumes (int)((long long)a * b) == (long long)a * b; 
  @   ensures \result == a * b;
  @
  @ // Behavior tracking upper overflow using mathematical logic
  @ behavior upper_overflow:
  @   assumes ( \let prod = a * b; prod > INT_MAX );
  @   ensures \result == INT_MAX;
  @
  @ // Behavior tracking lower underflow using mathematical logic
  @ behavior lower_underflow:
  @   assumes ( \let prod = a * b; prod < INT_MIN );
  @   ensures \result == INT_MIN;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int saturated_multiply(int a, int b) {
    long long long_prod = (long long)a * b;
    if (long_prod > INT_MAX) {
        return INT_MAX;
    }
    if (long_prod < INT_MIN) {
        return INT_MIN;
    }
    return a * b;
}