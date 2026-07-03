#include "limits.h"
/*@ requires INT_MIN < min < max && min <= timer <= max < INT_MAX;
    assigns \nothing;
    ensures
      (cond == 0 ==> \result == \max(min, \old(timer) - 1)) &&
      (cond != 0 ==> \result == \min(max, \old(timer) + 1)); */
int update_sat(int cond, int timer, int min, int max) {
  int res = timer;
  if (cond) {res += 1;} else {res -= 1;}
  if (res > max) res = max;
  if (res < min) res = min;
  return res;
}