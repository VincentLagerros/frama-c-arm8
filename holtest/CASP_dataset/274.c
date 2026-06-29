#include <limits.h>
/*@
  requires INT_MIN <= a - b <= INT_MAX;
  ensures (\result == a - b);
  assigns \nothing;
*/
int sub(int a,int b)
{
  int diff =  a - b;
  return diff;
}
/*@ assigns \nothing; */
int main(void)
{
   int a = 7;
   int b = 6;
   sub(a,b);
   return 0;
}