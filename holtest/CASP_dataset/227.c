/*@ requires n <= 2147483646;
  ensures \result == \old(n) + 1 ;
 assigns \nothing; */

int incr(int n)
{
  return n+1;
};