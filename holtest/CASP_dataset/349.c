/*@ requires \valid(p) && *p <= 100 && *p >= -100;
 assigns *p;
 ensures *p == \old(*p)+ 1 ;  */

int incr(int *p)
{
  *p = *p + 1;
  return *p;
};