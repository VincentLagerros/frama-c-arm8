int m = 0;
int t[10];
int *q = &m;

/*@ requires *p <= 100 && *p >= -100 && \valid(p);
    ensures \result == \old(*p)+ 1;
*/
int incr(int *p)
{
  q = p;
  *p = *p + 1;   
  return *p;
}