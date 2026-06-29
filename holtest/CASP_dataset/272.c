#pragma CIVL ACSL
enum t{RED, BLUE};

/*@ requires \valid_read(a) && *a==BLUE;
  @ ensures \result == 2;
  @ assigns \nothing;
  @*/
int f(enum t* a){
  return (*a)*2;
}