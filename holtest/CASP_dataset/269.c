/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.xluat.com/questions/31235938/java-order-by-priority-list
 *
 */

struct MyClass{
  int Name;
};

struct hack{
  int t[3];
};

/*@ assigns \result \from x,y;
  @ ensures x < y ==> \result == -1;
  @ ensures x > y ==> \result == 1;
  @ ensures x == y ==> \result == 0;
*/
int IntCompare(int x, int y){
  if (x < y){
    return -1;
  }
  if(x > y){
    return 1;
  }

  return 0;
}

/*@ assigns \result \from o1.Name, o2.Name, h.t[0..2];
  @ ensures \result == -1 || \result == 0 || \result == 1;
*/
int compare(struct MyClass o1, struct MyClass o2,struct hack h){
  int x = o1.Name;
  int y = o2.Name;
  int i = 0;

  /*@ loop invariant 0 <= i <= 3;
      loop invariant \forall integer k; 0 <= k < i ==> h.t[k] != x && h.t[k] != y;
      loop invariant \forall integer k; 0 <= k < 3 ==> h.t[k] == \at(h.t[k],LoopEntry);
      loop assigns i;
      loop variant 3 - i;
  */
  while(i < 3){
    /*@ assert \forall integer k; 0 <= k < i ==> h.t[k] != x && h.t[k] != y; */
    if(h.t[i] == x) {
      return 1;
    }
    if(h.t[i] == y) {
      return -1;
    }
    i++;
  }
  return IntCompare(x,y);
}