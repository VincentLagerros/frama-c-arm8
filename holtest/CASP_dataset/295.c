/* run.config
   EXECNOW: make tests/aorai/Aorai_test.cmxs
   OPT: -aorai-automata tests/aorai/test_boucle_rechercheTableau.ya -aorai-test 1 -aorai-acceptance -load-module tests/aorai/Aorai_test.cmxs -aorai-test-number @PTEST_NUMBER@
*/



/*@ requires \valid(t+(0..max));
  @ requires max>=0;
  @ requires max < 2147483647;
  @ ensures 0<=\result && \result<=max || \result==-1 ;
  @ ensures 0<=\result && \result<=max ==> t[\result]==val;
  @ ensures \result==-1 ==> (\forall integer j; 0<=j<=max ==> t[j]!=val);
  @ assigns \nothing;
 */
int isPresent(int t[], int max, int val) {  
  int i=0;
  /*@ loop invariant inv :
    @      0<=i<=max+1
    @   && \valid(t+(0..max))
    @   && max>=0
    @   && (\forall integer j; 0<=j<i ==> t[j]!=val);
    @  loop assigns i;
    @  loop variant v : max-i ;
   */
  while (i<max+1 && t[i]!=val) {
    i++;
  }
  if(i<=max && t[i]==val) return i;
  return -1;
}

/*@ assigns \nothing; */
void foo(){}

/*@ assigns \nothing; */
int main(int argc, char** argv) {
  int tab[]={10,20,33,15};
  int r=isPresent(tab, 3, 33);

  if (r==-1) foo();
  
  return 1;
}