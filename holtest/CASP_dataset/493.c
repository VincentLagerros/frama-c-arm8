/*@ requires \valid(t+(0..max));
  @ requires max>=0;
  @ assigns \nothing;
 */
int isPresent(int t[], int max, int val);

int isPresent(int t[], int max, int val) {
  return isPresentRec(t, 0, max, val);
}

/*@ requires \valid(t+(0..max));
  @ requires max>=0;
  @ requires 0<=i<=max;
  @ decreases max-i;
  @ ensures i<=\result<=max || \result==-1 ;
  @ ensures \result!=-1 ==> t[\result]==val;
  @ ensures \result==-1 ==> (\forall integer j; i<=j<=max ==> t[j]!=val);
  @ assigns \nothing;
 */
int isPresentRec(int t[], int i, int max, int val) {
  if(t[i]==val) return i;
  if(max==i) return -1;
  return isPresentRec(t, i+1, max, val);
}