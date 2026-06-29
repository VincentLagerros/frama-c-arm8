/* run.config_qualif
   OPT: -pp-annot -wp -wp-par 1 -wp-prop="-qed_ko"
   OPT: -pp-annot -wp -wp-par 1 -wp-prop qed_ko -wp-timeout 2
*/

#define OK 33
#define KO 55

int k ;
int inp[5] ;
int out[5] ;

/*@ requires 0 <= k < 5 ;
  @ ensures \result == out[\old(k)] ; 
  @ ensures inp[\old(k)] == u;
  @ ensures k == \old(k)+1 ;
  @ assigns k,inp[k] ;
  @ */
int g(int u);

/*@ requires k == 0 ;
  @ assigns k, inp[0], inp[1];
  @ behavior FST_FAIL:
  @   assumes out[0] != OK ;
  @   ensures k == 1 ;
  @   ensures inp[0] == a ;
  @   ensures \result == KO ;
  @ behavior SND_FAIL:
  @   assumes out[0] == OK ;
  @   assumes out[1] != OK ;
  @   ensures k == 2 ;
  @   ensures inp[0] == a ;
  @   ensures inp[1] == b ;
  @   ensures \result == KO ;
  @ behavior SUCCESS:
  @   assumes out[0] == OK ;
  @   assumes out[1] == OK ;
  @   ensures k == 2 ;
  @   ensures inp[0] == a ;
  @   ensures inp[1] == b ;
  @   ensures \result == OK ;
  @ complete behaviors FST_FAIL, SND_FAIL, SUCCESS;
  @ disjoint behaviors FST_FAIL, SND_FAIL, SUCCESS;
  @ */
int f(int a,int b)
{
  int x ;
  int y ;
  x = g(a);
  if (x != OK) return KO ;
  y = g(b);
  if (y != OK) return KO ;
  return OK ;
}
