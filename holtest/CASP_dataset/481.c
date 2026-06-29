/*@ 
    ensures \result>=a && \result>=b && \result>=c;
    ensures \result==a || \result==b || \result==c;
    ensures a>=b && a>=c ==> \result==a;
    ensures b>=a && b>=c ==> \result==b;
    ensures c>=a && c>=b ==> \result==c;
*/

int max3(int a,int b,int c) {
      int max;
      if((a >= b) && (a >= c)) {
        max = a;
      }
      else if((b >= a) && (b >= c)) {
        max = b;
      }
      else if((c >= a) && (c >= b)) {
        max = c;
      }
    return max;
}