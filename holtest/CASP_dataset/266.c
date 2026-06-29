/*@
  requires -2147483647 <= n <= 2147483647;
  ensures \result >=0;
  assigns \nothing;

  behavior positive:
    assumes n >= 0;
    ensures \result == n;
    assigns \nothing;

  behavior negative:
    assumes n < 0;
    ensures \result == -n;
    assigns \nothing;

  complete behaviors positive, negative;
  disjoint behaviors positive, negative;
*/
int abs(int n){
    if(n<0){
        return -n;
    }
    return n;
}