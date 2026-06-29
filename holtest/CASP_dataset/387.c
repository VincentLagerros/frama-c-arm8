/*@ 
  requires 0 <= N <= 1000000000;
  assigns \nothing;
  ensures \result * \result <= N ;
  ensures N < (\result+1) * (\result+1);
*/
int root(int N){
  int R = 0;
  /*@ 
    loop invariant 0 <= R * R <= N;
    loop assigns R;
    loop variant N-R;
  */
  while(((R+1)*(R+1)) <= N) {
    R = R + 1;
  }
  return R;
}