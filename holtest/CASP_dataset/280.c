/*@ ensures (x==0||y==1)?\result==1:\result == 0; 
  assigns \nothing;
 */
int f(int x, int y) { return (x==0||y==1); }

/*@ assigns \nothing; */
int main() {
  int x = f(42,1);
  int y = f(0,36);
  return 0;
}