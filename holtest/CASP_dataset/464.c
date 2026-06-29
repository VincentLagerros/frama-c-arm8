/*@ requires k>0;
  @ ensures \result<1;
  @*/
int f(int k, int g);


int f(int k, int g){
  return 0;
}

void main(){
  f(1,0);
}