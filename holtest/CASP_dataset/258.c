/*@
  requires \valid(a) && \valid(b);
  requires \separated(a,b);
  assigns *a, *b;
  ensures *a == \old(*b) && *b == \old(*a);
*/
void swap(int *a, int *b){
  int tmp = *a ; *a = *b ; *b = tmp ;
}

int main(){
  int x = 2;
  int y = 4;
  swap(&x, &y);
  //@ assert x == 4 && y == 2 ;
}