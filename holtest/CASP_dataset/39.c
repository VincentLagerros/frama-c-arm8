/*@
	requires \valid(a) && \valid(b);
	requires -10000000<*a<10000000 && -10000000<*b<10000000;
	ensures \result==*a && \result>=*b || \result==*b && \result>=*a;
*/
int max_ptr(int* a,int* b){
	return(*a > *b) ? *a: *b ;
}
extern int h ;
int main(){
	h =42;
	int a =24,b =42;
	int x= max_ptr(&a,&b);
}
