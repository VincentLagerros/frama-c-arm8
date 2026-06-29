/*@
	requires \valid(q) && \valid(r);
	requires 0<y<1000000000 && 0<=x<1000000000;
	assigns *q, *r ;
*/
void div_rem(unsigned x,unsigned y,unsigned* q,unsigned* r){
	*q = x / y ;
	//@ assert *q==x/y;
	*r = x % y ;
	//@ assert *r==x%y;
}
