/*@ ghost const int MYOBJECT_MYTAB_SIZE = 5; */
#define MYOBJECT_MYTAB_SIZE 5

typedef struct MyObject{
	int id;
	int myTab[MYOBJECT_MYTAB_SIZE];
}MyObject;


/*@ requires \valid(self);
    requires Inv1 : self->id == 0;

    assigns self->id, self->myTab[0..MYOBJECT_MYTAB_SIZE-1];

    ensures self->id == 0;
    ensures \forall integer it_x; 0 <= it_x < MYOBJECT_MYTAB_SIZE ==> self->myTab[it_x] == 0;
*/
void test(MyObject* self){
	self->id = 0;
	/*@ loop invariant 0 <= i <= MYOBJECT_MYTAB_SIZE;
	    loop invariant \forall integer j; 0 <= j < i ==> self->myTab[j] == 0;
	    loop assigns i, self->myTab[0..MYOBJECT_MYTAB_SIZE-1];
	    loop variant MYOBJECT_MYTAB_SIZE - i;
	*/
	for (int i=0; i<MYOBJECT_MYTAB_SIZE;i++){
		self->myTab[i] = 0;
	}
}