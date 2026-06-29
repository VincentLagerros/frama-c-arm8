//In the assigns clause of g(), parameter p refers to g()'s argument, not to the global variable p.

//This problem can be circumvented using ghost variables.


typedef struct { int a; } las;

las * p;


/*@
requires alid(p);
assigns p->a;
@*/

void f() { p->a = 5; }

/*@
requires alid(p);
assigns p->a;
@*/

void g(int * p_arg) { f(); }

