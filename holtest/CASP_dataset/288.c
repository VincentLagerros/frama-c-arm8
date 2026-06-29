/* bts 60: 1 should be lifted to a real number implicitely.  */

/*@ ensures 1.0 == 1; 
    assigns \nothing;*/
void f();

/*@ lemma foo: 1.0 == (float)1; */


void f() {
 double B;

}


typedef int T, T4[4], *T_PTR;
const T X, Tab[4];
typedef T_PTR T_PTR_T4[4];
const T_PTR_T4  Tab_Ptr = { &X, &X, &X, &X};
