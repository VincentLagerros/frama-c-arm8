 #include<limits.h>
/*@
    requires INT_MIN - b <= a <= INT_MAX - b;
    ensures \result == a+b;
    assigns \nothing;
*/
int add(int a,int b){
    return a+b;
}