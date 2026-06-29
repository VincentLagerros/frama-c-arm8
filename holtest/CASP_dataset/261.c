/*@ requires 1==1;
*/
void test(long x)
{
    unsigned a = 0x10203040;
    unsigned b = (a << 16);
    
    unsigned long long al = a;
    unsigned long long bl = al << 16;
    
    //@ assert b == (unsigned)bl;
    //@ assert b == 0x30400000;
}