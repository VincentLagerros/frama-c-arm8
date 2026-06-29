int t[100];

/*@ requires \valid(t+(0..99)) && (\forall integer k ; 0 <= k < 100 ==> t[k] == 1) ;
    assigns t[0..99];
    ensures \valid(t+(0..99)) && (\forall integer k ; 0 <= k < 100 ==> t[k] == 2) ;
 */
void f(void)
{
   int i;

   /*@
        loop invariant 0 <= i <= 100 && (\forall integer k ; 0 <= k < i ==> t[k] == 2)
        && (\forall integer k ; i <= k < 100 ==> t[k] == 1) ;
        loop assigns t[0..99], i;
        loop variant 100 - i;
    */
   for (i=0; i<100; i++) t[i]++;
}
