/*@ logic integer \fact(integer n) = (n <= 0) ? 1 : n * \fact(n-1);
*/

/*@ requires n >= 0 && n <= 10;
    ensures \result == \fact(n);
    assigns \nothing;
*/
int factorial(int n)
{
	int i = 1;

    int f = 1;

     /*@
         loop invariant 1 <= i <= n+1;
         loop invariant f == \fact(i-1);
         loop assigns f, i;
         loop variant n-i+1;
         */

     while (i<=n) {

           f = f * i;

           i = i + 1;

     }

   return f;
}

/*@ assigns \nothing; */
int main(void) {
  int n = 5;
  int ret = factorial(n);
  return 0;
}