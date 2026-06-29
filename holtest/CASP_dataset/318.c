/* run.config
   OPT: -load-module report -then -report 
*/

/* run.config_qualif
   OPT: -load-module report -then -report 
   EXECNOW: LOG stmt.log LOG f.dot LOG f_default_for_stmt_2.dot LOG g.dot LOG g_default_for_stmt_11.dot @frama-c@ -no-autoload-plugins -load-module wp -wp-precond-weakening -wp -wp-model Dump -wp-out tests/wp_plugin/result_qualif @PTEST_FILE@ 1> tests/wp_plugin/result_qualif/stmt.log
*/

/*@ requires a < 2147483647 && b < 2147483647 && a > -2147483648 && b > -2147483648 && a + b <= 2147483647 && a + b >= -2147483648;
  @ ensures a > 0 ==> \result == a + b;
  @ ensures a <= 0 ==> \result == -1;
  @ assigns \nothing;
*/
int f(int a, int b) {

	if (a > 0)
		return a + b;

	return -1;
}


/*@ requires a < 2147483647 && b < 2147483647 && a > -2147483648 && b > -2147483648 && a + b <= 2147483647 && a + b >= -2147483648;
  @ ensures \result == a + b;
  @ assigns \nothing;
*/
int g(int a, int b) {

	return a + b;

}

/*@ ensures \result == (e ? a : b) ;
    @ assigns \nothing;
    @ behavior POS:
    @   assumes e ;
    @   ensures \result == a;
    @ behavior NEG:
    @   assumes !e ;
    @   ensures \result == b;
    @ complete behaviors POS, NEG;
    @ disjoint behaviors POS, NEG;
*/
int h(int e,int a,int b) {

        if (e) return a; else return b;

}
