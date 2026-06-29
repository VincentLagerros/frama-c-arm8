/* run.config
   OPT: -load-module lib/plugins/Obfuscator -obfuscate -journal-disable
*/

/*@ ensures \valid(q); 
 */
int f(int *q) ;

#define LV X_9999999999999999999999999999999999999999999999999999
int global_LV;
enum { OK = 1,
       NOT_OK = 0 } e ;

/*@ ensures \valid(p);
 */
void main (int * p) {
int LV = 0;
 e = OK ;
 f(p);
}