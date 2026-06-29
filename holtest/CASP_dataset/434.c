#ifndef __is_included__eb42c25c_df0f_11eb_ba7e_b499badf00a1
#define __is_included__eb42c25c_df0f_11eb_ba7e_b499badf00a1 1

/* Declaration of SREG */
extern volatile unsigned char SREG;

void sysclockInit();

/*@
        requires \valid(&SREG);
        assigns SREG;
*/
unsigned long int micros();

/*@
        requires millisecs >= 0;
        requires \valid(&SREG);
        assigns SREG;
*/
void delay(unsigned long millisecs);

#endif /* __is_included__eb42c25c_df0f_11eb_ba7e_b499badf00a1 */


#include <stdio.h>

/* Dummy implementations to allow Frama-C to parse the code */

void sysclockInit() {}

/*@
        requires \valid(&SREG);
        assigns SREG;
*/
unsigned long int micros() {
  SREG = 0; /* dummy assignment */
  return 0;
}

/*@
        requires millisecs >= 0;
        requires \valid(&SREG);
        assigns SREG;
*/
void delay(unsigned long millisecs) {
  SREG = 0; /* dummy assignment */
}
