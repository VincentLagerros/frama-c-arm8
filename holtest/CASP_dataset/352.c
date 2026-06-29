/*@ requires \valid(a + (0..6));
    ensures  \valid_read(a + (0..6)) && a[6] == '\0' && 
             (a[0] == 'a') && (a[1] == 'b') && (a[2] == 'c') && 
             (a[3] == 'a') && (a[4] == 'b') && (a[5] == 'c');
*/
char* strtest(char* a){
    a[0] = 'a'; a[1] = 'b'; a[2] = 'c'; a[3] = 'a'; a[4] = 'b'; a[5] = 'c'; a[6] = '\0';
    return a;
}