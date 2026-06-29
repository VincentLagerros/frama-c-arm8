/*@
    requires 0<=first<=180 && 0<=second<=180;
    ensures \result + first + second == 180;
*/
int last_angle(int first,int second){
    return 180 - first - second;
}
