/*@
requires base >= 0 && height >= 0 && base <= 2147483647 / height;
ensures \result == (base * height)/2;
assigns \nothing;
*/
int area(int base, int height){
    int res = (base *  height)/2;
    return res;
}
/*@
 assigns \nothing;
*/
int main() {
    int a = area(4, 5);
    //@ assert a == 10;
}