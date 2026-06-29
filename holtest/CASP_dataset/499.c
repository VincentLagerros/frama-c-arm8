#include<limits.h>

/*@ requires x >= 1;
 requires y >= 1;
 requires z>= 1;
 requires x<=INT_MAX && y<=INT_MAX && z<=INT_MAX;
 requires x+y<=INT_MAX && y+z<=INT_MAX && z+x<=INT_MAX;
 ensures (x+y <= z || y+z <=x || x+z <=y) ==> \result == 0;
 ensures x+y > z && y+z >x && x+z >y && x == y && y == z ==> \result==1;
 ensures x+y > z && y+z >x && x+z >y && (x != y || y != z) ==> \result==0;
 assigns \nothing;
*/
int triangle(int x,int y,int z)
{

 if(x+y > z && y+z >x && x+z >y)
 {
     if(x == y && y == z){
     return 1;
     }
     else if(x == y || y == z || x==z){
     return 0;
     }
     else if((x!=y)&&(y!=z)&&(z!=x)) {
     return 0;
     }
   }
    return 0;
}

int main()
{
 int t = triangle(4,4,4);
 return 0;
}