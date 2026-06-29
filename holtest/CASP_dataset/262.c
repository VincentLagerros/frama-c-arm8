/*@ requires -1000000 < x < 1000000;
 ensures \result == x + 1; 
 assigns \nothing; */
int f(int x) { return x+1; }

/*@ requires -1000000 < x < 1000000;
    requires -1000000 < y < 1000000;
 ensures \result == x + y + 1;
 assigns \nothing; */
int g(int x, int y) { return (x+y+1); }