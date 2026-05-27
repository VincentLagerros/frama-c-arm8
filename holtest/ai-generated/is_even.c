/*@ // Forward declaration of specs so the mutual recursive calls can see each other's contracts
  @ requires n >= 0;
  @ terminates n >= 0;
  @ decreases n;
  @ assigns \nothing;
  @ ensures \result == 1 <==> (n % 2 == 0);
  @*/
int is_even(int n);

/*@
  @ requires n >= 0;
  @ terminates n >= 0;
  @ decreases n;
  @ assigns \nothing;
  @ ensures \result == 1 <==> (n % 2 != 0);
  @*/
int is_odd(int n);


int is_even(int n) {
    if (n == 0) {
        return 1; // 0 is even
    }
    return is_odd(n - 1);
}

int is_odd(int n) {
    if (n == 0) {
        return 0; // 0 is not odd
    }
    return is_even(n - 1);
}