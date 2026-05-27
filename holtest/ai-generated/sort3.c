/*@
  @ requires \valid(a) && \valid(b) && \valid(c);
  @ requires \separated(a, b, c); 
  @
  @ assigns *a, *b, *c;
  @
  @ // Postcondition: The values are strictly ordered
  @ ensures *a <= *b && *b <= *c;
  @
  @ // Postcondition: Conservation of data (The final values must be a permutation of the original values)
  @ ensures (*a == \old(*a) || *a == \old(*b) || *a == \old(*c)) &&
  @         (*b == \old(*a) || *b == \old(*b) || *b == \old(*c)) &&
  @         (*c == \old(*a) || *c == \old(*b) || *c == \old(*c));
  @*/
void sort_three(int *a, int *b, int *c) {
    if (*a > *b) {
        int t = *a; *a = *b; *b = t;
    }
    if (*b > *c) {
        int t = *b; *b = *c; *c = t;
        if (*a > *b) {
            int t = *a; *a = *b; *b = t;
        }
    }
}