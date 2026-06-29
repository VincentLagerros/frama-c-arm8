// complete is not effective, although negative is missing, taking it in/out doesn't make a difference still proved.

#pragma JessieIntegerModel(exact)

/*@ requires -2147483647 <= a <= 2147483647;
    assigns \nothing;

    behavior zero:
        assumes a == 0;
        ensures \result == 0;

    behavior positive:
        assumes a > 0;
        ensures \result == a;

    behavior negative:
    	assumes a < 0;
    	ensures \result == -a;

    complete behaviors zero, positive, negative;
    disjoint behaviors zero, positive, negative;


*/
int abs(int a)
{
    if (a == 0)
        return 0;
    else if (a > 0)
        return a;
    else
        return -a;
}