// Extracted from the CN tutorial — see THIRD_PARTY for license.

unsigned int min3(unsigned int x, unsigned int y, unsigned int z)
/*@ ensures return <= x
            && return <= y
            && return <= z;
@*/
{
    if (x <= y && x <= z) {
        return x;
    }
    else if (y <= x && y <= z) {
        return y;
    }
    else {
        return z;
    }
}

unsigned int min3_invalid_spec(unsigned int x, unsigned int y, unsigned int z)
/*@ ensures return <= x
            && return <= y
            && z <= return; // This doesn't hold
@*/
{
    if (x <= y && x <= z) {
        return x;
    }
    else if (y <= x && y <= z) {
        return y;
    }
    else {
        return z;
    }
}

unsigned int min3_invalid_code(unsigned int x, unsigned int y, unsigned int z)
/*@ ensures return <= x
            && return <= y
            && return <= z;
@*/
{
    if (x <= y && x <= z) {
        return x;
    }
    else if (y <= x && y <= z) {
        return *((unsigned int*) 0);
    }
    else {
        return z;
    }
}

