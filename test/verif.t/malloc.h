// Extracted from the CN tutorial — see THIRD_PARTY for license.

// I don't understand the allocation model in CN,
// do they have real specs for malloc and free or only erroneous ones?

extern int *malloc__int ();
/*@ spec malloc__int();
    requires true;
    ensures take R = W<int>(return);
@*/

extern unsigned int *malloc__unsigned_int ();
/*@ spec malloc__unsigned_int();
    requires true;
    ensures take R = W<unsigned int>(return);
@*/

extern void free__int (int *p);
/*@ spec free__int(pointer p);
    requires take P = W<int>(p);
    ensures true;
@*/

extern void free__unsigned_int (unsigned int *p);
/*@ spec free__unsigned_int(pointer p);
    requires take P = W<unsigned int>(p);
    ensures true;
@*/