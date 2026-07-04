needsPackage "Dmodules"
print "=== Macaulay2 Multi-Loop Groebner Basis ==="

W = QQ[x, y, Dx, Dy, WeylAlgebra => {x => Dx, y => Dy}]
use W

-- Multi-loop logarithmic score D-module extension
I = ideal(Dx * x * Dx, Dy * y * Dy)

print "Computing non-commutative Groebner basis in the Weyl algebra..."
G = gb I
gensG = gens G
print gensG

print "Terms and coefficients of the Groebner basis elements:"
for i from 0 to numColumns(gensG) - 1 do (
    p = gensG_(0,i);
    print ("Generator " | toString(i) | ": " | toString(p));
    ts = terms p;
    for j from 0 to length(ts) - 1 do (
        print ("  Term " | toString(j) | ": " | toString(ts_j));
    );
)

print "MULTI_LOOP_GROEBNER_OK"
exit
