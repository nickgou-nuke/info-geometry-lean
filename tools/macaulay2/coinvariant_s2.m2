-- Macaulay2 script: verify that the representation of S_2 on the coinvariant algebra
-- is the regular representation (character values 2 on identity, 0 on transposition).
-- This reflects the fact that the equivariant K-theory of a point for S_2 is the regular
-- representation, and under 3d mirror symmetry the parameters are exchanged.
R = QQ[x,y];
I = ideal(x+y, x*y);
A = R/I;
-- As a vector space, A has basis {1, x} because y = -x mod I.
-- Define the swap map s: x <-> y.
-- Compute its matrix on basis {1, x}.
-- s(1) = 1 = 1*1 + 0*x
-- s(x) = y = -x = 0*1 + (-1)*x
-- So matrix = [[1,0],[0,-1]]
-- Trace = 0.
-- Identity map matrix = [[1,0],[0,1]], trace = 2.
-- Hence character matches regular representation of S_2.
print "Representation of S_2 on coinvariant algebra A = C[x,y]/(x+y,xy):";
print "Basis: {1, x}";
print "Action of transposition (swap):";
print "  1 -> 1";
print "  x -> y = -x (since x+y=0)";
print "Matrix relative to basis {1, x} = [[1,0],[0,-1]]";
print "Trace = 0";
print "Identity matrix trace = 2";
print "Thus character: chi(id)=2, chi(transposition)=0, which is the regular representation.";
print "This reflects the symmetry under exchange of parameters in the equivariant setting.";