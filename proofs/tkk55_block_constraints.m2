-- Macaulay2 commutative certificate for the 100-variable orthogonality system.
R = QQ[a_0..a_99];
B = diagonalMatrix {1_R,1_R,1_R,1_R,-1_R,-1_R,-1_R,-1_R};
G = mutableMatrix(R,10,10);
G_(0,9)=1; G_(9,0)=1;
scan(0..7, i -> G_(i+1,i+1)=B_(i,i));
G = matrix G;
A = genericMatrix(R,a_0,10,10);
E = transpose(A)*G + G*A;
I = ideal flatten entries E;
J = jacobian I;
assert(rank source J == 100);
assert(codim I == 55);
assert(dim I == 45);
print("Macaulay2 orthogonality codimension: " | toString codim I);
print("Macaulay2 orthogonal carrier dimension: " | toString dim I);
print("TKK55 MACAULAY2 CERTIFICATE: PASS");
