-- mobius_lorentz.m2
-- Symbolically construct the outer product of a 2-component complex vector with its conjugate transpose
-- and prove that det(X) is identically 0.

R = QQ[x1, x2, y1, y2];
-- xi corresponds to [xi_1, xi_2]^T
xi = matrix {{x1}, {x2}};
-- y1, y2 correspond to the complex conjugates of xi_1, xi_2
xistar = matrix {{y1, y2}};

X = xi * xistar;
print "Matrix X = xi * xi^*:";
print X;

D = det X;
print "det(X) = ";
print D;

if D == 0 then (
    print "Success: det(X) is identically 0, linking the null cone of Minkowski space to rank-1 matrices.";
) else (
    print "Error: det(X) is not 0.";
    exit 1;
);
exit 0;
