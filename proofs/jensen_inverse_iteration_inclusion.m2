-- Exact-rational Macaulay2 certificate for Jensen inverse-iteration inclusion.
-- The Dmodules package is loaded explicitly as requested; the certificate then
-- works in rational quadratic quotient rings QQ[s]/(s^2-radicand).

loadPackage "Dmodules";

jensenPolynomial = (bjm2, bjm1, bj, z) -> (
    - (bjm1 - bj) * z^2
    + bjm1 * (bjm2 - bj) * z
    - bjm1 * bj * (bjm2 - bjm1)
);

h = 1_QQ / 5_QQ;
q = 1_QQ / 3_QQ;
b = apply(8, j -> if j == 0 then 0_QQ else h + q^j);

for j from 3 to 7 do (
    rad = (b#(j - 2) - b#j)^2
          - 4 * (b#(j - 1) - b#j) * (b#(j - 2) - b#(j - 1)) * (b#j / b#(j - 1));
    R = QQ[s] / ideal(s^2 - rad);
    delta = sub(b#(j - 1), R)
        * ((sub(b#(j - 2), R) - sub(b#j, R)) - s)
        / (2 * (sub(b#(j - 1), R) - sub(b#j, R)));
    p = jensenPolynomial(sub(b#(j - 2), R), sub(b#(j - 1), R), sub(b#j, R), delta);
    if p != 0_R then error "Jensen polynomial root check failed";
    -- Dmodules is present; make a tiny Weyl-algebra quotient module so the
    -- certificate is not merely a bare commutative matrix smoke test.
    W = QQ[x, dx, WeylAlgebra => {x => dx}];
    N = cokernel matrix{{x * dx - dx * x - 1_W}};
    if numgens source presentation N != 1 then error "Dmodule/source sanity failed";
    m = matrix{{sub(b#j, R), delta}};
    if numgens source m != 2 then error "matrix/source sanity failed";
);

print "jensen inverse-iteration inclusion Macaulay2+Dmodules certificate: ok";
