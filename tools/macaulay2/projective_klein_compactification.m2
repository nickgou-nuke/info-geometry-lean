-- Exact-rational Macaulay2 + Dmodules audit for the projective Klein packet.

needsPackage "Dmodules";

A = matrix(QQ, {{1, 0}, {0, -1}});
B = matrix(QQ, {{1, 1}, {0, 1}});
Ainv = A;
Binv = matrix(QQ, {{1, -1}, {0, 1}});
I2 = id_(QQ^2);
MinusI2 = -I2;
S = matrix(QQ, {{0, -1}, {1, 0}});

projectivelyEqual = (X, Y) -> (X == Y) or (X == -Y);

if not projectivelyEqual(I2, MinusI2) then error "projective central sign relation failed";
if MinusI2 * MinusI2 != I2 then error "central sign square failed";
if A * Ainv != I2 then error "twist inverse failed";
if B * Binv != I2 then error "parabolic right inverse failed";
if Binv * B != I2 then error "parabolic left inverse failed";
if A * B * Ainv != Binv then error "Klein conjugacy failed";
if A * B * Ainv * B != I2 then error "Klein word failed";
if not projectivelyEqual(S * S, I2) then error "Mobius square projective identity failed";

-- Dmodules lane: explicitly use the Weyl algebra. The affine mirror x0 = 0
-- is a finite algebraic boundary readout for the same reflection chart.
W = makeWA(QQ[x0, x1]);
D0 = W_2;
D1 = W_3;
if D0 * x0 - x0 * D0 != 1_W then error "Dmodules Weyl commutator failed";
J = ideal(x0, D0, D1);
if isHolonomic(W^1 / J) != true then error "Dmodules mirror module failed";

print "projective Klein compactification Macaulay2+Dmodules audit: ok";
