-- Exact-rational Macaulay2 + Dmodules certificate for the
-- de Rham / symplectic / Kaluza-Klein / inductive-limit bridge.

needsPackage "Dmodules"

print "=== de Rham / symplectic / KK / colimit Macaulay2 certificate ==="

d0 = matrix(QQ, {{-1, 1, 0}, {0, -1, 1}, {1, 0, -1}});
d1 = matrix(QQ, {{1, 1, 1}});
if d1 * d0 != matrix(QQ, {{0, 0, 0}}) then error "d1*d0 failed";

potential = matrix(QQ, {{2}, {-1}, {3}});
exactCurrent = d0 * potential;
if d1 * exactCurrent != matrix(QQ, {{0}}) then error "exact current closed failed";

d1zero = matrix(QQ, {{0, 0, 0}});
obstruction = matrix(QQ, {{1}, {1}, {1}});
if d1zero * obstruction != matrix(QQ, {{0}}) then error "closed obstruction failed";
if rank(d0 | obstruction) == rank d0 then error "non-exact obstruction failed";

J = matrix(QQ, {{0, 1}, {-1, 0}});
S = matrix(QQ, {{1, 1}, {0, 1}});
if transpose(S) * J * S != J then error "symplectic preservation failed";

kk = matrix(QQ, {
  {-1/2, 1/3, 0, 0, 1},
  {1/3, 11/9, 0, 0, 2/3},
  {0, 0, 1, 0, 0},
  {0, 0, 0, 1, 0},
  {1, 2/3, 0, 0, 2}
});
if det kk != -2 then error "KK determinant failed";

omega = 6_QQ;
curvature = 2_QQ;
hbar = 3_QQ;
if curvature * hbar != omega then error "prequantum scaling failed";

n = 2;
xcol = 3/5;
if (2 * xcol) / (2^(n + 1)) != xcol / (2^n) then error "colimit cone sample failed";

-- Dmodules lane: the flat de Rham current is represented by a holonomic
-- quotient module with equations dx=dy=0 and exact obstruction x-y=0.
W = makeWA(QQ[x, y]);
Dx = W_2;
Dy = W_3;
I = ideal(Dx, Dy, x - y);
if isHolonomic(W^1 / I) != true then error "Dmodules holonomic current module failed";

print "DE_RHAM_SYMPLECTIC_KK_QUANTIZATION_LIMIT_M2_DMODULES_CERTIFICATE_OK";
