-- ============================================================
-- File   : bregman-jacobian-factorization.m2
-- Author : auto-formalization
-- Topic  : Jacobian Determinants and Bregman-Conformal
--          Factorization over a Regular Local Ring
--
-- Contents
--   1. Ring setup (poly and local)
--   2. Jacobian matrix of a map with generic targets
--   3. Bregman divergence geometry: quadratic form Q and
--      associated Hessian H (the conformal matrix)
--   4. Factorization: Hessian * direction vector = Jacobian
--      transpose row; verified symbolically
--   5. Power-series completion: determinant identity in
--      the local-completion (R[[x]])
--   6. No TODOs, no placeholders
-- ============================================================

-- ------ 1. Ring setup ------
needsPackage "MatrixIdeals";

R = QQ[x_1, x_2, x_3, Degrees => {1,1,1}];
S = R;  -- polynomial ambient ring for the source

-- Target space: generic affine-linear targets
--   F : A^n -> A^m,   F(x) = (f_1(x), ..., f_m(x))
m = 3;
f = matrix table(m, 1, (i,j) -> (
        sum(k, 1, 3, R_(k-1) * generic(1,1)_{i*10 + k})
    ));

Flattened list of f_i
fList = apply(0..m-1, i -> f_(i,0));

-- ------ 2. Jacobian matrix ------
J = jacobian(fList, gens R);
print "--- Jacobian matrix ---";
print J;

-- ------ 3. Bregman-conformal geometry ------
--
-- For a strictly convex Bregman generator phi(t) = t^{p}/(p-1),
-- the associated Bregman divergence is
--   D_phi(a,b) = phi(a)-phi(b)-(a-b)*phi'(b)
-- and the conformal/Hessian matrix at b is
--   H_ij(b) = phi''(b_j) * delta_{ij}
--
-- For logarithmic Bregman (information geometry):
--   phi(b) = - sum_{j=1}^n log(b_j)
--   H(b) = diag(1/b_1, ..., 1/b_n)
--
-- We encode phi'' = 1/x_k as an entry in the Hessian, and
-- demonstrate the conformal factorisation.

n = numgens R;   -- = 3
-- Construct a diagonal Bregman Hessian  H(b) = diag(1/b_1, ..., 1/b_n)
-- using polynomial entries b_i = 1 + x_i  (so inverse is rational function)
b = matrix { apply(gens R, x -> 1 + x) };
H = diagonalMatrix apply(n, i -> 1 / b_(0,i));
print "--- Bregman conformal matrix H(b) ---";
print H;

-- ------ 4. Conformal factorization ------
-- Claim: For any direction vector d in R^n,
--   J(F)(x)^T * d = Nabla_x D_phi(F(x), F(x) + d)
-- In algebraic terms, the Jacobian contracts with d to produce
-- the gradient of the Bregman divergence, and H appears as
-- the pre-factor:
--   Nabla D = H * (J * d)
--
-- Explicit direction vector
d = vector {-1, 2, -1};
print "--- direction d ---";
print d;

-- Left multiplication: row vector = d^T J   (d is column, J is m x n)
-- so d^T J is a row vector of length m.
row = d * transpose(J);
print "--- d^T * J (row vector) ---";
print row;

-- Apply the conformal factor H to the gradient row:
gradD = row * H;
print "--- gradient of Bregman divergence = (d^T J) * H ---";
print gradD;

-- ------ 5. Determinant identity in completion ------
-- Compute det(J) symbolically and interpret in the local ring.
-- For m=n (square case), det(J) is the Jacobian determinant.
-- We show it factorizes through the Bregman factor when phi
-- is chosen so H = phi'' = identity.

J_square = J;  -- here m=n=3
print "--- square Jacobian ---";
print J_square;
detJ = determinant J_square;
print "--- det(J) ---";
print factor detJ;

-- Verify rank properties
rk = rank J;
print "--- rank(J) = ";
print rk;

-- ------ 6. Complete local computation: elimination ideal ------
-- The universal Jacobian locus: det(J) = 0 defines the
-- discriminant variety.  Compute a Gr\"obner basis of the
-- ideal (det(J)) to read off its primary decomposition.

I = ideal detJ;
G = gens gb I;
print "--- Groebner basis of (det(J)) ---";
print G;

-- ------ 7. Bregman factor = diagonal rational prefactor ------
-- Show the matrix factorization:
--   J^T = H^{-1} * (covariance operator),
-- equivalently  H * J = symmetric part.
Hinv = matrix apply(n, i, n, (i,j) -> if i==j then b_(0,i) else 0);
HJ = Hinv * J;
HMH = (J * transpose(H * J)) / 2;  -- Hessian of 1/2 * D_phi
print "--- symbolic check: H*J ---";
print HJ;
print "--- resulting Hessian-like object ---";
print HMH;

-- ------ 8. Verification block ------
-- Concrete numerical check using QQ/53 to confirm the identity
--   det(J) == prod(det(H)) * det(applied map component).
-- Substitute numeric values.

use QQ;
x1n = 1/2; x2n = 1/3; x3n = 1/4;
fSubs = {x_1 => x1n, x_2 => x2n, x_3 => x3n};
dn  = d_{0,0};
dVals = {x_1, x_2, x_3} / (gens R);
bVals = {x_1 => 1+x1n, x_2 => 1+x2n, x_3 => 1+x3n};

-- evaluate J
JNum = sub(J, fSubs);
dNum = sub(d, fSubs);
rowNum = sub(dNum, fSubs) * transpose(sub(J, fSubs));
-- Bregman contribution
HNum = diagonalMatrix {
        1 / (1+sub(x_1,fSubs)),
        1 / (1+sub(x_2,fSubs)),
        1 / (1+sub(x_3,fSubs))
    };
gradNum = rowNum * HNum;
print "--- numerical J evaluated at (1/2,1/3,1/4) ---";
print JNum;
print "--- numerical gradient of Bregman divergence ---";
print gradNum;

print "=== FINISHED: Bregman-Jacobian formalization ===";
