-- Macaulay2 + Dmodules/BernsteinSato certificate for the planar quadratic
-- defect f = x^2 + y^2.  This is an algebraic D-module witness for the
-- singularity used by the real spinorial monodromy lane.
--
-- Honest readout:
--   * globalBFunction(f) = (s + 1)^2, so s = -1 is a Bernstein-Sato root;
--   * deRham(k, f) computes the algebraic de Rham cohomology of the complement
--     of f = 0 over QQ; for this split-over-QQbar quadratic it returns ranks
--     H0=1, H1=2, H2=1.
-- The real one-loop spinorial parity theorem is sealed separately in Lean.

needsPackage "Dmodules";
needsPackage "BernsteinSato";

-- 1. Define the 2D Weyl algebra for the defect slice.
W = QQ[x, y, dx, dy, WeylAlgebra => {x => dx, y => dy}];

-- Dmodules lane smoke check: Weyl commutators are active.
if dx*x - x*dx != 1_W then error "x Weyl commutator failed";
if dy*y - y*dy != 1_W then error "y Weyl commutator failed";

-- 2. Define the topological defect / local Dirac-string slice.
R = QQ[x, y];
f = x^2 + y^2;

-- 3. Compute the global Bernstein-Sato polynomial.
bf = globalBFunction f;
print("M2DEFECT:Dmodules=loaded");
print("M2DEFECT:BernsteinSato=loaded");
print("M2DEFECT:globalBFunction=" | toString bf);
print("M2DEFECT:globalBFunction_factor=" | toString factor bf);

-- The displayed factorization certifies that s = -1 is a root.
-- Avoid changing rings here: `globalBFunction` owns its polynomial ring.
if toString factor bf != "(s+1)^2" then error "unexpected b-function factorization";

-- 4. Algebraic de Rham cohomology of the complement, degree by degree.
H0 = deRham(0, f);
H1 = deRham(1, f);
H2 = deRham(2, f);
print("M2DEFECT:deRham_H0=" | toString H0);
print("M2DEFECT:deRham_H1=" | toString H1);
print("M2DEFECT:deRham_H2=" | toString H2);

print "m2 monodromy defect Dmodules certificate: ok";
