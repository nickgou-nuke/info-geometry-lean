-- Macaulay2/Oaku-style template for the D=4 non-isotropic Conf_3 complement.
-- This file is intentionally a template: Macaulay2 is not installed in the
-- current local environment.  Use a Macaulay2 build with the Dmodules package.
--
-- Target: de Rham cohomology of QQ[a,b,1/f], f=qa*qb*qab.
-- Run in a suitable M2 installation with something like:
--   M2 proofs/macaulay2_noniso_conf3_d4_dmodule_template.m2

needsPackage "Dmodules"

R = QQ[a0,a1,a2,a3,b0,b1,b2,b3]
qa  = a0*a1 + a2*a3
qb  = b0*b1 + b2*b3
qab = (a0-b0)*(a1-b1) + (a2-b2)*(a3-b3)
f = qa*qb*qab

print "D=4 split quadric Conf_3 complement D-module target"
print f

-- Useful preliminary invariants.
I = ideal(qa,qb,qab)
print "dim R/I; expected 5"
print dim(R/I)
print "degree R/I"
print degree(R/I)

-- D-module route.  Exact command names vary across Dmodules versions.
-- Typical Oaku/Takayama workflow:
--   1. compute Ann(f^s) or Ann(1/f) in the Weyl algebra;
--   2. form the localization module R_f;
--   3. compute the algebraic de Rham complex;
--   4. extract vector-space dimensions of cohomology.
--
-- Pseudocode placeholders to adapt to your Dmodules version:
--   A = makeWeylAlgebra R
--   ann = annihilatorPower(f, -1)  -- or annFs/bFunction/localize API
--   M = A^1 / ann
--   C = deRhamComplex M
--   HH = prune HH C
--   apply(HH, h -> rank source gens h)
--
-- Required output certificate:
--   * Betti numbers b_0..b_8;
--   * total rank;
--   * basis labels if available;
--   * software version and full transcript.

print "TODO: adapt Dmodules API for Ann(1/f) and deRhamComplex; do not treat this template as a proof."
