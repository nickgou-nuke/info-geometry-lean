# Reflection and torsion claim boundaries

## Source convention

Inspected https://arxiv.org/html/2511.23447v2 sections 2.1–2.2.
The spatial gamma matrix squares to minus the identity and is skew-Hermitian;
chirality squares to the identity and is Hermitian. Their anticommuting product
is the Hermitian square-one reflection. The paper also allows multiplication
of that reflection by `i`, producing the square-minus-one boundary condition.
Identifying the spatial gamma directly with the Peirce `d+B` therefore changes
the Clifford square. The pasted abstract was also checked against
https://arxiv.org/abs/2510.05270. No repository theorem identifying the physical
fields, boundary conditions, condensate expectations, or particle-production
coefficients is claimed by this intake.

## Algebraic corrections

`PeirceReflectionClaimBoundaries` records a self-adjoint integer matrix whose
square is not one. It also uses actual noncommuting 2×2 matrices over `ZMod 6`:
the reflexive square-zero seeds are E01 and E10, both wall coefficients 1 and 3
are nonzero, and the wall itself is nonzero but reflection invariant.
The correct equality criterion from a defect formula is
`(2*beta) • J = 0`; coefficient nonvanishing alone cannot cancel this product.
The owner passed parent session 17205 (8,924 jobs, exit 0), with zero own
warnings, log `/tmp/peirce-reflection-boundaries-v2.log`. The companion audit
requests five axiom reports and two examples. Independent QA session 32658 passed (8,925 jobs, exit 0), five axiom
reports, two examples, zero own warnings and traps. Semantic source review
passed; the defect iff assumes rather than derives the defect formula.

## Fixed-pairing torsion replacement

`FixedPairingTorsionBoundary` localizes the anti-isometry theorem to two fixed
vectors, without symmetry or global fixedness assumptions. It characterizes
uniform cancellation exactly by absence of two-torsion, testing native rank-one
bilinear forms for necessity. The `ZMod 6` form `g(x,y)=3*x*y` is anti-invariant
under the identity and has nonzero value at `(1,1)`, although `2` is nonzero.
This is a genuine bilinear-form counterexample, not a claimed operator proxy.

Parent audit session 35764 passed (8,926 jobs, exit 0), with five axiom reports
using only `propext` and optionally `Quot.sound`, plus two examples.
Evidence: `/tmp/fixed-pairing-torsion-audit.log`. Independent QA session
46921 also passed (8,926 jobs, exit 0), five axiom reports, two examples,
zero own warnings and traps. Semantic source review passed and the remaining prose correction was
independently confirmed closed.
The original `NullEigenspace` documentation was corrected to distinguish
sufficient cancellation assumptions from necessary ones, exclude characteristic
two from the field statement, and distinguish isotropy from maximal isotropy.
