# Peirce reflection, parity defects, and CAR normalization

## Intake and ownership

Source: `Pasted text(20261024-114042).txt`, proposing
`KleinBottleCondensateCpViolation.lean` and a dictionary to two physics papers.
Base inspected: `73006b1342e449348fa626995ad96c6a2b48a9e6`.

Reuse `Core.DualSeedPeirce.IsDualSeedPair`, its multiplication table and aliases
to the existing support/Majorana owners. No new MP predicate, seed predicate,
projection predicate, or duplicated basic square-zero library is introduced.
The only added algebra elements are an odd linear combination and arbitrary
diagonal weights. The carrier is an arbitrary associative algebra, not a
replacement scalar or diagonal model. Finite matrices are examples only.

## Ground-truth theorem contract

Let d^2=b^2=0, dbd=d, bdb=b. Put p=db, q=bd, Delta=p+q,
G=p-q, Q=d+b and J=d-b, using existing owners.

1. GQ=J, QG=-J, JG=-Q. The spatial-minus-square choice J therefore gives
   (JG)^2=Delta, unlike the incorrect spatial identification Q.
2. Q exchanges p and q and reverses G. Both Q and J have the star symmetries
   stated in the source only under b=star d. Hermiticity alone is insufficient
   to deduce an involution; a separate normalization equation is explicit.
3. On every native left module, a pure p-sector vector with Q-eigenvalue +1
   or -1 vanishes. For any base set X, map g:X->X and module-valued field psi,
   psi(g x)=Q psi(x) plus globally pure p chirality implies psi=0. This is a
   genuine equivariant-field statement, but no topology or Pin bundle is built.
4. W(a,beta)=a Q+beta J anticommutes with G, and QWQ=W(a,-beta).
   The fixed and negative-fixed criteria are exactly 2 beta J=0 and 2 a Q=0.
   Nonzero coefficients alone are not enough over rings with torsion or zero seeds.
5. For rho=x p+y q and an actually tracial linear map tau, equal support traces
   follow from cyclicity: tau(p)=tau(q). Mass and polarization are respectively
   (x+y)tau(p) and (x-y)tau(p). A real tracial functional vanishes on G rho
   whenever Q rho Q=rho. No normalized positive state or dynamics is inferred.
6. The real/central coefficient CAR anticommutator of mixed independent inputs
   scales by u^2+v^2. A separate theorem records the additional square obstruction
   uv Delta when mixing a single seed with its own partner. Preservation of one
   anticommutator is not claimed to prove every CAR equation.

The dependency order is seed multiplication -> reflection products/exchange ->
equivariant-field obstruction and parity defects -> trace/normalization identities.
No causal edge from these equations to cosmological baryogenesis is asserted.

## External verification and explicit departures from the attachment

Primary papers inspected:
- Greene, Kabat, Levin, Porrati, *Klein Bottle Cosmology*,
  arXiv:2511.23447v3 (22 May 2026), sections 2.1-2.2, 3, 4.2-4.3.
  https://arxiv.org/html/2511.23447v3
- Same authors, *Compactification Without Orientation, or a Topological Scenario
  for CP Violation*, arXiv:2510.05270v2 (21 March 2026), sections 2-3.
  https://arxiv.org/html/2510.05270v2

The first paper uses mostly-minus signature. Its spatial Gamma^4 squares to -I
and is skew-adjoint, whereas its chirality squares to I and is self-adjoint.
R4=Gamma^4*chirality is self-adjoint and squares to I. Mapping Gamma^4 directly
to Q, whose square is +Delta, does not preserve these relations. The algebraic
pair J,G gives R4=-Q consistently for this two-generator subalgebra; no map of
the entire eight-dimensional spinor representation or full Clifford algebra is
constructed. In the papers the alternative reflection is i*R4, not an assertion
that it is literally G*Q. `phase_twisted_square` retains the scalar-phase option.

The boundary condition relates psi(x) and psi(g x), not generally psi(x) and
Q psi(x) at the same point. The exact two-sheet example exhibits this difference.
The full Klein-bottle glide includes a half-period translation; the parity axes
are fixed for its reflection component, not fixed points of that free glide.

Equation (59) of arXiv:2511.23447v3 states the fermion normalization
|alpha|^2+|beta|^2=1; the immediately following scalar comparison uses the minus
sign. The source's hyperbolic normalization is therefore not this fermionic
normalization. The formal CAR mixing theorem specializes to real/central
coefficients; no complex Bogoliubov evolution equation is solved.

The actual condensate in section 3 is a position-dependent two-point-function
contribution. W(a,beta) has no position, Green function, vacuum, or expectation
value, and is not generally self-adjoint. Anticommuting with a grading is an
operator-parity statement, not by itself proof of broken physical chiral symmetry.
The defined Q-conjugation is not automatically charge conjugation or CP: those
require the paper's spacetime and spinor transformations, including its complex
conjugation convention. The proposed interview timestamps have no supplied media
source and are not used as verification evidence.

The weight rho(u,v)=u^2 p+v^2 q is not automatically normalized. With tau(p)=1 and
u^2-v^2=1, its trace is 1+2v^2. The trace identity is not a derivation of baryon
number, a KMS condition, a wall profile, a mass transition, or a generated matter
asymmetry. The papers describe a potential mechanism and require extra dynamical
and model ingredients. Those are outside these formal statements.

## Verification boundary

Three new modules plus their complete unchanged repository import closure are
checked against the exact root Lean and Mathlib pins by the new scoped workflow.
Every declaration owned by the new modules, including generated declarations,
is audited with public Lean.collectAxioms. The allowlist is only propext,
Classical.choice and Quot.sound; unsafe/partial declarations are rejected.

No import is stripped, dependency pin/source altered, or build cache deleted.
The checker uses the shared sequential build lock. This is not a full root-Lake
or All.lean build. Original upload prose and code are not asserted verified
unchanged. CI status and source hashes must be read from the produced artifact.

Production import: `InfoGeometry.Core.PeirceParityWeights`.
Checked example target: `InfoGeometry.Canonical.PeirceReflectionAudit`.
