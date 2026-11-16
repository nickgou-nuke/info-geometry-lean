# Holographic white paper: canonical mathematics and Lean results

## Result and source

The implementation extracts the algebraic content of *Complete Holographic
White Paper v6.1* into six native Lean/Mathlib modules. The mathematical core
is a split encoding map and its noncommutative operator corner, ordered
gauge transport, and exact obstructions to several claims in the source.

The six modules contain 67 theorem declarations and seven definitions.
Their selected source closure compiles against Lean `4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The native declaration audit covers
104 declarations, including generated auxiliaries. It reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Source provenance, carrier choices, owner searches, and the initial acceptance
contract are recorded in [the theorem contract](HOLOGRAPHIC_WHITE_PAPER_CONTRACT.md).
All source page numbers below are PDF page numbers.

## 1. Distinction becomes an explicit recoverable/hidden decomposition

Owner: `InfoGeometry.Holographic.BoundaryReconstruction`.

Let `R` be any ring, with no commutativity assumption. Let `Bulk` and
`Boundary` be left `R`-modules, and let

\[
E:B\to L,\qquad D:L\to B,\qquad E\circ D=\operatorname{id}_L.
\]

The last equation is an explicit hypothesis of boundary consistency. It
does not assert that every bulk state is recoverable. Define the ordered
bulk reconstruction operator by the native composition `D.comp E`:

\[
P=DE,\qquad P^2=P.
\]

The module proves

\[
\operatorname{range}P=\operatorname{range}D,\quad
\ker P=\ker E,\quad
\operatorname{range}(1-P)=\ker E.
\]

More substantially, `splitEquiv` constructs the actual native linear
equivalence

\[
B\simeq_R L\times\ker E,
\qquad x\longmapsto(Ex,x-DEx),
\]

with explicit inverse `(b,k) ↦ D b + k`. There is no assumed splitting
field or choice of an unconstructed inverse.

This explains precisely what the source's boundary-reconstruction language
requires (section 2.5, pp. 12-13). If `k` is a nonzero hidden state, then
`x` and `x+k` are different bulk states with the same encoding.
Under `ED=1`, the theorem `full_reconstruction_iff_injective` proves

\[
DE=1_B\quad\Longleftrightarrow\quad E\text{ is injective}.
\]

Over a division ring `K`, full reconstruction and finite-dimensional
`Boundary` give the capacity bound `finrank K Bulk ≤ finrank K Boundary`.
A separate finite-set theorem proves the corresponding cardinality bound.
When `Bulk` is finite-dimensional and `ED=1`, rank-nullity accounts exactly
for the hidden component:

\[
\dim L+\dim\ker E=\dim B.
\]

These are algebraic reconstruction results. They do not derive a physical
bulk spacetime, entropy-area law, or bulk-boundary propagator.

## 2. The retained sector is a genuine noncommutative operator corner

For an arbitrary boundary endomorphism `A`, define

\[
\Phi(A)=DAE\in\operatorname{End}_R(B).
\]

The hypothesis `ED=1` proves

\[
\Phi(AB)=\Phi(A)\Phi(B),\qquad
\Phi(A+B)=\Phi(A)+\Phi(B),\qquad
\Phi(1)=P.
\]

`liftOperatorHom` bundles this as Mathlib's native `NonUnitalRingHom`.
It is deliberately non-unital as a map into all bulk endomorphisms: the
image of the boundary identity is the recoverable projector, which need
not be the bulk identity.

The lift is injective and its image is characterized exactly:

\[
X\in\operatorname{range}\Phi
\quad\Longleftrightarrow\quad PXP=X.
\]

Thus this is an actual faithful identification with the recoverable
corner, expressed through a native homomorphism and a proved image theorem.
The file also proves

\[
\Phi([A,B])=[\Phi(A),\Phi(B)],\qquad
[\Phi(A),\Phi(B)]=0\Longleftrightarrow[A,B]=0.
\]

No diagonalization, commutativity hypothesis, or scalar replacement is used.
The general module theorems have no finite-dimensional assumption; only the
explicit dimension bounds invoke finite-dimensional hypotheses. No analytic
completion, topological limit, or Morita-equivalence theorem is claimed.

## 3. Ordered transport gives finite amplitudes and gauge-invariant traces

Owner: `InfoGeometry.Holographic.PathAmplitudes`.

The file imports the existing
`Canonical.OperatorContentNetwork.PathTransport` owner. The carrier is a
native quiver with arbitrary real square-matrix edge labels. Products follow
the owner's left-to-right path-word convention.

For a finite family of paths with fixed endpoints,

\[
\mathcal A_{ab}=\sum_i w_i T(\gamma_i),
\]

the new theorem proves the endpoint gauge law

\[
\mathcal A'_{ab}=G_a\mathcal A_{ab}G_b^{-1}.
\]

The composition theorem preserves the exact ordered products:

\[
\mathcal A_{ab}\mathcal B_{bc}
=\sum_{i,j}w_i v_jT(\gamma_i\cdot\delta_j).
\]

Only real scalar weights commute; the proof does not exchange the matrix
transports. For loops, `loop_amplitude_trace_gauge` derives trace invariance
from Mathlib's cyclic matrix trace theorem. The loop matrix itself transforms
by conjugation and is not asserted to be gauge invariant.

The module also proves that a nontrivial loop obstructs both path independence
and a global vertex potential. This identifies an obstruction to the source's
definition of phase using "any path" (section 5.3, pp. 19-20). On an arbitrary
directed quiver, trivial loop holonomy alone need not imply path independence
or existence of a global vertex potential.

For finite edge set `Edge` and exactly `steps` time slices, native finite-type
cardinality gives

\[
\#\{\text{quarter-phase histories}\}
=4^{\#\mathrm{Edge}\cdot\mathrm{steps}}.
\]

Both cutoffs are explicit. A finite graph alone can have infinitely many
walks. No continuum path-integral convergence is asserted.

## 4. The proposed curvature-to-metric formula has an exact obstruction

Owner: `InfoGeometry.Holographic.CurvatureObstruction`.

The source defines (Eq. 30, p. 29)

\[
F_{ij}(p)=A_j(s_i p)-A_i(s_j p)-A_j(p)+A_i(p).
\]

The implementation makes the shift maps explicit and proves

\[
F(p)^T=-F(p),\qquad
H^T=-H,\quad H=\sum_{p\in S}w_pF(p).
\]

The cutoff `S` is finite; the weights alone are not treated as an infinite
summability proof. For symmetric `eta`, the decisive theorem is

\[
(\eta+\kappa H)^T=\eta+\kappa H
\quad\Longleftrightarrow\quad\kappa H=0.
\]

If `kappa ≠ 0`, this is equivalent to `H=0`. A nonzero skew term therefore
cannot supply the symmetric metric perturbation claimed in Eq. 31.

The existing `OperatorAlgebra.RealMatrixSplit` owner is used to identify the
native self-adjoint part with `eta` and the skew-adjoint part with `kappa • H`.
It also supplies the exact ordered normality defect

\[
M^TM-MM^T=2\kappa(\eta H-H\eta),\qquad M=\eta+\kappa H.
\]

The alternative Gram expression `eta + kappa • (H * H.transpose)` is proved
symmetric. This is an algebraic observation, not a derivation of a metric's
nondegeneracy, signature, or Einstein equations.

## 5. Prime arithmetic and the circle intersection

Owner: `InfoGeometry.Holographic.ArithmeticGeometry`.

The arithmetic results use native `Nat.Prime`:

- `p > 3` and primality imply `p % 6 = 1` or `5`.
- For twin primes beyond `(3,5)`, the residues are `(5,1)`.
- `25` and `35` certify that neither residue class implies primality.
- Moduli 3 and 4 also restrict the relevant primes to two possible residue
  classes, correcting the source's minimality assertion as stated.
- Mathlib's CRT ring equivalence sends `1` to `(1,1)` and `5` to `(1,2)`.

The quadratic result proves the exact equivalence

\[
\begin{cases}
x^2+y^2-u^2-v^2=1,\\
x^2+y^2+u^2+v^2=1
\end{cases}
\quad\Longleftrightarrow\quad
u=v=0\ \text{and}\ x^2+y^2=1.
\]

The rational point `(3/5,4/5,0,0)` satisfies the intersection equations and
lies outside the four coordinate directions. Selecting four cardinal points
from this circle is additional data, not a consequence of the intersection.
None of these arithmetic or quadratic statements selects a continuous
Standard Model gauge group.

## 6. Unique factorization does not force prime-distribution asymptotics

Owner: `InfoGeometry.Holographic.MonoidCounterexample`.

The native carrier `Multiplicative ℕ` is the free cyclic monoid. Put
`q = Multiplicative.ofAdd 1`. The implementation proves:

\[
q^n=\operatorname{ofAdd}(n),\qquad
q^m\mid q^n\Longleftrightarrow m\le n.
\]

Powers are injective and form a strict divisibility chain at every successor.
Every element has a unique exponent and a unique finite list factorization
into irreducibles. Nevertheless,

\[
\operatorname{Irreducible}(x)\Longleftrightarrow x=q.
\]

This is a concrete countermodel to the algebraic implication asserted in
section 4.1, p. 16: associativity, identity, unique factorization, and unbounded
compositional depth do not force infinitely many irreducibles. They cannot
alone force prime-number-theorem asymptotics. The paper does not specify the
height/counting structure needed for its distribution claim.

The example is an ordinary monoid. Mathlib's `UniqueFactorizationMonoid`
class requires an absorbing zero, so the code proves the ordinary monoid's
factorization property explicitly instead of introducing an artificial
instance or assuming the conclusion.

## 7. The real information budget is a conditional theorem

Owner: `InfoGeometry.Holographic.RateBudget`.

For real rates, the postulated budget and calibration are

\[
I_{\rm int}^2+I_{\rm sp}^2=M^2,
\qquad I_{\rm sp}=vM/c.
\]

With `M > 0` and `c > 0`, the module proves `|v| ≤ c`. With a nonnegative
internal rate, it proves

\[
I_{\rm int}=M\sqrt{1-v^2/c^2}.
\]

These are consequences of the supplied real budget, not a derivation of
the Lorentz transformation group or observer independence. The source's
complex phase-weighted sums require separate reality and convergence results.

The module additionally proves that the printed inequality in Eq. 25,
at unit effective speed,

\[
|\Delta t|+d\le|\Delta t|,\qquad d\ge0,
\]

is equivalent to `d=0`. It also proves nonnegativity of the source's finite
real lattice-energy expression for nonnegative weights. Physical use of the
energy formula requires nonzero coupling; the algebraic theorem explicitly
documents Lean's total division convention at zero.

## 8. Validation and integration boundary

The source modules are added to `InfoGeometry.All` through six imports.
They reuse the existing path-transport and real-matrix-split owners and the
repository's unchanged pinned Mathlib version.

The following are distinct pieces of evidence:

| Check | Observed result |
|---|---|
| Selected source-closure compilation | Nine repository modules passed; all returned zero, with zero compiler warnings |
| Native declaration axiom audit | 104 declarations; only the three permitted foundational axioms |
| Strict placeholder scanner | Exit 0; no hard findings; three soft lexical findings independently classified |
| Strict OpenGauss screener and refutation scan | Exit 0; no traps |
| Static Gate 4 | Exit 0; correctly reports that the static command itself does not run the kernel |
| Semantic-vacuity gate | Exit 0 at error threshold; two warnings for short native corollaries independently reviewed as legitimate |
| Independent source review | PASS at recorded source hashes |
| Independent fresh verification | `ACCEPTED_WITH_LIMITED_SCOPE`: all nine repository modules freshly compiled without incremental reuse; 104 declarations audited; all source gates passed at their stated thresholds |
| Root path-package preflight | Blocked by the existing missing path dependencies listed below |

The soft findings are not suppressed or relabeled as compiler failures:
ordinary kernel `decide` proves closed finite arithmetic facts; module
parameters are the actual ring/module carriers; and the short pure-potential
amplitude/history-count proofs reuse substantive native theorems.

The root package build is blocked in this checkout by the following path
dependencies:

- `external_refs/atlas-lean`: untracked path dependency; configuration absent.
- `external_refs/homotopy-hypothesis-lean4`: untracked path dependency;
  configuration absent.
- `external_refs/gift-framework-core`: recorded gitlink
  `e6f3c3ac2140c2324fb2ae029c32233e73aa5e92` is uninitialized.

The maintained `ci_bootstrap.py paths` command reports these conditions.
No dependency pin was changed, no stub package was introduced, and the
root publication gate is not claimed to pass. The selected source-closure
certificate does not certify the remainder of `InfoGeometry.All` or the
white paper's physical interpretations.

### Reproduce the selected verification

Run from the repository root with an initialized, exact-pinned Mathlib cache
and the matching Lean executable:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /path/to/mathlib-4.34.1 \
  --lean /path/to/lean-4.34.1/bin/lean \
  --output /tmp/holographic-verification \
  --target InfoGeometry.Holographic.BoundaryReconstruction \
  --target InfoGeometry.Holographic.CurvatureObstruction \
  --target InfoGeometry.Holographic.ArithmeticGeometry \
  --target InfoGeometry.Holographic.RateBudget \
  --target InfoGeometry.Holographic.PathAmplitudes \
  --target InfoGeometry.Holographic.MonoidCounterexample

python3 tools/quality/placeholder_audit.py \
  --strict --root lean/InfoGeometry/Holographic
python3 tools/infra/opengauss_screener.py \
  --strict lean/InfoGeometry/Holographic
python3 tools/infra/opengauss_cli.py refute \
  lean/InfoGeometry/Holographic --strict
python3 tools/quality/semantic_vacuity_gate.py \
  lean/InfoGeometry/Holographic --fail-on error
python3 tools/infra/ci_bootstrap.py paths --root .
```

Despite its historical filename, the maintained source-closure checker accepts
the explicit target list, checks dependency/toolchain pins, acquires the shared
build lock, compiles the import closure, and audits all selected declarations.

## Remaining mathematical work

The input does not provide enough mathematical data to derive its physical
claims from the proved fragments. Explicit further constructions would be
needed for the proposed prime-indexed Hilbert space and infinite sums,
continuum gauge fields, self-adjoint dynamics, K₃-to-Sierpiński geometry,
Hausdorff dimension, the Lorentz group, a spin double cover, boundary-to-bulk
field equations, entropy scaling, and Einstein-equation emergence.

In particular, the source's own qualification in section 5.6.1, pp. 21-22,
should be preserved: CRT is arithmetic, while its proposed identification
with continuous gauge groups is an interpretation requiring additional work.
