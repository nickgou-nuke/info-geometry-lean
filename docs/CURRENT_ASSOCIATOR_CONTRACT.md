# Real Clifford currents and split-octonion dissipation

## Source and scope

This change extracts algebraic and finite operator statements from two supplied
notes. It preserves the existing native Mathlib Clifford algebra and the existing
quaternion-pair split-octonion algebra. A linear coordinate chart is never treated
as a multiplicative identification between those algebras.

The source inputs, read in full, are:

| Input | SHA256 |
|---|---|
| `Pasted text(20261117-085825).txt` | `b9de16352e57d99545684be35d91d935df030bc68a57849584caaff133edede0` |
| `Pasted text (2)(20261117-091052).txt` | `1fef0d88c605c9d59f6590503b776362454f6b30b5022bbdec25dc1b12960e48` |

The base is upstream commit `08c34e03f610b452e03422037949196dc7d92d6d`.
The work is independent of the pending real Krein–Cartan PR #377. PR #371's
Klein/CAR native verification has already passed at its own published head;
the second input's description of that earlier CI as queued is historical.

The acceptance state belongs in [CURRENT_ASSOCIATOR_VERIFICATION.md](CURRENT_ASSOCIATOR_VERIFICATION.md).
Complete proof terms in source and independent review are distinct from native
kernel acceptance.

## Existing owners and the missing connections

The source search inspected definitions, hypotheses, imports, and nearby consumers
in the canonical `lean/InfoGeometry` tree. It did not infer theorem coverage from
filenames or from informal descriptions of results.

| Existing owner | Reused content | New connection |
|---|---|---|
| `Canonical/HestenesClPlus14` | `Q14` of signature `(+---)`, native `CliffordAlgebra Q14`, native even subalgebra and generators | Keep this exact full carrier for the current sandwiches. |
| `Canonical/HestenesPauliSheetBridgeFinite`, `HestenesEvenPauliEquiv` | Explicit paravectors and the proved real algebra equivalence of the entire even algebra with `M₂(ℂ)`; dimensions 16 and 8 | Transport native reversion to the matrix adjugate, then derive both reversion products. |
| `Canonical/HestenesKreinMatrixBridge`, `HestenesHermitianAdjoint`, `HestenesHermitianMatrixBridge` | Native `reverseEven` and the actual `γ₀ reverse(.) γ₀` / conjugate-transpose compatibility | Derive current and axial-current identities without assuming Fierz identities or spinor invertibility. |
| `Canonical/SplitOctonionQuaternionChart`, `SplitOctonionConjugation` | Full eight-dimensional quaternion-pair product, split norm and Cayley conjugation | Prove the scalar sandwich, symmetric scalar pairing and its nondegeneracy in this actual algebra. |
| `Canonical/SplitOctonionRegularOperators`, `SplitOctonionRegularProjectors` | Actual regular linear operators and normalized-axis complementary projectors | Derive nullity and the cross-pairing formula for these existing projectors. |
| `Algebra/SplitOctonionManivelCompositionBridge` | Full norm composition for the same quaternion-pair carrier | Confirms the existing composition-algebra interface; the scalar-potential proof uses a smaller direct dependency set. |
| `Physics/FiniteOnsagerGram` | Exact Gram contraction and nonnegative production | Construct an explicit energy-annihilating projector and apply Gram positivity to the projected actual associator channels. |
| `SuperMetriplectic/Flow` | Native `OnsagerMetricData` interface | Instantiate the interface with constructed operators and proved laws, rather than accepting PSD as an input. |
| `Thermo/GenericMetriplecticFlow` | State/covector operators and the injective-reversible-operator obstruction | Reuse the distinction between a full entropy Casimir and vanishing reversible entropy rate for one chosen Hamiltonian. |

Nearby simplified current models do not close the native Clifford obligation.
For example, a density defined directly as eight squares needs a theorem relating
it to the actual Clifford sandwich; a two-coefficient matrix readout is not a
faithful representation of an eight-dimensional even spinor. Similarly, the
existing `Clifford/HestenesDirac` conservation packet assumes a conservation field;
extracting that field is not a derivation of the PDE continuity equation.

The import-closure check exposed three archived `proofs.*` imports in the existing
`Canonical/ChiralCausalCone` dependency. They are repaired to the actual canonical
Physics owners, with explicit qualification of their migrated namespaces.
Corresponding declarations and downstream consumers were inspected; the source
repair changes no proof strategy and introduces no duplicate owner. The maintained
compiler checker, build lock and dependency pins are unchanged.

## Dependency order of the mathematical statements

The three chains have separate conclusions. No least-upper-bound argument on a
chosen diagram establishes extra physical laws.

1. Native even Clifford algebra → full Pauli equivalence → reversion/adjugate
   compatibility → scalar–pseudoscalar norm decomposition → current squares,
   mixed anticommutator and covariance → faithful Hermitian paravector inverse →
   actual grade-one current, positive time coordinate and future causality.
2. Native split-octonion product and conjugation → scalar pairing and norm
   polarization → existing axis projectors → nullity and nonzero cross-potential.
3. Native right-regular maps → actual first-slot associator operators → faithful
   eight-coordinate linear chart → explicit energy projection → projected Gram
   operator → energy degeneracy, exact production, and its zero/strict criteria.

## Clifford contract

Write `ψ : HestenesCl14.ClPlus14`, `I = volumeEven`, and let `a(ψ), b(ψ)`
be the real and imaginary parts of the determinant under the existing full
Pauli equivalence. `HestenesCurrentAlgebra` derives

\[
\psi\widetilde\psi=\widetilde\psi\psi=a(\psi)1+b(\psi)I,
\qquad I^2=-1.
\]

These numbers are the coefficients in this proved decomposition. The definitions
do not postulate a scalar projection on arbitrary Clifford elements.

For the actual sandwiches

\[
J=\psi\gamma_0\widetilde\psi,
\qquad A=\psi\gamma_3\widetilde\psi,
\]

the identities are

\[
J^2=(a^2+b^2)1,\qquad A^2=-(a^2+b^2)1,\qquad JA+AJ=0.
\]

They hold for singular spinors as well as invertible ones. Sandwich covariance
holds under arbitrary left multiplication, while the coefficient invariance
theorems explicitly assume `R * reverseEven R = 1`. The native current's right
paravector is exactly `ψ * hestenesAdjoint ψ`.

Odd parity and reverse-fixedness are recorded as their own statements. The
separate `HestenesCurrentGeometry` owner goes further: it constructs real vector
coordinates from the full Hermitian Gram image and proves the actual equality

\[
\iota(\mathrm{currentCoordinates}(\psi))=J(\psi).
\]

Its time coordinate equals half the sum of the four squared complex entry norms
of the faithful Pauli image. It is therefore positive exactly when `ψ ≠ 0`,
and its native Minkowski quadratic form equals `a²+b²`. This proves algebraic
future causality in the chosen `(+---)` frame, including nonzero null currents.
The third inverse paravector coordinate is `-Im(A₀₁)`, matching the existing
off-diagonal convention `A₀₁ = x - i y`.

No theorem in this contract establishes a general observer-flux functional,
differentiable Dirac evolution, local continuity, Cauchy-surface integration,
or a spectral energy interpretation.

## Scalar-potential contract

For the actual Cayley conjugation, set `B(x,y) = Re(x * splitConj y)` and
`q(x) = normSQ x`. The fixed-bracketing identity is

\[
\operatorname{Re}((xu)\bar x)=q(x)\operatorname{Re}(u).
\]

Thus the proposed imaginary scalar sandwich is identically zero. The corrected
cross-potential uses the symmetric pairing. For the existing axis `J_g g = (0,g)`
and `Quaternion.normSq g = 1`, both projector images are null, and

\[
B(P_+x,P_-x)=\tfrac12q(x).
\]

At `g = 1, x = 1` its value is `1/2`. The pairing is proved nondegenerate on the
full carrier. These results do not claim a four-dimensional rank theorem for each
projector range, a bundled para-Kähler manifold, a Fréchet Hessian calculation,
or a Monge–Ampère solution.

## Dissipation contract

The auxiliary pairing is the positive ordinary real coordinate dot product.
It is distinct from the indefinite split norm. For any energy covector `h`, define

\[
P_h=I-\frac{hh^T}{h^Th},\qquad M=\gamma(RP_h)^T(RP_h).
\]

The native real-field convention makes `P_0 = I`. The source proves the projector
formula, symmetry, idempotence and `P_h h = 0`, including the zero case.
For `γ ≥ 0`, the constructed `M` is symmetric and positive semidefinite and
annihilates `h`. For every force `v`,

\[
v^TMv=\gamma\|RP_hv\|^2.
\]

For `γ > 0`, this scalar is zero exactly when `RP_hv = 0`, and is strictly
positive exactly when the projected leakage is nonzero. The symbol `γ` is a real
rate, never a Clifford gamma matrix.

The specialization uses the actual first-slot maps

\[
R_k(v)=[v,a_k,b_k]=(va_k)b_k-v(a_kb_k).
\]

Their eight coordinates are stacked into one rectangular matrix. The zero
criterion is exactly that every selected associator of the projected force
vanishes. A quaternion subalgebra only suffices when the arguments of each tested
associator lie together in an associative subalgebra.

The explicit witness uses `h = 1`, `v = ell`, `a = i ell`, `b = j`.
In the repository's multiplication convention `[ell, i ell, j] = -2 k`.
The energy projection retains `ell`, so positive rate gives strictly positive
production with a nonzero energy covector.

The total energy-rate identity combines this constructed dissipation with
`A-Aᵀ`. The total entropy-rate identity requires the explicit pair-specific
condition `s · ((A-Aᵀ) h) = 0`. It does not assert the stronger full Casimir law
for every observable, nor a Jacobi identity for a state-dependent bracket.

## Corrections and analytic boundaries

| Input claim | Correction or remaining obligation |
|---|---|
| The pseudoscalar readout of `(a+bI)I` has scalar coefficient `b` | Its scalar coefficient is `-b`; the source proves the actual product `-b+aI`. |
| Rearranging `∇ψ B - eAψ = mψγ₀`, with `B²=-1`, produces `+eAψB` | Right multiplication by `-B` gives `∇ψ = -eAψB - mψγ₀B`. No PDE is formalized from the inconsistent rearrangement. |
| Every nonzero axial current is strictly spacelike | The square may vanish for singular spinors. Preserve the null cases. |
| Covariance alone proves finite conserved Cauchy charge or bounds a coordinate density under all boosts | A PDE solution, spacetime and observer conventions, integrability and boundary-flux conditions are separate requirements. |
| The sign of a Krein scalar decides energy for general states | A specific Hamiltonian and spectral hypotheses are required. The algebraic bilinear has no automatic general energy interpretation. |
| Universal stability iff `|e ΔV|<2m`, or universal pointwise positivity after normal ordering | These assertions are not established by the spinor algebra and are not included as formal theorems. |
| A nondegenerate symplectic Poisson operator, full entropy Casimir, and positive gradient entropy production all coexist on the same state space | The full Casimir condition forces `dS=0` when the reversible operator is injective. Use a degenerate Poisson structure or state the weaker pair-specific condition explicitly. |
| The Gram construction proves a Landauer heat law | Reservoir, temperature, heat, entropy identification and logical-erasure assumptions are absent. Only the stated finite operator production laws are included. |
| A compact-type temperature generator guarantees Gibbs convergence | Convergence depends on the specified moment map, orbit and measure. The generalized-temperature domain is defined through integrability, not a blanket subalgebra-membership rule. |
| The mixed determinant and full neutral metric determinant give the same logarithm | For mixed block `C`, the full block metric determinant is `(-1)^n (det C)^2`; signs, normalizations and curvature conventions must be tracked. |
| `dx^A ⊙ dx^B = 0` | These tensors do not vanish. The adapted neutral metric has zero coefficients in its same-sector blocks. |
| A geometric potential is automatically a Massieu potential with a canonical entropy | Adding `f(x)+g(y)` leaves the mixed Hessian unchanged but changes the proposed Legendre data. A statistical model and normalization are additional structure. |
| A finite narrative dependency poset proves uniqueness or necessity of the physical synthesis | A dependency order records implications only after each mathematical assertion and its hypotheses have been established. |

Primary references for the two geometric/statistical boundary checks:

- C.-M. Marle, [On Gibbs States of Mechanical Systems with Symmetries](https://marle.perso.math.cnrs.fr/pdffiles/2020/GibbsStatesJGSPPart1.pdf),
  definitions 3.1.2 and proposition 3.1.3: the normally convergent temperature
  domain, when nonempty, is open and convex.
- G. Bor, O. Makhmali and P. Nurowski,
  [Para-Kähler-Einstein 4-manifolds and non-integrable twistor distributions](https://doi.org/10.1007/s10711-021-00665-4),
  section 2.3.3: an explicit convention gives the mixed Ricci components as the
  negative mixed derivative of the logarithm of the mixed Hessian determinant.
  A different sign requires a declared curvature convention.

## Verification requirements

Acceptance requires native compilation of the selected owners and their complete
repository import closure at the unchanged Lean/Mathlib pins, followed by the
native all-declaration axiom audit. The only permitted foundational axioms are
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom
axiom, unsafe proof, `native_decide`, or assumed-target result is introduced.

The source gates, independent review and staged commit hook provide additional
checks. None is reported as a substitute for the Lean kernel. The root Lake
package and analytical/global physical claims remain outside this scoped check.
