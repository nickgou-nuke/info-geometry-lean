# Majorana quartets and fourth-order clock re-encoding

## Intent and provenance

Task: formalize the exact operator content of the supplied parafermion narrative
in Lean 4, using native Mathlib carriers and existing repository owners, and
prepare an upstream commit and pull request. Publication is authorized in the
conversation. This change is independent of the earlier Kitaev rotor PR #300.

Baseline: `3d7eb6d9b0af5636ab12b3d0b91b82740507e49e` on upstream `main`.
Compiler: `leanprover/lean4:v4.34.1`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
No dependency or toolchain change is part of this task.

The normalized source is preserved in
[`PARAFERMION_QUARTET_SOURCE.md`](PARAFERMION_QUARTET_SOURCE.md).
Its SHA-256 is
`d4a83d56fa8469f2e3f1c32097add21d591d711154c0cd9daed58ede880aa204`.
The provenance note distinguishes this transcription from a raw chat export.

Risk classification: R2 for reuse of existing finite algebra owners; R4 for the
proposed physics interpretation. The latter is not promoted by finite matrix
verification. Generation, semantic audit, and acceptance are separate roles.

## Atomic claim ledger

| ID | Supplied claim | Formal disposition |
| --- | --- | --- |
| C1 | Majoranas satisfy squares one and pairwise anticommutation. | Existing `MajoranaSystem`; self-adjointness is a separate explicit assumption. Construct the actual four-matrix instance. |
| C2 | A fourfold Majorana product supplies a quartic interaction. | Prove the ordered product is an involution, self-adjoint under the stated star assumptions, and odd against each constituent generator. |
| C3 | A quartic interaction destroys parity. | Prove that any operator anticommuting with all four generators commutes with their product and its scalar Hamiltonian. Subsystem parity requires a separately specified subsystem. |
| C4 | Four Majoranas can be re-encoded as a fourth-order phase pair. | Prove explicit forward and inverse polynomial identities in the existing native `Matrix (Fin 4) (Fin 4) ℂ` model, and equality of the generated native subalgebras. |
| C5 | The exchange law implies non-Abelian braiding. | Open: static phase exchange supplies neither braid operators nor their Yang–Baxter, locality, adiabatic, or protection properties. |
| C6 | A single quartic interaction creates a protected topological phase. | Open: prove the finite Hamiltonian's actual spectrum and characteristic polynomial; no phase diagram, chain limit, edge localization, or phase transition follows. |
| C7 | At N=4, `(sqrt N)^M` grows differently from `(sqrt 2)^(2M)`. | False numerical comparison: both equal `2^M`. A physical count also needs a fixed number of defects and a total-charge sector. No separate wrapper theorem is needed for elementary power arithmetic. |
| C8 | The cyclic generator can be identified with a higher nilpotent variable. | Contradiction if the same element has fourth power both one and zero in this nontrivial matrix ring. Reuse the existing cyclic/nilpotent separation owner. |
| C9 | Roots of unity replace KO theory with a quantum group. | Open: no Hopf algebra, quantum-group relations, or classification map is supplied. |
| C10 | A quantum super-Grassmannian/amplituhedron follows. | Open: no coordinate algebra, deformation, or connecting morphism is supplied. |
| C11 | The construction proves a SYM mass gap and removes loop IR divergences. | Open: no relevant SYM Hamiltonian, vacuum, spectral lower bound, or analytic estimate is supplied. A four-state spectrum is not this statement. |
| C12 | Brown invariants and experimental realization. | Context and possible later tasks; no quadratic refinement, Gauss-sum classification, or experimental analysis is claimed here. |

## Existing owners and bounded discovery

Searches covered repository-owned `lean/`, `proofs/`, and `lib/` using Majorana,
quartic, Fidkowski, parafermion, clock/shift, CAR, parity, and cyclotomic names,
then followed the carriers and imports of the selected owners. This is a
bounded source search, not a claim of an exhaustive theorem index.

| Owner | Actual reusable surface | Boundary |
| --- | --- | --- |
| `Algebra.CliffordBraidingInterfaces` | `MajoranaSystem n A`: `gamma`, `square_one`, `anti_comm`. | These fields are assumptions until a concrete instance is constructed. Its `ParafermionSystem` uses the opposite index/product convention from the supplied text. |
| `Quantum.MajoranaVacuumWickFour` | `gamma : Fin 4 → Mat4C`, the explicit Jordan–Wigner matrices `X⊗I`, `Y⊗I`, `Z⊗X`, `Z⊗Y`. | Existing vacuum and Wick identities do not prove the quartet re-encoding. |
| `Algebra.FourthRootPeirceProjectors` | `degreeClock`, `cyclicShift`, their fourth powers, `degreeClock_shift`, complete Fourier projectors and their covariance. | Actual finite matrices and spectral corners; no topological phase theorem. Reuse these definitions unchanged. |
| `Algebra.CyclicShiftNilpotencySeparation` | Native four-state cyclic and truncated shifts; fourth power one versus zero. | Separates covariance from nilpotency; does not identify the two operators. |
| `Core.FinitePeirceMatrix` | Complete orthogonal idempotents, block multiplication, and corner equivalence. | Algebraic decomposition, not a quantum super-Grassmannian. |
| `Canonical.CyclotomicProjectorReadout` | Fourier readout from supplied complete spectral projectors. | Structure fields are hypotheses; the fourth-root owner constructs the relevant projectors. |
| `Algebra.OperatorCyclotomicParafermions` | Ordered operator polynomials, Reynolds sums, and nilpotent/cyclotomic identities. | The inspected sections do not construct the requested Majorana quartet re-encoding. |
| `Algebra.ParafermionGaugeTwist` | Conditional central-phase twisted Cuntz maps. | A different carrier and conditional theorem. |
| `Topology.ParafermionBraiding` | A concrete three-dimensional Burau-style Artin relation. | A different representation, not braid dynamics of the four-state clock pair. |
| `Canonical.MajoranaUHFJordanWignerInduction` | Successor CAR and parity constructions. | Not a proof of condensation from one fourfold monomial. |
| Mathlib native spectrum and subalgebra owners | `spectrum.pow_mem_pow`, `spectrum.scalar_eq`, matrix spectrum/characteristic polynomial, and `Algebra.adjoin`. | Native algebraic consequences; do not import a physical interpretation through the names. |

The relevant categorical infrastructure map was consulted. Existing
categorical Majorana, Fibonacci, and monodromy owners are separate constructions;
this task supplies no new categorical equivalence or colimit theorem.

### Focused import boundary

Source-level import traversal found that `FourthRootPeirceProjectors` reaches
418 repository modules through the concrete readout imports. The new bridge
needs only its already-proved finite clock/shift algebra. The approved
owner-preserving extraction moves these eight declarations verbatim to
`Algebra.FourthRootClockShift`, retaining their existing fully qualified names:
`phase`, `phase_fourth`, `cyclicShift`, `degreeClock`, `cyclicShift_fourth`,
`degreeClock_fourth`, `degreeClock_shift`, and `cyclicShift_fourth_ne_zero`.
`FourthRootPeirceProjectors` imports the focused owner and retains all
projector-dependent definitions and proofs. There is no duplicate clock model
or compatibility alias. Validate declaration text preservation, the focused
owner, the edited owner where its baseline dependencies permit, and direct
consumers at their observed scope. A source-preservation check is distinct
from compilation of the original broad dependency graph.

## Contract A: generic quartic Majorana algebra

Candidate owner: `InfoGeometry.Algebra.MajoranaQuartic`.

Reuse `s : MajoranaSystem 4 A`, with `[Ring A]`, and define the ordered product

\[
Q = s.\gamma(0)s.\gamma(1)s.\gamma(2)s.\gamma(3).
\]

Prove `Q * Q = 1`, and `Q * s.gamma i = -(s.gamma i * Q)` for each `i`.
If a star-ring structure is available and all four generators are
self-adjoint, prove `IsSelfAdjoint Q`. If `p` anticommutes with each generator,
prove native `Commute p Q`.

Over a central coefficient field `K` with `[Algebra K A]`, define
`H(g) = (-g) • Q`. Prove

\[
H(g)^2=g^2\,1,\qquad
\operatorname{spec}_K(H(g))\subseteq\{g,-g\}.
\]

The spectrum theorem is a native `spectrum` statement. It is a containment;
existence of both eigenvalues is not inferred in an arbitrary algebra. For
real coupling in a star-compatible algebra, prove self-adjointness of `H(g)`.
Transport the parity commutation result through the scalar action.

## Contract B: explicit operator re-encoding

Candidate owner: `InfoGeometry.Algebra.MajoranaClockReencoding`.

Carrier: the existing native `Matrix (Fin 4) (Fin 4) ℂ`, with the exact matrices
`gamma`, `degreeClock`, and `cyclicShift` from the owners above. Establish the
Majorana hypotheses and construct the existing `MajoranaSystem` interface.

Use ordered matrix multiplication. With `c₀,…,c₃ = gamma 0,…,gamma 3`, set

\[
z=-i c_0c_1,\quad w=-i c_2c_3,\quad x=c_0,\quad y=zc_2,
\qquad P_\pm=(1\pm w)/2.
\]

Prove the explicit forward polynomial identities for the existing matrices
`C = degreeClock` and `S = cyclicShift`:

\[
C=z(P_++iP_-),\qquad S=yP_++xyP_-.
\]

Prove the inverse reconstruction, including the required identities

\[
x=S^2,\quad w=C^2,\quad
z=C(P_+-iP_-),\quad y=S(P_++xP_-),
\]

and recovery of each `gamma` by the corresponding ordered polynomials.
Conclude native subalgebra equality

\[
\operatorname{Algebra.adjoin}_{\mathbb C}(\operatorname{range}\gamma)
=\operatorname{Algebra.adjoin}_{\mathbb C}\{C,S\}.
\]

Prove actual noncommutation `C*S ≠ S*C` and unitarity in the native star/matrix
API. Reuse the existing `C^4=S^4=1` and `C*S=i•(S*C)` laws. Assigning
`α₁=S`, `α₂=C` matches the user's `j>i` exchange orientation exactly. A native
`ParafermionSystem` consumer, if used, must account for that interface's
different order convention rather than silently reversing a sign.

In this explicit ordering `C² = w` is the second-site parity. Total two-site
fermion parity is `z*w = -Q`. These operators are distinct. In particular, do
not identify this local clock square with the separately defined global
symmetry square discussed in the external fermionization paper.

## Contract C: concrete quartet spectrum

Candidate owner: `InfoGeometry.Quantum.MajoranaQuarticFour`.

Instantiate Contract A with Contract B's proved matrix Majorana system.
Identify the actual matrices

\[
Q=\operatorname{diag}(-1,1,1,-1),\qquad
H(g)=\operatorname{diag}(g,-g,-g,g).
\]

Prove native spectrum equality `spectrum ℂ H(g) = {g,-g}` and characteristic
polynomial

\[
\operatorname{charpoly}(H(g))=(X-C(g))^2(X+C(g))^2.
\]

Here `C(g)` denotes Mathlib's constant polynomial, not the clock matrix.
When `g ≠ 0` the two roots are distinct and each has algebraic multiplicity two;
at `g = 0` they coincide. The polynomial factorization itself is valid for all
couplings. Do not claim a separate multiplicity API theorem unless one is
actually proved. This four-state finite Hamiltonian supplies no many-body
topological protection or field-theoretic mass gap.

## Dependency order

Only the following proof dependencies are intended:

1. Existing ring/field/matrix operations and CAR hypotheses give the ordered
   quartet identities and parity conservation.
2. The quartet's quadratic equation gives the generic spectrum containment.
3. Existing concrete Majorana matrices satisfy the interface hypotheses.
4. Their forward and inverse ordered polynomials identify the generated
   subalgebra with that of the existing fourth-root clock and shift.
5. The concrete quartet calculation identifies its diagonal Hamiltonian;
   native matrix spectrum and characteristic-polynomial results then give the
   exact finite spectral result.

The physical phase, braid dynamics, quantum-group deformation, and SYM claims
are outside this proved dependency order.

## Literature boundary

These are external primary sources, not kernel evidence:

- [Chew, Mross, Alicea, arXiv:1802.04809](https://arxiv.org/abs/1802.04809),
  equations (69)–(70): Majorana-quartet/parafermion reorganization; the surrounding
  discussion explicitly cautions about locality and physical interpretation.
- [Fendley, arXiv:1209.0472](https://arxiv.org/abs/1209.0472): clock/string
  parafermion algebra and edge-zero-mode constructions for specified chains.
- [Fidkowski, Kitaev, arXiv:0904.2197](https://arxiv.org/abs/0904.2197): the
  interaction-induced `ℤ → ℤ₈` classification result under specified symmetry
  conditions, distinct from the narrative's generic quartet-to-phase claim.
- [Lindner et al., arXiv:1204.5733](https://arxiv.org/abs/1204.5733): physical
  interface models, charge-sector ground-state counting, and separately
  constructed braid unitaries satisfying Yang–Baxter relations.

## Acceptance plan

Generators work in isolated candidate directories. The root agent reads the
actual candidate source and audits the theorem meanings. A fresh independent
acceptance agent reruns strict compilation and type/value axiom inspection on
the frozen files. Only then are byte-identical candidates promoted.

Required checks: exact compiler/dependency fingerprints; strict narrow compile;
no placeholders, custom axioms, `native_decide`, or unsafe bypasses; source
semantic review; actual noncommutative witness; permitted axiom closure only
(`propext`, `Classical.choice`, `Quot.sound`); staged proof gate and actual Git
hooks. Any root build/dependency failure is reported at its observed scope.
The previous task's missing `HomotopyHypothesis` dependency is a lead to check,
not a current test result. Final commands, hashes, warnings, and scope are
recorded separately after execution.
