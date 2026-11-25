# Nambu scalar sectors and real metriplectic matrix pencils

## Intake and source authority

Task date: 2026-11-23. Base: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
Branch: `codex/nambu-metriplectic-audit-20261123`.

Status: the five-owner baseline passed native compilation, fresh
warnings-as-errors checks and the 157-declaration axiom audit at `d7c16f16` in
[run 45185104156](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45185104156).
The two follow-up owners below were integrated only after that result and are
included in the expanded seven-owner gate. Their acceptance must be read from
the exact source revision's CI result. See the [verification record](../verification/nambu-metriplectic/README.md)
for scope and remaining root integration requirements.

The three uploads contain two distinct notes. Their original bytes and SHA-256
hashes are preserved in `docs/intake/nambu-metriplectic-20261123/`.
The two metriplectic/GRH uploads are byte-identical. The proposed Lean code and
claims of proof in those notes are intake, not compiler evidence.

The user's subsequent audit confirmation and requested native-gated follow-up
are preserved as [normalized conversation intake](intake/nambu-metriplectic-20261123/followup-20261123.md).
The existing `gen_eq_scalarPencil_iff` already owns the coincidence criterion;
the Peirce-defect, Klein-four and KMS-coordinate extensions reuse it. The
baseline compilation, warnings-as-errors and declaration-audit condition was
satisfied before their owner integration.

Primary references:

- C. Sochichiu, [On Nambu-Lie 3-algebra representations](https://arxiv.org/pdf/0806.3520),
  arXiv:0806.3520v2, §§2.2–2.4 and 3.
- A. Mielke, M. A. Peletier, J. Zimmer,
  [Deriving a GENERIC system from a Hamiltonian system](https://publications.imp.fu-berlin.de/3270/1/MielkePeletierZimmer2024-1.pdf),
  §4.1, for the distinction between pointwise rate laws and full GENERIC data.

## Owner search and reuse

The bounded search covered repository-owned Nambu, real Pauli/Clifford,
metriplectic, dual, matrix-split, zeta-dihedral and Weil-positivity source;
related filenames, declaration bodies, imports and consumers were inspected.
The categorical infrastructure map was consulted. No colimit, completion or
analytic consequence is part of this finite construction.

| Existing owner | Reused content |
| --- | --- |
| `Algebra.NoncommutativeZornNambuAssociator` | `Vec3`, ordered `nambu`, `comm`, alternating-cubic and cyclic-commutator formulas |
| `Clifford.Cl11Matrix` | Actual `Mat2`, `Eplus`, `Eminus`, `J1`, native linear map `gen`, and `gen_sq` |
| `Clifford.SignedPermutation` | Existing transpose laws for the two Clifford generators |
| `OperatorAlgebra.RealMatrixSplit` | Native self/skew-adjoint parts and normality/commutation theorem |
| `Clifford.GullDoranPseudoscalarBridge` | Actual real `4 × 4` Pauli matrices and commuting square-minus-one phase |
| `Thermo.GenericMetriplecticFlow` | Existing covector-based `System` and its energy/entropy rate laws |
| `Clifford.SplitQ11CausalCone` | The same-family negative Krein projector, `(1/2) • (1 - Eplus)` |
| `Canonical.Cl11KleinFourAdjointRepresentation` | Native units, algebra automorphisms and `localCl11Map` action |
| `Arithmetic.ZetaCoordinateSymmetry`, `Arithmetic.ZetaDihedral` | Existing centered real chart, three reflections and critical-mirror fixed locus |
| `NCG.KMSStripKleinMonodromy` | Existing real strip-to-zeta map, coordinate recovery and reflection transport |
| Mathlib | `dotProductEquiv`, `Matrix.toLin'`, `Matrix.PosSemidef`, determinants, square roots and native matrix operations |

An independent local branch, `codex/real-nambu-a4-unfolding-20261123`, was
observed at `b6108067`. Its four-generator construction concerns a different
upload and has its own pending validation. It is not imported, copied, or
represented as verified by this change. The present branch starts from main
and does not depend on an unmerged PR.

## Exact implementation contracts

### Mathematical motifs and dependency order

| Motif in the notes | Canonical mathematical object | Dependency that can be stated exactly |
| --- | --- | --- |
| Identity and center | Unit in an associative algebra; scalar commutant | A scalar Nambu slot reduces to a commutator; the additional scalar-commutant hypothesis and one noncommuting pair force the Nambu-central element to vanish |
| Ordered interaction | Associative alternating cubic polynomial | Keep all six ordered products, then use the cyclic-commutator identity |
| Phase and rotation | An operator `J` with `J²=-1` | The common phase commutes with the three specified generators; scalar multiplication is over `ℝ` |
| Quadratic invariant | Explicit scalar Casimir equation | Cyclic commutators and the Casimir give a scalar multiple of `J`; the remaining Nambu equation gives the signed quartic |
| Mirror and split signature | Actual `Cl(1,1)` matrices | The native symmetric/skew decomposition gives the commutation and positivity criteria |
| Conservation and entropy | Covector actions with skewness, positive semidefiniteness and two degeneracies | Construct the existing GENERIC system, then specialize its pointwise energy and entropy laws |
| Arithmetic positivity | Actual zeros, explicit formula and a Weil form | The required analytic map and compatibility/positivity proofs remain open |

The implementation has three separate dependency chains:

1. Associative polynomial → scalar-slot identities → phase/Casimir reduction →
   signed quartic → real scalar obstruction. Separately, the concrete Pauli
   identities and a chosen positive fourth root verify the changed-sign example;
   the scalar quartic alone is not a sufficient representation construction.
2. Real Clifford generators → native adjoint decomposition → commutator,
   positive-semidefinite criterion, scalar-pencil distinction and counterexamples.
3. Native vector/covector duality → matrix construction of the existing system →
   pointwise conservation and entropy production.

The arithmetic conclusion is not a consequence of any of these chains without
the analytic constructions listed under unresolved obligations.

### 1. Associative scalar-sector reduction

Owner: `Algebra.AssociativeNambuScalarReduction`.

The coefficient carrier is an arbitrary associative algebra over a field for
the scalar lemmas, and a nontrivial associative real algebra for the quartic
reduction. Nontriviality is required to deduce `J≠0` from `J²=-1`.
The existing Nambu polynomial is used directly, without a second bracket API.

The first-slot expansion retains all multiplication orders. A scalar first or
third argument gives the corresponding ordinary commutator. Cancellation uses
an explicitly nonzero scalar or nonzero commutator. The center theorem assumes
the scalar-commutant property explicitly; real irreducibility alone is not
substituted for it.

For real operators `J,T₁,T₂,T₃`, assume:

```
J*J = -1,        J*Tᵢ = Tᵢ*J,        t ≠ 0,
[T₂,T₃] = -t⁻¹ • (J*T₁), with the two cyclic analogues,
T₁²+T₂²+T₃² = (t⁻²*c) • 1,
N(T₁,T₂,T₃) = (k*t) • J.
```

The conclusion is `k*t⁴ = -c`. The Euclidean sign `k=1` gives `t⁴=-c`;
the changed sign `k=-1` gives `t⁴=c`. When `c>0`, the Euclidean remaining
equation is impossible. This is a no-go result for the displayed scalar-sector
hypotheses, not a classification of arbitrary Hermitian representations.

### 2. Actual real Pauli equations

Owner: `Algebra.RealPauliNambuSign`.

The carrier is the existing `Matrix (Fin 4) (Fin 4) ℝ` family. Write its three
symmetric matrices as `P₁,P₂,P₃` and its skew phase as `Ω`. The source retains
ordinary associative matrix multiplication and the original Nambu polynomial.

For real coefficients and a common spatial scale `c`, the exact first cyclic
formula is

```
N(μ₀ I + μ₁ P₁ + μ₂ P₂ + μ₃ P₃, c P₁, c P₂)
  = c² (2 μ₀ Ω P₃ + 6 μ₃ Ω).
```

The other cyclic formulas are separate declarations. If `c≠0`, the three
equations `N(T₄,Tᵢ,Tⱼ)=-ΩTₖ` force `μ₁=μ₂=μ₃=0` and `2μ₀c=-1`.
Adding the Euclidean fourth equation forces `μ₀⁴=-3/4`, hence impossibility
over the real coefficients of this ansatz.

For the changed fourth sign, the construction is explicit:

```
t = sqrt(sqrt(3/4)),  c = -(2t)⁻¹,
T₄ = t I,            Tᵢ = c Pᵢ.
```

All four matrices are symmetric and nonzero. All four displayed equations
are provided individually, including `N(T₁,T₂,T₃)=-ΩT₄`.
The source also proves independence of the four coefficient directions.

This does not assert raw-bracket closure on their real span, a Filippov
identity on arbitrary matrices, or a Krein-adjoint representation of the
unchanged Euclidean equations.

### 3. Clifford pencil versus scalar multiplication

Owner: `Clifford.Cl11MetriplecticPencil`, extending the `Cl11Matrix` namespace.

The existing `gen (σ,γ)` is `σ Eplus + γ Eminus`. Its native self-adjoint part
is `σ Eplus`, and its skew-adjoint part is `γ Eminus`. The ordered commutator is

```
[σ Eplus, γ Eminus] = +2σγ J1.
```

It vanishes exactly when `σ=0` or `γ=0`. The native general matrix-split theorem
therefore gives the same condition for `IsStarNormal (gen (σ,γ))`.
The square is the existing `gen_sq` theorem; the determinant is `γ²-σ²`.
Mirror conjugation negates the pencil.

The real quadratic form of the symmetric part is `σ(v₀²-v₁²)`. Both the
quadratic criterion and Mathlib's `Matrix.PosSemidef` predicate are equivalent
to `σ=0`; for nonzero `σ`, explicit directions of both signs are supplied.

Real scalar multiplication is separately represented by
`scalarPencil σ γ = σ I + γ Eminus`. Its ordinary two-coordinate multiplication
law and determinant `σ²+γ²` are explicit. It equals the Clifford pencil exactly
when `σ=0`. `gen (1,1)` is a nonzero square-zero matrix. These facts prevent the
two constructions from being silently identified.

The nonstationarity witness has zero symmetric part but sends `(1,0)` to a
nonzero vector. Zero dissipation alone does not imply a stationary vector.

### 4. Real matrix root

Owner: `Clifford.Cl11EighthRoot`, extending `Cl11Matrix`.

The constructed real matrix is `R=(I+Eminus)/sqrt(2)`, with
`R²=Eminus`, `R⁴=-I`, `R⁸=I`, and `Rᵀ≠R`. The nonsymmetry assertion is part
of the contract. A real matrix root is not a real scalar root or a symmetric
solution of the Euclidean scalar-sector equations.

### 5. Matrix realization of the owned GENERIC system

Owner: `Thermo.MatrixGENERICRealization`.

For an arbitrary finite coordinate index, Mathlib's `dotProductEquiv` identifies
vectors with actual covectors, and `Matrix.toLin'` supplies their matrix action.
This constructs the existing `GenericMetriplecticFlow.System` from
`Lᵀ=-L`, `M.PosSemidef`, `M gradH=0` and `L gradS=0`.

The energy and entropy laws reuse the existing abstract owner:

```
gradH · (L gradH + M gradS) = 0,
gradS · (L gradH + M gradS) = gradS · M gradS ≥ 0.
```

No differentiable functions, ODE solution or Jacobi identity is assumed to
have been constructed. Injectivity of `L.mulVec` and the entropy degeneracy
force `gradS=0`; this limitation is exposed explicitly.

### 6. Peirce defect and the existing Klein four action

Owner: `Clifford.Cl11MetriplecticSymmetry`.

The two real matrix pencils have the exact defect

```
gen (σ,γ) - scalarPencil σ γ = (-2*σ) • matrixKreinMinusProjector.
```

The projector is `(1/2) • (1 - Eplus) = diag(0,1)` from the same matrix
family. The already-owned `gen_eq_scalarPencil_iff` is reused, not duplicated.

| Native tag and conjugation | Clifford-pencil coordinates | Scalar-pencil coordinates |
| --- | --- | --- |
| `P`: `Eplus * A * Eplus` | `(σ,-γ)` | `(σ,-γ)` |
| `T`: `J1 * A * J1` | `(-σ,-γ)` | `(σ,-γ)` |
| `PT`: `(-Eminus) * A * Eminus` | `(-σ,γ)` | `(σ,γ)` |

The source exposes these identities through the existing `adjointAlgEquiv`
and `localCl11Map`; it creates no second action. The native causal unit has
value `Eminus` and inverse `-Eminus`, and its adjoint agrees with the displayed
order because the scalar minus sign is central. The scalar pencil's identity
coefficient stays fixed under every inner conjugation. The conjugations form
the existing Klein four image; the four raw matrices are not asserted to be a
four-element multiplicative group.

### 7. Real zeta-chart and KMS midline transport

Owner: `NCG.MetriplecticZetaKMSBridge`.

The only new definitions evaluate the existing pencils on the existing chart:

```
chartPencil z       = gen (centeredSigma z, z.tau)
chartScalarPencil z = scalarPencil (centeredSigma z) z.tau.
```

Here `centeredSigma z = z.sigma - 1/2`. The three matrix conjugations transport
the chart's conjugation, functional dual and critical mirror. Coincidence is
equivalent to the chart critical line, to fixedness under its critical mirror,
and through the existing chart conversion to `ZetaDihedral.gamma z.toComplex = z.toComplex`.

The existing map is `kmsToZeta β (t,τ) = (1 - τ/β, t/β)`. For `β > 0`,
coincidence of the two evaluated matrix pencils is equivalent to `τ = β/2`.
The three matrix conjugations transport `(t,τ)` respectively to `(-t,τ)`,
`(-t,β-τ)` and `(t,β-τ)`. This is the imaginary-time strip midline; it is
distinct from the owner's separate logistic real-time compactification.

Every matrix coefficient remains real. The existing conversion to a complex
chart is used only to identify its fixed locus. These coordinate identities
construct no zeta/L-function zero correspondence, arithmetic positivity
theorem, analytic KMS state or equilibrium trajectory.

## Corrections to the prose intake

1. The Clifford commutator sign was negative in the uploads and is positive
   for their displayed matrices.
2. `σZ+γε` is a Clifford-vector representation, not the algebra representation
   of the scalar `σ+iγ`. The latter uses `σI+γε`.
3. A symmetric matrix need not be positive semidefinite. The displayed `σZ`
   is indefinite off `σ=0`.
4. Zero quadratic dissipation is not stationary equilibrium, and the fixed
   Krein form `Z` still has a negative direction at `σ=0`.
5. Real irreducibility does not by itself give a real scalar commutant.
6. The paper's Hermitian no-go is qualified by its construction. Its discussion
   of a Lorentzian possibility does not prove the uploaded explicit model;
   the four matrix equations are independently constructed here.
7. The paper's equation (2.24) is not simply a missing global factor of `i`:
   that factor can cancel against (2.22). The first component of (2.25) has
   an inconsistent phase relative to that cancellation. General spatial scalar
   components also contribute terms absent from (2.24). The exact witness
   `N(P₂,I,P₁)=2ΩP₃≠0` records one such contribution. The formalized rigidity
   statement therefore retains its common-scale traceless ansatz.

## Unresolved analytic obligations

No new theorem mentions actual zeta/L-function zeros or a Weil quadratic form.
To turn the matrix positivity condition into an arithmetic conclusion one
would need a constructed map from those analytic objects to this matrix carrier,
its compatibility with the relevant explicit formula and involution, and a
proof that the resulting positivity holds. None follows from defining a pencil.
Contour/Stokes statements also need a domain, regularity, boundary hypotheses,
and treatment of zeros and poles. These obligations remain open.

The separate [GRH analytic-obligation ledger](GRH_ANALYTIC_OBLIGATIONS.md)
records the three required layers: genuine arithmetic data and a faithful
carrier map; explicit-formula and involution compatibility; and positivity
on the actual arithmetic quotient with a proved implication back to zeros.
It distinguishes radical descent from discarding negative directions and
identifies reusable native owners without treating their supplied hypotheses
as constructed arithmetic results. The proposed first analytic family is
primitive Dirichlet L-functions, beginning with the zeta instance; all three
obligations remain open.

## Verification and review

See `verification/nambu-metriplectic/README.md` for the exact reproducible
commands and current status. Independent source reviewers checked the operator
order, sign conventions, carrier scope, native API names and counterexamples.
Candidate authors did not certify their own Lean code. The maintained staged
proof-integrity gate passed at the recorded source snapshot. Heuristic vacuity
findings concern ordinary `nlinarith` proofs and the elementary `(-I)²=I`
simplification; they do not replace semantic review or native verification.

Native acceptance is recorded per checked revision and owner set. The accepted
five-owner baseline does not certify the two added owners; the expanded gate
checks all seven together. A successful focused run certifies only its selected
owners and imported source closure, not the root workspace or every historical file.
