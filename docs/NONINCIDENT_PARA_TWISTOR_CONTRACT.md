# Nonincident dual twistors and neutral cross duality

## Intake, provenance, and intended result

This change extracts precise mathematical claims from
`Pasted text(20261116-184144).txt`, supplied on 2026-11-16. The unchanged intake
is retained as
[`docs/sources/nonincident_para_twistor_20261116.txt`](sources/nonincident_para_twistor_20261116.txt).
Its SHA-256 is
`36f218938a18f175c8961fae548b39dfa0fd1ed8e8ae8e0929d3cf2095134799`.
The source baseline is upstream `main` at
`08c34e03f610b452e03422037949196dc7d92d6d`.

The implementation extends existing operators and bilinear forms. Its central
objects are a real vector space with its actual algebraic dual, noncommuting
linear endomorphisms, and a nondegenerate neutral bilinear form compatible
with a linear involution. Arbitrary operators are not assumed to commute.
The generic normalized-dyad additions work over an arbitrary field; their
endomorphism ring remains noncommutative even though the scalar field is
commutative.

The complete source text is research intake, not a theorem specification.
Statements about gauge theory, conformal infinity, amplituhedron residues,
global manifolds, or uniqueness of a physical synthesis require their own
maps and hypotheses. They are classified below rather than promoted through
names, graph edges, or unproved structure fields.

The intended addition comprises **32 theorem declarations and 7 definitions**:

| Promotion owner | New theorems | New definitions | Purpose |
|---|---:|---:|---|
| `Canonical/ParaComplexNeutralForm.lean` | 10 | 5 | Derived cross nondegeneracy, actual dual maps and equivalences, finite-rank equality |
| `LinearAlgebra/RegularDyadCompression.lean` | 3 | 0 | Ordered product, representative rescaling, and exact image |
| `Optics/SheetWittCircularBasis.lean` | 1 | 1 | Derived half-projector commutation and constructor |
| `Twistor/NonincidentLogPairing.lean` | 18 | 1 | Mixed logarithmic kernel, exact radicals, derivatives, covariance, and noncommutation witness |
| **Total** | **32** | **7** | Source declaration inventory, not compiler evidence |

These counts concern explicit declarations added by this patch. The complete-owner
native audit additionally includes existing and generated declarations. No existing normalized dyad, mass invariant, or basic para-complex
decomposition is counted as new work.

## Source-backed owner search

Search covered repository-owned definitions, imports, instances, statements,
proofs, and consumers for real/projective incidence, normalized dyads,
para-complex neutral forms, commuting involutions, infinity-twistor pairing,
constituent momentum, and logarithmic potentials. The search is bounded to
these mathematical surfaces; it does not certify all historical files or the
entire repository.

| Mathematical surface | Existing owner | Reused substance |
|---|---|---|
| A real vector and its actual covector | [RealDualTwistor](../lean/InfoGeometry/Twistor/RealDualTwistor.lean) | `Carrier`, `dyad`, `dyad_mul`, `dyad_sq`, `dyad_frameAction`, `eq_zero_of_dual_vanishes`, and actual contragredient `frameAction` |
| Normalized rank-one operator | [RegularDyadCompression](../lean/InfoGeometry/LinearAlgebra/RegularDyadCompression.lean) | `normalizedDyad`, `normalizedDyad_idempotent`, `normalizedDyad_compression`, `normalizedDyad_ker`, `covector_normalizedDyad` |
| Native projective incidence | [RealProjectiveAmbitwistor](../lean/InfoGeometry/Twistor/RealProjectiveAmbitwistor.lean) | `Incident`, `incident_mk_iff`, `incident_mk_iff_dyad_sq_zero`, `incident_frame_iff` |
| Para-complex decomposition | [ParaComplexConnectionBridge](../lean/InfoGeometry/Canonical/ParaComplexConnectionBridge.lean) | `ParaComplexStructure`, eigenspace submodules, `peirceDecomposition`, `peirce_sum_id` |
| Neutral form | [ParaComplexNeutralForm](../lean/InfoGeometry/Canonical/ParaComplexNeutralForm.lean) | `Datum`, `AntiCompatible`, same-eigenspace isotropy, annihilator results, finite-rank sum |
| Joint projectors | [SheetWittCircularBasis](../lean/InfoGeometry/Optics/SheetWittCircularBasis.lean) | `CommutingInvolutions`, `jointProjector_idem`, `jointProjectors_pairwise_disjoint`, `jointProjector_sum` |
| Multiplicative operator parity | [ModularZ2CubeGrading](../lean/InfoGeometry/Canonical/ModularZ2CubeGrading.lean) | `hasGrading_mul`, `isHomogeneous_mul` over an arbitrary ring |
| Infinity pairing and its radical | [InfinityTwistor](../lean/InfoGeometry/Twistor/InfinityTwistor.lean) | A degenerate alternating form into the actual dual; lower-spinor minor, radical, translation and frame covariance |
| Two-constituent momentum | [TwistorConstituentKinematics](../lean/InfoGeometry/Twistor/TwistorConstituentKinematics.lean) | `pairMomentum_determinant`, zero/positive mass criteria, `paper_pair_mass`, pairing-separation witnesses |
| Mass and ordered moment operators | [TwoTwistorGramMass](../lean/InfoGeometry/Twistor/TwoTwistorGramMass.lean) | `paperMassSq_eq_infinity_normSq`, `paperMassSq_eq_twice_momentum_det`, and ordered moment-operator products |

The normalized dyad and basic mass identities already exist. This change
does not introduce second owners for them. Equal para-eigenspace ranks were
previously available through a supplied cross-equivalence assumption in the
neutral owner; the new construction derives the actual cross duality from
nondegeneracy.

## Exact theorem contracts

### 1. Neutral cross duality

Let `PCS : ParaComplexStructure V`, with linear involution `tau`, and let
`D : Datum PCS`. Its real bilinear form is symmetric and obeys

\[
B(Kx,Ky)=-B(x,y).
\]

Assume ambient left nondegeneracy: if `B x y = 0` for every `y`, then `x = 0`.
Using the existing decomposition `y = P₊y + P₋y` and same-eigenspace
isotropy, derive both cross-nondegeneracy conditions. These are derived
fields in `Datum.toNondegenerateDatum`, not additional hypotheses.

The linear maps

\[
V_+\longrightarrow V_-^*,\quad u\longmapsto B(u,-)|_{V_-},
\qquad
V_-\longrightarrow V_+^*,\quad u\longmapsto B(u,-)|_{V_+}
\]

are actual restrictions of `B`, with exact evaluation lemmas and injectivity.
In finite dimension, the two injections and the dimension formula for the
algebraic dual imply equal dimensions. Each map then yields a linear
equivalence to the opposite algebraic dual, retaining its original
evaluation. Consequently,

\[
\dim V_+=\dim V_-,\qquad \dim V=2\dim V_+.
\]

No cross-space equivalence is supplied to obtain this equality. The results
are finite-dimensional bilinear algebra; they do not construct a global
pseudo-Riemannian manifold or a signature-classification API. Positive
dimension is not assumed, so strict indefiniteness is not asserted for the
zero-dimensional case.

The hypotheses have nontrivial models. The existing real dual-twistor owner
constructs its symmetric evaluation form on `U × Module.Dual ℝ U`, proves
`neutralForm_nondegenerate`, and gives the involution `(u, φ) ↦ (u, -φ)` with
`para_sq` and `neutralForm_para_anti`. This does not imply that every arbitrary
`PCS` admits a nondegenerate compatible form, nor require a dummy global
`Inhabited` instance.

### 2. Ordered normalized dyads

For a field `𝕜`, a `𝕜`-vector space `E`, vectors `v, w`, and actual covectors
`f, g`, reuse the existing endomorphism

\[
P_{v,f}(u)=\frac{f(u)}{f(v)}v.
\]

The new ordered-product identity is

\[
P_{v,f}P_{w,g}
=\frac{f(w)}{f(v)g(w)}\bigl(u\mapsto g(u)v\bigr).
\]

The first vector and second covector are retained in this order. This is an
identity in `Module.End 𝕜 E`, where multiplication is composition. The
formula itself uses the field's totalized division and does not require
nonzero denominators. The geometric projector and image conclusions use
`f v ≠ 0` explicitly.

For `a ≠ 0`, `b ≠ 0`, and `f v ≠ 0`, independent representative rescaling
satisfies `P_(a•v,b•f) = P_(v,f)`. Under the same nonincident condition the
image is exactly `𝕜 ∙ v`, with no finite-dimensional assumption. Idempotence
and the exact kernel `ker f` are reused from the existing owner.

### 3. Nonincident pair and mixed logarithmic kernel

Let `p = (v, φ) : V × Module.Dual ℝ V` and `s = φ v ≠ 0`. Reuse
`P_p = normalizedDyad v φ`. The new bridge identifies it with
`s⁻¹ • RealDualTwistor.dyad p`. A change of frame acts by conjugation using
the existing contragredient action on the actual dual.

The mixed logarithmic pairing is the native bilinear expression

\[
H_p(u,\psi)=\frac{\psi(u)}s-
 \frac{\varphi(u)\psi(v)}{s^2}
 =\frac{\psi((1-P_p)u)}s
 =\frac{(\psi-\frac{\psi(v)}s\varphi)(u)}s.
\]

The complement factorizations give the two Euler-direction cancellations
`H_p(v, ψ) = 0` and `H_p(u, φ) = 0`. The claimed radical results are the
following exact biconditionals, not only one-way radial cancellation:

\[
\bigl(\forall\psi\in V^*,\ H_p(u,\psi)=0\bigr)
\quad\Longleftrightarrow\quad u\in\mathbb Rv,
\]

\[
\bigl(\forall u\in V,\ H_p(u,\psi)=0\bigr)
\quad\Longleftrightarrow\quad\psi\in\mathbb R\varphi.
\]

Their declarations are `mixedLogKernel_left_radical` and
`mixedLogKernel_right_radical`. Algebraic covector separation is reused from
the real dual-twistor owner. Neither result assumes finite dimension.

On `ker φ` and the covectors annihilating `v`, the pairing reduces to
`ψ u / s`. The two horizontal separation theorems say:

- If `φ u = 0` and `H_p(u, ψ) = 0` for every `ψ` with `ψ v = 0`, then `u = 0`.
- If `ψ v = 0` and `H_p(u, ψ) = 0` for every `u` with `φ u = 0`, then `ψ = 0`.

These prove nondegeneracy on the indicated complementary slices. They do
not construct a quotient manifold.

Independent nonzero rescalings of representatives and their corresponding
tangent variables preserve the kernel:

\[
H_{(av,b\varphi)}(au,b\psi)=H_{(v,\varphi)}(u,\psi).
\]

For a linear equivalence `e : V ≃ₗ[ℝ] W`, contragredient covariance is

\[
H_{(ev,\varphi\circ e^{-1})}(eu,\psi\circ e^{-1})=H_p(u,\psi).
\]

This equality follows from evaluation through `e⁻¹ ∘ e`; covariance is not
assumed as a structure field. In contrast, the logarithmic potential itself
changes by separate representative terms:

\[
\log|(b\varphi)(av)|=\log|a|+\log|b|+\log|\varphi(v)|.
\]

The analytic connection is an actual iterated real-line derivative. With

\[
F(t,r)=\log\bigl|(\varphi+t\psi)(v+ru)\bigr|,
\]

`hasDerivAt_logPairing` establishes the primal derivative
`φ u / φ v`. `hasDerivAt_logPairing_readout` differentiates this readout in
the dual direction. Finally, `hasDerivAt_mixed_logPairing` has the native
statement

```lean
HasDerivAt
  (fun t : ℝ =>
    deriv (fun r : ℝ => Real.log |(p.2 + t • ψ) (p.1 + r • u)|) 0)
  (mixedLogKernel p u ψ) 0
```

The nonzero pairing supplies the neighborhood where the inner derivative
formula holds. This is not merely the definition of a rational expression
named a mixed derivative. All differentiation takes place in real scalar
parameters; no norm, topology, or continuous-dual identification on the
algebraic carrier `V` is imposed.

A concrete pair of normalized projectors on `ℝ × ℝ` witnesses
noncommutation. The source chooses
`p = ((1, 0), fst)` and `q = ((1, 1), snd)`, both with pairing equal to one.
Their ordered compositions differ already on `(0, 1)`. This does not infer
a commutator from the difference of two scalar invariants.

The nonzero-pairing condition is essential to the geometric and derivative
interpretations. Lean's totalized division and logarithm at zero do not
establish a regular extension across incidence. No global projective metric,
closed two-form, residue, or scattering amplitude is asserted by this local
algebraic and derivative construction.

### 4. Constructed joint-projector interface

Work in an arbitrary `[Ring Op] [Algebra ℝ Op]`. From `h*k = k*h`, derive
commutation of every selected affine half-projector `(1±h)/2` with every
selected half-projector `(1±k)/2`. This intermediate lemma needs no
involution equations.

Adding `h*h = 1` and `k*k = 1` constructs the existing
`CommutingInvolutions` interface via `CommutingInvolutions.ofCommute`.
Its `projector_commute` field is a consequence of the new lemma. Existing
orthogonality, idempotence, and resolution-of-identity theorems apply without
changing their definitions.

Only the two grading operators are required to commute. The ambient
operator algebra remains noncommutative. This construction supplies four
projectors; identifying either axis with physical statistics, gauge symmetry,
or R-symmetry is a separate obligation. A vector-space decomposition and a
multiplicative algebra grading must also be distinguished.

## Actual dependency order

The implemented order is mathematical dependence:

1. Existing involution decomposition and isotropy imply cross nondegeneracy.
   The actual restricted cross maps then imply equal finite dimensions and
   yield dual equivalences.
2. The existing normalized dyad gives its complementary operator. Covector
   evaluation through that complement gives the mixed kernel, the exact
   radial kernels, and horizontal separation.
3. Real-line differentiation of the evaluation pairing identifies this
   kernel with an actual mixed derivative on the nonincident domain.
4. Commutation of two specified grading operators gives half-projector
   commutation, making the existing four-projector construction available
   from fewer independent assumptions.

There is no proved dependency from these results to amplituhedron residues
or to a necessary physical synthesis. The intake's graphical proximity is
not treated as a mathematical implication.

## Claim ledger and corrections

| Intake claim | Disposition and exact boundary |
|---|---|
| Para eigenspaces are null | Existing theorem under bilinear compatibility; an involution alone is insufficient. Nondegeneracy is additional when asserting a symplectic or maximal-isotropic interpretation. |
| A nondegenerate neutral form has equally sized eigenspaces | New finite-dimensional consequence derived from actual cross maps. Strict indefiniteness additionally excludes zero dimension. No signature-classification API is constructed here. |
| A nonincident pair gives a normalized operator | Existing normalized dyad, reused and connected to actual dual-twistor data. New ordered-product, image, rescaling, and mixed-kernel results extend that owner. |
| `log\|φ(v)\|` is a global function on projective pairs | Incorrect as stated: independent scaling adds `log\|a\| + log\|b\|`. A local potential and its mixed derivative must be distinguished. |
| Euler cancellation establishes all para-Kähler geometry | It proves radial degeneracy. The two exact radical biconditionals and horizontal separation are separate results here. Global smooth descent, integrability, and closedness remain separate obligations. |
| Ordinary absolute values and logarithms immediately apply to supernumbers | A super extension needs its body, invertibility condition, and nilpotent expansion. None is supplied by the real algebraic construction. |
| Every single-twistor momentum has rank one | Its outer product has rank at most one; exact rank one needs nonzero factors. Its determinant vanishes. Reality/Hermiticity needs the appropriate conjugate spinors. |
| An arbitrary dual pairing `W(Z)` is automatically physical helicity | That interpretation needs a twistor reality structure and normalization; the algebraic pairing alone is not such a construction. |
| Two twistors necessarily give positive mass | Existing owner proves positivity exactly when the lower-spinor minor is nonzero. Independent full twistors may have dependent lower spinors. |
| `m² = 2\|I(Z₁,Z₂)\|²` | Existing theorem with the paper's explicit factor-two convention. The repository's `pairMassSq` is the norm square without that factor; `paperMassSq` is twice `pairMassSq`. The momentum determinant matches `pairMassSq`. |
| The mass-zero locus is automatically spacetime conformal infinity | Not established. Momentum constituents and the Klein-quadric spacetime chart require an explicit incidence/reality comparison before sharing that interpretation. |
| A covariant infinity twistor is a nilpotent endomorphism | Ill-typed without an identification with the dual. A separately specified covariant/contravariant contraction is a different statement. The existing owner uses an alternating form into the actual dual. |
| Distinct scalar invariants imply a nonzero commutator | False inference. Ordered operators and an explicit witness are required; this change supplies a concrete normalized-projector witness. |
| Noncommuting matrices destroy every notion of positivity | Overstated. Ordinary scalar determinant inequalities and operator positive cones are different structures. No universal obstruction to operator positivity is claimed. |
| A pair of commuting involutions yields four projectors | Constructed in the ambient noncommutative algebra using the existing owner. Physical identifications and any algebra-grading compatibility remain additional obligations. |
| Differentiation or a limit turns `log\|μ\|` into a residue | Differentiation gives `dμ/μ` away from zero; this form still has a pole. A residue requires a specified form, divisor, and normalization. The iterated derivative proved here does not construct such a residue. |
| HLS settles every local-gauge/superconformal extension | The theorem's hypotheses and symmetry setting must be specified. No universal Lean theorem of that kind is claimed. |
| Nonplanar positive geometry is universally impossible | Unsupported. The original amplituhedron has planar scope, while primary literature studies nonplanar generalizations. |
| The supplied 15-vertex order proves a unique physical synthesis | A chosen finite order cannot establish physical necessity. Its levels increase strictly but are not a cover-rank function, and some pairs have no join. |

The original planar scope is stated in Arkani-Hamed and Trnka,
[The Amplituhedron](https://arxiv.org/abs/1312.2007).
Bern, Herrmann, Litsey, Stankowicz, and Trnka give
[Evidence for a Nonplanar Amplituhedron](https://arxiv.org/abs/1512.08591).
These are contextual literature references, not Lean proof dependencies or
claims of a fresh literature review.

### The supplied finite graph

The listed covering edges include `K_TT → Bridge` and `Gamma_SS → Bridge`
with assigned levels `2 → 4`. Strict increase proves acyclicity of the
specified edge relation and its strict transitive closure, but the levels
are not a usual rank function increasing by one along covers.

There are saturated bottom-to-top chains of lengths five and six. For
example, `Cut → Thesis → K_TT → Bridge → Holonomy → Top` has length five,
while `Cut → Thesis → Pi_ST → Gravity → Bridge → Holonomy → Top` has length
six. Thus the poset is not graded in the usual cover-rank sense.

`K_TT` and `Pi_ST` have incomparable minimal common upper bounds `A0` and
`Bridge`. The supplied poset therefore is not a join-semilattice. The
chosen final two vertices, `Holonomy` and `Stratification`, can still have
the stipulated terminal vertex as their join. None of these observations
proves a unique physical synthesis. These are source-graph observations;
this change does not add a Lean formalization of that finite order.

## Validation record

The [verification record](NONINCIDENT_PARA_TWISTOR_VERIFICATION.md) identifies
the source hashes, native compiler results, declaration and axiom coverage,
independent review, retained static warnings, and status of each check.
The exact publication-commit pre-push result is recorded in the PR description.

This contract fixes the mathematical scope. Acceptance applies to the
revisions and targets identified in that record; selected source-closure
verification and full-root integration have separate coverage.
