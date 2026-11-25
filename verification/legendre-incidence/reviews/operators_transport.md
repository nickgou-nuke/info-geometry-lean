# Independent source review: cotangent operators and contact transport

Date: 2026-11-24
Reviewer: `/root/incidence_grassmann_audit`
Review mode: independent source and mathematics review; no Lean, Lake, or build execution.

## Reviewed snapshots

| Candidate | SHA-256 |
| --- | --- |
| `CotangentOperators.lean` | `ac6f6a4dbad391260c87d2179096164c85d5dcf263d8f7cd0017c134ac0ca674` |
| `ContactTransport.lean` | `87e27694ff6ef78c54673164ecb3d630b368aff11c73d1352542b46230baef7b` |

These hashes identify the exact source reviewed. The pinned Mathlib source inspected was commit `d13f23b723b8a846827a245b89c10fc7d3f11612` at `/workspace/scratch/058543be00a5/info-geometry-lean/.lake/packages/mathlib`. Existing repository owners were read in `/workspace/scratch/0e51269094a7/info-geometry-lean`.

## Assessment

No mathematical blocker, reversed composition, missing mathematical hypothesis, or false theorem statement was found in either snapshot. The native API names and the particular definition reductions used in the proofs agree with the inspected sources. The candidates are suitable for the next serialized compiler-validation step. This is a source-review conclusion, not a claim that Lean has accepted these files.

No occurrences of `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` were found in either candidate. No candidate or owner source was edited during this review.

## CotangentOperators.lean

### Transport and graph geometry

For a frame `g : V ≃ₗ[ℝ] W`, the candidate uses

\[
T_g(x,p)=(gx,p\circ g^{-1}),\qquad
H_g=(g^{-1})^*\circ H\circ g^{-1}.
\]

The two inverse factors and their order are correct. Evaluating `H_g` gives `H (g.symm x) (g.symm y)`, so symmetry and alternation are inherited without a metric or finite-dimensionality assumption. `frameAction_graphLift` and `map_graph_frameAction` describe the actual graph submodule, not a selected set of graph vectors alone.

Native `LinearMap.graph` has membership `z.2 = H z.1`; this agrees with the equalities extracted directly from graph-membership hypotheses in the proof. Native `LinearMap.BilinForm.IsAlt` reduces to `∀ x, H x x = 0`, so the proof of `transportDuality_alternating` is correctly typed at the mathematical/API level.

### Lie lift and composition order

The infinitesimal lift is

\[
L_A(x,p)=(Ax,-p\circ A).
\]

The negative dual is necessary. With endomorphism multiplication as composition,

\[
(L_A L_B)(x,p)=(ABx,p\circ B\circ A),
\]

and therefore

\[
[L_A,L_B]=L_{AB-BA}.
\]

The candidate's expanded second-coordinate proof follows this reversed dual order correctly. The native `LieHom` fields match the supplied linearity and commutator identities. The associative Lie-ring instance is localized, in the same style as Mathlib's `Algebra/Lie/OfAssociative.lean`. Faithfulness is correctly witnessed by evaluating the first component at `(v,0)`.

The equivariance statement transports `A` as `g ∘ A ∘ g⁻¹`, with the corresponding negative dual action. The lift commutes with the primal/dual grading and infinitesimally preserves both existing evaluation forms.

### Fixed graph preservation

`infinitesimalLift_graph_le_iff` proves the exact condition

\[
L_A(\operatorname{graph}H)\subseteq\operatorname{graph}H
\quad\Longleftrightarrow\quad
H\circ A+A^*\circ H=0.
\]

This follows by applying the graph equation to `(Av,-(Hv)∘A)`. Neither symmetry nor nondegeneracy of `H` is needed. Both directions in the source correctly extract/evaluate this equality.

**Interpretation boundary:** this is a fixed-bilinear-form infinitesimal invariance condition. It does not by itself prove a Killing equation for a position-dependent Hessian `H_x`; that equation would also involve the variation of `H_x` along a vector field. The candidate currently respects this boundary.

### Hamiltonian signs

The existing Geometry convention is

\[
\omega((x,p),(y,q))=q(x)-p(y).
\]

For `h_A(x,p)=p(Ax)`, the candidate's linear tangent coefficient is

\[
\mathrm dh_A|_{(x,p)}(y,q)=q(Ax)+p(Ay).
\]

Its quadratic expansion is exact, so this coefficient is derived algebraically. Direct substitution verifies the two sign-sensitive identities:

\[
\omega(L_Az,w)=\mathrm dh_A|_z(w),\qquad
\mathrm dh_B|_z(L_Az)=-h_{AB-BA}(z).
\]

The commuting-operator conservation corollary follows. The comparison to `Quantum.DualFlatKreinGraph.symplecticPair` has the correct opposite sign. There is no assertion of a differentiable flow, Poisson-bracket convention, or quantization beyond these algebraic identities.

## ContactTransport.lean

### Actual moving cut and Peirce signs

Write `P` for the existing homogeneous contact projector, `D` for the incidence dyad, and `g` for the existing Fenchel gap. The imported owner proves

\[
P^2=P,\qquad PD=D,\qquad DP=-gP.
\]

At contact `g=0`, the candidate consequently has

\[
S=2P-1,\quad S^2=1,\quad SD=D,\quad DS=-D,\quad SDS=-D.
\]

The theorem `contactDyad_eq_conePlus` uses the exact corner `P D (1-P)`. The A27 projections `.1` and `.2.1` select the left and right parities for that upper corner. No lower-corner term has been substituted by mistake.

### Nonzero nilpotent superderivation

The constructed native linear endomorphism of the operator algebra is

\[
\delta_D(A)=DA-(SAS)D.
\]

Its scalar-linearity proof uses only the native central real scalar action on the endomorphism algebra. At contact it agrees exactly with the existing `superDerivPlus P D`. The imported A28 theorem's `.1` gives its square-zero law, and `.2.2.2.2.1` gives the stated graded Leibniz law.

The nonvanishing argument is substantive:

\[
\delta_D(P)=DP-PD=-D\ne0.
\]

The imported dyad nonzero theorem needs no nontriviality assumption on `E`; the additional real height and homogeneous coordinates make both factors nonzero even when `E` is the zero space. The actual-conjugate corollary correctly obtains Fenchel equality from the existing global-convexity/local-derivative theorem rather than assuming equality or boundedness as an extra premise.

### Frame transport and actual conjugation

Native `LinearEquiv.conjAlgEquiv_apply` is `A ↦ e ∘ A ∘ e⁻¹`. This agrees, up to the explicit composition reassociation, with `RealDualTwistor.dyad_frameAction`.

The projector conjugation hypotheses are sufficient and correctly directed: the frame sends the homogeneous point to the new point, and the final-coordinate covector pulls back along the inverse to the new final-coordinate covector. This transports projectors and reflections. Multiplicativity and subtraction preservation of the native algebra equivalence then transport the twisted commutator without changing the order of its factors.

For a continuous primal equivalence `e`, the transformed potentials are

\[
f_e(y)=f(e^{-1}y),\qquad f^*_e(q)=f^*(q\circ e).
\]

The transformed selected covector is `p∘e⁻¹`. These two directions are consistent. The proof of `fenchelConj_framePotential` correctly applies `transportedFenchelConjFromDual_eq` with `e.symm` and then cancels the two dual transports.

No boundedness premise is needed for that last equality: it follows from equality of the defining support sets, before taking `sSup`. However, this equality does not remove the existing bounded-above condition when interpreting a real-valued conjugate as a support value or using the Fenchel inequality. The candidate does not make that invalid inference.

### Explicit transvection

Mathlib's `LinearEquiv.transvection` takes a covector `λ`, a vector `v` with `λ(v)=0`, and acts as `z ↦ z + λ(z) • v`; its inverse uses `-v`. With `v=(x,f x,0)` and the final-coordinate covector, the candidate's forward and inverse formulas are exact.

The shear sends `(0,0,1)` to `(x,f x,1)` and preserves the final coordinate. For the reference covector `ℓ₀(y,t,s)=p(y)-t`, inverse pullback gives

\[
\ell_0(T^{-1}(y,t,s))
=p(y)-t-(p(x)-f(x))s.
\]

Fenchel equality supplies `fStar p = p x - f x`, exactly the intercept required by `contactPair_shear_of_equality`. Consequently the subsequent dyad and superderivation conjugations have the correct orientation.

**Interpretation boundary:** the reference pair built from the two zero functions is an algebraic contact normal form. The shear theorem does not assert that the zero dual function supplies bounded convex support for the zero primal potential at every covector. This distinction should remain in any explanatory documentation.

## Native sources checked

- `InfoGeometry/Twistor/RealDualTwistor.lean`: carrier, both forms, para involution, frame action, dyad square/nonvanishing/conjugation.
- `InfoGeometry/Twistor/FenchelContactIncidence.lean`: point and hyperplane definitions, homogeneous coordinate, projector/dyad products, contact equivalence, actual-conjugate derivative corollary.
- `InfoGeometry/OperatorAlgebra/PeirceSpine/Basic.lean`: `invS`, `conePlus`, `coneMinus`.
- `InfoGeometry/OperatorAlgebra/PeirceSpine/Supercharge.lean`: parity conjugation, upper superderivation, and exact A27/A28 conjunction order.
- `InfoGeometry/Convex/TransportedFenchel.lean`: pullback direction and equality of support sets/suprema.
- `InfoGeometry/Convex/FenchelConjugate.lean`: real-valued conditional-supremum interpretation.
- `InfoGeometry/Geometry/LegendreDuality.lean`: exact gap and Fenchel equality definitions.
- `InfoGeometry/Geometry/DualFlatKreinLegendreGraph.lean` and `InfoGeometry/Quantum/DualFlatKreinGraph.lean`: opposite symplectic conventions.
- Mathlib `LinearAlgebra/Prod.lean`: native graph membership.
- Mathlib `LinearAlgebra/BilinearForm/Properties.lean` and `LinearAlgebra/SesquilinearForm/Basic.lean`: alternation predicate.
- Mathlib `Algebra/Lie/Basic.lean` and `Algebra/Lie/OfAssociative.lean`: native Lie hom fields and associative bracket instances.
- Mathlib `Algebra/Algebra/Equiv.lean`: `LinearEquiv.conjAlgEquiv_apply`.
- Mathlib `LinearAlgebra/Transvection/Basic.lean`: actual transvection and inverse definitions.

## Remaining gate

Run the root-owned serialized verifier against the final integrated modules and imports. Source-level agreement cannot certify elaboration of tactic scripts, simplifier normalization, typeclass search, or module availability. If compiler repairs change mathematical statements, composition order, hypotheses, or the Peirce identities, those changes need a targeted review; cosmetic or straightforward elaboration repairs do not alter the mathematical conclusions above.
