# Open analytic obligations after the real matrix and chart identities

## Status and scope

This is an **open-obligation ledger**, not a proof of RH or GRH and not a new
Lean interface. It supplements
[NAMBU_METRIPLECTIC_CONTRACT.md](NAMBU_METRIPLECTIC_CONTRACT.md). Source review
was performed on 2026-11-23, at checkout
`3561393e4cb01370f00658cad5a293985c8345d0`; no native compilation was performed
for this ledger. Validation of the finite owners is recorded separately.

The proposed first family is **primitive Dirichlet L-functions**. The first
instance should be the conductor-one character, hence the Riemann zeta
function. The detailed test-function contracts below specify that instance.
A theorem uniform in primitive characters is a further task; it must retain
the character, conductor, parity, root number and dual character. A completed
zeta instance would establish an RH result only after all three obligations
and their final implication are proved. It would not establish general GRH.

The finite results concern `gen (σ,γ) = σ Eplus + γ Eminus`, the distinct
`scalarPencil σ γ = σ I + γ Eminus`, and chosen affine coordinates. Their
coincidence locus is `σ = 0`. Evaluating these matrices at
`σ = Re(s) - 1/2` or at KMS coordinates identifies a locus; it does not prove
that arithmetic zeros lie there. The fixed Krein form with matrix `Eplus`
still has a negative direction when the pencil's symmetric part vanishes.

## Existing sources and their precise role

| Source | Reusable content and boundary |
| --- | --- |
| [Arithmetic/ActualRiemannXiEntireBridge.lean](../lean/InfoGeometry/Arithmetic/ActualRiemannXiEntireBridge.lean) | `entireRiemannXi`, `analyticOnNhd_entireRiemannXi`, `entireRiemannXi_one_sub`, and `entireRiemannXi_eq_riemannXi` away from `0,1`. This supplies an actual entire function, not a free function symbol. |
| [Arithmetic/ActualRiemannXiSchwarzBridge.lean](../lean/InfoGeometry/Arithmetic/ActualRiemannXiSchwarzBridge.lean) and [Arithmetic/RiemannXiCayleyZeroBridge.lean](../lean/InfoGeometry/Arithmetic/RiemannXiCayleyZeroBridge.lean) | Concrete completed-zeta Schwarz symmetry; `riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_strip`. The latter has open-strip hypotheses, which must be preserved. |
| Pinned Mathlib `NumberTheory/LSeries/DirichletContinuation.lean` | `DirichletCharacter.LFunction`, `completedLFunction`, `gammaFactor`, `rootNumber`, and `IsPrimitive.completedLFunction_one_sub`. Its completed-function normalization must be used explicitly. |
| [Arithmetic/FiniteWeilMangoldtQuadraticFormBridge.lean](../lean/InfoGeometry/Arithmetic/FiniteWeilMangoldtQuadraticFormBridge.lean) | A finite Mangoldt contribution is Hermitian for a supplied self-adjoint operator family. This is neither the complete explicit formula nor a positivity theorem. |
| [Spectral/WeilPositivityCriterion.lean](../lean/InfoGeometry/Spectral/WeilPositivityCriterion.lean), [Spectral/WeilPositivityGNSBridge.lean](../lean/InfoGeometry/Spectral/WeilPositivityGNSBridge.lean), and [Canonical/WeilPositivityHestenesKrein.lean](../lean/InfoGeometry/Canonical/WeilPositivityHestenesKrein.lean) | Finite square-form positivity and transport. The displayed weights, sampled coordinates or readouts require a separate identification with genuine arithmetic test data. |
| [Canonical/HestenesKreinWeilCriterionColimit.lean](../lean/InfoGeometry/Canonical/HestenesKreinWeilCriterionColimit.lean) | `rh_of_colimitReadout` assumes an arbitrary proposition `RH`, its positivity criterion, exact kernel/readout equalities and global positivity. It composes these hypotheses; it does not construct them. |
| [Arithmetic/ExplicitFormula.lean](../lean/InfoGeometry/Arithmetic/ExplicitFormula.lean) | `ExplicitFormula.formula_holds` is supplied data. `explicitFormulaFromRH` takes the desired `hformula` as an argument; it does not derive a prime–zero formula. Its finite zero set does not supply all zeros with multiplicity or an infinite-limit theorem. |

Two normalization cautions matter before constructing further objects.
Mathlib's `completedRiemannZeta₀` is the additive pole-removal of completed
zeta, not xi and not automatically a function with the same zeros. Reuse
`entireRiemannXi` and its comparison theorem. For a primitive character, the
pinned Mathlib functional equation is

```text
completedLFunction χ (1 - s)
  = N^(s - 1/2) * rootNumber χ * completedLFunction χ⁻¹ s.
```

Its normalization leaves this conductor factor visible. Any alternative
completion needs a proved comparison, including its nonzero factors on the
domain used for zeros and multiplicities. The conjugate-character dependence
is also present in the primary reference
[DLMF 25.15.5](https://dlmf.nist.gov/25.15#E5). In particular, the two zeta
generators must not both be declared symmetries of an arbitrary fixed
character's zero set. Work with the paired character data when needed;
[DLMF §25.15(ii)](https://dlmf.nist.gov/25.15#ii) explicitly distinguishes
critical-line symmetry from symmetry about the real axis.

## 1. OPEN — Genuine arithmetic test data and a faithful carrier map

**Required input.** Use the actual `entireRiemannXi` for the first instance.
Construct its zero data with the actual order of vanishing at each zero,
including a proof that the function is not identically zero, local finiteness
and the indexing needed for sums. Do not start
with points already parametrized as `1/2 + iγ`, or with a supplied list whose
membership is disconnected from the function. Transfer to the usual zeta
zero predicate through the existing comparison theorems and any additionally
required boundary or exceptional-point results.

Fix a concrete test algebra before choosing a carrier. One proposed first
domain is smooth compactly supported complex functions on the additive real
logarithmic coordinate, with Lebesgue measure, ordinary convolution and

\[
 f^\sharp(u)=\overline{f(-u)},\qquad
 \mathcal M f(s)=\int_{\mathbb R}f(u)e^{(s-1/2)u}\,du.
\]

This specifies the transform's centering, sign and measure. Native function,
regularity, support and integration types should be used; the notation here
does not assert that a new test-function owner already exists. Closure under
convolution and `sharp`, integrability and the necessary transform bounds
remain proof requirements.

Define the complete arithmetic Weil functional from the genuine arithmetic
data, with a fixed normalization of its prime, archimedean, pole and conductor
terms. Write its prospective Hermitian form, using the convention conjugate
linear in the first variable, as

\[
 B_{\rm arith}(f,g)=W_{\rm arith}(f^\sharp*g).
\]

Hermitian symmetry must be proved. Finite sums of nonnegative squares, a lone
prime contribution, or a freely supplied real-valued `weil` are not this
construction.

**Required output.** Construct a specified operator or Krein carrier and an
explicit linear map from these test data, preserving the arithmetic form.
For a real carrier, use genuine restriction of scalars and require

\[
 [Tf,Tg]_K=\operatorname{Re}B_{\rm arith}(f,g).
\]

For realification, prove the correspondence of radicals and diagonal
positivity with the original complex form. Record the map's kernel and its
relation to the radical used in obligation 3;
prove injectivity of the induced map on the intended arithmetic quotient if
faithfulness is claimed. A map collapsing any nonradical arithmetic direction
does not meet this requirement. A finite matrix realization also
needs a proved finite-rank factorization of this particular form; the
`Cl(1,1)` identities alone do not supply one.

If the route uses a Krein space, provide its actual topology and fundamental
symmetry. If it uses an unbounded operator, specify its dense domain,
invariant core, closure and the adjoint notion required by the argument.
Formal symmetry of an everywhere-defined `LinearMap` does not establish
self-adjointness of an unbounded operator. No operator theory is required
merely to state the arithmetic form; add it only when the chosen proof uses
it.

**Exit condition:** actual arithmetic definitions, a constructed carrier map,
and proved form and kernel identities, with no assumed positivity or
zero-location conclusion.

## 2. OPEN — Explicit-formula and functional-involution compatibility

For the fixed test algebra, first prove the transform identities

\[
 \mathcal M(f*g)(s)=\mathcal M f(s)\mathcal M g(s),\qquad
 \mathcal M(f^\sharp)(s)=
   \overline{\mathcal M f(1-\overline s)}.
\]

Construct the spectral distribution from **all actual zeros with their
multiplicities**, and prove the complete explicit-formula equality. In the
first instance its required form is

\[
 W_{\rm arith}(h)=W_{\rm zero}(h)
   =\sum_\rho m_\rho\,\mathcal M h(\rho),
\]

with the prime, gamma and pole terms incorporated into the specified
`W_arith`. Consequently the required sesquilinear identity is

\[
 B_{\rm arith}(f,g)
   =\sum_\rho m_\rho\,
       \overline{\mathcal M f(1-\overline\rho)}\,
       \mathcal M g(\rho).
\]

These are **targets**, not established equalities in this change. The exact
arithmetic side must be written and proved with the selected normalization;
an argument named `hformula` is not a discharge of this obligation.

Specify the zero-sum convention and prove its validity: absolute convergence
on the chosen test class, or an explicit truncation/regularization and limit
theorem. Prove the bounds needed to interchange sums, integrals, conjugation
and limits. Compact support in the logarithmic variable can make a given
prime-power test sum finite; it does not eliminate the zero-series and
archimedean-integral obligations. A larger test class needs its own estimates.
Contour proofs additionally need zero-free contour boundaries, residue
multiplicities, treatment of poles and gamma factors, and justified limits.
None of these steps may assume RH as a convergence shortcut for an argument
intended to prove RH.

The arithmetic functional equation must act on these same tests, zero data
and carrier map. Prove the relevant domain preservation and intertwining
identity, for example `T(f^sharp) = S_K(Tf)` with its correct linearity type.
The functional involution `S_K` and a Krein fundamental symmetry are distinct
objects unless their equality is proved. Preserve multiplicities under zero
symmetries. In the Dirichlet extension, retain the dual-character labels and
the root-number/conductor factors rather than importing the fixed-zeta V4
action unchanged.

The existing `ZetaDihedral` and KMS chart maps can be used after the appropriate
coordinate conversion is proved. KMS strip midpoint transport does not
construct an analytic KMS state, a Weil functional, or their identification.

**Exit condition:** a derived arithmetic–spectral equality and commuting
involution maps on the same domain, with all convergence and normalization
hypotheses visible and no zero-location assumption.

## 3. OPEN — Positivity on the arithmetic quotient and the return to zeros

Use the radical of the actual Hermitian form,

\[
 R=\{f:\ \forall g,\ B_{\rm arith}(f,g)=0\},\qquad
 A=\mathcal D/R.
\]

Prove that it is a submodule and that the form descends to `A`. If an
independently motivated quotient `D/N` is proposed, prove `N ≤ R`; if it is
claimed to be the nondegenerate quotient, prove the additional equality or
nondegeneracy statement. Involution and operator actions must preserve the
quotiented submodule and the domains on which they are used.

Do not quotient by the set `B(f,f)=0` before proving it has the required
radical property. For the split form `x²-y²`, `(1,1)` and `(1,-1)` have zero
quadratic value but their sum does not; this set is not a subspace. Nor can a
negative eigenspace be removed while claiming the original form descends:
nonzero negative vectors are not radical vectors. A positive restriction or
projection requires a separate proof that it retains the full arithmetic
criterion.

The substantive target is

\[
 \forall a\in A,\qquad 0\le\operatorname{Re}B_A(a,a),
\]

where `B_A` denotes the descended form. Prove this from the constructed
arithmetic data. It is not supplied by positivity of an unrelated Euclidean
norm, a finite weighted-square kernel, a GNS state assumed positive, or the
condition `σ = 0` for one matrix pencil.

If the result is expressed as **zero negative index**, define or instantiate
an index that measures negative-definite subspaces of this actual form and
prove its equivalence to the displayed nonnegativity statement. An algebraic
index may take the supremum of dimensions of finite-dimensional
negative-definite subspaces, allowing infinity; index zero then excludes
every negative vector. A natural-number `finrank` without finite-dimensional
hypotheses, or absence of negative eigenvectors without the required spectral
theory, is not a substitute.

If a completion or directed limit is used, prove form descent/continuity or
closed-form properties, the relevant density or exhaustion, and convergence
of the actual arithmetic forms. Stagewise positive models and compatible
maps alone do not identify a positive limiting arithmetic form.

**Required return implication.** Establish the appropriate Weil criterion
for these exact objects, at least the direction

\[
 \bigl(\forall f\in\mathcal D,
    \ 0\le\operatorname{Re}B_{\rm arith}(f,f)\bigr)
 \quad\Longrightarrow\quad
 \bigl(\forall\rho,
    \ \mathrm{entireRiemannXi}(\rho)=0
       \Rightarrow\operatorname{Re}\rho=1/2\bigr).
\]

A concrete route is a proved test-function separation theorem: an actual
off-line zero yields an admissible test with negative quadratic value. Such a
test cannot vanish in the radical quotient. This step must control the other
zeros and the convergent sum; a finite interpolation calculation alone does
not establish it. A spectral route instead needs a proved correspondence
covering every actual zero with its multiplicity. Supplying only spectral
points already on the critical line leaves the missing direction unchanged.

Finally transfer the conclusion to the intended native zero predicate,
including its exceptional-point and trivial-zero conventions. For the
Dirichlet family, repeat or generalize the criterion with the character data
retained. An arbitrary proposition field named `RH` or `GRH` does not perform
this transfer.

**Exit condition:** positivity of the faithful arithmetic quotient form and a
proved implication from it to the actual zero-location statement. Both are
currently open in this task.

## Native implementation reuse and completion record

The ledger calls for owner-sized proofs as the mathematical objects become
concrete, not another package of assumed `criterion`, `hkernel` and
`hpositive` fields. Relevant native descent APIs include Mathlib
`LinearAlgebra/Quotient/Bilinear.lean` (`LinearMap.liftQ₂`, `liftQ₂_mk`) and
`LinearAlgebra/QuadraticForm/Radical.lean` (`QuadraticMap.radical`,
`QuadraticMap.lift`, `lift_mk`). Their annihilation/radical hypotheses must be
proved for the selected arithmetic form.

The repository's
[FilteredGNSTomitaModularQuotient.lean](../lean/InfoGeometry/Canonical/FilteredGNSTomitaModularQuotient.lean)
already has a genuine `modularNullSubmodule`, `ModularFormQuotient` and
`quotientModularForm` under compatible-state and Tomita-core hypotheses.
Reuse is appropriate only after constructing those hypotheses and identifying
that form with the arithmetic form. A generic quotient construction does not
supply the arithmetic identification or establish the positivity assumed by
its state data.

Record completion separately for the three obligations: exact owner
declarations and hypotheses, native build scope and axiom dependencies, and
which arithmetic family they cover. This document adds no Lean theorem and
does not change the acceptance status of any finite candidate.
