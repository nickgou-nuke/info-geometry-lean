# Schwinger operator bases: formal contract

Date: 2026-11-20. Source baseline:
`8ac42b1efaa7fe8ad92df3c5acadf0c3a3534ebe` (open upstream PR #414).

## Intake and scope

The user supplied Julian Schwinger, *Unitary Operator Bases*, PNAS **46**
(1960), 570–579, DOI [10.1073/pnas.46.4.570](https://doi.org/10.1073/pnas.46.4.570).
The ten-page attachment is identified byte-for-byte by
[`intake/2026-11-20-schwinger-source.json`](intake/2026-11-20-schwinger-source.json).
Its formulas were checked against rendered pages; text extraction alone is
not the authority for equations. This follow-up formalizes finite algebraic
statements on actual matrix algebras. The paper's discussion of limiting
canonical variables does not establish an analytic limit for these owners.

The mathematical work is split between generation, independent source review,
and independent kernel/axiom acceptance. Until the validation record is
complete, this document records intended statements, not successful builds.

## A. Internal cubic Fourier coordinates

Let `R` be an associative ring and a real algebra, and let `q : R` satisfy
the existing `cyclo3 q = 0`, namely `q*q + q + 1 = 0`. There is no assumption
that `q` is central in `R`. Set `I = ZMod 3` and use the existing
`SylvesterWeylBraid.shiftMatrix 3` and `clockMatrix 3 q` as `Q` and `K`.

For `a,b : I`, construct the actual ordered words

$$
W_{ab}=Q^{a.val}K^{b.val},\qquad
(W_{ab})_{ij}=\mathbf1_{i=j+a}\,q^{(bj).val}.
$$

For every `X : Matrix I I R`, construct the left `R`-linear coordinates

$$
c_{ab}(X)=\frac13\sum_{j\in I}X_{j+a,j}\,q^{(-bj).val}.
$$

The factor `1/3` is a central real scalar. All internal phase factors remain
on the right of the matrix entries. Prove both inverse laws for this
coordinate transform and the synthesis map `c ↦ ∑ a,b, c(a,b) • W(a,b)`.
Use the resulting native `LinearEquiv` to construct a native
`Module.Basis (I × I) R (Matrix I I R)`. No claim of multiplication-preserving
Fourier coordinates or central scalar coefficients is intended.

### Existing owners and missing implication

- `Quantum/SylvesterWeylBraidBridge`: actual ring-valued clock and shift,
  braid relation, and modular powers.
- `Algebra/IsotropicCyclotomicGalois`: `cyclo3_root_cube`.
- `Canonical/QutritWeylOperatorBasis`: an existing genuine complex qutrit
  basis, expansion, uniqueness, and trace readout. This already solves the
  complex scalar problem; its scalar hypothesis does not cover internal
  noncentral coefficients.
- Mathlib `Module.Basis.ofEquivFun` and `Module.Basis.smulTower`: native
  finite coordinates and scalar-tower bases, including noncommutative
  intermediate coefficient rings.

The missing implication is an explicitly inverted, ordered coordinate map
over the noncommutative coefficient ring. Merely proving the Weyl braid
relation or listing nine words does not supply this basis.

## B. Full real block-algebra instance

Instantiate A with the exact existing `RealCubicAdjointWitness.RealCubicOperator`
carrier `Matrix (ZMod 3) (ZMod 3) (Matrix (Fin 2) (Fin 2) ℝ)` and the existing
`LieCyclotomicBridge.thirdRoot`. Identify the constructed words with powers of
the existing `charge` and `clock`.

Combine the four native real matrix units of `Matrix (Fin 2) (Fin 2) ℝ` with
the nine-word coefficient basis using `Module.Basis.smulTower`. This constructs
the actual 36-element real basis, with vectors `E_uv • W_ab`, along with its
coordinate formula and reconstruction. This is a basis of the entire operator
algebra, including entries that do not commute with the internal phase.

As a concrete consumer, represent the existing real twisted differential in
this basis using Mathlib's `LinearMap.toMatrixAlgEquiv`. The resulting real
36-by-36 matrix has cube zero and nonzero square, transported through the
actual algebra equivalence from the existing proved endomorphism identities.

The nine words alone are not asserted to span that algebra over `ℝ`. The
companion phase is not orthogonal for the standard transpose; a claim about
unitarity or Hilbert–Schmidt orthonormality would require an explicit compatible
adjoint/metric. The algebraic basis construction does not assume those claims.

## C. Seeded Schwinger averaging and the normalization condition

On an associative star ring, for any finite operator family `X`, seed `B`,
and operator `T`, prove the ordered identity

$$
\sum_\alpha X_\alpha B(T^*X_\alpha T)^*
=\operatorname{krausChannel}_X(BT^*)\,T.
$$

This identity itself requires only the star-ring laws, not unitarity of `T`.
Reuse `NoncommutativeKrausChannel.krausChannel` and the existing
`WeylFrameMasks.weyl_twirl` to obtain the corresponding full ring-valued
two-by-two formula. Do not duplicate the already proved four-Weyl twirl.

For the paper's orthonormal-basis setting (p. 571), use the native real matrix
unit basis of `M₂(ℝ)` and the existing `Gamma_mat = diag(1,-1)`:

1. Establish its trace Gram normalization and the conjugated family's same
   multiplication law/Gram normalization on the actual matrix carrier.
2. Prove that the unseeded cross sum is zero despite the exhibited orthogonal
   conjugator. Thus no scalar normalization of that sum can produce a unitary.
3. Prove that the matrix-unit seed `E₀₀` produces `Gamma_mat` itself.

Use native matrix units and their ordered multiplication laws. A generic
matrix-unit averaging identity, if needed, must preserve order over an
arbitrary coefficient ring; its coefficient-diagonal output need not be in
the center of the full algebra.

The real native basis also supplies an explicit noncommutativity witness:
`E₀₁ E₁₀ = E₀₀` and `E₁₀ E₀₁ = E₁₁`. These distinct ordered products
identify the actual noncommutative carrier used by the source counterexample.

These results identify a nonvanishing condition in the displayed normalization
formula. They do not refute existence of an intertwiner. A formula stated for
an already supplied conjugator is not a construction of a conjugator from two
abstract multiplication-table-equivalent bases.

## Source distinctions retained

| Printed pages | Source statement | Formalization boundary |
|---|---|---|
| 571–572 | Cross-family intertwiner and scalar normalization | The unseeded sum must be nonzero; preserve the zero-sum counterexample and a successful seed. |
| 575–576 | Unitary words `U^m V^n`, normalized operator basis, completeness twirl | `N^(-1/2) U^m V^n` has Hilbert–Schmidt norm one; it is not itself unitary for `N > 1`. The full-real extension uses operator-valued coordinates. |
| 577 | Factorization of a cyclic pair by powers | Requires coprime factors and consistent exponents. From `U₁=U^{N₂}`, `U₂=U^{N₁}`, the product exponent is `m₁N₂+m₂N₁`. |
| 578–579 | Product-coordinate decomposition and repeated prime factors | Separate tensor/product-coordinate construction; not a powers-only factorization for noncoprime factors. |
| 579 | Discussion of an infinite-dimensional limit | No analytic completion or uniform-convergence theorem is supplied by this finite follow-up. |

## Acceptance scope

Use pinned Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Preserve dependency pins and
maintained gates. Compile the selected owners and actual import closure under
the shared build lock, audit every owned declaration, inspect source hashes,
and run the maintained placeholder, semantic, refutation, and staged-content
checks. The existing five PR owners remain covered by the focused workflow.

No authored `Complex.I`, new axiom, proof placeholder, unsafe bypass, scalar
replacement of the full operator algebra, or assumption of the desired basis
is permitted. The published validation record must state warnings, exact
targets, declaration coverage, source identity, and any unrun checks.
