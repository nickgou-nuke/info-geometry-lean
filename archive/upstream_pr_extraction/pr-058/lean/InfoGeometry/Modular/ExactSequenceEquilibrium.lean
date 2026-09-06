import InfoGeometry.Modular.ExactSequence

/-!
# Exact commutator equilibrium criterion

This module sharpens the associative dual-flow owner with the exact algebraic
criterion for vanishing commutator flow.

For an associative ring `A`, the imported owner proves

* `ker_adK_eq_center`: `ad_K = 0` pointwise iff `K` is central;
* `commutator_eq_modularDerivation`:
  `[D, ad_K] = ad_(D K)` as bundled derivations.

Combining them gives the exact criterion

`[D, ad_K] = 0 ↔ D K ∈ Z(A)`.

The stronger-looking condition `D K = 0` is therefore sufficient but not
necessary: a derivation may change `K` by a central element without changing
its inner commutator flow.

## Structural boundary

`ExactSequence.lean` currently defines `Out` only as the additive quotient
`Derivation A ⧸ Inn`.  This module does not claim that this quotient is already
bundled as a Lie quotient, and it does not claim a semidirect-product splitting.
A splitting would require additional data: a Lie-homomorphic section of the
quotient projection.

The theorem below is purely algebraic.  It does not identify `D` with spacetime
geometry, `K` with a Tomita--Takesaki modular generator, or the equivariance
identity with reciprocal physical backreaction.
-/

noncomputable section

namespace InfoGeometry.Modular.ExactSequence

variable {A : Type*} [Ring A]

/--
The exact equilibrium criterion for the associative inner-derivation flow:
`[D, ad_K]` vanishes exactly when `D K` is central.
-/
theorem commutator_eq_zero_iff_DK_central (D : Derivation A) (K : A) :
    Derivation.derivationCommutator D (modularDerivation K) = 0 ↔
      ∀ X : A, D K * X = X * D K := by
  rw [commutator_eq_modularDerivation]
  constructor
  · intro h
    apply (ker_adK_eq_center (D K)).mp
    intro X
    have hx := congrArg (fun E : Derivation A => E X) h
    change adK (D K) X = 0 at hx
    exact hx
  · intro h
    ext X
    change adK (D K) X = 0
    exact (ker_adK_eq_center (D K)).mpr h X

end InfoGeometry.Modular.ExactSequence

end noncomputable section
