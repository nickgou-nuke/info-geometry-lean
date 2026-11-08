import InfoGeometry.Modular.ExactSequence
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exact commutator equilibrium criterion

This module sharpens the associative dual-flow owner with the exact algebraic
criterion for vanishing commutator flow.

The criterion is `[D, ad_K] = 0` exactly when `D K` is central.  No claim is
made here about a Lie quotient or a geometric interpretation.
-/

noncomputable section

namespace InfoGeometry.Modular.ExactSequence

variable {A : Type*} [Ring A]

/-- The exact equilibrium criterion for the associative inner-derivation flow. -/
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
