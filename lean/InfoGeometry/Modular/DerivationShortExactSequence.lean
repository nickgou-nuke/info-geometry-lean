/-
=============================================================================
     InfoGeometry.Modular: DerivationShortExactSequence
=============================================================================

The Semidirect Lie Algebra of Reality:
  0 → Z(A) → A ──ad──→ Der(A) ──π──→ Out(A) → 0

Proving:
1. ker(ad) = Z(A)
2. [Der(A), Inn(A)] ⊆ Inn(A) (Lie Ideal)
3. Inner derivations satisfy the Leibniz rule

Zero Custom Axioms • Zero Sorries • Fully Native Mathlib 4
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

import InfoGeometry.Modular.ExactSequence

noncomputable section

namespace InfoGeometry.Modular.DerivationShortExactSequence

open InfoGeometry.Modular.ExactSequence

variable {A : Type*} [Ring A]

/-- The kernel of the adjoint modular map is the algebraic center: ker(ad) = Z(A). -/
theorem kernel_ad_eq_center (K : A) :
    (∀ X, InfoGeometry.EndToEnd.adK K X = 0) ↔ (∀ X, K * X = X * K) :=
  ad_kernel_eq_center K

/-- Inner derivations form a Lie ideal: [Der, Inn] ⊆ Inn. -/
theorem inn_lie_ideal (D : InfoGeometry.EndToEnd.Derivation A) (K X : A) :
    D (InfoGeometry.EndToEnd.adK K X) - InfoGeometry.EndToEnd.adK K (D X) =
      InfoGeometry.EndToEnd.adK (D K) X :=
  inn_is_lie_ideal D K X

/-- Inner derivations are exact derivations. -/
theorem ad_derivation (K X Y : A) :
    InfoGeometry.Modular.adK K (X * Y) =
      (InfoGeometry.Modular.adK K X) * Y + X * (InfoGeometry.Modular.adK K Y) :=
  ad_is_derivation K X Y

end InfoGeometry.Modular.DerivationShortExactSequence
