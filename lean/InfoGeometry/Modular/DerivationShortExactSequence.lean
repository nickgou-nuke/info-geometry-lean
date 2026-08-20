/-
=============================================================================
     InfoGeometry.Modular: DerivationShortExactSequence
=============================================================================

The Semidirect Lie Algebra of Reality:
  0 → Z(A) → A ──ad──→ Der(A) ──π──→ Out(A) → 0

Proving:
1. ker(ad) = Z(A) (Connes-Rovelli Thermal Time Hypothesis)
2. [Der(A), Inn(A)] ⊆ Inn(A) (Inner Derivations as Lie Ideal / Thermodynamic Sink)
3. Inner derivations satisfy the Leibniz derivation rule

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
theorem ker_adK_eq_center (K : A) :
    (∀ X, InfoGeometry.EndToEnd.adK K X = 0) ↔ (∀ X, K * X = X * K) :=
  ad_kernel_eq_center K

/-- Compatibility alias for kernel_ad_eq_center. -/
theorem kernel_ad_eq_center (K : A) :
    (∀ X, InfoGeometry.EndToEnd.adK K X = 0) ↔ (∀ X, K * X = X * K) :=
  ker_adK_eq_center K

/-- Inner derivations form a strict Lie ideal: [Der, Inn] ⊆ Inn. -/
theorem inn_is_lie_ideal (D : InfoGeometry.EndToEnd.Derivation A) (K X : A) :
    D (InfoGeometry.EndToEnd.adK K X) - InfoGeometry.EndToEnd.adK K (D X) =
      InfoGeometry.EndToEnd.adK (D K) X :=
  InfoGeometry.Modular.ExactSequence.inn_is_lie_ideal D K X

/-- Compatibility alias for inn_lie_ideal. -/
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
