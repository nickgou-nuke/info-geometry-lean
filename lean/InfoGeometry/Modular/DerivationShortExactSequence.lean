import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Center
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

import InfoGeometry.EndToEnd
import InfoGeometry.Modular.DualFlowLieAlgebraBridge

noncomputable section

namespace InfoGeometry.Modular.DerivationShortExactSequence

open InfoGeometry.EndToEnd
open InfoGeometry.Modular
open InfoGeometry.Modular.FullLieAlgebra

variable {A : Type*} [Ring A]

/-- The Lie bracket / commutator of two derivations is a derivation. -/
def commutator (D₁ D₂ : Derivation A) : Derivation A where
  toFun x := D₁ (D₂ x) - D₂ (D₁ x)
  map_add' x y := by
    rw [D₂.map_add, D₁.map_add, D₁.map_add, D₂.map_add]
    abel
  leibniz' x y := by
    rw [D₂.leibniz, D₁.map_add, D₁.leibniz, D₁.leibniz,
        D₁.leibniz, D₂.map_add, D₂.leibniz, D₂.leibniz]
    simp only [sub_mul, mul_sub]
    abel

/-- The inner modular derivation ad_K as a bundled Derivation. -/
def modularDerivation (K : A) : Derivation A where
  toFun := adK K
  map_add' x y := by
    dsimp [adK]
    simp only [mul_add, add_mul]
    abel
  leibniz' x y := by
    dsimp [adK]
    calc
      K * (x * y) - (x * y) * K = (K * x - x * K) * y + x * (K * y - y * K) := by
        simp only [sub_mul, mul_sub, mul_assoc]
        abel

theorem ker_adK_eq_center (K : A) :
    (∀ X, adK K X = 0) ↔ (∀ X, K * X = X * K) :=
  InfoGeometry.EndToEnd.thermal_time_kernel K

theorem center_generates_zero_flow (K : A) (hK : ∀ X, K * X = X * K) (X : A) :
    adK K X = 0 := by
  have h := (ker_adK_eq_center K).mpr hK
  exact h X

theorem master_dual_flow_commutator (D : Derivation A) (K X : A) :
    D (adK K X) - adK K (D X) = adK (D K) X :=
  InfoGeometry.EndToEnd.master_dual_flow_commutator D K X

theorem commutator_modular_apply (D : Derivation A) (K X : A) :
    commutator D (modularDerivation K) X = modularDerivation (D K) X :=
  master_dual_flow_commutator D K X

theorem inn_is_lie_ideal (D : Derivation A) (K : A) :
    ∃ K' : A, ∀ X : A, commutator D (modularDerivation K) X = modularDerivation K' X := by
  use D K
  intro X
  exact commutator_modular_apply D K X

theorem inner_derivation_bracket (K₁ K₂ : A) (X : A) :
    commutator (modularDerivation K₁) (modularDerivation K₂) X =
      modularDerivation (adK K₁ K₂) X :=
  commutator_modular_apply (modularDerivation K₁) K₂ X

theorem derivation_short_exact_sequence_summary (D : Derivation A) (K X : A) :
    ((∀ Y, adK K Y = 0) ↔ (∀ Y, K * Y = Y * K)) ∧
    (D (adK K X) - adK K (D X) = adK (D K) X) ∧
    (∃ K' : A, ∀ Y : A, commutator D (modularDerivation K) Y = modularDerivation K' Y) := by
  exact ⟨ker_adK_eq_center K, master_dual_flow_commutator D K X, inn_is_lie_ideal D K⟩

/-!
### Bundled Native Mathlib Short Exact Sequence
-/
variable {R : Type*} [CommRing R] [Algebra R A]

/-- The native Mathlib Lie ideal of inner modular derivations. -/
abbrev InnLieIdeal (R : Type*) (A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    LieIdeal R (Der R A) :=
  Inn R A

/-- The native Mathlib Lie algebra of outer derivations Out(A) = Der(A) ⧸ Inn(A). -/
abbrev OutLieAlgebra (R : Type*) (A : Type*) [CommRing R] [Ring A] [Algebra R A] : Type _ :=
  Out R A

/-- Full Lie short exact sequence in native Mathlib. -/
theorem native_mathlib_derivation_short_exact_sequence :
    (toOut R A).ker = Inn R A ∧
    Function.Surjective (toOut R A) ∧
    ((LieDerivation.ad R A).ker = LieAlgebra.center R A) :=
  FullLieAlgebra.derivation_short_exact_sequence R A

end InfoGeometry.Modular.DerivationShortExactSequence
