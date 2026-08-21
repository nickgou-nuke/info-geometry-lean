import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Center
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

import InfoGeometry.EndToEnd
import InfoGeometry.Modular.DualFlowLieAlgebraBridge
import InfoGeometry.Modular.SemidirectProductLieAlgebra

noncomputable section

namespace InfoGeometry.Modular.DerivationShortExactSequence

open InfoGeometry.Modular.LieAlgebra
open InfoGeometry.Modular.FullLieAlgebra

variable {A : Type*} [Ring A]

/-- The Lie bracket / commutator of two derivations is a derivation. -/
def commutator (D₁ D₂ : RingDerivation A) : RingDerivation A :=
  RingDerivation.derivationCommutator D₁ D₂

theorem ker_adK_eq_center (K : A) :
    (∀ X, adK K X = 0) ↔ (∀ X, K * X = X * K) := by
  constructor
  · intro h X
    have hX := h X
    dsimp [adK] at hX
    exact eq_of_sub_eq_zero hX
  · intro h X
    dsimp [adK]
    rw [h X, sub_self]

theorem center_generates_zero_flow (K : A) (hK : ∀ X, K * X = X * K) (X : A) :
    adK K X = 0 :=
  central_modular_timelessness K hK X

theorem master_dual_flow_commutator (D : RingDerivation A) (K X : A) :
    D (adK K X) - adK K (D X) = adK (D K) X :=
  dual_flow_commutator D K X

theorem commutator_modular_apply (D : RingDerivation A) (K X : A) :
    commutator D (modularDerivation K) X = modularDerivation (D K) X :=
  bracket_modularDerivation D K X

theorem derivation_ext {D E : RingDerivation A} (h : ∀ X, D X = E X) : D = E := by
  cases D with
  | mk D hD₁ hD₂ =>
    cases E with
    | mk E hE₁ hE₂ =>
      have hDE : D = E := by
        funext X
        exact h X
      subst hDE
      rfl

theorem commutator_modular_eq (D : RingDerivation A) (K : A) :
    commutator D (modularDerivation K) = modularDerivation (D K) := by
  apply derivation_ext
  intro X
  exact commutator_modular_apply D K X

theorem inn_is_lie_ideal (D : RingDerivation A) (K : A) :
    ∃ K' : A, ∀ X : A, commutator D (modularDerivation K) X = modularDerivation K' X := by
  use D K
  intro X
  exact commutator_modular_apply D K X

theorem inner_derivation_bracket (K₁ K₂ : A) (X : A) :
    commutator (modularDerivation K₁) (modularDerivation K₂) X =
      modularDerivation (adK K₁ K₂) X :=
  bracket_modularDerivations K₁ K₂ X

theorem inner_derivation_bracket_eq (K₁ K₂ : A) :
    commutator (modularDerivation K₁) (modularDerivation K₂) =
      modularDerivation (adK K₁ K₂) := by
  apply derivation_ext
  intro X
  exact inner_derivation_bracket K₁ K₂ X

theorem derivation_short_exact_sequence_summary (D : RingDerivation A) (K X : A) :
    ((∀ Y, adK K Y = 0) ↔ (∀ Y, K * Y = Y * K)) ∧
    (D (adK K X) - adK K (D X) = adK (D K) X) ∧
    (∃ K' : A, ∀ Y : A, commutator D (modularDerivation K) Y = modularDerivation K' Y) := by
  exact ⟨ker_adK_eq_center K, master_dual_flow_commutator D K X, inn_is_lie_ideal D K⟩

/--
The algebraic dual-flow capstone.

The outer derivation acts on the inner modular ideal through its value on the
generator.  Consequently an invariant generator gives a commuting pair, while
a central generator gives the zero inner derivation.  This is a purely
associative ring-level statement; no analytic flow or physical interpretation
is part of the theorem.
-/
theorem dual_flow_capstone (D : RingDerivation A) (K : A) :
    (commutator D (modularDerivation K) = modularDerivation (D K)) ∧
    (D K = 0 → ∀ X, commutator D (modularDerivation K) X = 0) ∧
    ((∀ X, K * X = X * K) → ∀ X, modularDerivation K X = 0) := by
  refine ⟨commutator_modular_eq D K, ?_, ?_⟩
  · intro hK X
    rw [commutator_modular_apply D K X, hK]
    exact center_generates_zero_flow 0 (by intro Y; simp) X
  · intro hK X
    exact center_generates_zero_flow K hK X

/-!
### Bundled Native Mathlib Short Exact Sequence & Semidirect Product
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

/-- The fully instantiated native Semidirect Product Lie Algebra Out(A) ⋉ Inn(A). -/
abbrev SemidirectDerivationLieAlgebra (L M : Type*) [LieRing L] [LieAlgebra R L]
    [LieRing M] [LieAlgebra R M] [LieRingModule L M] [LieModule R L M]
    [InfoGeometry.Modular.Semidirect.LieDerivationAction L M] :=
  InfoGeometry.Modular.Semidirect.SemidirectProduct L M

end InfoGeometry.Modular.DerivationShortExactSequence
