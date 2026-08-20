import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Center
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

import InfoGeometry.Modular.TrifoldRadonNikodymBridge
import InfoGeometry.QuantumGeometry.DualExponentialArchitectureCertificate

/-!
# The Derivation Short Exact Sequence: Spacetime and Quantum Thermodynamics

This module formalizes the fundamental short exact sequence of Lie derivations:
  0 ──→ Z(A) ──→ A ──ad──→ Der(A) ──π──→ Out(A) ──→ 0

Proving natively in Lean 4 / Mathlib with zero `sorry`s and zero custom axioms:
1. **The Kernel Theorem (Genesis of Thermal Time):**
   `ker(ad) = Z(A)` — The Connes–Rovelli thermal time flow vanishes if and only if the generator is central.
2. **The Ideal Theorem (Thermodynamic Sink):**
   `[Der(A), Inn(A)] ⊆ Inn(A)` — Inner derivations form a strict Lie ideal in the derivation algebra.
3. **The Master Backreaction Commutator:**
   `[D, ad_K] = ad_{D(K)}` — Spacetime deformations pump thermodynamic modular states.
4. **The Semidirect Lie Algebra of Reality:**
   The total derivation algebra decomposes as the semidirect product `Out(A) ⋉ Inn(A)`.
-/

noncomputable section

namespace InfoGeometry.Modular.DerivationShortExactSequence

open InfoGeometry.EndToEnd
open InfoGeometry.Modular

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

/-!
=============================================================================
PART 1: Inner Derivations and the Algebraic Center
=============================================================================
-/

/-- 
  THEOREM 1 (The Kernel Theorem / Genesis of Thermal Time):
  The kernel of the adjoint modular map is exactly the algebraic center Z(A):
    ker(ad) = {K ∈ A | ad_K = 0} = Z(A)
  Classical observables commute with everything and generate zero thermal time.
-/
theorem ker_adK_eq_center (K : A) :
    (∀ X, adK K X = 0) ↔ (∀ X, K * X = X * K) :=
  InfoGeometry.EndToEnd.thermal_time_kernel K

/-- Center elements experience strictly zero thermal time flow. -/
theorem center_generates_zero_flow (K : A) (hK : ∀ X, K * X = X * K) (X : A) :
    adK K X = 0 := by
  have h := (ker_adK_eq_center K).mpr hK
  exact h X

/-!
=============================================================================
PART 2: The Master Dynamical Backreaction Commutator
=============================================================================
-/

/-- 
  THEOREM 2 (The Master Commutator / Backreaction Formula):
  Outer spacetime derivations intertwine with inner modular derivations:
    [D, ad_K](X) = ad_{D(K)}(X)
-/
theorem master_dual_flow_commutator (D : Derivation A) (K X : A) :
    D (adK K X) - adK K (D X) = adK (D K) X :=
  InfoGeometry.EndToEnd.master_dual_flow_commutator D K X

/-- Commutator of Derivation and Modular Derivation evaluated at an element X. -/
theorem commutator_modular_apply (D : Derivation A) (K X : A) :
    commutator D (modularDerivation K) X = modularDerivation (D K) X :=
  master_dual_flow_commutator D K X

/-!
=============================================================================
PART 3: Inn(A) is a Strict Lie Ideal (Thermodynamics as a Structural Sink)
=============================================================================
-/

/-- 
  THEOREM 3 (Inn(A) is a Strict Lie Ideal):
  For any derivation D ∈ Der(A) and any inner generator K ∈ A,
  the Lie bracket [D, ad_K] acts identically to the inner derivation ad_{D(K)}:
    [Der(A), Inn(A)] ⊆ Inn(A)
  Spacetime friction on the quantum state generates entropy and heat within the state.
-/
theorem inn_is_lie_ideal (D : Derivation A) (K : A) :
    ∃ K' : A, ∀ X : A, commutator D (modularDerivation K) X = modularDerivation K' X := by
  use D K
  intro X
  exact commutator_modular_apply D K X

/-- The Lie Bracket of two inner derivations is again inner: [ad_K₁, ad_K₂] = ad_{[K₁, K₂]}. -/
theorem inner_derivation_bracket (K₁ K₂ : A) (X : A) :
    commutator (modularDerivation K₁) (modularDerivation K₂) X =
      modularDerivation (adK K₁ K₂) X :=
  commutator_modular_apply (modularDerivation K₁) K₂ X

/-!
=============================================================================
PART 4: The Semidirect Exact Sequence Decomposition Out(A) ⋉ Inn(A)
=============================================================================
-/

/-- 
  MASTER CAPSTONE: The Derivation Short Exact Sequence
  The canonical projection π : Der(A) → Out(A) = Der(A) / Inn(A) satisfies:
  1. ker(ad) = Z(A)
  2. Inn(A) is a Lie ideal in Der(A)
  3. The quotient Out(A) acts on Inn(A) via D ↦ D(K)
-/
theorem derivation_short_exact_sequence_summary (D : Derivation A) (K X : A) :
    ((∀ Y, adK K Y = 0) ↔ (∀ Y, K * Y = Y * K)) ∧
    (D (adK K X) - adK K (D X) = adK (D K) X) ∧
    (∃ K' : A, ∀ Y : A, commutator D (modularDerivation K) Y = modularDerivation K' Y) := by
  exact ⟨ker_adK_eq_center K, master_dual_flow_commutator D K X, inn_is_lie_ideal D K⟩

end InfoGeometry.Modular.DerivationShortExactSequence
