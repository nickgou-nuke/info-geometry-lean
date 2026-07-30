import Mathlib.Tactic
import InfoGeometry.Canonical.CuntzMapKreinBridge

/-!
# Cuntz Map — Discrete Modular Step and Fixed Readouts

`Φ(X) = S_L * X * S_L^* + S_R * X * S_R^*`.

This file proves the finite algebraic fixed-readout consequences of the
symmetric branch law. It does not prove uniqueness of a KMS state, norm
contraction, Ruelle--Perron--Frobenius classification, or equality with a
continuous modular flow.

#### BUCKET 1: CLOSED FINITE THEOREMS
Unitality, one-step fixed readout, iterated fixed readout, and finite orbit-sum
readout under explicit half-branch hypotheses.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The Cuntz map is exposed as a witnessed `DiscreteCuntzModularStep`.

#### BUCKET 3: OPEN CLOSURE DEBT
Uniqueness, contraction, complete positivity, and continuous modular-flow
classification.
-/

set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.CuntzMapFixedPoint

open InfoGeometry.Canonical.CuntzMapKreinBridge

variable {Op : Type*} [Ring Op] [StarRing Op]

/-! ### 1. The Cuntz Map Φ -/

def cuntzMap (S_left S_right : Op) (X : Op) : Op :=
  CuntzMapKreinBridge.cuntzMapTwo S_left S_right X

theorem cuntzMap_unital (S_left S_right : Op) (h_range : S_left * star S_left + S_right * star S_right = 1) :
    cuntzMap S_left S_right 1 = 1 := by
  exact CuntzMapKreinBridge.cuntzMapTwo_one_of_partition
    (S_left := S_left) (S_right := S_right) h_range

/-! ### 2. KMS Symmetric State — the Jaynes Maxent Point -/

structure KMSSymmetricState (S_left S_right : Op) where
  φ : Op →+ ℝ
  φ_one : φ 1 = 1
  half_L : ∀ X, φ (S_left * X * star S_left) = (1/2 : ℝ) * φ X
  half_R : ∀ X, φ (S_right * X * star S_right) = (1/2 : ℝ) * φ X

namespace KMSSymmetricState

variable {S_left S_right : Op} (state : KMSSymmetricState S_left S_right)

abbrev φ_add : ∀ X Y, state.φ (X + Y) = state.φ X + state.φ Y :=
  state.φ.map_add

/-- φ(Φ(X)) = φ(X) — the KMS state is the Cuntz map fixed point. -/
theorem cuntzMap_fixed_point (X : Op) : state.φ (cuntzMap S_left S_right X) = state.φ X := by
  simpa [cuntzMap] using
    CuntzMapKreinBridge.real_additive_readout_fixed_of_half_branch_scaling
      (φ := state.φ) (S_left := S_left) (S_right := S_right) (X := X)
      (state.half_L X) (state.half_R X)

/-- φ(Φ^n(X)) = φ(X) — the full RG flow preserves expectations. -/
theorem cuntzMap_iterate_fixed_point (X : Op) (n : ℕ) :
    state.φ (Nat.iterate (cuntzMap S_left S_right) n X) = state.φ X := by
  revert X
  induction' n with k ih
  · intro X
    rfl
  · intro X
    rw [Function.iterate_succ_apply]
    rw [ih (cuntzMap S_left S_right X)]
    exact cuntzMap_fixed_point state X

/-- `φ(Σ_{k=0}^{N-1} Φ^k(X)) = N * φ(X)`: finite orbit-sum readout. -/
theorem cuntzMap_sum_iterate_fixed_point (X : Op) (N : ℕ) :
    state.φ (Finset.sum (Finset.range N) (fun k => Nat.iterate (cuntzMap S_left S_right) k X)) =
    (N : ℝ) * state.φ X := by
  induction' N with n ih
  · have hφ0 : state.φ 0 = 0 := by
      exact state.φ.map_zero
    simp [hφ0]
  · rw [Finset.sum_range_succ,
      state.φ_add (Finset.sum (Finset.range n) _) (Nat.iterate (cuntzMap S_left S_right) n X),
      ih,
      cuntzMap_iterate_fixed_point state X n]
    push_cast; ring

/--
Witnessed discrete modular step carried by the Cuntz map.

This is the honest theorem surface behind the slogan that the Cuntz map is the
clock tick: the supplied `sigma` is definitionally the two-branch Cuntz map.
-/
def discreteCuntzStep :
    DiscreteCuntzModularStep Op where
  S_left := S_left
  S_right := S_right
  sigma := cuntzMap S_left S_right
  sigma_eq_cuntzMap := by
    intro X
    rfl

theorem discreteCuntzStep_apply (X : Op) :
    (discreteCuntzStep (S_left := S_left) (S_right := S_right)).sigma X =
      cuntzMap S_left S_right X := by
  rfl

end KMSSymmetricState

end InfoGeometry.Canonical.CuntzMapFixedPoint
