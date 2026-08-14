import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzConditionalExpectation

/-!
# Cuntz Tensor Tree Realization Bridge

Finite rooted-tree and cylinder-projection facts for the Cuntz algebra.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzConditionalExpectation
open InfoGeometry.Algebra.CuntzContractionLemmas

variable {n : ℕ}

def cuntzWordShift : List (Fin n) → CuntzAlg n
  | [] => 1
  | (i :: is) => cuntzS n i * cuntzWordShift is

def cuntzWordShiftDag : List (Fin n) → CuntzAlg n
  | [] => 1
  | (i :: is) => cuntzWordShiftDag is * cuntzSdag n i

@[simp] theorem cuntzWordShift_nil : cuntzWordShift ([] : List (Fin n)) = 1 := rfl
@[simp] theorem cuntzWordShiftDag_nil : cuntzWordShiftDag ([] : List (Fin n)) = 1 := rfl

theorem cuntzWordShift_append (w₁ w₂ : List (Fin n)) :
    cuntzWordShift (w₁ ++ w₂) = cuntzWordShift w₁ * cuntzWordShift w₂ := by
  induction w₁ with
  | nil => simp
  | cons i is ih => simp [cuntzWordShift, ih, mul_assoc]

theorem cuntzWordShiftDag_append (w₁ w₂ : List (Fin n)) :
    cuntzWordShiftDag (w₁ ++ w₂) = cuntzWordShiftDag w₂ * cuntzWordShiftDag w₁ := by
  induction w₁ with
  | nil => simp
  | cons i is ih => simp [cuntzWordShiftDag, ih, mul_assoc]

def cylinderProjection (w : List (Fin n)) : CuntzAlg n :=
  cuntzWordShift w * cuntzWordShiftDag w

def cuntzPrefixEndomorphism (x : CuntzAlg n) : CuntzAlg n :=
  ∑ i : Fin n, cuntzS n i * x * cuntzSdag n i

theorem cuntzPrefixEndomorphism_cylinderProjection (w : List (Fin n)) :
    cuntzPrefixEndomorphism (cylinderProjection w) =
      ∑ i : Fin n, cylinderProjection (i :: w) := by
  unfold cuntzPrefixEndomorphism
  apply Finset.sum_congr rfl
  intro i _
  simp [cylinderProjection, cuntzWordShift, cuntzWordShiftDag, mul_assoc]

theorem cylinderProjection_append (w₁ w₂ : List (Fin n)) :
    cylinderProjection (w₁ ++ w₂) =
      cuntzWordShift w₁ * cylinderProjection w₂ * cuntzWordShiftDag w₁ := by
  unfold cylinderProjection
  rw [cuntzWordShift_append, cuntzWordShiftDag_append]
  noncomm_ring

@[simp] theorem cylinderProjection_nil : cylinderProjection ([] : List (Fin n)) = 1 := by
  simp [cylinderProjection]

theorem cylinderProjection_children_sum (w : List (Fin n)) :
    (∑ i : Fin n, cylinderProjection (w ++ [i])) = cylinderProjection w := by
  have h_append_shift : ∀ i, cuntzWordShift (w ++ [i]) = cuntzWordShift w * cuntzS n i := by
    intro i
    rw [cuntzWordShift_append]
    simp [cuntzWordShift]
  have h_append_dag : ∀ i, cuntzWordShiftDag (w ++ [i]) = cuntzSdag n i * cuntzWordShiftDag w := by
    intro i
    rw [cuntzWordShiftDag_append]
    simp [cuntzWordShiftDag]
  calc
    (∑ i : Fin n, cylinderProjection (w ++ [i]))
        = ∑ i : Fin n, (cuntzWordShift w * cuntzS n i) *
            (cuntzSdag n i * cuntzWordShiftDag w) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [cylinderProjection]
          rw [h_append_shift i, h_append_dag i]
    _ = ∑ i : Fin n, cuntzWordShift w *
          (cuntzS n i * cuntzSdag n i) * cuntzWordShiftDag w := by
          simp_rw [mul_assoc]
    _ = cuntzWordShift w * (∑ i : Fin n, cuntzS n i * cuntzSdag n i) *
          cuntzWordShiftDag w := by
          rw [Finset.mul_sum, Finset.sum_mul]
    _ = cuntzWordShift w * 1 * cuntzWordShiftDag w := by
          rw [cuntz_ranges_sum_one n]
    _ = cylinderProjection w := by simp [cylinderProjection]

theorem expectation_cylinderProjection_fixed_length_one (i : Fin n) :
    expectation n (cylinderProjection [i]) = cylinderProjection [i] := by
  dsimp [cylinderProjection, cuntzWordShift, cuntzWordShiftDag]
  simp [expectation_projector]

theorem expectation_cylinderProjection_fixed
    (w : List (Fin n)) :
    expectation n (cylinderProjection w) = cylinderProjection w := by
  induction w with
  | nil => simpa [cylinderProjection] using expectation_one n
  | cons i w ih =>
      let T := cuntzWordShift w
      let Tdag := cuntzWordShiftDag w
      unfold expectation
      change
        (∑ k : Fin n,
          (cuntzS n k * cuntzSdag n k) *
            ((cuntzS n i * T) * (Tdag * cuntzSdag n i)) *
              (cuntzS n k * cuntzSdag n k)) =
          (cuntzS n i * T) * (Tdag * cuntzSdag n i)
      have hterm : ∀ k : Fin n,
          (cuntzS n k * cuntzSdag n k) *
              ((cuntzS n i * T) * (Tdag * cuntzSdag n i)) *
                (cuntzS n k * cuntzSdag n k) =
            (if k = i then cuntzS n i else 0) * T * Tdag *
              (if k = i then cuntzSdag n i else 0) := by
        intro k
        calc
          (cuntzS n k * cuntzSdag n k) *
                ((cuntzS n i * T) * (Tdag * cuntzSdag n i)) *
                  (cuntzS n k * cuntzSdag n k) =
              ((cuntzS n k * cuntzSdag n k) * cuntzS n i) *
                T * Tdag * (cuntzSdag n i *
                  (cuntzS n k * cuntzSdag n k)) := by
            noncomm_ring
          _ = (if k = i then cuntzS n i else 0) * T * Tdag *
                (if k = i then cuntzSdag n i else 0) := by
            rw [projector_right_contract n k i,
              projector_left_contract n k i]
            by_cases hki : k = i <;> simp [hki]
      rw [Finset.sum_congr rfl (fun k _ => hterm k)]
      simp [mul_assoc]

end InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge
