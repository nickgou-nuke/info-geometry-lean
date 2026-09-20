import InfoGeometry.Algebra.CyclicOrderThree
import InfoGeometry.Canonical.CanonicalZornOuterTrialityGroup

noncomputable section

namespace InfoGeometry.Algebra.SplitOctonionTriality

open CanonicalZornCompositionTriality CanonicalZornOuterTrialityGroup
open InfoGeometry.Algebra.CyclicOrderThree

abbrev TrialityCarrier := Vector8 × SpinorPlus8 × SpinorMinus8

def cycle : Module.End ℂ TrialityCarrier where
  toFun state := (spinorMinusToVector state.2.2,
    vectorToSpinorPlus state.1, spinorPlusToSpinorMinus state.2.1)
  map_add' first second := by ext <;> simp
  map_smul' scalar state := by ext <;> simp

theorem cycle_order_three (state : TrialityCarrier) :
    cycle (cycle (cycle state)) = state := by
  apply Prod.ext
  · exact typed_triality_order_three state.1
  · apply Prod.ext
    · exact typed_triality_order_three_spinorPlus state.2.1
    · exact typed_triality_order_three_spinorMinus state.2.2

def cycleEquiv : TrialityCarrier ≃ₗ[ℂ] TrialityCarrier where
  toLinearMap := cycle
  invFun state := cycle (cycle state)
  left_inv := cycle_order_three
  right_inv := cycle_order_three

def coupling (state : TrialityCarrier) : ℂ :=
  trialityForm state.1 state.2.1 state.2.2

theorem coupling_cycle (state : TrialityCarrier) :
    coupling (cycle state) = coupling state :=
  (trialityForm_cyclic state.1 state.2.1 state.2.2).symm

theorem reynolds_cycle_idempotent :
    (reynolds cycle).comp (reynolds cycle) = reynolds cycle :=
  reynolds_idempotent cycle cycle_order_three

theorem cycle_boundary_cancellation (state : TrialityCarrier) :
    orbitSum cycle (boundary cycle state) = 0 :=
  orbitSum_boundary cycle cycle_order_three state

theorem cycle_cancellation_iff_boundary (state : TrialityCarrier) :
    orbitSum cycle state = 0 ↔ ∃ source, boundary cycle source = state :=
  orbitSum_eq_zero_iff_boundary cycle cycle_order_three state

def diagonal (vector : Vector8) : TrialityCarrier :=
  (vector, vectorToSpinorPlus vector,
    spinorPlusToSpinorMinus (vectorToSpinorPlus vector))

theorem cycle_diagonal (vector : Vector8) : cycle (diagonal vector) = diagonal vector := by
  apply Prod.ext
  · exact typed_triality_order_three vector
  · rfl

theorem orbitSum_diagonal (vector : Vector8) :
    orbitSum cycle (diagonal vector) = (3 : ℂ) • diagonal vector :=
  orbitSum_of_fixed cycle _ (cycle_diagonal vector)

section Seam

variable {Space : Type*} [AddCommGroup Space] [Module ℝ Space]

theorem even_odd_intersection (seam : Module.End ℝ Space) (vector : Space)
    (heven : seam vector = vector) (hodd : seam vector = -vector) : vector = 0 := by
  have htwice : (2 : ℝ) • vector = 0 := by
    have hequal : vector = -vector := heven.symm.trans hodd
    calc
      (2 : ℝ) • vector = vector + vector := by module
      _ = -vector + vector := congrArg (fun value => value + vector) hequal
      _ = 0 := neg_add_cancel vector
  exact (smul_eq_zero.mp htwice).resolve_left (by norm_num)

end Seam

end InfoGeometry.Algebra.SplitOctonionTriality
