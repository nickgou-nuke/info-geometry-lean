/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevBoundaryDiracPair
import InfoGeometry.Physics.KreinDiracKasparovSpinorBilinear

/-! A metric constructed from the actual two endpoint operators. Ordinary
self-adjointness is an explicit input; the resulting metric adjoint reverses
the signs of both endpoints. No positivity is asserted. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevBoundaryConstructedMetric

open InfoGeometry.Quantum.KitaevChain InfoGeometry.Physics
open KitaevBoundaryDiracPair

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {N : ℕ} (hN : 0 < N) (ops : MajoranaCliffordOperators N A)

def endpointMetric : A := Complex.I • (leftEndpoint hN ops * rightEndpoint hN ops)

theorem endpoint_reverse : rightEndpoint hN ops * leftEndpoint hN ops =
    -(leftEndpoint hN ops * rightEndpoint hN ops) := by
  apply eq_neg_of_add_eq_zero_right
  apply ops.h_ortho
  intro h
  have := congrArg Fin.val h
  dsimp at this
  omega

theorem endpointMetric_sq : endpointMetric hN ops * endpointMetric hN ops = 1 := by
  have hsq : (leftEndpoint hN ops * rightEndpoint hN ops) *
      (leftEndpoint hN ops * rightEndpoint hN ops) = -1 := by
    calc
      _ = leftEndpoint hN ops * (rightEndpoint hN ops * leftEndpoint hN ops) *
          rightEndpoint hN ops := by noncomm_ring
      _ = -(leftEndpoint hN ops * leftEndpoint hN ops) *
          (rightEndpoint hN ops * rightEndpoint hN ops) := by
            rw [endpoint_reverse]
            noncomm_ring
      _ = -1 := by rw [leftEndpoint_sq, ops.h_sq]; simp
  simp only [endpointMetric, smul_mul_smul, Complex.I_mul_I, hsq, neg_one_smul, neg_neg]

theorem endpointMetric_star
    (hL : star (leftEndpoint hN ops) = leftEndpoint hN ops)
    (hR : star (rightEndpoint hN ops) = rightEndpoint hN ops) :
    star (endpointMetric hN ops) = endpointMetric hN ops := by
  simp [endpointMetric, star_smul, star_mul, hL, hR, endpoint_reverse]

/-- Existing Kasparov/Krein carrier, with this metric and trivial grading. -/
def endpointKreinData
    (hL : star (leftEndpoint hN ops) = leftEndpoint hN ops)
    (hR : star (rightEndpoint hN ops) = rightEndpoint hN ops) : KasparovKreinData A :=
  ⟨⟨endpointMetric hN ops, 1⟩,
    endpointMetric_sq hN ops, endpointMetric_star hN ops hL hR, by simp, by simp⟩

theorem endpointMetric_conjugate_left :
    endpointMetric hN ops * leftEndpoint hN ops * endpointMetric hN ops =
      -leftEndpoint hN ops := by
  have hp : (leftEndpoint hN ops * rightEndpoint hN ops) * leftEndpoint hN ops *
      (leftEndpoint hN ops * rightEndpoint hN ops) = leftEndpoint hN ops := by
    calc
      _ = leftEndpoint hN ops * rightEndpoint hN ops *
          (leftEndpoint hN ops * leftEndpoint hN ops) * rightEndpoint hN ops := by noncomm_ring
      _ = leftEndpoint hN ops := by
        rw [leftEndpoint_sq, mul_one, mul_assoc, ops.h_sq, mul_one]
  simp only [endpointMetric, smul_mul_assoc, mul_smul_comm, smul_smul,
    Complex.I_mul_I, neg_one_smul, hp]

theorem endpointMetric_conjugate_right :
    endpointMetric hN ops * rightEndpoint hN ops * endpointMetric hN ops =
      -rightEndpoint hN ops := by
  have hp : (leftEndpoint hN ops * rightEndpoint hN ops) * rightEndpoint hN ops *
      (leftEndpoint hN ops * rightEndpoint hN ops) = rightEndpoint hN ops := by
    calc
      _ = leftEndpoint hN ops * (rightEndpoint hN ops * rightEndpoint hN ops) *
          leftEndpoint hN ops * rightEndpoint hN ops := by noncomm_ring
      _ = rightEndpoint hN ops := by
        rw [ops.h_sq, mul_one, leftEndpoint_sq, one_mul]
  simp only [endpointMetric, smul_mul_assoc, mul_smul_comm, smul_smul,
    Complex.I_mul_I, neg_one_smul, hp]

theorem endpointKreinData_left_negative
    (hL : star (leftEndpoint hN ops) = leftEndpoint hN ops)
    (hR : star (rightEndpoint hN ops) = rightEndpoint hN ops) :
    (endpointKreinData hN ops hL hR).diracAdjoint (leftEndpoint hN ops) =
      -leftEndpoint hN ops := by
  change endpointMetric hN ops * star (leftEndpoint hN ops) * endpointMetric hN ops = _
  rw [hL, endpointMetric_conjugate_left]

theorem endpointKreinData_right_negative
    (hL : star (leftEndpoint hN ops) = leftEndpoint hN ops)
    (hR : star (rightEndpoint hN ops) = rightEndpoint hN ops) :
    (endpointKreinData hN ops hL hR).diracAdjoint (rightEndpoint hN ops) =
      -rightEndpoint hN ops := by
  change endpointMetric hN ops * star (rightEndpoint hN ops) * endpointMetric hN ops = _
  rw [hR, endpointMetric_conjugate_right]

end InfoGeometry.Canonical.KitaevBoundaryConstructedMetric
