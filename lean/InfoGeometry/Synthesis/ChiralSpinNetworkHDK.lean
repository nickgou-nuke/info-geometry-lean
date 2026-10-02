import InfoGeometry.CliffordWeyl.ChiralIdeals
import InfoGeometry.Synthesis.CuntzKleinPropagation
import InfoGeometry.Synthesis.KleinDiracKahler

noncomputable section

namespace InfoGeometry.Synthesis.ChiralSpinNetworkHDK

open InfoGeometry.OperatorAlgebra
open InfoGeometry.CliffordWeyl
open InfoGeometry.Synthesis.CuntzKleinPropagation

variable {Carrier : Type*} [Ring Carrier] [Algebra ℝ Carrier]

def residual (difference coefficient phase : Carrier) : Module.End ℝ Carrier :=
  LinearMap.mulLeft ℝ difference -
    (LinearMap.mulRight ℝ phase).comp (LinearMap.mulLeft ℝ coefficient)

@[simp] theorem residual_apply (difference coefficient phase state : Carrier) :
    residual difference coefficient phase state =
      difference * state - coefficient * state * phase := rfl

theorem mem_residual_kernel_iff (difference coefficient phase state : Carrier) :
    state ∈ LinearMap.ker (residual difference coefficient phase) ↔
      difference * state = coefficient * state * phase := by
  rw [LinearMap.mem_ker, residual_apply, sub_eq_zero]

def seamChirality (twist : Carrier ≃ₐ[ℝ] Carrier)
    (involutive : Function.Involutive twist) : ChiralInvolution (Module.End ℝ Carrier) where
  chi := twist.toLinearMap
  chi_sq := by
    ext state
    exact involutive state

theorem residual_commutes_twist (twist : Carrier ≃ₐ[ℝ] Carrier)
    (difference coefficient phase : Carrier)
    (difference_fixed : twist difference = difference)
    (coefficient_odd : twist coefficient = -coefficient)
    (phase_odd : twist phase = -phase) :
    Commute twist.toLinearMap (residual difference coefficient phase) := by
  change twist.toLinearMap * residual difference coefficient phase =
    residual difference coefficient phase * twist.toLinearMap
  ext state
  change twist (difference * state - coefficient * state * phase) =
    difference * twist state - coefficient * twist state * phase
  simp only [map_sub, map_mul, difference_fixed, coefficient_odd, phase_odd,
    neg_mul, mul_neg, neg_neg]

theorem mem_kernel_iff_chiral_parts
    (chirality : ChiralInvolution (Module.End ℝ Carrier))
    (operator : Module.End ℝ Carrier) (commutes : Commute chirality.chi operator)
    (state : Carrier) :
    state ∈ LinearMap.ker operator ↔
      chirality.Pleft state ∈ LinearMap.ker operator ∧
        chirality.Pright state ∈ LinearMap.ker operator := by
  constructor
  · intro member
    have killed : operator state = 0 := member
    constructor
    · change operator (chirality.Pleft state) = 0
      have exchange := congrArg (fun action : Module.End ℝ Carrier => action state)
        (commute_Pleft chirality operator commutes).eq.symm
      change operator (chirality.Pleft state) = chirality.Pleft (operator state) at exchange
      rw [exchange, killed, map_zero]
    · change operator (chirality.Pright state) = 0
      have exchange := congrArg (fun action : Module.End ℝ Carrier => action state)
        (commute_Pright chirality operator commutes).eq.symm
      change operator (chirality.Pright state) = chirality.Pright (operator state) at exchange
      rw [exchange, killed, map_zero]
  · rintro ⟨left_member, right_member⟩
    have decomposition : chirality.Pleft state + chirality.Pright state = state :=
      congrArg (fun action : Module.End ℝ Carrier => action state) chirality.Pleft_add_Pright
    rw [← decomposition]
    exact (LinearMap.ker operator).add_mem left_member right_member

theorem seam_solution_decomposition (twist : Carrier ≃ₐ[ℝ] Carrier)
    (involutive : Function.Involutive twist) (difference coefficient phase state : Carrier)
    (difference_fixed : twist difference = difference)
    (coefficient_odd : twist coefficient = -coefficient)
    (phase_odd : twist phase = -phase) :
    state ∈ LinearMap.ker (residual difference coefficient phase) ↔
      (seamChirality twist involutive).Pleft state ∈
          LinearMap.ker (residual difference coefficient phase) ∧
        (seamChirality twist involutive).Pright state ∈
          LinearMap.ker (residual difference coefficient phase) :=
  mem_kernel_iff_chiral_parts (seamChirality twist involutive) _
    (residual_commutes_twist twist difference coefficient phase
      difference_fixed coefficient_odd phase_odd) state

theorem first_order_kernel_le_second_order (difference coefficient phase : Carrier)
    (phase_square : phase * phase = -1)
    (anticommutes : difference * coefficient = -(coefficient * difference)) :
    LinearMap.ker (residual difference coefficient phase) ≤
      LinearMap.ker (LinearMap.mulLeft ℝ (difference * difference) -
        LinearMap.mulLeft ℝ (coefficient * coefficient)) := by
  intro state member
  change difference * difference * state - coefficient * coefficient * state = 0
  exact sub_eq_zero.mpr (square_equation_of_anticommute difference coefficient state phase
    phase_square anticommutes ((mem_residual_kernel_iff _ _ _ _).mp member))

end InfoGeometry.Synthesis.ChiralSpinNetworkHDK
