theorem self_consistency_loop (m : ℝ) (Q : Spinor)
    (gamma_action : idx → Spinor → Spinor)
    (h_vacuum : quaternion_field_equation nabla e_inv m Q gamma_action) :
    (∑ a : idx, ∑ mu : SpaceTime, (e_inv mu a : ℂ) • gamma_action a (nabla mu Q)) - (m : ℂ) • Q = 0 := by
  dsimp [quaternion_field_equation] at h_vacuum
  exact sub_eq_zero.mpr h_vacuum