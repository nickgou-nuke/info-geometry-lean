import InfoGeometry.Quantum.EllipticYangBaxter

namespace InfoGeometry.Canonical.EllipticYangBaxterCapstone

open InfoGeometry.Quantum.EllipticYangBaxter

theorem capstone_elliptic_yang_baxter_synthesis (γ₁ γ₂ γ₃ γ_i γ_j Ω u v : ℝ) :
    (let Ω₁₂ := casimirInvariant γ₁ γ₂
     let Ω₁₃ := casimirInvariant γ₁ γ₃
     let Ω₂₃ := casimirInvariant γ₂ γ₃
     let R₁₂_u := ellipticRMatrix Ω₁₂ u
     let R₁₃_uv := ellipticRMatrix Ω₁₃ (u + v)
     let R₂₃_v := ellipticRMatrix Ω₂₃ v
     R₁₂_u * R₁₃_uv * R₂₃_v = R₂₃_v * R₁₃_uv * R₁₂_u) ∧
    (‖ellipticRMatrix Ω u‖ = 1) ∧
    (ellipticRMatrix (γ_i * γ_j) 0 = 1) ∧
    (ellipticRMatrix Ω u * ellipticRMatrix Ω (-u) = 1) := by
  exact ⟨elliptic_yang_baxter_identity γ₁ γ₂ γ₃ u v,
    elliptic_R_matrix_unitary Ω u,
    elliptic_R_matrix_at_zero γ_i γ_j,
    elliptic_R_matrix_inversion Ω u⟩

end InfoGeometry.Canonical.EllipticYangBaxterCapstone
