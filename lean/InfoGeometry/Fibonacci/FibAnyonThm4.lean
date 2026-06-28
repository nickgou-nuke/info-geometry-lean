import InfoGeometry.Canonical.YangBaxterProof

noncomputable section

/-!
# Fibonacci Yang-Baxter Bridge

The matrix-level Yang-Baxter proof is owned by
`InfoGeometry.Canonical.YangBaxterProof`.  This Fibonacci archive module keeps
the old theorem surface as a bridge and avoids maintaining a divergent scalar
proof with a different root-of-unity convention.
-/

namespace InfoGeometry.Fibonacci.FibAnyonThm4

open InfoGeometry.Canonical.YangBaxterProof

/-- The Fibonacci scalar constraints used by the finite matrix owner. -/
theorem fibonacci_scalar_packet :
    q ^ 5 = -1 ∧ τ ^ 2 + τ = 1 ∧ s ^ 2 = τ :=
  ⟨q_pow_five, tau_sq_add_tau, s_sq_eq_tau⟩

/-- The finite Fibonacci recoupling matrix is involutive. -/
theorem fusion_matrix_involutive :
    F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  F_sq

/-- Conjugating the middle braid by the fusion matrix recovers the diagonal braid. -/
theorem middle_braid_conjugation :
    F * B * F = R :=
  F_B_F_eq_R

/-- Concrete finite Fibonacci Artin/Yang-Baxter matrix relation. -/
theorem braid_relation : R * B * R = B * R * B :=
  InfoGeometry.Canonical.YangBaxterProof.braid_relation

/-- The archived theorem surface is backed by the owner scalar, fusion, and braid facts. -/
theorem theorem4_packet :
    (q ^ 5 = -1 ∧ τ ^ 2 + τ = 1 ∧ s ^ 2 = τ) ∧
      F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
        F * B * F = R ∧
          R * B * R = B * R * B :=
  ⟨fibonacci_scalar_packet, fusion_matrix_involutive, middle_braid_conjugation, braid_relation⟩

end InfoGeometry.Fibonacci.FibAnyonThm4
