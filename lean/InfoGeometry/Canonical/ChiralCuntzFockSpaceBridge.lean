import InfoGeometry.Canonical.ChiralCuntzSuperchargeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.ChiralCuntzFockSpaceBridge

open ChiralCuntzSuperchargeBridge

variable {R : Type*} [Ring R] [StarRing R] (sys : Cuntz2System R)

/-- **Definition**: Right Lightcone Momentum P+ = Q+ Q- = S1 S1*. -/
def P_plus : R := Q_plus sys * Q_minus sys

/-- **Definition**: Left Lightcone Momentum P- = Q- Q+ = S2 S2*. -/
def P_minus : R := Q_minus sys * Q_plus sys

/-- **Definition**: Z2-Grading Involution Operator Γ = P+ - P- = S1 S1* - S2 S2*. -/
def grading : R := P_plus sys - P_minus sys

/-- **Theorem**: Q- is the star adjoint of Q+ (Q- = Q+*). -/
theorem Q_minus_eq_star_Q_plus :
    Q_minus sys = star (Q_plus sys) := by
  dsimp [Q_plus, Q_minus]
  simp

/-- **Theorem**: Right Lightcone Momentum equals Cuntz Projection e1 = S1 S1*. -/
theorem P_plus_eq_e1 :
    P_plus sys = _root_.CuntzAlgebra.S1 sys * star (_root_.CuntzAlgebra.S1 sys) := by
  dsimp [P_plus, Q_plus, Q_minus]
  calc
    (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys)) * (CuntzAlgebra.S2 sys * star (CuntzAlgebra.S1 sys)) =
        CuntzAlgebra.S1 sys * (star (CuntzAlgebra.S2 sys) * CuntzAlgebra.S2 sys) * star (CuntzAlgebra.S1 sys) := by
          simp [mul_assoc]
    _ = CuntzAlgebra.S1 sys * 1 * star (CuntzAlgebra.S1 sys) := by
      have h2 : star (CuntzAlgebra.S2 sys) * CuntzAlgebra.S2 sys = 1 := by
        simpa [CuntzAlgebra.S2] using sys.isometry 1 1
      rw [h2]
    _ = CuntzAlgebra.S1 sys * star (CuntzAlgebra.S1 sys) := by simp

/-- **Theorem**: Left Lightcone Momentum equals Cuntz Projection e2 = S2 S2*. -/
theorem P_minus_eq_e2 :
    P_minus sys = _root_.CuntzAlgebra.S2 sys * star (_root_.CuntzAlgebra.S2 sys) := by
  dsimp [P_minus, Q_plus, Q_minus]
  calc
    (CuntzAlgebra.S2 sys * star (CuntzAlgebra.S1 sys)) * (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys)) =
        CuntzAlgebra.S2 sys * (star (CuntzAlgebra.S1 sys) * CuntzAlgebra.S1 sys) * star (CuntzAlgebra.S2 sys) := by
          simp [mul_assoc]
    _ = CuntzAlgebra.S2 sys * 1 * star (CuntzAlgebra.S2 sys) := by
      have h1 : star (CuntzAlgebra.S1 sys) * CuntzAlgebra.S1 sys = 1 := by
        simpa [CuntzAlgebra.S1] using sys.isometry 0 0
      rw [h1]
    _ = CuntzAlgebra.S2 sys * star (CuntzAlgebra.S2 sys) := by simp

/-- **Theorem**: Right Chiral Projection Idempotency P+² = P+. -/
theorem chiral_projection_plus_sq :
    P_plus sys * P_plus sys = P_plus sys := by
  rw [P_plus_eq_e1]
  calc
    (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S1 sys)) * (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S1 sys)) =
        CuntzAlgebra.S1 sys * (star (CuntzAlgebra.S1 sys) * CuntzAlgebra.S1 sys) * star (CuntzAlgebra.S1 sys) := by
          simp [mul_assoc]
    _ = CuntzAlgebra.S1 sys * 1 * star (CuntzAlgebra.S1 sys) := by
      have h1 : star (CuntzAlgebra.S1 sys) * CuntzAlgebra.S1 sys = 1 := by
        simpa [CuntzAlgebra.S1] using sys.isometry 0 0
      rw [h1]
    _ = CuntzAlgebra.S1 sys * star (CuntzAlgebra.S1 sys) := by simp

/-- **Theorem**: Left Chiral Projection Idempotency P-² = P-. -/
theorem chiral_projection_minus_sq :
    P_minus sys * P_minus sys = P_minus sys := by
  rw [P_minus_eq_e2]
  calc
    (CuntzAlgebra.S2 sys * star (CuntzAlgebra.S2 sys)) * (CuntzAlgebra.S2 sys * star (CuntzAlgebra.S2 sys)) =
        CuntzAlgebra.S2 sys * (star (CuntzAlgebra.S2 sys) * CuntzAlgebra.S2 sys) * star (CuntzAlgebra.S2 sys) := by
          simp [mul_assoc]
    _ = CuntzAlgebra.S2 sys * 1 * star (CuntzAlgebra.S2 sys) := by
      have h2 : star (CuntzAlgebra.S2 sys) * CuntzAlgebra.S2 sys = 1 := by
        simpa [CuntzAlgebra.S2] using sys.isometry 1 1
      rw [h2]
    _ = CuntzAlgebra.S2 sys * star (CuntzAlgebra.S2 sys) := by simp

/-- **Theorem**: P+ is a Self-Adjoint Projection (P+* = P+ and P+² = P+). -/
theorem P_plus_isProjection :
    IsSelfAdjoint (P_plus sys) ∧ P_plus sys * P_plus sys = P_plus sys := by
  constructor
  · rw [IsSelfAdjoint, P_plus_eq_e1]
    simp
  · exact chiral_projection_plus_sq sys

/-- **Theorem**: P- is a Self-Adjoint Projection (P-* = P- and P-² = P-). -/
theorem P_minus_isProjection :
    IsSelfAdjoint (P_minus sys) ∧ P_minus sys * P_minus sys = P_minus sys := by
  constructor
  · rw [IsSelfAdjoint, P_minus_eq_e2]
    simp
  · exact chiral_projection_minus_sq sys

/-- **Theorem**: Lightcone Momentum Orthogonality (P+ P- = 0). -/
theorem P_plus_P_minus_ortho :
    P_plus sys * P_minus sys = 0 := by
  rw [P_plus_eq_e1, P_minus_eq_e2]
  calc
    (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S1 sys)) * (CuntzAlgebra.S2 sys * star (CuntzAlgebra.S2 sys)) =
        CuntzAlgebra.S1 sys * (star (CuntzAlgebra.S1 sys) * CuntzAlgebra.S2 sys) * star (CuntzAlgebra.S2 sys) := by
          simp [mul_assoc]
    _ = 0 := by
      have h : star (CuntzAlgebra.S1 sys) * CuntzAlgebra.S2 sys = 0 := by
        simpa [CuntzAlgebra.S1, CuntzAlgebra.S2] using sys.isometry 0 1
      rw [h, mul_zero, zero_mul]

/-- **Theorem**: Reversed Lightcone Momentum Orthogonality (P- P+ = 0). -/
theorem P_minus_P_plus_ortho :
    P_minus sys * P_plus sys = 0 := by
  rw [P_plus_eq_e1, P_minus_eq_e2]
  calc
    (CuntzAlgebra.S2 sys * star (CuntzAlgebra.S2 sys)) * (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S1 sys)) =
        CuntzAlgebra.S2 sys * (star (CuntzAlgebra.S2 sys) * CuntzAlgebra.S1 sys) * star (CuntzAlgebra.S1 sys) := by
          simp [mul_assoc]
    _ = 0 := by
      have h : star (CuntzAlgebra.S2 sys) * CuntzAlgebra.S1 sys = 0 := by
        simpa [CuntzAlgebra.S1, CuntzAlgebra.S2] using sys.isometry 1 0
      rw [h, mul_zero, zero_mul]

/-- **Theorem**: Q+ Source Projection (Q+* Q+ = P-) and Range Projection (Q+ Q+* = P+). -/
theorem Q_plus_source_range :
    star (Q_plus sys) * Q_plus sys = P_minus sys ∧
    Q_plus sys * star (Q_plus sys) = P_plus sys := by
  constructor
  · rw [← Q_minus_eq_star_Q_plus]
    exact rfl
  · rw [← Q_minus_eq_star_Q_plus]
    exact rfl

/-- **Theorem**: Total Lightcone Hamiltonian Identity H = P+ + P- = 1. -/
theorem total_lightcone_hamiltonian_eq_one :
    P_plus sys + P_minus sys = 1 := by
  rw [P_plus_eq_e1, P_minus_eq_e2]
  simpa [CuntzAlgebra.S1, CuntzAlgebra.S2] using sys.range_sum

/-- **Theorem**: Grading Operator Involution Identity Γ² = 1. -/
theorem grading_sq_eq_one :
    grading sys * grading sys = 1 := by
  dsimp [grading]
  have hp_plus := chiral_projection_plus_sq sys
  have hp_minus := chiral_projection_minus_sq sys
  have hp_ortho := P_plus_P_minus_ortho sys
  have hp_comp := total_lightcone_hamiltonian_eq_one sys
  calc
    (P_plus sys - P_minus sys) * (P_plus sys - P_minus sys)
      = P_plus sys * P_plus sys - P_plus sys * P_minus sys - P_minus sys * P_plus sys + P_minus sys * P_minus sys := by
          noncomm_ring
    _ = P_plus sys - 0 - 0 + P_minus sys := by
          have hp_ortho2 : P_minus sys * P_plus sys = 0 := P_minus_P_plus_ortho sys
          rw [hp_plus, hp_minus, hp_ortho, hp_ortho2]
    _ = P_plus sys + P_minus sys := by noncomm_ring
    _ = 1 := hp_comp

/-- **Theorem**: Grading Operator Anti-Commutes with Q+ ({Γ, Q+} = 0). -/
theorem grading_anticommutes_Q_plus :
    grading sys * Q_plus sys + Q_plus sys * grading sys = 0 := by
  dsimp [grading, Q_plus, Q_minus]
  rw [P_plus_eq_e1, P_minus_eq_e2]
  calc
    (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S1 sys) - CuntzAlgebra.S2 sys * star (CuntzAlgebra.S2 sys)) *
        (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys)) +
    (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys)) *
        (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S1 sys) - CuntzAlgebra.S2 sys * star (CuntzAlgebra.S2 sys))
      = (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S1 sys) * (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys)) -
         CuntzAlgebra.S2 sys * star (CuntzAlgebra.S2 sys) * (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys))) +
        ((CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys)) * (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S1 sys)) -
         (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys)) * (CuntzAlgebra.S2 sys * star (CuntzAlgebra.S2 sys))) := by noncomm_ring
    _ = (CuntzAlgebra.S1 sys * (star (CuntzAlgebra.S1 sys) * CuntzAlgebra.S1 sys) * star (CuntzAlgebra.S2 sys) - 0) +
        (0 - CuntzAlgebra.S1 sys * (star (CuntzAlgebra.S2 sys) * CuntzAlgebra.S2 sys) * star (CuntzAlgebra.S2 sys)) := by
          have h21 : star (CuntzAlgebra.S2 sys) * CuntzAlgebra.S1 sys = 0 := by
            simpa [CuntzAlgebra.S1, CuntzAlgebra.S2] using sys.isometry 1 0
          have term2 : CuntzAlgebra.S2 sys * star (CuntzAlgebra.S2 sys) * (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys)) = 0 := by
            calc CuntzAlgebra.S2 sys * star (CuntzAlgebra.S2 sys) * (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys))
              _ = CuntzAlgebra.S2 sys * (star (CuntzAlgebra.S2 sys) * CuntzAlgebra.S1 sys) * star (CuntzAlgebra.S2 sys) := by simp [mul_assoc]
              _ = 0 := by rw [h21, mul_zero, zero_mul]
          have term3 : (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys)) * (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S1 sys)) = 0 := by
            calc (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys)) * (CuntzAlgebra.S1 sys * star (CuntzAlgebra.S1 sys))
              _ = CuntzAlgebra.S1 sys * (star (CuntzAlgebra.S2 sys) * CuntzAlgebra.S1 sys) * star (CuntzAlgebra.S1 sys) := by simp [mul_assoc]
              _ = 0 := by rw [h21, mul_zero, zero_mul]
          rw [term2, term3]
          simp [mul_assoc]
    _ = CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys) - CuntzAlgebra.S1 sys * star (CuntzAlgebra.S2 sys) := by
          have h1 : star (CuntzAlgebra.S1 sys) * CuntzAlgebra.S1 sys = 1 := by
            simpa [CuntzAlgebra.S1] using sys.isometry 0 0
          have h2 : star (CuntzAlgebra.S2 sys) * CuntzAlgebra.S2 sys = 1 := by
            simpa [CuntzAlgebra.S2] using sys.isometry 1 1
          rw [h1, h2]
          simp
    _ = 0 := by noncomm_ring

/-- **Theorem**: Master Cuntz-SUSY Lightcone Dynamics, Grading & CAR1 Synthesis.
    Unifies:
    1. Q- = Q+*.
    2. Self-adjoint projection laws IsSelfAdjoint P+ and IsSelfAdjoint P-.
    3. Source and range projections: Q+* Q+ = P- and Q+ Q+* = P+.
    4. Two-sided orthogonality: P+ P- = 0 and P- P+ = 0.
    5. Total lightcone Hamiltonian H = P+ + P- = 1.
    6. Grading operator involution Γ² = 1.
    7. Grading operator anti-commutation with Q+ ({Γ, Q+} = 0). -/
theorem master_cuntz_susy_fock_space_synthesis :
    (Q_minus sys = star (Q_plus sys)) ∧
    (IsSelfAdjoint (P_plus sys) ∧ P_plus sys * P_plus sys = P_plus sys) ∧
    (IsSelfAdjoint (P_minus sys) ∧ P_minus sys * P_minus sys = P_minus sys) ∧
    (star (Q_plus sys) * Q_plus sys = P_minus sys ∧ Q_plus sys * star (Q_plus sys) = P_plus sys) ∧
    (P_plus sys * P_minus sys = 0 ∧ P_minus sys * P_plus sys = 0) ∧
    (P_plus sys + P_minus sys = 1) ∧
    (grading sys * grading sys = 1) ∧
    (grading sys * Q_plus sys + Q_plus sys * grading sys = 0) := ⟨
  Q_minus_eq_star_Q_plus sys,
  P_plus_isProjection sys,
  P_minus_isProjection sys,
  Q_plus_source_range sys,
  ⟨P_plus_P_minus_ortho sys, P_minus_P_plus_ortho sys⟩,
  total_lightcone_hamiltonian_eq_one sys,
  grading_sq_eq_one sys,
  grading_anticommutes_Q_plus sys
⟩

end InfoGeometry.Canonical.ChiralCuntzFockSpaceBridge
