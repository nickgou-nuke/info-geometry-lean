import Mathlib

/-!
# Souriau Dirac-Hodge Coupling & Anomaly Elimination

Proved theorem:
  `twisted_index_vanishing` — trace-cyclicity + J²=1 + J·K·J = -K ⇒ φ(K·P) = 0

All hypotheses are explicit: J²=1, J*=J, K*=-K, J·K·J=-K, and φ cyclic/additive.
-/

namespace SouriauAnomalyCancellation

variable (Op : Type*) [Ring Op] [StarRing Op]

structure ModularConjugation where
  J : Op
  J_sq : J * J = 1
  J_star : star J = J

structure PhaseAxis where
  K : Op
  K_skew : star K = -K

/--
**Theorem: Twisted Sector Index Vanishes.**

Hypotheses:
  φ: Op → ℝ — linear functional (additive and ℝ-homogeneous)
  φ(A*B) = φ(B*A) — cyclicity of trace
  φ(A*B) = φ(B*A) and J²=1 imply φ(J·A·J) = φ(A)
  J·K·J = -K — CP-anticommutation
  J·P = P·J — projector commutes with modular conjugation

Conclusion: φ(K·P) = 0.

Proof: compute φ(K·P) = φ(J·(K·P)·J) = φ((-K)·P) = -φ(K·P) ⇒ φ = 0.
-/
theorem twisted_index_vanishing
    (J : ModularConjugation Op) (K : PhaseAxis Op)
    (P : Op) (hP_J_comm : J.J * P = P * J.J)
    (φ : Op → ℝ)
    (h_φ_add : ∀ A B, φ (A + B) = φ A + φ B)
    (h_φ_mul_cyclic : ∀ A B, φ (A * B) = φ (B * A))
    (h_J_K : J.J * K.K * J.J = -K.K) :
    φ (K.K * P) = 0 := by
  have hJsq : J.J * J.J = 1 := J.J_sq
  have h_φ_J_invariant : ∀ A, φ (J.J * A * J.J) = φ A := by
    intro A
    calc
      φ (J.J * A * J.J) = φ ((J.J * A) * J.J) := by rfl
      _ = φ (J.J * (J.J * A)) := h_φ_mul_cyclic (J.J * A) J.J
      _ = φ ((J.J * J.J) * A) := by rw [mul_assoc]
      _ = φ (1 * A) := by rw [hJsq]
      _ = φ A := by simp
  -- J·(K·P)·J = (J·K·J)·(J·P·J) = -K·P.
  have h_conj : J.J * (K.K * P) * J.J = -(K.K * P) := by
    calc
      J.J * (K.K * P) * J.J
          = J.J * K.K * ((J.J * J.J) * P) * J.J := by
            rw [hJsq]
            noncomm_ring
      _ = (J.J * K.K * J.J) * (J.J * P * J.J) := by noncomm_ring
      _ = (-K.K) * (J.J * P * J.J) := by rw [h_J_K]
      _ = (-K.K) * (P * J.J * J.J) := by rw [hP_J_comm]
      _ = (-K.K) * (P * (J.J * J.J)) := by noncomm_ring
      _ = (-K.K) * (P * 1) := by rw [hJsq]
      _ = -(K.K * P) := by noncomm_ring
  -- φ(K·P) = φ(J·(K·P)·J) = φ(-(K·P)) = -φ(K·P)
  have h_φ_additive : ∀ A, φ (-A) = -φ A := by
    intro A
    have hzero : φ (0 : Op) = 0 := by
      have h : φ (0 : Op) = φ (0 : Op) + φ (0 : Op) := by
        simpa using h_φ_add 0 0
      linarith
    have hsum : φ (A + (-A)) = φ A + φ (-A) := h_φ_add A (-A)
    have hsum0 : φ A + φ (-A) = 0 := by
      simpa [hzero] using hsum.symm
    linarith
  have h_φ_eq : φ (K.K * P) = -φ (K.K * P) := by
    calc
      φ (K.K * P) = φ (J.J * (K.K * P) * J.J) := by rw [h_φ_J_invariant]
      _ = φ (-(K.K * P)) := by rw [h_conj]
      _ = -φ (K.K * P) := by rw [h_φ_additive]
  linarith

end SouriauAnomalyCancellation
