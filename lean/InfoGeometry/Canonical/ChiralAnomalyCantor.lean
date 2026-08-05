import Mathlib.Tactic
open Matrix Complex

noncomputable section

/-!
# Finite graded-trace cancellation

This owner proves a finite-dimensional algebraic cancellation statement.  It
does not construct a cyclic cocycle, a K-theory pairing, or a geometric
flat-boundary theorem.
-/

abbrev KTheoryProjection (n : ℕ) :=
  { e : Matrix (Fin n) (Fin n) ℂ // IsIdempotentElem e }

namespace KTheoryProjection

abbrev e {n : ℕ} (proj : KTheoryProjection n) : Matrix (Fin n) (Fin n) ℂ := proj.1

theorem is_idempotent {n : ℕ} (proj : KTheoryProjection n) :
    e proj * e proj = e proj := by
  simpa only [e, IsIdempotentElem] using proj.2

end KTheoryProjection

/-- The tilted trace functional `A ↦ Tr(tilt · A)`. -/
noncomputable def tiltedTraceFunctional
    (tilt : Matrix (Fin 2) (Fin 2) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (tilt * A)

/- Compatibility alias retained for existing downstream code. -/
noncomputable def cyclic_0_cocycle
    (tilt : Matrix (Fin 2) (Fin 2) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  tiltedTraceFunctional tilt A

/-- The tilted trace evaluated on an algebraic idempotent. -/
noncomputable def tiltedTraceOnIdempotent
    (tilt : Matrix (Fin 2) (Fin 2) ℂ) (proj : KTheoryProjection 2) : ℂ :=
  tiltedTraceFunctional tilt proj.e

/- Compatibility alias retained for existing downstream code. -/
noncomputable def index_pairing
    (tilt : Matrix (Fin 2) (Fin 2) ℂ) (proj : KTheoryProjection 2) : ℂ :=
  tiltedTraceOnIdempotent tilt proj

lemma trace_rot (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    (A * B * C).trace = (B * C * A).trace := by
  calc
    (A * B * C).trace = ((A * B) * C).trace := by simp [mul_assoc]
    _ = (C * (A * B)).trace := Matrix.trace_mul_comm (A * B) C
    _ = (C * A * B).trace := by simp [mul_assoc]
    _ = (B * (C * A)).trace := (Matrix.trace_mul_comm B (C * A)).symm
    _ = (B * C * A).trace := by simp [mul_assoc]

lemma trace_rot_fin {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ) :
    (A * B * C).trace = (B * C * A).trace := by
  calc
    (A * B * C).trace = ((A * B) * C).trace := by simp [mul_assoc]
    _ = (C * (A * B)).trace := Matrix.trace_mul_comm (A * B) C
    _ = (C * A * B).trace := by simp [mul_assoc]
    _ = (B * (C * A)).trace := (Matrix.trace_mul_comm B (C * A)).symm
    _ = (B * C * A).trace := by simp [mul_assoc]

theorem graded_trace_vanishes_of_invertible_anticommuting
    {n : ℕ}
    (tilt D A D_inv : Matrix (Fin n) (Fin n) ℂ)
    (h_anticomm : D * tilt + tilt * D = 0)
    (h_comm : D * A = A * D)
    (h_Dleft : D * D_inv = 1)
    (h_Dright : D_inv * D = 1) :
    Matrix.trace (tilt * A) = 0 := by
  have h_D_tilt : D * tilt = -(tilt * D) := by
    exact eq_neg_of_add_eq_zero_left h_anticomm
  have h_neg : Matrix.trace (tilt * A) = -Matrix.trace (tilt * A) := by
    calc
      Matrix.trace (tilt * A) =
          Matrix.trace ((D_inv * D) * (tilt * A)) := by rw [h_Dright]; simp
      _ = Matrix.trace (D_inv * (D * tilt) * A) := by simp [mul_assoc]
      _ = Matrix.trace (D_inv * (-(tilt * D)) * A) := by rw [h_D_tilt]
      _ = -Matrix.trace (D_inv * (tilt * D) * A) := by simp
      _ = -Matrix.trace ((D_inv * tilt * A) * D) := by
        congr 1
        simp [mul_assoc, h_comm]
      _ = -Matrix.trace (D * (D_inv * tilt * A)) := by
        rw [Matrix.trace_mul_comm]
      _ = -Matrix.trace (tilt * A) := by
        rw [show D * (D_inv * tilt * A) = tilt * A by
          calc
            D * (D_inv * tilt * A) = ((D * D_inv) * tilt) * A := by
              simp [mul_assoc]
            _ = tilt * A := by rw [h_Dleft]; simp]
  have h_two : (2 : ℂ) * Matrix.trace (tilt * A) = 0 := by
    have h_sum : Matrix.trace (tilt * A) + Matrix.trace (tilt * A) = 0 := by
      calc
        Matrix.trace (tilt * A) + Matrix.trace (tilt * A) =
            Matrix.trace (tilt * A) + -Matrix.trace (tilt * A) := by
              exact congrArg (fun z => Matrix.trace (tilt * A) + z) h_neg
        _ = 0 := add_neg_cancel _
    calc
      (2 : ℂ) * Matrix.trace (tilt * A) =
          Matrix.trace (tilt * A) + Matrix.trace (tilt * A) := by ring
      _ = 0 := h_sum
  exact (mul_eq_zero.mp h_two).resolve_left (by norm_num)

theorem tilted_trace_vanishes_on_dirac_commutant
    {n : ℕ}
    (tilt D D_inv : Matrix (Fin n) (Fin n) ℂ)
    (proj : KTheoryProjection n)
    (h_anticomm : D * tilt + tilt * D = 0)
    (h_comm : D * proj.e = proj.e * D)
    (h_Dleft : D * D_inv = 1)
    (h_Dright : D_inv * D = 1) :
    Matrix.trace (tilt * proj.e) = 0 :=
  graded_trace_vanishes_of_invertible_anticommuting
    tilt D proj.e D_inv h_anticomm h_comm h_Dleft h_Dright

/-- Compatibility wrapper for the historical theorem name.  The proof uses
only the finite graded-trace cancellation above; no flat-boundary or
K-theory claim is made here. -/
theorem chiral_anomaly_vanishes_at_flat_boundary
    (tilt D : Matrix (Fin 2) (Fin 2) ℂ)
    (h_anticomm : D * tilt + tilt * D = 0)
    (proj : KTheoryProjection 2)
    (h_comm : D * proj.e = proj.e * D)
    (h_Dinv : ∃ D_inv, D * D_inv = 1 ∧ D_inv * D = 1) :
    index_pairing tilt proj = 0 := by
  rcases h_Dinv with ⟨D_inv, hD_Dinv, hDinv_D⟩
  change Matrix.trace (tilt * proj.e) = 0
  exact tilted_trace_vanishes_on_dirac_commutant
    tilt D D_inv proj h_anticomm h_comm hD_Dinv hDinv_D
