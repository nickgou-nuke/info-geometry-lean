import Mathlib.Tactic
open Matrix Complex

noncomputable section

/-!
# Chiral Anomaly Vanishes at the Flat Boundary

The chiral anomaly `Tr(tilt · proj)` vanishes when the K-theory projection
commutes with the Dirac operator `D` and `D` is invertible.

**Zero global axioms.** The tilt, D, anticommutation, and tilt_sq are all
local hypotheses parameterized into the theorem.
-/

abbrev KTheoryProjection (n : ℕ) :=
  { e : Matrix (Fin n) (Fin n) ℂ // IsIdempotentElem e }

namespace KTheoryProjection

def e {n : ℕ} (proj : KTheoryProjection n) : Matrix (Fin n) (Fin n) ℂ := proj.1

theorem is_idempotent {n : ℕ} (proj : KTheoryProjection n) :
    e proj * e proj = e proj := by
  simpa only [e, IsIdempotentElem] using proj.2

end KTheoryProjection

/-- Cyclic 0-cocycle: `τ_tilt(A) = Tr(tilt · A)`. -/
noncomputable def cyclic_0_cocycle
    (tilt : Matrix (Fin 2) (Fin 2) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (tilt * A)

/-- Index pairing: `⟨[proj], τ_tilt⟩`. -/
noncomputable def index_pairing
    (tilt : Matrix (Fin 2) (Fin 2) ℂ) (proj : KTheoryProjection 2) : ℂ :=
  cyclic_0_cocycle tilt proj.e

lemma trace_rot (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    (A * B * C).trace = (B * C * A).trace := by
  calc
    (A * B * C).trace = ((A * B) * C).trace := by simp [mul_assoc]
    _ = (C * (A * B)).trace := Matrix.trace_mul_comm (A * B) C
    _ = (C * A * B).trace := by simp [mul_assoc]
    _ = (B * (C * A)).trace := (Matrix.trace_mul_comm B (C * A)).symm
    _ = (B * C * A).trace := by simp [mul_assoc]

/--
**Theorem**: The chiral anomaly vanishes when the projection commutes with
the Dirac operator and D is invertible.

Hypotheses:
  - `tilt` : the chirality/parity operator (tilt² = 1)
  - `D`     : the Dirac operator
  - `h_anticomm` : `D * tilt + tilt * D = 0` (chiral anticommutation)
  - `h_comm` : `D * proj.e = proj.e * D` (the projection is D-invariant)
  - `h_Dinv` : D is invertible

The proof uses the cyclic property of the trace and the anticommutation
to show `τ(proj) = -τ(proj)`, hence `τ(proj) = 0`.
-/
theorem chiral_anomaly_vanishes_at_flat_boundary
    (tilt D : Matrix (Fin 2) (Fin 2) ℂ)
    (h_anticomm : D * tilt + tilt * D = 0)
    (proj : KTheoryProjection 2)
    (h_comm : D * proj.e = proj.e * D)
    (h_Dinv : ∃ D_inv, D * D_inv = 1 ∧ D_inv * D = 1) :
    index_pairing tilt proj = 0 := by
  rcases h_Dinv with ⟨D_inv, hD_Dinv, hDinv_D⟩
  unfold index_pairing cyclic_0_cocycle
  have h_D_tilt : D * tilt = -(tilt * D) := by
    calc
      D * tilt = (D * tilt + tilt * D) - (tilt * D) := by simp
      _ = 0 - (tilt * D) := by rw [h_anticomm]
      _ = -(tilt * D) := by simp
  have h_tilt_D : tilt * D = -(D * tilt) := by
    calc
      tilt * D = (tilt * D + D * tilt) - (D * tilt) := by simp
      _ = (D * tilt + tilt * D) - (D * tilt) := by abel
      _ = 0 - (D * tilt) := by rw [h_anticomm]
      _ = -(D * tilt) := by simp
  have h_comm_tilt_e_D : tilt * proj.e * D = -(D * tilt * proj.e) := by
    calc
      tilt * proj.e * D = tilt * (proj.e * D) := by simp [mul_assoc]
      _ = tilt * (D * proj.e) := by rw [h_comm]
      _ = (tilt * D) * proj.e := by simp [mul_assoc]
      _ = (-(D * tilt)) * proj.e := by rw [h_tilt_D]
      _ = -(D * tilt * proj.e) := by simp [mul_assoc]
  have hτ_neg : Matrix.trace (tilt * proj.e) = -Matrix.trace (tilt * proj.e) := by
    calc
      Matrix.trace (tilt * proj.e) = Matrix.trace ((tilt * proj.e) * (D * D_inv)) := by
        simp [hD_Dinv]
      _ = Matrix.trace ((tilt * proj.e * D) * D_inv) := by simp [mul_assoc]
      _ = Matrix.trace ((-(D * tilt * proj.e)) * D_inv) := by rw [h_comm_tilt_e_D]
      _ = -Matrix.trace (D * tilt * proj.e * D_inv) := by simp
      _ = -Matrix.trace ((D * (tilt * proj.e)) * D_inv) := by simp [mul_assoc]
      _ = -Matrix.trace ((tilt * proj.e) * D_inv * D) := by
        rw [trace_rot D (tilt * proj.e) D_inv]
      _ = -Matrix.trace (tilt * proj.e * (D_inv * D)) := by simp [mul_assoc]
      _ = -Matrix.trace (tilt * proj.e * 1) := by rw [hDinv_D]
      _ = -Matrix.trace (tilt * proj.e) := by simp
  have h_sum : Matrix.trace (tilt * proj.e) + Matrix.trace (tilt * proj.e) = 0 := by
    calc
      Matrix.trace (tilt * proj.e) + Matrix.trace (tilt * proj.e) =
        Matrix.trace (tilt * proj.e) + (-Matrix.trace (tilt * proj.e)) := by
          nth_rw 2 [hτ_neg]
      _ = 0 := by simp
  have h2 : (2 : ℂ) * Matrix.trace (tilt * proj.e) = 0 := by
    calc
      (2 : ℂ) * Matrix.trace (tilt * proj.e) =
          Matrix.trace (tilt * proj.e) + Matrix.trace (tilt * proj.e) := by ring
      _ = 0 := by rw [h_sum]
  rcases mul_eq_zero.mp h2 with (h2z | hz)
  · exact absurd h2z (by norm_num : (2 : ℂ) ≠ 0)
  · exact hz
