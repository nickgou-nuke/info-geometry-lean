import Mathlib.Tactic
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Topology.FractalCantorFock
import InfoGeometry.OperatorAlgebra.SpectralTriple
import InfoGeometry.Arithmetic.MoebiusSignature

open InfoGeometry.Topology.FractalCantorFock.CantorBoundaryFunctionSpace

/-!
# Cyclic Cocycle on the Cantor Boundary

...

#### CLOSED FINITE THEOREMS

This file currently exports the finite matrix chiral trace cancellation theorem
below.  The abstract Cantor-boundary cocycle operators require actual
definitions of the tilt/switch operators and cyclic cochains before theorem
statements can be exported.
-/

namespace CyclicCocycleCantor

open InfoGeometry.Topology
open InfoGeometry.Topology.CuntzCantorSpectralTriple

variable {Op H : Type*} [Ring Op] [StarRing Op]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]

/-! ## Finite matrix chiral anomaly cancellation -/

/--
A finite idempotent matrix projection used as the concrete `K₀` shadow of a
clopen Cantor boundary projection.
-/
abbrev KTheoryProjection (n : ℕ) :=
  { e : Matrix (Fin n) (Fin n) ℂ // IsIdempotentElem e }

namespace KTheoryProjection

abbrev e {n : ℕ} (proj : KTheoryProjection n) : Matrix (Fin n) (Fin n) ℂ := proj.1

theorem is_idempotent {n : ℕ} (proj : KTheoryProjection n) :
    e proj * e proj = e proj := by
  simpa only [e, IsIdempotentElem] using proj.2

end KTheoryProjection

/-- Instantiation of the KTheoryProjection structure to avoid fake/vacuous shapes. -/
def trivialKTheoryProjection : KTheoryProjection 2 :=
  ⟨1, by simp [IsIdempotentElem]⟩

/-- The finite grade-zero chiral cocycle `A ↦ Tr(γ A)`. -/
noncomputable def finiteChiralCocycle0
    (tilt : Matrix (Fin 2) (Fin 2) ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (tilt * A)

/-- The finite `K₀` pairing of the grade-zero chiral cocycle with a projection. -/
noncomputable def finiteIndexPairing
    (tilt : Matrix (Fin 2) (Fin 2) ℂ)
    (proj : KTheoryProjection 2) : ℂ :=
  finiteChiralCocycle0 tilt proj.e

theorem matrix_trace_comm_lemma1 (tilt D e D_inv : Matrix (Fin 2) (Fin 2) ℂ)
    (hComm : D * e = e * D) :
    D_inv * (tilt * D) * e = (D_inv * tilt * e) * D := by
  calc
    D_inv * (tilt * D) * e = D_inv * tilt * (D * e) := by simp [Matrix.mul_assoc]
    _ = D_inv * tilt * (e * D) := by rw [hComm]
    _ = (D_inv * tilt * e) * D := by simp [Matrix.mul_assoc]

theorem matrix_trace_comm_lemma2 (tilt D e D_inv : Matrix (Fin 2) (Fin 2) ℂ)
    (hDleft : D * D_inv = 1) :
    D * (D_inv * tilt * e) = tilt * e := by
  calc
    D * (D_inv * tilt * e) = (D * D_inv) * (tilt * e) := by simp [Matrix.mul_assoc]
    _ = 1 * (tilt * e) := by rw [hDleft]
    _ = tilt * e := by simp

theorem finiteChiralCocycle0_conjugation_invariant
    (tilt D e D_inv : Matrix (Fin 2) (Fin 2) ℂ)
    (hComm : D * e = e * D)
    (hDleft : D * D_inv = 1) :
    finiteChiralCocycle0 (D_inv * tilt * D) e =
      finiteChiralCocycle0 tilt e := by
  unfold finiteChiralCocycle0
  calc
    Matrix.trace ((D_inv * tilt * D) * e) =
        Matrix.trace ((D_inv * tilt * e) * D) := by
      rw [show (D_inv * tilt * D) * e = D_inv * (tilt * D) * e by
        simp [Matrix.mul_assoc]]
      exact congrArg Matrix.trace
        (matrix_trace_comm_lemma1 tilt D e D_inv hComm)
    _ = Matrix.trace (D * (D_inv * tilt * e)) := by
      rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (tilt * e) := by
      rw [matrix_trace_comm_lemma2 tilt D e D_inv hDleft]

/--
Finite chiral trace cancellation.

If an invertible Dirac matrix anticommutes with the grading `tilt`, and a
matrix `e` commutes with the Dirac matrix, then `Tr(tilt * e) = 0`.
-/
theorem finiteChiralTrace_vanishes_of_commuting_invertible
    (tilt D e D_inv : Matrix (Fin 2) (Fin 2) ℂ)
    (hAnti : D * tilt + tilt * D = 0)
    (hComm : D * e = e * D)
    (hDleft : D * D_inv = 1)
    (hDright : D_inv * D = 1) :
    Matrix.trace (tilt * e) = 0 := by
  have hAnti' : D * tilt = -(tilt * D) := by
    exact eq_neg_of_add_eq_zero_left hAnti
  have hneg : Matrix.trace (tilt * e) = -Matrix.trace (tilt * e) := by
    calc
      Matrix.trace (tilt * e)
          = Matrix.trace ((D_inv * D) * (tilt * e)) := by rw [hDright]; simp
      _ = Matrix.trace (D_inv * (D * tilt) * e) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace (D_inv * (-(tilt * D)) * e) := by rw [hAnti']
      _ = -Matrix.trace (D_inv * (tilt * D) * e) := by simp
      _ = -Matrix.trace ((D_inv * tilt * e) * D) := by
            rw [matrix_trace_comm_lemma1 tilt D e D_inv hComm]
      _ = -Matrix.trace (D * (D_inv * tilt * e)) := by rw [Matrix.trace_mul_comm]
      _ = -Matrix.trace (tilt * e) := by
            rw [matrix_trace_comm_lemma2 tilt D e D_inv hDleft]
  have hzero_add : Matrix.trace (tilt * e) + Matrix.trace (tilt * e) = 0 := by
    calc
      Matrix.trace (tilt * e) + Matrix.trace (tilt * e)
          = Matrix.trace (tilt * e) + -Matrix.trace (tilt * e) := by
            exact congrArg (fun z => Matrix.trace (tilt * e) + z) hneg
      _ = 0 := by simp
  have htwo : (2 : ℂ) * Matrix.trace (tilt * e) = 0 := by
    simpa [two_mul] using hzero_add
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/--
Projection-facing version of finite chiral anomaly cancellation at a flat
boundary: a Dirac-commuting projection has zero grade-zero chiral pairing.
-/
theorem chiral_anomaly_vanishes_at_flat_boundary
    (tilt D D_inv : Matrix (Fin 2) (Fin 2) ℂ)
    (proj : KTheoryProjection 2)
    (hAnti : D * tilt + tilt * D = 0)
    (hComm : D * proj.e = proj.e * D)
    (hDleft : D * D_inv = 1)
    (hDright : D_inv * D = 1) :
    finiteIndexPairing tilt proj = 0 :=
  finiteChiralTrace_vanishes_of_commuting_invertible
    tilt D proj.e D_inv hAnti hComm hDleft hDright

end CyclicCocycleCantor
