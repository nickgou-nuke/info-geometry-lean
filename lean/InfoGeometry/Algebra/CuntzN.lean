import Mathlib
import InfoGeometry.Algebra.GenericDirac

/-!
# Cuntz-N Algebra — Finite Hodge-Dirac Operator

General Cuntz algebra O_N with N isometries S_1,…,S_N on a *-ring.
The Dirac operator is D = Σ_i (S_i + S*_i). Proved self-adjoint.

For O_∞ indexed by primes: D_β = Σ_p p^{-β}(S_p + S*_p), Boltzmann regularized.

Uses the same abstract star-ring approach as `CuntzCantorSpectralTriple.lean`.
-/

namespace InfoGeometry.Algebra.Cuntz

variable {N : ℕ}

/--
**Cuntz algebra O_N** on a star ring.

  S*_i·S_j = δ_{ij}·1    (isometries with orthogonal ranges)
  Σ_i S_i·S*_i = 1         (completeness / range sum)
-/
structure CuntzNAlgebra (Op : Type*) [Ring Op] [StarRing Op] where
  S : Fin N → Op
  isometry : ∀ i j, star (S i) * (S j) = if i = j then 1 else 0
  range_sum : ∑ i : Fin N, (S i) * star (S i) = 1

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (O : CuntzNAlgebra (N := N) Op)

/--
**Discrete Hodge-Dirac operator for O_N**.

  D = Σ_{i=1}^N (S_i + S*_i)
-/
def hodgeDirac : Op :=
  finiteDirac O.S

/--
**Self-adjointness of the Hodge-Dirac operator (PROVED).**

  D* = Σ (S_i + S*_i)* = Σ (S*_i + S_i) = Σ (S_i + S*_i) = D.
-/
theorem hodge_dirac_self_adjoint : star (hodgeDirac O) = hodgeDirac O := by
  exact (finiteDirac_selfAdjoint O.S).star_eq

/--
**Idempotence of range projections (PROVED).**

  P_i = S_i·S*_i,  P_i² = P_i.
-/
theorem range_projection_idempotent (i : Fin N) :
    (O.S i * star (O.S i)) * (O.S i * star (O.S i)) = O.S i * star (O.S i) := by
  have h_isom : star (O.S i) * (O.S i) = 1 := by
    simpa using O.isometry i i
  calc
    (O.S i * star (O.S i)) * (O.S i * star (O.S i))
        = O.S i * (star (O.S i) * (O.S i)) * star (O.S i) := by noncomm_ring
    _ = O.S i * 1 * star (O.S i) := by rw [h_isom]
    _ = O.S i * star (O.S i) := by simp

/--
**Orthogonality of range projections for i ≠ j (PROVED).**

  P_i·P_j = 0.
-/
theorem range_projection_orthogonal (i j : Fin N) (hij : i ≠ j) :
    (O.S i * star (O.S i)) * (O.S j * star (O.S j)) = 0 := by
  have h_orth : star (O.S i) * (O.S j) = 0 := by
    simpa [hij] using O.isometry i j
  calc
    (O.S i * star (O.S i)) * (O.S j * star (O.S j))
        = O.S i * (star (O.S i) * (O.S j)) * star (O.S j) := by noncomm_ring
    _ = O.S i * 0 * star (O.S j) := by rw [h_orth]
    _ = 0 := by simp

/--
**Completeness: Σ_i P_i = 1 (PROVED).**
-/
theorem range_projections_sum_one :
    ∑ i : Fin N, (O.S i) * star (O.S i) = 1 :=
  O.range_sum

end InfoGeometry.Algebra.Cuntz
