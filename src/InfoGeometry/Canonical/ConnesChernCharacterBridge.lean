import InfoGeometry.Canonical.ConnesKMSIndexPairing
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace ConnesChern

open InfoGeometry.Canonical.ConnesKMSIndexPairing

variable {n : Type*} [Fintype n] [DecidableEq n]

section NoncommRing
variable {R : Type*} [Ring R]

/-- A matrix idempotent representing a finite projective module over any ring `[Ring R]`. -/
abbrev IdempotentProjection :=
  {e : Matrix n n R // IsIdempotentElem e}

namespace IdempotentProjection

variable (proj : IdempotentProjection (n := n) (R := R))

def e : Matrix n n R := proj.1

theorem idem : e proj * e proj = e proj := by
  simpa only [e, IsIdempotentElem] using proj.2

theorem idempotent_cube : e proj * e proj * e proj = e proj := by
  rw [idem proj, idem proj]

theorem idempotent_trace_sq : Matrix.trace (e proj * e proj) = Matrix.trace (e proj) := by
  rw [idem proj]

end IdempotentProjection

/-- Over any non-commutative ring `R`, the Chern pairing difference under `[D, Z]` homotopy
equals the trace commutator defect `Tr((γ D) Z - Z (γ D))`. -/
theorem chern_pairing_homotopy_noncomm
    (ST : ConnesGradedSpectralTriple n R)
    (X Y Z : Matrix n n R)
    (h_comm : (ST.gamma : Matrix n n R) * Z = Z * ST.gamma)
    (h_homotopy : X - Y = ST.D * Z - Z * ST.D) :
    connesIndexPairing ST X - connesIndexPairing ST Y =
      Matrix.trace (((ST.gamma : Matrix n n R) * ST.D) * Z -
        Z * ((ST.gamma : Matrix n n R) * ST.D)) := by
  have hdiff : connesIndexPairing ST X - connesIndexPairing ST Y =
      connesIndexPairing ST (X - Y) := by
    unfold connesIndexPairing
    rw [Matrix.mul_sub, Matrix.trace_sub]
  rw [hdiff, h_homotopy]
  exact connes_pairing_commutator_noncomm ST Z h_comm

end NoncommRing

variable {R : Type*} [CommRing R]

theorem chern_pairing_homotopy_invariance
    (ST : ConnesGradedSpectralTriple n R)
    (X Y Z : Matrix n n R)
    (h_comm : (ST.gamma : Matrix n n R) * Z = Z * ST.gamma)
    (h_homotopy : X - Y = ST.D * Z - Z * ST.D) :
    connesIndexPairing ST X = connesIndexPairing ST Y := by
  have hzero : connesIndexPairing ST (X - Y) = 0 := by
    rw [h_homotopy]
    exact connes_pairing_commutator_zero ST Z h_comm
  unfold connesIndexPairing at hzero ⊢
  rw [Matrix.mul_sub, Matrix.trace_sub] at hzero
  exact sub_eq_zero.mp hzero

end ConnesChern
