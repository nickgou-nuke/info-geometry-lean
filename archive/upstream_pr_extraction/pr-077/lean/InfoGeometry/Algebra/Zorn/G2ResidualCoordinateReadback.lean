import InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity

namespace InfoGeometry.Algebra.Zorn.G2ResidualCoordinateReadback

open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate

/-! Coordinate-level interface for the residual PC word.  This is the native
readback boundary used by later separation proofs; it does not assert that
coordinates separate flag indices. -/

theorem residualWord_apply_eq_of_eq
    (k : Fin 12) (i j : Fin 189)
    (h : residualWord k i = residualWord k j) (a : Fin 6) :
    residualWord k i a = residualWord k j a := by
  exact congrFun h a

theorem residualWord_eq_of_forall_apply_eq
    (k : Fin 12) (i j : Fin 189)
    (h : ∀ a : Fin 6, residualWord k i a = residualWord k j a) :
    residualWord k i = residualWord k j := by
  funext a
  exact h a

theorem residualWord_eq_iff_forall_apply_eq
    (k : Fin 12) (i j : Fin 189) :
    residualWord k i = residualWord k j ↔
      ∀ a : Fin 6, residualWord k i a = residualWord k j a := by
  constructor
  · intro h a
    exact residualWord_apply_eq_of_eq k i j h a
  · exact residualWord_eq_of_forall_apply_eq k i j

theorem residualWord_injective_on_cell_of_coordinate_separation
    (hsep : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k → i ≠ j →
      ∃ a : Fin 6, residualWord k i a ≠ residualWord k j a) :
    ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      residualWord k i = residualWord k j → i = j := by
  intro k i j hik hjk hword
  by_contra hne
  obtain ⟨a, ha⟩ := hsep k i j hik hjk hne
  exact ha (residualWord_apply_eq_of_eq k i j hword a)

end InfoGeometry.Algebra.Zorn.G2ResidualCoordinateReadback
