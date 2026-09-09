import InfoGeometry.Clifford.SplitAtomDoubling
import InfoGeometry.Algebra.H3ZornCarrierBasis

/-!
# Matrix stages are not the octonion or Albert carriers

These are linear-dimension obstructions on the actual repository carriers.
They do not rule out spinor realizations, multiplication tensors, embeddings,
triality, or exceptional constructions.  They rule out the carrier
identifications made in the source's tensor-tower diagram.
-/

namespace InfoGeometry.Canonical.SplitAtomCarrierObstructions

open InfoGeometry.Algebra
open InfoGeometry.Clifford.SplitAtomDoubling

theorem zorn_finrank_eight : Module.finrank ℝ (ZornVectorMatrix ℝ) = 8 := by
  rw [Module.finrank_eq_card_basis zornCoordinateBasis]
  simp

theorem matrix_eight_not_zorn :
    ¬ Nonempty (MatrixModel 3 ≃ₗ[ℝ] ZornVectorMatrix ℝ) := by
  rintro ⟨e⟩
  have h := e.finrank_eq
  rw [matrixModel_three_finrank, zorn_finrank_eight] at h
  norm_num at h

theorem matrix_sixteen_not_albert :
    ¬ Nonempty (MatrixModel 4 ≃ₗ[ℝ] H3Zorn ℝ) := by
  rintro ⟨e⟩
  have h := e.finrank_eq
  rw [matrixModel_four_finrank, finrank_h3zorn] at h
  norm_num at h

end InfoGeometry.Canonical.SplitAtomCarrierObstructions
