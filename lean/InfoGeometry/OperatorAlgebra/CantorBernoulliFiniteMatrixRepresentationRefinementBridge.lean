import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStarRepresentationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Generator-level dyadic refinement of the finite matrix readout

The concrete matrix representation is already a `StarAlgHom` at each depth.
This owner records the compatible refinement identity on matrix-unit
generators, using the independently proved Cuntz-unit refinement theorem.
It intentionally does not choose a second matrix embedding or claim an
infinite C⋆ completion.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge

open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStarRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.Canonical.CantorKMSState
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

def dyadicMatrixEmbedding (n : ℕ) (A : BitWordMatrixStage n) :
    BitWordMatrixStage (n + 1) :=
  ∑ u : BitWord n, ∑ v : BitWord n,
    A u v •
      (Matrix.single (extendBitWord n u false) (extendBitWord n v false) 1 +
        Matrix.single (extendBitWord n u true) (extendBitWord n v true) 1)
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

theorem bitWordMatrixLinearRepresentation_single_refinement
    (n : ℕ) (u v : BitWord n) :
    bitWordMatrixLinearRepresentation n (Matrix.single u v 1) =
      bitWordMatrixLinearRepresentation (n + 1)
        (Matrix.single (extendBitWord n u false) (extendBitWord n v false) 1) +
      bitWordMatrixLinearRepresentation (n + 1)
        (Matrix.single (extendBitWord n u true) (extendBitWord n v true) 1) := by
  rw [bitWordMatrixLinearRepresentation_single,
    bitWordMatrixLinearRepresentation_single,
    bitWordMatrixLinearRepresentation_single,
    bitWordUnit_refinement]

theorem bitWordMatrixLinearRepresentation_single_smul_refinement
    (n : ℕ) (u v : BitWord n) (c : ℂ) :
    bitWordMatrixLinearRepresentation n (Matrix.single u v c) =
      bitWordMatrixLinearRepresentation (n + 1)
        (c • Matrix.single (extendBitWord n u false) (extendBitWord n v false) 1) +
      bitWordMatrixLinearRepresentation (n + 1)
        (c • Matrix.single (extendBitWord n u true) (extendBitWord n v true) 1) := by
  rw [bitWordMatrixLinearRepresentation_single_smul,
    map_smul,
    bitWordMatrixLinearRepresentation_single_smul,
    map_smul,
    bitWordMatrixLinearRepresentation_single_smul,
    bitWordUnit_refinement]
  simp [smul_add]

theorem bitWordMatrixLinearRepresentation_refinement
    (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordMatrixLinearRepresentation n A =
      bitWordMatrixLinearRepresentation (n + 1) (dyadicMatrixEmbedding n A) := by
  classical
  rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, map_smul]
  unfold dyadicMatrixEmbedding
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [bitWordMatrixLinearRepresentation_single_smul_refinement]
  have hA :
      (∑ i, ∑ j, Matrix.single i j (A i j)) u v = A u v := by
    exact congrArg (fun M => M u v) (Matrix.matrix_eq_sum_single A).symm
  rw [hA]
  simp only [map_smul, map_add]
  rw [smul_add]

/-- The same refinement identity for the already packaged finite
`StarAlgHom` representations.  This is a transport corollary: the source
embedding remains the explicit dyadic coefficient map above, while the
operator readout is the native finite star-algebra representation. -/
theorem bitWordMatrixStarRepresentation_refinement
    (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordMatrixStarRepresentation n A =
      bitWordMatrixStarRepresentation (n + 1) (dyadicMatrixEmbedding n A) := by
  exact bitWordMatrixLinearRepresentation_refinement n A

end InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge
