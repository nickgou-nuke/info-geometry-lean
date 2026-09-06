import InfoGeometry.Categorical.FibonacciFusionTreeAssociator

/-!
# Scalar naturality on Fibonacci fusion Hom-spaces

The finite fusion-tree associator is already a genuine `FibHom` isomorphism.
This owner records the reusable scalar naturality that is valid on the whole
existing block Hom-space, without promoting the fixed-sector block to a
global braided-category instance.
-/

namespace InfoGeometry.Categorical.FibonacciAssociatorScalarNaturality

open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciFusionTreeAssociator
open InfoGeometry.Categorical.FibonacciHomSpace

noncomputable def scalarFibHom (X : FibCat) (c : ℂ) : FibHom X X :=
  { unit_comp := c • (1 : Matrix (Fin (X FibSimple.unit)) (Fin (X FibSimple.unit)) ℂ)
    tau_comp := c • (1 : Matrix (Fin (X FibSimple.tau)) (Fin (X FibSimple.tau)) ℂ) }

theorem scalarFibHom_comp (X : FibCat) (c d : ℂ) :
    FibHom.comp (scalarFibHom X c) (scalarFibHom X d) =
      scalarFibHom X (c * d) := by
  apply FibHom.ext
  · simp [FibHom.comp, scalarFibHom, smul_smul, mul_comm]
  · simp [FibHom.comp, scalarFibHom, smul_smul, mul_comm]

theorem scalarFibHom_naturality {X Y : FibCat} (f : FibHom X Y) (c : ℂ) :
    FibHom.comp (scalarFibHom X c) f =
      FibHom.comp f (scalarFibHom Y c) := by
  apply FibHom.ext
  · simp [FibHom.comp, scalarFibHom, Matrix.smul_mul, Matrix.mul_smul]
  · simp [FibHom.comp, scalarFibHom, Matrix.smul_mul, Matrix.mul_smul]

theorem tauFusionTreeAssociator_scalar_naturality (τ s c : ℂ) :
    FibHom.comp
        (scalarFibHom
          (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) c)
        (tauFusionTreeAssociator τ s) =
      FibHom.comp
        (tauFusionTreeAssociator τ s)
        (scalarFibHom
          (fibTensorObj tauObject (fibTensorObj tauObject tauObject)) c) := by
  exact scalarFibHom_naturality (tauFusionTreeAssociator τ s) c

end InfoGeometry.Categorical.FibonacciAssociatorScalarNaturality
