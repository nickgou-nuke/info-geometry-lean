import InfoGeometry.Categorical.FibonacciFusionTreeCategoricalBraiding
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.FibonacciAssociatorScalarNaturality

/-!
# Scalar naturality of the Fibonacci fusion-tree braiding block

This is the scalar component of naturality for the concrete braiding
isomorphism on the `1 ⊕ 2τ` fusion-tree sector.  It is a genuine statement in
the existing `FibHom` carrier; it does not promote the sector construction to
a global `BraidedCategory` instance.
-/

namespace InfoGeometry.Categorical.FibonacciFusionTreeCategoricalBraiding

open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciFusionTreeAssociator
open InfoGeometry.Categorical.FibonacciAssociatorScalarNaturality
open InfoGeometry.Categorical.FibonacciHomSpace

theorem tauFusionTreeBraiding_scalar_naturality
    (q : Units ℂ) (τ s c : ℂ) :
    FibHom.comp
        (scalarFibHom
          (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) c)
        (tauFusionTreeBraiding q τ s) =
      FibHom.comp
        (tauFusionTreeBraiding q τ s)
        (scalarFibHom
          (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) c) := by
  apply FibHom.ext
  · simp [FibHom.comp, scalarFibHom, tauFusionTreeBraiding]
  · simp [FibHom.comp, scalarFibHom, tauFusionTreeBraiding]

theorem tauFusionTreeR_scalar_naturality
    (q : Units ℂ) (c : ℂ) :
    FibHom.comp
        (scalarFibHom
          (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) c)
        (tauFusionTreeR q) =
      FibHom.comp
        (tauFusionTreeR q)
        (scalarFibHom
          (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) c) := by
  apply FibHom.ext
  · simp [FibHom.comp, scalarFibHom, tauFusionTreeR]
  · simp [FibHom.comp, scalarFibHom, tauFusionTreeR]

end InfoGeometry.Categorical.FibonacciFusionTreeCategoricalBraiding
