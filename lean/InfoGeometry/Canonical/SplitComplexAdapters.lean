import InfoGeometry.Canonical.SplitComplex
import InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra
import InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics
import InfoGeometry.Algebra.SplitAlgebraHierarchyBridge

namespace InfoGeometry.Canonical.SplitComplexAdapters

open InfoGeometry.Canonical.SplitComplex

noncomputable def hyperbolicToCanonical {R : Type*} [CommRing R] :
    InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra.SplitComplex R ≃
      Carrier R where
  toFun z := ⟨z.real, z.split⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

theorem hyperbolicToCanonical_mul {R : Type*} [CommRing R]
    (x y : InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra.SplitComplex R) :
    hyperbolicToCanonical (InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra.SplitComplex.mul x y) =
      hyperbolicToCanonical x * hyperbolicToCanonical y := by
  cases x; cases y; rfl

noncomputable def hestenesToCanonical :
    InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex ≃
      Carrier ℝ where
  toFun z := ⟨z.re, z.hyp⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

theorem hestenesToCanonical_mul (x y :
    InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex) :
    hestenesToCanonical
        (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.mul x y) =
      hestenesToCanonical x * hestenesToCanonical y := by
  cases x; cases y; rfl

noncomputable def hierarchyToCanonical {R : Type*} [CommRing R] :
    InfoGeometry.Algebra.SplitAlgebraHierarchyBridge.SplitComplex R ≃
      Carrier R where
  toFun z := ⟨z.re, z.j_im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

theorem hierarchyToCanonical_mul {R : Type*} [CommRing R]
    (x y : InfoGeometry.Algebra.SplitAlgebraHierarchyBridge.SplitComplex R) :
    hierarchyToCanonical
        (InfoGeometry.Algebra.SplitAlgebraHierarchyBridge.SplitComplex.mul x y) =
      hierarchyToCanonical x * hierarchyToCanonical y := by
  cases x; cases y; rfl

end InfoGeometry.Canonical.SplitComplexAdapters
