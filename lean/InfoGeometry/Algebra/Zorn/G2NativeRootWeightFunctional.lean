import InfoGeometry.Lie.CanonicalZornCartanRootSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Bundled native root-weight functionals

The native root system exposes `nativeRootWeight` as a function-valued
functional.  This owner supplies only the linear-map packaging needed by
generic Lie-equivalence transport lemmas; it makes no claim about a finite
Weyl-label compatibility.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2NativeRootWeightFunctional

open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

abbrev Cartan := axialCartanLieSubalgebra
abbrev Weight := Cartan →ₗ[ℝ] ℝ
abbrev NativeIndex :=
  InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.nonzeroIndex

def nativeRootWeightLinear (i : NativeIndex) : Weight where
  toFun := nativeRootWeight i
  map_add' := by
    intro H K
    simp [nativeRootWeight]
  map_smul' := by
    intro r H
    simp [nativeRootWeight]

@[simp] theorem nativeRootWeightLinear_apply
    (i : NativeIndex) (H : Cartan) :
    nativeRootWeightLinear i H = nativeRootWeight i H :=
  rfl

@[simp] theorem nativeRootWeight_on_axialCartanLieEquiv
    (i : NativeIndex) (k : InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.TracelessWeight) :
    nativeRootWeight i (axialCartanLieEquiv k) =
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootWeight i.1 k :=
  by
    simp [nativeRootWeight]

def transportedNativeRootWeight
    (i : NativeIndex) (c : Cartan ≃ₗ[ℝ] Cartan) : Weight :=
  (nativeRootWeightLinear i).comp c.symm.toLinearMap

@[simp] theorem transportedNativeRootWeight_apply
    (i : NativeIndex) (c : Cartan ≃ₗ[ℝ] Cartan) (H : Cartan) :
    transportedNativeRootWeight i c H =
      nativeRootWeight i (c.symm H) :=
  rfl

end InfoGeometry.Algebra.Zorn.G2NativeRootWeightFunctional
