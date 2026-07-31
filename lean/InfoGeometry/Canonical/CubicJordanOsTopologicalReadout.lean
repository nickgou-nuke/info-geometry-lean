import InfoGeometry.Algebra.CubicJordanOsExtensions

/-!
# Topological readouts for the native cubic Albert carrier

The native `CubicJordanOs.AlbertMatrix` currently has additive and coordinate
structure, but no Jordan product.  This owner therefore adds only the honest
finite-coordinate topology induced by its existing equivalence and proves
continuity of the coordinate and Peirce readouts.
-/

noncomputable section

namespace InfoGeometry.Algebra.CubicJordanOs

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

instance splitOctTopologicalSpace : TopologicalSpace SplitOct :=
  TopologicalSpace.induced splitOctEquiv.toFun inferInstance

instance albertMatrixTopologicalSpace : TopologicalSpace AlbertMatrix :=
  TopologicalSpace.induced albertMatrixEquiv.toFun inferInstance

private theorem continuous_splitOctEquiv :
    Continuous (splitOctEquiv : SplitOct → ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :=
  continuous_induced_dom

private theorem continuous_albertMatrixEquiv :
    Continuous
      (albertMatrixEquiv :
        AlbertMatrix → ℝ × ℝ × ℝ × SplitOct × SplitOct × SplitOct) :=
  continuous_induced_dom

theorem continuous_albertMatrix_α₁ :
    Continuous (fun X : AlbertMatrix => X.α₁) := by
  simpa [albertMatrixEquiv] using continuous_albertMatrixEquiv.fst

theorem continuous_albertMatrix_α₂ :
    Continuous (fun X : AlbertMatrix => X.α₂) := by
  simpa [albertMatrixEquiv] using continuous_albertMatrixEquiv.snd.fst

theorem continuous_albertMatrix_α₃ :
    Continuous (fun X : AlbertMatrix => X.α₃) := by
  simpa [albertMatrixEquiv] using continuous_albertMatrixEquiv.snd.snd.fst

theorem continuous_albertMatrix_z₁ :
    Continuous (fun X : AlbertMatrix => X.z₁) := by
  simpa [albertMatrixEquiv] using continuous_albertMatrixEquiv.snd.snd.snd.fst

theorem continuous_albertMatrix_z₂ :
    Continuous (fun X : AlbertMatrix => X.z₂) := by
  simpa [albertMatrixEquiv] using continuous_albertMatrixEquiv.snd.snd.snd.snd.fst

theorem continuous_albertMatrix_z₃ :
    Continuous (fun X : AlbertMatrix => X.z₃) := by
  exact continuous_albertMatrixEquiv.snd.snd.snd.snd.snd

theorem continuous_peirceDecomposition_diag₁ :
    Continuous (fun X : AlbertMatrix => (peirceDecomposition X).diag₁) := by
  simpa using continuous_albertMatrix_α₁

theorem continuous_peirceDecomposition_diag₂ :
    Continuous (fun X : AlbertMatrix => (peirceDecomposition X).diag₂) := by
  simpa using continuous_albertMatrix_α₂

theorem continuous_peirceDecomposition_diag₃ :
    Continuous (fun X : AlbertMatrix => (peirceDecomposition X).diag₃) := by
  simpa using continuous_albertMatrix_α₃

theorem continuous_peirceDecomposition_off₂₃ :
    Continuous (fun X : AlbertMatrix => (peirceDecomposition X).off₂₃) := by
  simpa using continuous_albertMatrix_z₁

theorem continuous_peirceDecomposition_off₃₁ :
    Continuous (fun X : AlbertMatrix => (peirceDecomposition X).off₃₁) := by
  simpa using continuous_albertMatrix_z₂

theorem continuous_peirceDecomposition_off₁₂ :
    Continuous (fun X : AlbertMatrix => (peirceDecomposition X).off₁₂) := by
  simpa using continuous_albertMatrix_z₃

end InfoGeometry.Algebra.CubicJordanOs
