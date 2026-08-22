import InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
import Mathlib.Data.Finset.Basic

/-!
# The seven-dimensional trace-zero carrier

For the split Zorn model in characteristic two, trace zero is the equation
`a = b`.  Its isotropic cone has 64 elements, hence 63 nonzero points.  This
is the correct point carrier for the 63-point geometry; it is not the full
eight-dimensional isotropic cone.
-/

namespace InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints

/-- Trace-zero (imaginary) elements in the split Zorn carrier over `𝔽₂`. -/
def TraceZero (X : SplitOctF2) : Prop := X.a = X.b

instance : DecidablePred TraceZero := by
  intro X
  unfold TraceZero
  infer_instance

/-- The seven-dimensional trace-zero carrier. -/
def Imaginary : Type := {X : SplitOctF2 // TraceZero X}

instance : Fintype Imaginary := Subtype.fintype TraceZero
deriving instance DecidableEq for Imaginary

/-- Zero in the trace-zero carrier. -/
def zeroImaginary : Imaginary := ⟨zero, by rfl⟩

instance : DecidablePred (fun X : Imaginary =>
    Isotropic X.1 ∧ X ≠ zeroImaginary) := by
  intro X
  change Decidable (zornNorm X.1 = false ∧ X ≠ zeroImaginary)
  exact inferInstance

/-- Isotropic points in the trace-zero carrier, excluding zero. -/
def isotropicPoints7 : Finset Imaginary :=
  Finset.univ.filter (fun X => Isotropic X.1 ∧ X ≠ zeroImaginary)

theorem isotropicPoints7_card : isotropicPoints7.card = 63 := by
  native_decide

theorem mem_isotropicPoints7 (X : Imaginary) :
    X ∈ isotropicPoints7 ↔ Isotropic X.1 ∧ X ≠ zeroImaginary := by
  simp [isotropicPoints7]

end InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints
