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

/-! The trace-zero condition can be recovered intrinsically from the
finite algebra multiplication.  This is the key fact needed before an
automorphism action can be restricted to the seven-dimensional carrier. -/

private theorem add_self (X : SplitOctF2) : add X X = zero := by
  native_decide +revert

private theorem map_zero (f : SplitOctF2Aut) : f.1 zero = zero := by
  calc
    f.1 zero = f.1 (add zero zero) := by rw [add_zero]
    _ = add (f.1 zero) (f.1 zero) := f.2.2.1 zero zero
    _ = zero := add_self (f.1 zero)

private def SquareScalar (X : SplitOctF2) : Prop :=
  mul X X = zero ∨ mul X X = one

theorem traceZero_iff_squareScalar (X : SplitOctF2) :
    TraceZero X ↔ SquareScalar X := by
  dsimp [TraceZero, SquareScalar]
  native_decide +revert

theorem automorphism_map_traceZero (f : SplitOctF2Aut) (X : SplitOctF2)
    (hX : TraceZero X) : TraceZero (f.1 X) := by
  rw [traceZero_iff_squareScalar] at hX ⊢
  rcases hX with hX | hX
  · left
    rw [← map_zero f, ← f.2.2.2 X X, hX]
  · right
    rw [← f.2.1, ← f.2.2.2 X X, hX]

theorem isotropic_iff_square_zero (X : SplitOctF2) (hX : TraceZero X) :
    Isotropic X ↔ mul X X = zero := by
  dsimp [Isotropic, zornNorm, TraceZero] at hX ⊢
  native_decide +revert

theorem automorphism_map_isotropic (f : SplitOctF2Aut) (X : SplitOctF2)
    (hX : TraceZero X) (hiso : Isotropic X) :
    Isotropic (f.1 X) := by
  rw [isotropic_iff_square_zero X hX] at hiso
  rw [isotropic_iff_square_zero (f.1 X) (automorphism_map_traceZero f X hX)]
  rw [← map_zero f, ← f.2.2.2 X X, hiso]

/-- The seven-dimensional trace-zero carrier. -/
def Imaginary : Type := {X : SplitOctF2 // TraceZero X}

instance : Fintype Imaginary := Subtype.fintype TraceZero
deriving instance DecidableEq for Imaginary

/-- The actual left action induced by the automorphism group law.  The
underlying automorphism multiplication is function composition in the
opposite order, so the inverse is used to obtain the ordinary left action. -/
def actImaginary (f : SplitOctF2Aut) (X : Imaginary) : Imaginary :=
  ⟨f⁻¹.1 X.1, automorphism_map_traceZero f⁻¹ X.1 X.2⟩

instance : SMul SplitOctF2Aut Imaginary where
  smul := actImaginary

instance : MulAction SplitOctF2Aut Imaginary where
  one_smul X := by
    apply Subtype.ext
    rfl
  mul_smul f g X := by
    apply Subtype.ext
    change (f * g)⁻¹.1 X.1 = f⁻¹.1 (g⁻¹.1 X.1)
    rw [mul_inv_rev]
    rfl

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
