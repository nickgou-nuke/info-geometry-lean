import InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
  exact InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add_self X

private theorem map_zero (f : SplitOctF2Aut) : f.1 zero = zero := by
  calc
    f.1 zero = f.1 (add zero zero) := by rw [add_zero]
    _ = add (f.1 zero) (f.1 zero) := f.2.2.1 zero zero
    _ = zero := add_self (f.1 zero)

private def SquareScalar (X : SplitOctF2) : Prop :=
  mul X X = zero ∨ mul X X = one

private theorem dot3_swap (x0 x1 x2 y0 y1 y2 : Bool) :
    dot3 x0 x1 x2 y0 y1 y2 = dot3 y0 y1 y2 x0 x1 x2 := by
  simp [dot3, mul2, Bool.and_comm]

private theorem add2_is_xor (x y : Bool) : add2 x y = Bool.xor x y := by
  cases x <;> cases y <;> rfl

private theorem add2_self_false (x : Bool) : add2 x x = false := by
  cases x <;> rfl

private theorem mul2_comm (x y : Bool) : mul2 x y = mul2 y x := by
  simp [mul2, Bool.and_comm]

private theorem cross0_diagonal (x y : Bool) : cross0 x y x y = false := by
  unfold cross0
  rw [mul2_comm y x, add2_self_false]

private theorem cross1_diagonal (x y : Bool) : cross1 x y x y = false := by
  unfold cross1
  rw [mul2_comm y x, add2_self_false]

private theorem cross2_diagonal (x y : Bool) : cross2 x y x y = false := by
  unfold cross2
  rw [mul2_comm y x, add2_self_false]

private theorem mul_self_scalar_coordinates (X : SplitOctF2) (c : Bool)
    (h : mul X X = ⟨c, c, false, false, false, false, false, false⟩) :
    X.a = X.b := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  have ha := congrArg SplitOctF2.a h
  have hb := congrArg SplitOctF2.b h
  simp [mul, mul2] at ha hb
  rw [dot3_swap] at hb
  cases a <;> cases b <;> cases hq : dot3 x0 x1 x2 y0 y1 y2 <;>
    cases c <;> simp_all [add2]

private theorem mul_self_traceZero (X : SplitOctF2) (h : TraceZero X) :
    mul X X = ⟨zornNorm X, zornNorm X, false, false, false, false, false, false⟩ := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  change a = b at h
  subst b
  apply SplitOctF2.ext
  · change add2 (mul2 a a) (dot3 x0 x1 x2 y0 y1 y2) =
      Bool.xor (mul2 a a) (dot3 x0 x1 x2 y0 y1 y2)
    rw [add2_is_xor]
  · change add2 (mul2 a a) (dot3 y0 y1 y2 x0 x1 x2) =
      Bool.xor (mul2 a a) (dot3 x0 x1 x2 y0 y1 y2)
    rw [dot3_swap, add2_is_xor]
  · change add2 (add2 (mul2 a x0) (mul2 a x0)) (cross0 y1 y2 y1 y2) = false
    rw [add2_self_false, cross0_diagonal, add2_self_false]
  · change add2 (add2 (mul2 a x1) (mul2 a x1)) (cross1 y0 y2 y0 y2) = false
    rw [add2_self_false, cross1_diagonal, add2_self_false]
  · change add2 (add2 (mul2 a x2) (mul2 a x2)) (cross2 y0 y1 y0 y1) = false
    rw [add2_self_false, cross2_diagonal, add2_self_false]
  · change add2 (add2 (mul2 a y0) (mul2 a y0)) (cross0 x1 x2 x1 x2) = false
    rw [add2_self_false, cross0_diagonal, add2_self_false]
  · change add2 (add2 (mul2 a y1) (mul2 a y1)) (cross1 x0 x2 x0 x2) = false
    rw [add2_self_false, cross1_diagonal, add2_self_false]
  · change add2 (add2 (mul2 a y2) (mul2 a y2)) (cross2 x0 x1 x0 x1) = false
    rw [add2_self_false, cross2_diagonal, add2_self_false]

theorem traceZero_iff_squareScalar (X : SplitOctF2) :
    TraceZero X ↔ SquareScalar X := by
  change TraceZero X ↔ mul X X = zero ∨ mul X X = one
  constructor
  · intro h
    rw [mul_self_traceZero X h]
    cases hz : zornNorm X <;> simp [zero, one]
  · intro h
    rcases h with hzero | hone
    · have hab := mul_self_scalar_coordinates X false (by simpa [zero] using hzero)
      exact hab
    · have hab := mul_self_scalar_coordinates X true (by simpa [one] using hone)
      exact hab

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
  change zornNorm X = false ↔ mul X X = zero
  rw [mul_self_traceZero X hX]
  simp [zero]

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

/-- The 63 nonzero isotropic points in the trace-zero carrier. -/
def IsotropicPoint : Type :=
  {X : Imaginary // Isotropic X.1 ∧ X ≠ zeroImaginary}

instance : Fintype IsotropicPoint :=
  Subtype.fintype (fun X : Imaginary => Isotropic X.1 ∧ X ≠ zeroImaginary)

deriving instance DecidableEq for IsotropicPoint

def actIsotropicPoint (f : SplitOctF2Aut) (X : IsotropicPoint) : IsotropicPoint :=
  ⟨actImaginary f X.1,
    ⟨(by
        change Isotropic (f⁻¹.1 X.1.1)
        exact automorphism_map_isotropic f⁻¹ X.1.1 X.1.2 X.2.1),
      by
        intro hzero
        apply X.2.2
        apply Subtype.ext
        have hz : f.1.symm X.1.1 = zero := by
          change f.1.symm X.1.1 = zero
          exact congrArg (fun Y : Imaginary => Y.1) hzero
        have hz' := congrArg f.1 hz
        calc
          X.1.1 = f.1 (f.1.symm X.1.1) :=
            (f.1.apply_symm_apply X.1.1).symm
          _ = f.1 zero := hz'
          _ = zero := map_zero f⟩⟩

instance : SMul SplitOctF2Aut IsotropicPoint where
  smul := actIsotropicPoint

instance : MulAction SplitOctF2Aut IsotropicPoint where
  one_smul X := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  mul_smul f g X := by
    apply Subtype.ext
    apply Subtype.ext
    change (f * g)⁻¹.1 X.1.1 = f⁻¹.1 (g⁻¹.1 X.1.1)
    rw [mul_inv_rev]
    rfl

/-- Isotropic points in the trace-zero carrier, excluding zero. -/
def isotropicPoints7 : Finset Imaginary :=
  Finset.univ.filter (fun X => Isotropic X.1 ∧ X ≠ zeroImaginary)

theorem isotropicPoint_card : Fintype.card IsotropicPoint = 63 := by
  decide

theorem isotropicPoints7_card : isotropicPoints7.card = 63 := by
  decide

theorem mem_isotropicPoints7 (X : Imaginary) :
    X ∈ isotropicPoints7 ↔ Isotropic X.1 ∧ X ≠ zeroImaginary := by
  simp [isotropicPoints7]

end InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints
