import InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Native action on the 63-point imaginary isotropic carrier

The full split Zorn carrier has 135 nonzero isotropic elements.  The
parabolic 63-point carrier is the nonzero isotropic part of the trace-zero
(`imaginary`) subspace.  This file gives that carrier an honest action of
`SplitOctF2Aut`; it does not identify the resulting action with a quotient or
with the flag action until a separate stabilizer theorem is supplied.
-/

namespace InfoGeometry.Algebra.Zorn.G2ImaginaryPointAction

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints

/-- Nonzero isotropic points in the seven-dimensional trace-zero carrier. -/
def Point := {X : Imaginary // Isotropic X.1 ∧ X ≠ zeroImaginary}

instance : Fintype Point := Subtype.fintype (fun X : Imaginary =>
  Isotropic X.1 ∧ X ≠ zeroImaginary)

deriving instance DecidableEq for Point

private theorem isotropic_trace_zero_iff (X : Imaginary) :
    Isotropic X.1 ↔ mul X.1 X.1 = zero := by
  native_decide +revert

private theorem automorphism_map_traceZero (f : SplitOctF2Aut) (X : SplitOctF2)
    (hX : TraceZero X) : TraceZero (f.1 X) := by
  native_decide +revert

private theorem automorphism_map_zero (f : SplitOctF2Aut) :
    f.1 zero = zero := by
  have h := f.2.2.1 (0 : SplitOctF2) 0
  have hself : add (f.1 0) (f.1 0) = zero :=
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add_self (f.1 0)
  rw [InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add_self 0] at h
  exact h.trans hself

private theorem automorphism_map_isotropic (f : SplitOctF2Aut) (X : Imaginary)
    (hX : Isotropic X.1) : Isotropic
      ({ val := f.1 X.1
         property := automorphism_map_traceZero f X.2 } : Imaginary).1 := by
  rw [isotropic_trace_zero_iff]
  have hsq := (isotropic_trace_zero_iff X).mp hX
  rw [← f.2.2.2 X.1 X.1, hsq, automorphism_map_zero f]

private theorem automorphism_map_nonzero (f : SplitOctF2Aut) (X : Imaginary)
    (hX : X ≠ zeroImaginary) :
    ({ val := f.1 X.1
       property := automorphism_map_traceZero f X.2 } : Imaginary) ≠ zeroImaginary := by
  intro h
  apply hX
  apply Subtype.ext
  have hz := automorphism_map_zero f
  have hzero : f.1 X.1 = f.1 zero := by
    simpa [zeroImaginary] using congrArg Subtype.val h
  exact Subtype.ext (f.1.injective (hzero.trans hz.symm))

noncomputable instance : MulAction SplitOctF2Aut Point where
  smul g p :=
    let f := g⁻¹
    let X : Imaginary :=
      { val := f.1 p.1.1,
         property := automorphism_map_traceZero f p.1.1 p.1.2 }
    ⟨X, automorphism_map_isotropic f p.1.1 p.2.1,
      automorphism_map_nonzero f p.1.1 p.2.2⟩
  one_smul p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  mul_smul g h p := by
    apply Subtype.ext
    apply Subtype.ext
    change (g * h)⁻¹.1 p.1.1 = g⁻¹.1 (h⁻¹.1 p.1.1)
    rfl

theorem point_card : Fintype.card Point = 63 := by
  native_decide

theorem point_mem_isotropicPoints7 (p : Point) :
    p.1 ∈ isotropicPoints7 := by
  rw [mem_isotropicPoints7]
  exact p.2

end InfoGeometry.Algebra.Zorn.G2ImaginaryPointAction
