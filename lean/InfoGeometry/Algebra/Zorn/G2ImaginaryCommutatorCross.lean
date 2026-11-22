/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit

/-!
# The native imaginary commutator replaces the non-equivariant legacy cross map

The finite coordinate operation `octCross` is not equivariant for the native
split-Zorn automorphism action.  This owner defines the canonical replacement
by transporting the algebra commutator `XY + YX` on the trace-zero carrier.
In characteristic two this commutator is again trace-zero, and automorphisms
transport it because they preserve addition and multiplication.
-/

namespace InfoGeometry.Algebra.Zorn.G2ImaginaryCommutatorCross

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit
open InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

private theorem dot3_swap (x0 x1 x2 y0 y1 y2 : Bool) :
    dot3 x0 x1 x2 y0 y1 y2 = dot3 y0 y1 y2 x0 x1 x2 := by
  simp [dot3, mul2, Bool.and_comm]

private theorem commutator_traceZero (X Y : SplitOctF2)
    (hX : X.a = X.b) (hY : Y.a = Y.b) :
    (add (mul X Y) (mul Y X)).a = (add (mul X Y) (mul Y X)).b := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨c, d, u0, u1, u2, v0, v1, v2⟩
  change a = b at hX
  change c = d at hY
  subst b
  subst d
  simp [add, mul, dot3, mul2, Bool.and_comm, Bool.xor_comm]

/-- The commutator of two trace-zero split-Zorn elements remains trace-zero. -/
def imaginaryCommutator (X Y : Imaginary) : Imaginary :=
  ⟨add (mul X.1 Y.1) (mul Y.1 X.1), commutator_traceZero X.1 Y.1 X.2 Y.2⟩

/-- The native commutator is equivariant under the existing left action on the
trace-zero carrier. -/
theorem actImaginary_commutator (g : SplitOctF2Aut) (X Y : Imaginary) :
    G2ImaginaryIsotropicPoints.actImaginary g (imaginaryCommutator X Y) =
      imaginaryCommutator (G2ImaginaryIsotropicPoints.actImaginary g X)
        (G2ImaginaryIsotropicPoints.actImaginary g Y) := by
  apply Subtype.ext
  change g⁻¹.1 (add (mul X.1 Y.1) (mul Y.1 X.1)) =
    add (mul (g⁻¹.1 X.1) (g⁻¹.1 Y.1))
      (mul (g⁻¹.1 Y.1) (g⁻¹.1 X.1))
  rw [g⁻¹.2.2.1, g⁻¹.2.2.2, g⁻¹.2.2.2]

/-- Coordinate realization of the native trace-zero algebra commutator. -/
def nativeImaginaryCross (x y : OctImF2) : OctImF2 :=
  imaginaryToOctIm
    (imaginaryCommutator (octImToImaginary x) (octImToImaginary y))

private theorem octImToImaginary_imaginaryToOctIm (X : Imaginary) :
    octImToImaginary (imaginaryToOctIm X) = X := imaginaryOctImEquiv.left_inv X

/-- The corrected coordinate operation is equivariant under every native
split-octonion automorphism action. -/
theorem octImAction_nativeImaginaryCross (g : SplitOctF2Aut) (x y : OctImF2) :
    nativeImaginaryCross (octImAction g x) (octImAction g y) =
      octImAction g (nativeImaginaryCross x y) := by
  change imaginaryToOctIm (imaginaryCommutator
      (octImToImaginary (imaginaryToOctIm
        (G2ImaginaryIsotropicPoints.actImaginary g (octImToImaginary x))))
      (octImToImaginary (imaginaryToOctIm
        (G2ImaginaryIsotropicPoints.actImaginary g (octImToImaginary y)))) ) =
    imaginaryToOctIm (G2ImaginaryIsotropicPoints.actImaginary g
      (octImToImaginary (imaginaryToOctIm
        (imaginaryCommutator (octImToImaginary x) (octImToImaginary y)))))
  rw [octImToImaginary_imaginaryToOctIm, octImToImaginary_imaginaryToOctIm,
    octImToImaginary_imaginaryToOctIm]
  exact congrArg imaginaryToOctIm
    (actImaginary_commutator g (octImToImaginary x) (octImToImaginary y)).symm

/-- The legacy coordinate cross operation cannot agree everywhere with the
native transported commutator: such agreement would force the legacy
operation to satisfy the equivariance contradicted by the certified witness. -/
theorem octCross_not_everywhere_nativeImaginaryCross :
    ¬ ∀ x y : OctImF2, octCross x y = nativeImaginaryCross x y := by
  intro h
  apply InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit.octCross_pc1_not_equivariant
  calc
    octCross (octImAction pc1Aut
        InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit.testPointU)
        (octImAction pc1Aut InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit.testPointV) =
        nativeImaginaryCross (octImAction pc1Aut
          InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit.testPointU)
          (octImAction pc1Aut InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit.testPointV) := h _ _
    _ = octImAction pc1Aut (nativeImaginaryCross
        InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit.testPointU
        InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit.testPointV) :=
      octImAction_nativeImaginaryCross pc1Aut _ _
    _ = octImAction pc1Aut (octCross
        InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit.testPointU
        InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit.testPointV) := by
      rw [← h]

end InfoGeometry.Algebra.Zorn.G2ImaginaryCommutatorCross
