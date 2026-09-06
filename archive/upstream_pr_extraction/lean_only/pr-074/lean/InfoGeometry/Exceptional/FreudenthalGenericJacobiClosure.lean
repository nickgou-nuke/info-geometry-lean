import InfoGeometry.Exceptional.GenericGradedJacobiClosure
import InfoGeometry.Exceptional.FreudenthalExtremeActionData
import InfoGeometry.Exceptional.FreudenthalSymplecticTKKJacobiBridge

/-!
# Freudenthal adapter for generic graded Jacobi closure

This file supplies the finite homogeneous decomposition of the existing native
`FiveGradedCarrier`.  The zero grade is split into its symplectic and scale
lanes, so the actual linear decomposition has six atomic lanes:

`(-2), (-1), (0_symp), (0_scale), (+1), (+2)`.

The file does not manufacture a Jacobi theorem from `ExtremeActionData`.
`TKKMixedTripleData` is already known to be an independent missing identity.
Instead, it reduces global Jacobi to a finite set of six-lane cells through the
generic closure theorem.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

open InfoGeometry.Exceptional.GenericGradedJacobiClosure

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

namespace FiveGradedCarrier

/-- Upgrade the existing coordinatewise operations to an additive commutative
group, without changing any carrier operation. -/
instance instAddCommGroup : AddCommGroup (FiveGradedCarrier D) where
  add := (· + ·)
  add_assoc a b c := by
    apply FiveGradedCarrier.ext <;> simp [add_assoc]
  zero := 0
  zero_add a := by
    apply FiveGradedCarrier.ext <;> simp
  add_zero a := by
    apply FiveGradedCarrier.ext <;> simp
  neg := Neg.neg
  add_left_neg a := by
    apply FiveGradedCarrier.ext <;> simp
  add_comm a b := by
    apply FiveGradedCarrier.ext <;> simp [add_comm]
  nsmul := nsmulRec

/-- Coordinatewise real module structure on the full five-graded carrier. -/
instance instModule : Module ℝ (FiveGradedCarrier D) where
  one_smul x := by
    apply FiveGradedCarrier.ext <;> simp
  mul_smul a b x := by
    apply FiveGradedCarrier.ext <;> simp [mul_assoc, mul_smul]
  smul_add a x y := by
    apply FiveGradedCarrier.ext <;> simp [mul_add, smul_add]
  smul_zero a := by
    apply FiveGradedCarrier.ext <;> simp
  add_smul a b x := by
    apply FiveGradedCarrier.ext <;> simp [add_mul, add_smul]
  zero_smul x := by
    apply FiveGradedCarrier.ext <;> simp

end FiveGradedCarrier

/-- Atomic linear lanes of the native carrier.  The two zero-grade summands are
kept separate because they have different formulas in the bracket. -/
inductive JacobiLane
  | minus2
  | minus1
  | zeroSymp
  | zeroScale
  | plus1
  | plus2
  deriving DecidableEq, Fintype

/-- Linear homogeneous projection to one atomic lane. -/
def lanePart (g : JacobiLane) :
    FiveGradedCarrier D →ₗ[ℝ] FiveGradedCarrier D where
  toFun x :=
    match g with
    | .minus2 => ⟨x.minus2, 0, 0, 0, 0, 0⟩
    | .minus1 => ⟨0, x.minus1, 0, 0, 0, 0⟩
    | .zeroSymp => ⟨0, 0, x.zero_symp, 0, 0, 0⟩
    | .zeroScale => ⟨0, 0, 0, x.zero_scale, 0, 0⟩
    | .plus1 => ⟨0, 0, 0, 0, x.plus1, 0⟩
    | .plus2 => ⟨0, 0, 0, 0, 0, x.plus2⟩
  map_add' x y := by
    cases g <;> apply FiveGradedCarrier.ext <;> simp
  map_smul' r x := by
    cases g <;> apply FiveGradedCarrier.ext <;> simp

/-- The six homogeneous projections reconstruct every carrier element. -/
theorem sum_lanePart (x : FiveGradedCarrier D) :
    (∑ g : JacobiLane, lanePart D g x) = x := by
  apply FiveGradedCarrier.ext <;>
    simp [lanePart, JacobiLane]

/-- Native six-lane decomposition consumed by the generic closure engine. -/
def jacobiDecomposition :
    DecompositionData (R := ℝ) (V := FiveGradedCarrier D) (ι := JacobiLane) where
  part := lanePart D
  sum_part := sum_lanePart D

/-- A corrected Freudenthal bracket is admissible for the generic closure engine
only after its bilinearity and alternation are proved.  These are mathematical
properties, not opaque Boolean flags. -/
structure BilinearCorrectedBracketData
    (E : ExtremeActionData D) extends CorrectedFiveGradedBracketData D E where
  bracketLinear :
    FiveGradedCarrier D →ₗ[ℝ] FiveGradedCarrier D →ₗ[ℝ] FiveGradedCarrier D
  bracketLinear_apply : ∀ x y, bracketLinear x y = toCorrectedFiveGradedBracketData.bracket x y
  alternating : ∀ x, bracketLinear x x = 0

namespace BilinearCorrectedBracketData

/-- Forget the Freudenthal-specific readback and expose exactly the generic
bilinear alternating bracket contract. -/
def toBracketData {E : ExtremeActionData D}
    (B : BilinearCorrectedBracketData D E) :
    BracketData (R := ℝ) (V := FiveGradedCarrier D) where
  bracket := B.bracketLinear
  alternating := B.alternating

/-- Finite local Jacobi contract: only homogeneous six-lane triples are needed.
This is the precise frontier that must be discharged from TKK/extreme
compatibility lemmas. -/
abbrev HomogeneousCertificate {E : ExtremeActionData D}
    (B : BilinearCorrectedBracketData D E) : Prop :=
  HomogeneousJacobiCertificate (B.toBracketData D) (jacobiDecomposition D)

/-- Global Jacobi/Leibniz follows mechanically from the finite homogeneous
certificate. -/
theorem global_leibniz {E : ExtremeActionData D}
    (B : BilinearCorrectedBracketData D E)
    (C : B.HomogeneousCertificate D)
    (x y z : FiveGradedCarrier D) :
    B.bracketLinear x (B.bracketLinear y z) =
      B.bracketLinear (B.bracketLinear x y) z +
        B.bracketLinear y (B.bracketLinear x z) := by
  exact global_leibniz_of_homogeneous
    (B.toBracketData D) (jacobiDecomposition D) C x y z

/-- Native Lie-ring structure produced from the finite cell certificate. -/
def lieRing {E : ExtremeActionData D}
    (B : BilinearCorrectedBracketData D E)
    (C : B.HomogeneousCertificate D) : LieRing (FiveGradedCarrier D) :=
  lieRingOfHomogeneous (B.toBracketData D) (jacobiDecomposition D) C

/-- Native real Lie-algebra structure produced from the same certificate. -/
def lieAlgebra {E : ExtremeActionData D}
    (B : BilinearCorrectedBracketData D E)
    (C : B.HomogeneousCertificate D) :
    @LieAlgebra ℝ (FiveGradedCarrier D) _ _ _ _ (B.lieRing D C) :=
  lieAlgebraOfHomogeneous (B.toBracketData D) (jacobiDecomposition D) C

end BilinearCorrectedBracketData

/-- The existing TKK obstruction remains a genuine prerequisite: any closure
route that uses the native mixed bracket must provide this datum separately.
This theorem records that the required local identity is directly available
from the native owner once `TKKMixedTripleData` is supplied. -/
theorem mixedTriple_cell_identity
    (T : TKKMixedTripleData D)
    (x z y : FreudenthalCharge J) :
    (mixedSymplecticBracket D z y : Module.End ℝ (FreudenthalCharge J)) x =
      (mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z :=
  T.mixed_triple x z y

end InfoGeometry.Exceptional.Freudenthal
