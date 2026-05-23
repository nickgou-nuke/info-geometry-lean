import InfoGeometry.Algebra.Zorn.NullCone

/-!
# InfoGeometry.Algebra.Zorn.Projective

Projectivized null cone of the explicit split-octonion Zorn carrier.

This file stays at the quadratic/projective level:

* nonzero null vectors modulo nonzero real rescaling;
* scale-invariance of nullness;
* canonical null representatives for the Zorn projectors and lightrays.

It does not introduce a `Ring` instance on `ZornMatrix` and it does not touch
associators.
-/

namespace InfoGeometry.Algebra.Zorn

open scoped BigOperators
open InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-- A nonzero null Zorn vector. -/
structure NonzeroNullCone where
  X : ZornCoord
  nonzero : X ≠ 0
  null : IsZornNull X

/-- Real rescaling of an explicit Zorn coordinate. -/
def rescale (c : ℝ) (X : ZornCoord) : ZornCoord :=
  c • X

/-- The Zorn norm is homogeneous of degree two under scalar rescaling. -/
theorem zornNorm_rescale (c : ℝ) (X : ZornCoord) :
    zornNorm (rescale c X) = c * c * zornNorm X := by
  rcases X with ⟨a, b, x, y⟩
  simp [rescale, zornNorm, dot3, mul_add, add_mul, mul_comm, mul_left_comm,
    mul_assoc]
  ring

/-- Nullness is preserved by real rescaling. -/
theorem isZornNull_rescale
    (c : ℝ) (X : ZornCoord)
    (hX : IsZornNull X) :
    IsZornNull (rescale c X) := by
  unfold IsZornNull
  rw [zornNorm_rescale, hX]
  simp

/-- Same-ray relation on nonzero null Zorn vectors. -/
def SameRay (X Y : NonzeroNullCone) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ Y.X = rescale c X.X

theorem SameRay.refl (X : NonzeroNullCone) : SameRay X X := by
  refine ⟨1, one_ne_zero, ?_⟩
  simp [SameRay, rescale]

theorem SameRay.symm {X Y : NonzeroNullCone} (h : SameRay X Y) :
    SameRay Y X := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  simp [SameRay, rescale, smul_smul, hc]

theorem SameRay.trans {X Y Z : NonzeroNullCone}
    (hXY : SameRay X Y) (hYZ : SameRay Y Z) :
    SameRay X Z := by
  rcases hXY with ⟨c, hc, rfl⟩
  rcases hYZ with ⟨d, hd, rfl⟩
  refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
  simp [SameRay, rescale, smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- Setoid for the projectivized Zorn null cone. -/
def projectiveNullSetoid : Setoid (NonzeroNullCone) where
  r := SameRay
  iseqv := ⟨SameRay.refl, @SameRay.symm, @SameRay.trans⟩

/--
Projectivized Zorn null cone.

This is the quotient of nonzero null Zorn vectors by nonzero real rescaling.
-/
abbrev ProjectiveNullCone : Type := Quotient projectiveNullSetoid

/-- The projective class of a nonzero null representative. -/
def projectiveNullClass (X : NonzeroNullCone) : ProjectiveNullCone :=
  Quotient.mk _ X

/-- The positive diagonal projector is null. -/
@[simp] theorem pPlus_null : IsZornNull pPlus := by
  simp [IsZornNull, zornNorm, pPlus, dot3]

/-- The negative diagonal projector is null. -/
@[simp] theorem pMinus_null : IsZornNull pMinus := by
  simp [IsZornNull, zornNorm, pMinus, dot3]

/-- The upper off-diagonal lightray is null. -/
@[simp] theorem upperVector_null (x : Vec3) :
    IsZornNull (upperVectorZorn x) := by
  simp [IsZornNull, zornNorm, upperVectorZorn, dot3]

/-- The lower off-diagonal lightray is null. -/
@[simp] theorem lowerVector_null (y : Vec3) :
    IsZornNull (lowerVectorZorn y) := by
  simp [IsZornNull, zornNorm, lowerVectorZorn, dot3]

/-- A projective null point represented by `pPlus`. -/
def projectivePPlus : ProjectiveNullCone :=
  projectiveNullClass
    ⟨pPlus, by
      intro h
      have h1 := congrArg (fun z : ZornCoord => z.1) h
      simpa [pPlus] using h1, pPlus_null⟩

/-- A projective null point represented by `pMinus`. -/
def projectivePMinus : ProjectiveNullCone :=
  projectiveNullClass
    ⟨pMinus, by
      intro h
      have h2 := congrArg (fun z : ZornCoord => z.2.1) h
      simpa [pMinus] using h2, pMinus_null⟩

/-- The projective null class is unchanged by a same-ray rescaling. -/
theorem projectiveNullClass_eq_of_sameRay
    {X Y : NonzeroNullCone} (h : SameRay X Y) :
    projectiveNullClass X = projectiveNullClass Y := by
  exact Quotient.sound h

end InfoGeometry.Algebra.Zorn

