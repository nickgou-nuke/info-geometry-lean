import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import InfoGeometry.Lie.SplitOctonionAnnihilatorDimension
import InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge

/-!
# Canonical split-octonion null fibres and the `(4,4) -> (5,5)` boundary

This owner closes the first typed wire in the null/boundary lane.  It does not
identify an annihilator fibre with a projective boundary fibre: it records the
two native maps and proves their null compatibility.
-/

noncomputable section

namespace InfoGeometry.Canonical.CanonicalZornNullProjectiveBoundaryBridge

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open ProjectiveAffineConformalClosure55

abbrev canonicalDet (X : CanonicalZorn) : ℝ :=
  InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X

/-! ## The real carrier equivalence -/

def canonicalToCore (X : CanonicalZorn) : ZornCore.Zorn :=
  { a := X.a, u := X.x, v := X.y, b := X.b }

def coreToCanonicalReal (X : ZornCore.Zorn) : CanonicalZorn :=
  { a := X.a, b := X.b, x := X.u, y := X.v }

def canonicalCoreEquiv : CanonicalZorn ≃ ZornCore.Zorn where
  toFun := canonicalToCore
  invFun := coreToCanonicalReal
  left_inv X := by cases X; rfl
  right_inv X := by cases X; rfl

theorem canonicalToCore_injective : Function.Injective canonicalToCore :=
  canonicalCoreEquiv.injective

theorem canonicalToCore_mul (X Y : CanonicalZorn) :
    canonicalToCore (zMul X Y) = canonicalToCore X * canonicalToCore Y := by
  apply ZornCore.Zorn.ext'
  · simp [canonicalToCore, zMul, ZornCore.mul_a]
    simp [InfoGeometry.Canonical.ZornMatrix.dot, ZornCore.dot,
      Fin.sum_univ_three]
  · funext i
    fin_cases i <;>
      simp [canonicalToCore, zMul, ZornCore.mul_u, ZornCore.cross,
        InfoGeometry.Canonical.ZornMatrix.cross]
  · funext i
    fin_cases i <;>
      simp [canonicalToCore, zMul, ZornCore.mul_v, ZornCore.cross,
        InfoGeometry.Canonical.ZornMatrix.cross]
      <;> ring
  · simp [canonicalToCore, zMul, ZornCore.mul_b,
      InfoGeometry.Canonical.ZornMatrix.dot, ZornCore.dot,
      Fin.sum_univ_three]
    ring

theorem canonicalToCore_det (X : CanonicalZorn) :
    ZornCore.det (canonicalToCore X) =
    canonicalDet X := by
  simp [canonicalToCore, ZornCore.det,
    InfoGeometry.Canonical.ZornMatrix.dot,
    canonicalDet, InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3,
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ, ZornCore.dot,
    Fin.sum_univ_three]

def coreTrace (X : ZornCore.Zorn) : ℝ := X.a + X.b

theorem canonicalToCore_trace (X : CanonicalZorn) :
    coreTrace (canonicalToCore X) = realZornTrace X := by
  rfl

theorem canonicalToCore_zero : canonicalToCore (0 : CanonicalZorn) = 0 := by
  rfl

theorem canonicalToCore_null_iff (X : CanonicalZorn) :
    ZornCore.det (canonicalToCore X) = 0 ↔
      canonicalDet X = 0 := by
  rw [canonicalToCore_det]

theorem canonicalToCore_annihilator_iff (X Y : CanonicalZorn) :
    zMul Y X = 0 ↔ canonicalToCore Y * canonicalToCore X = 0 := by
  constructor
  · intro h
    rw [← canonicalToCore_mul, h, canonicalToCore_zero]
  · intro h
    apply canonicalToCore_injective
    rw [canonicalToCore_mul, h, canonicalToCore_zero]

theorem canonical_det_mul (X Y : CanonicalZorn) :
    canonicalDet (zMul X Y) = canonicalDet X * canonicalDet Y := by
  exact InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionDatum.detZ_mul X Y

theorem canonical_annihilator_mem_null {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0)
    {Y : CanonicalZorn}
    (hY : Y ∈ LinearMap.ker (fullRightMulLinear X.1)) :
    canonicalDet Y = 0 := by
  rw [← fullRightMul_range_eq_ker hX0 hXnull] at hY
  obtain ⟨Z, rfl⟩ := hY
  change canonicalDet (zMul Z X.1) = 0
  rw [canonical_det_mul]
  have hdet : canonicalDet X.1 = 0 :=
    (mem_normLevel_iff 0 X).mp hXnull
  rw [hdet]
  simp

/-! ## Canonical real Zorn coordinates in the affine `(4,4)` chart -/

def canonicalToPAC44 (X : CanonicalZorn) : PACSplit44 where
  x0 := (X.a + X.b) / 2
  x1 := (X.x 0 - X.y 0) / 2
  x2 := (X.x 1 - X.y 1) / 2
  x3 := (X.x 2 - X.y 2) / 2
  y0 := (X.a - X.b) / 2
  y1 := (X.x 0 + X.y 0) / 2
  y2 := (X.x 1 + X.y 1) / 2
  y3 := (X.x 2 + X.y 2) / 2

theorem canonicalToPAC44_Q44 (X : CanonicalZorn) :
    Q44 (canonicalToPAC44 X) =
      canonicalDet X := by
  simp [canonicalToPAC44, Q44,
    canonicalDet,
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3,
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    InfoGeometry.Canonical.ZornMatrix.dot, Fin.sum_univ_three]
  ring

/-! ## The affine chart of the canonical Zorn null quadric -/

/-- The `a = 1` affine chart of the canonical Zorn null quadric. -/
def canonicalAffineNullChart (x y : Fin 3 → ℝ) : CanonicalZorn :=
  { a := 1
    b := InfoGeometry.Canonical.ZornMatrix.dot x y
    x := x
    y := y }

theorem canonicalAffineNullChart_det (x y : Fin 3 → ℝ) :
    canonicalDet (canonicalAffineNullChart x y) = 0 := by
  simp [canonicalDet, canonicalAffineNullChart,
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3]

theorem canonicalAffineNullChart_injective : Function.Injective
    (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      canonicalAffineNullChart p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · simpa [canonicalAffineNullChart] using
      congrArg (fun Z : CanonicalZorn => Z.x) h
  · simpa [canonicalAffineNullChart] using
      congrArg (fun Z : CanonicalZorn => Z.y) h

/-- A null Zorn element with `a = 1` is uniquely represented by the affine
chart coordinates `(x,y)`. -/
theorem canonicalAffineNullChart_eq_of_a_one
    (X : CanonicalZorn) (ha : X.a = 1)
    (hnull : canonicalDet X = 0) :
    canonicalAffineNullChart X.x X.y = X := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · exact ha.symm
  · have hdot : X.b = InfoGeometry.Canonical.ZornMatrix.dot X.x X.y := by
      rw [canonicalDet,
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3,
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ] at hnull
      rw [ha] at hnull
      linarith
    exact hdot.symm
  · rfl
  · rfl

/-! ## The conformal/projective null lift -/

def canonicalConformalLift (X : CanonicalZorn) : PACSplit55 :=
  conformalEmbed44to55 (canonicalToPAC44 X)

def pacSplit55Zero : PACSplit55 :=
  { x0 := 0, x1 := 0, x2 := 0, x3 := 0
    y0 := 0, y1 := 0, y2 := 0, y3 := 0, u := 0, v := 0 }

@[simp] theorem smul55_one (P : PACSplit55) : smul55 1 P = P := by
  cases P
  simp [smul55]

theorem smul55_smul (a b : ℝ) (P : PACSplit55) :
    smul55 a (smul55 b P) = smul55 (a * b) P := by
  cases P
  simp [smul55, mul_assoc]

theorem canonicalConformalLift_null (X : CanonicalZorn) :
    Q55 (canonicalConformalLift X) = 0 := by
  unfold canonicalConformalLift
  exact conformalEmbed44to55_null (canonicalToPAC44 X)

theorem canonicalConformalLift_ne_zero (X : CanonicalZorn) :
    canonicalConformalLift X ≠ pacSplit55Zero := by
  intro h
  have hu := congrArg PACSplit55.u h
  have hv := congrArg PACSplit55.v h
  dsimp [canonicalConformalLift, conformalEmbed44to55, pacSplit55Zero] at hu hv
  linarith

theorem canonicalConformalLift_null_of_normLevel
    {X : Imaginary} (hX : X ∈ NormLevel 0) :
    Q55 (canonicalConformalLift X.1) = 0 := by
  exact canonicalConformalLift_null X.1

theorem imaginary_annihilator_mem_null {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0)
    (Y : Annihilator X) :
    canonicalDet Y.1.1 = 0 := by
  apply canonical_annihilator_mem_null hX0 hXnull
  exact (mem_annihilator_iff X Y.1).mp Y.2

def annihilatorBoundaryMap {X : Imaginary} :
    Annihilator X → PACSplit55 :=
  fun Y => canonicalConformalLift Y.1.1

def annihilatorProjectiveRepresentative {X : Imaginary} (Y : Annihilator X) :
    {P : PACSplit55 // P ≠ pacSplit55Zero ∧ Q55 P = 0} :=
  ⟨annihilatorBoundaryMap Y,
    canonicalConformalLift_ne_zero Y.1.1,
    canonicalConformalLift_null Y.1.1⟩

theorem annihilatorProjectiveRepresentative_null {X : Imaginary}
    (Y : Annihilator X) :
    Q55 (annihilatorProjectiveRepresentative Y).1 = 0 :=
  (annihilatorProjectiveRepresentative Y).2.2

theorem annihilatorProjectiveRepresentative_on_boundary
    {X : Imaginary} (Y : Annihilator X) :
    sameProjectiveLine55 (annihilatorProjectiveRepresentative Y).1
      (annihilatorProjectiveRepresentative Y).1 := by
  exact ⟨1, one_ne_zero, by simp [smul55]⟩

/-! The quotient is now an actual projective boundary object: its relation is
the nonzero-scalar line relation restricted to nonzero null representatives. -/
abbrev NullRepresentative55 := {P : PACSplit55 // P ≠ pacSplit55Zero ∧ Q55 P = 0}

def nullRepresentative55Rel : Setoid NullRepresentative55 where
  r P Q := sameProjectiveLine55 P.1 Q.1
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro P
      exact ⟨1, one_ne_zero, by simp [smul55_one]⟩
    · intro P Q h
      obtain ⟨a, ha, hPQ⟩ := h
      refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
      rw [hPQ, smul55_smul]
      simp [ha, smul55_one]
    · intro P Q R hPQ hQR
      obtain ⟨a, ha, hPQ⟩ := hPQ
      obtain ⟨b, hb, hQR⟩ := hQR
      refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
      rw [hQR, hPQ, ← smul55_smul]

abbrev ProjectiveNullBoundary55 := Quotient nullRepresentative55Rel

def annihilatorProjectiveClass {X : Imaginary} (Y : Annihilator X) :
    ProjectiveNullBoundary55 :=
  Quotient.mk nullRepresentative55Rel (annihilatorProjectiveRepresentative Y)

theorem annihilatorProjectiveClass_representative {X : Imaginary}
    (Y : Annihilator X) :
    Quotient.mk nullRepresentative55Rel (annihilatorProjectiveRepresentative Y) =
      annihilatorProjectiveClass Y := rfl

/-! The incidence fibre is typed as the image of the annihilator map.  This is
deliberately not called a projective quotient: projectivisation needs an
explicit scalar-action quotient and is a separate owner. -/
def annihilatorBoundaryIncidence {X : Imaginary} (P : PACSplit55) : Prop :=
  ∃ Y : Annihilator X, annihilatorBoundaryMap Y = P

theorem annihilatorBoundaryMap_incidence {X : Imaginary} (Y : Annihilator X) :
    annihilatorBoundaryIncidence (X := X) (annihilatorBoundaryMap Y) :=
  ⟨Y, rfl⟩

theorem annihilatorBoundaryIncidence_null {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0)
    {P : PACSplit55} (hP : annihilatorBoundaryIncidence (X := X) P) :
    Q55 P = 0 := by
  obtain ⟨Y, hY⟩ := hP
  rw [← hY]
  exact canonicalConformalLift_null Y.1.1

theorem annihilatorBoundaryMap_null {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0)
    (Y : Annihilator X) :
    Q55 (annihilatorBoundaryMap Y) = 0 := by
  exact canonicalConformalLift_null Y.1.1

/-! ## The null annihilator fibre certificate -/

theorem annihilator_fibre_finrank_three {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0) :
    Module.finrank ℝ (Annihilator X) = 3 :=
  annihilator_finrank_eq_three hX0 hXnull

/-! A canonical (choice-based) basis makes the fibre map reusable without
pretending that the annihilator has a preferred coordinate basis. -/
noncomputable def annihilatorBasis {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0) :
    Module.Basis
      (Module.Basis.ofVectorSpaceIndex ℝ (Annihilator X)) ℝ (Annihilator X) :=
  Module.Basis.ofVectorSpace ℝ (Annihilator X)

theorem annihilatorBasis_finrank_three {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0) :
    Module.finrank ℝ (Annihilator X) = 3 :=
  annihilator_fibre_finrank_three hX0 hXnull

theorem annihilatorBasis_spans {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0) :
    Submodule.span ℝ (Set.range (annihilatorBasis hX0 hXnull)) = ⊤ := by
  exact (annihilatorBasis hX0 hXnull).span_eq

def annihilator_fibre_trace_kernel_equiv (X : Imaginary) :
    Annihilator X ≃ₗ[ℝ] LinearMap.ker (fullAnnihilatorTrace X) :=
  annihilatorFullTraceKerEquiv X

/-! ## A single commuting null packet -/

theorem null_annihilator_projective_packet {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0) :
    Module.finrank ℝ (Annihilator X) = 3 ∧
      Q55 (canonicalConformalLift X.1) = 0 := by
  exact ⟨annihilator_fibre_finrank_three hX0 hXnull,
    canonicalConformalLift_null_of_normLevel hXnull⟩

end InfoGeometry.Canonical.CanonicalZornNullProjectiveBoundaryBridge
