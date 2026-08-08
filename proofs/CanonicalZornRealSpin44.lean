import proofs.CanonicalZornCliffordRepresentation

/-!
# Real split `(4,4)` Clifford and spin action through canonical Zorn triality

This file supplies the real-form bridge missing from the complex composition
triality construction.  The vector carrier is the standard diagonal real
quadratic space `ℝ⁴ ⊕ ℝ⁴`.  Its explicit linear embedding into the
typed canonical Zorn vector copy preserves the `(4,4)` quadratic form.

Restricting the complex Zorn gamma operators to real scalars gives a genuine
representation of the real Clifford algebra, and hence a group representation
of Mathlib's spin group.  The target is the underlying real general linear
group of the complex Dirac carrier; no irreducibility assertion is made.
-/

noncomputable section

namespace CanonicalZornRealSpin44

set_option synthInstance.maxHeartbeats 100000

open SplitOctonionBraidSU3
open CanonicalZornFiveGradedClosure
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open ProjectiveAffineConformalClosure55
open CanonicalZornProjectiveTKKBridge

/-! ## Standard real split quadratic carrier -/

abbrev RealSplit44 := (Fin 4 → ℝ) × (Fin 4 → ℝ)

def realCoord4 (i : Fin 4) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def realEuclidean4 : QuadraticForm ℝ (Fin 4 → ℝ) :=
  ∑ i : Fin 4, QuadraticMap.linMulLin (realCoord4 i) (realCoord4 i)

def realSplitFst : RealSplit44 →ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearMap.fst ℝ (Fin 4 → ℝ) (Fin 4 → ℝ)

def realSplitSnd : RealSplit44 →ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearMap.snd ℝ (Fin 4 → ℝ) (Fin 4 → ℝ)

/-- Standard diagonal quadratic form of signature `(4,4)`. -/
noncomputable def realQuadratic44 : QuadraticForm ℝ RealSplit44 :=
  realEuclidean4.comp realSplitFst - realEuclidean4.comp realSplitSnd

@[simp] theorem realEuclidean4_apply (x : Fin 4 → ℝ) :
    realEuclidean4 x = ∑ i, x i ^ 2 := by
  simp [realEuclidean4, QuadraticMap.linMulLin, realCoord4, pow_two]

@[simp] theorem realQuadratic44_apply (x : RealSplit44) :
    realQuadratic44 x = ∑ i, x.1 i ^ 2 - ∑ i, x.2 i ^ 2 := by
  simp [realQuadratic44, realSplitFst, realSplitSnd]

/-! ## Isometric embedding into the typed Zorn vector copy -/

/-- Diagonal split coordinates in the complex eight-coordinate presentation. -/
def realSplit44Coordinates : RealSplit44 →ₗ[ℝ] (Fin 8 → ℂ) where
  toFun x := ![
    (x.1 0 + x.2 0 : ℝ),
    (x.1 1 + x.2 1 : ℝ),
    (x.1 2 + x.2 2 : ℝ),
    (x.1 3 + x.2 3 : ℝ),
    (x.2 1 - x.1 1 : ℝ),
    (x.2 2 - x.1 2 : ℝ),
    (x.2 3 - x.1 3 : ℝ),
    (x.1 0 - x.2 0 : ℝ)]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

/-- Diagonal split coordinates mapped linearly to the typed Zorn vector copy. -/
def realSplit44ToVector8 : RealSplit44 →ₗ[ℝ] Vector8 :=
  ((copyLinearEquivCoordinates TrialitySector.vector).symm.restrictScalars ℝ).comp
    realSplit44Coordinates

theorem vectorQuadratic_realSplit44ToVector8 (x : RealSplit44) :
    vectorQuadratic (realSplit44ToVector8 x) = (realQuadratic44 x : ℂ) := by
  rw [vectorQuadratic_apply]
  simp [vectorNorm, realSplit44ToVector8, realSplit44Coordinates,
    copyLinearEquivCoordinates, copyEquivCoordinates, zornNorm, dot3,
    coordinatesToZorn, realQuadratic44_apply, Fin.sum_univ_four]
  ring

/-- Real-coordinate inverse on the image of `realSplit44ToVector8`. -/
def vector8ToRealSplit44 (V : Vector8) : RealSplit44 :=
  (![(V.val.a.re + V.val.b.re) / 2,
      ((V.val.u 0).re - (V.val.v 0).re) / 2,
      ((V.val.u 1).re - (V.val.v 1).re) / 2,
      ((V.val.u 2).re - (V.val.v 2).re) / 2],
   ![(V.val.a.re - V.val.b.re) / 2,
      ((V.val.u 0).re + (V.val.v 0).re) / 2,
      ((V.val.u 1).re + (V.val.v 1).re) / 2,
      ((V.val.u 2).re + (V.val.v 2).re) / 2])

theorem vector8ToRealSplit44_leftInverse (x : RealSplit44) :
    vector8ToRealSplit44 (realSplit44ToVector8 x) = x := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [vector8ToRealSplit44, realSplit44ToVector8,
      realSplit44Coordinates, copyLinearEquivCoordinates,
      copyEquivCoordinates, coordinatesToZorn] <;>
    ring

theorem realSplit44ToVector8_injective :
    Function.Injective realSplit44ToVector8 :=
  Function.LeftInverse.injective vector8ToRealSplit44_leftInverse

/-! ## Compatibility with the affine conformal projective carrier -/

def realSplit44ToPAC44 (x : RealSplit44) : PACSplit44 where
  x0 := x.1 0
  x1 := x.1 1
  x2 := x.1 2
  x3 := x.1 3
  y0 := x.2 0
  y1 := x.2 1
  y2 := x.2 2
  y3 := x.2 3

theorem Q44_realSplit44ToPAC44 (x : RealSplit44) :
    Q44 (realSplit44ToPAC44 x) = realQuadratic44 x := by
  simp [Q44, realSplit44ToPAC44, realQuadratic44_apply,
    Fin.sum_univ_four]

theorem realSplit44_projective_null (x : RealSplit44) :
    Q55 (conformalEmbed44to55 (realSplit44ToPAC44 x)) = 0 :=
  conformalEmbed44to55_null _

theorem realSplit44ToVector8_eq_canonical (x : RealSplit44) :
    realSplit44ToVector8 x =
      realVector8 (pac44ToCoreZorn (realSplit44ToPAC44 x)) := by
  apply ZornCopy.ext
  apply zornCoordinates_injective
  funext i
  fin_cases i <;>
    simp [realSplit44ToVector8, realSplit44Coordinates,
      copyLinearEquivCoordinates, copyEquivCoordinates, realVector8,
      coreToCanonical, pac44ToCoreZorn, realSplit44ToPAC44,
      zornCoordinates, coordinatesToZorn]

theorem realSplit44_vector_grade_plus (x : RealSplit44) :
    vectorGradePlus (realSplit44ToVector8 x) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 :=
  vectorGradePlus_mem _

/-! ## Real Clifford representation and spin action -/

/-- Forget complex linearity of an endomorphism while retaining real
linearity. -/
def restrictComplexEnd :
    Module.End ℂ DiracSpinor16 →ₗ[ℝ] Module.End ℝ DiracSpinor16 where
  toFun f := f.restrictScalars ℝ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Real gamma map obtained from the canonical Zorn gamma operators. -/
def realGammaLinear :
    RealSplit44 →ₗ[ℝ] Module.End ℝ DiracSpinor16 :=
  restrictComplexEnd.comp
    ((diracGammaLinear.restrictScalars ℝ).comp realSplit44ToVector8)

theorem realGammaLinear_apply (x : RealSplit44) :
    realGammaLinear x = (diracGamma (realSplit44ToVector8 x)).restrictScalars ℝ :=
  rfl

theorem realGamma_sq (x : RealSplit44) :
    realGammaLinear x * realGammaLinear x =
      algebraMap ℝ (Module.End ℝ DiracSpinor16) (realQuadratic44 x) := by
  apply LinearMap.ext
  intro Ψ
  change diracGamma (realSplit44ToVector8 x)
      (diracGamma (realSplit44ToVector8 x) Ψ) = realQuadratic44 x • Ψ
  rw [diracGamma_sq_apply, vectorQuadratic_realSplit44ToVector8]
  rfl

/-- Real Clifford algebra `Cl(4,4)` acting on the underlying real Dirac
carrier through canonical Zorn multiplication. -/
def realClifford44Representation :
    CliffordAlgebra realQuadratic44 →ₐ[ℝ] Module.End ℝ DiracSpinor16 :=
  CliffordAlgebra.lift realQuadratic44 ⟨realGammaLinear, realGamma_sq⟩

@[simp] theorem realClifford44Representation_ι (x : RealSplit44) :
    realClifford44Representation (CliffordAlgebra.ι realQuadratic44 x) =
      realGammaLinear x := by
  exact CliffordAlgebra.lift_ι_apply realGammaLinear realGamma_sq x

/-- Genuine group representation of the real split spin group associated to
the explicitly defined `(4,4)` quadratic form. -/
def realSpin44DiracRepresentation :
    spinGroup realQuadratic44 →*
      LinearMap.GeneralLinearGroup ℝ DiracSpinor16 :=
  (Units.map realClifford44Representation.toRingHom.toMonoidHom).comp
    spinGroup.toUnits

theorem realSpin44DiracRepresentation_val
    (g : spinGroup realQuadratic44) :
    ((realSpin44DiracRepresentation g :
      LinearMap.GeneralLinearGroup ℝ DiracSpinor16) :
        Module.End ℝ DiracSpinor16) =
      realClifford44Representation (g : CliffordAlgebra realQuadratic44) := by
  change
    ((Units.map realClifford44Representation.toRingHom.toMonoidHom)
      (spinGroup.toUnits g) : Module.End ℝ DiracSpinor16) = _
  simp

/-- The real `(4,4)` quadratic form, its canonical Zorn isometry, its Clifford
action, and the induced spin-group representation coexist in one theorem. -/
theorem real_spin44_zorn_triality_closure (x : RealSplit44) :
    Q55 (conformalEmbed44to55 (realSplit44ToPAC44 x)) = 0 ∧
    vectorGradePlus (realSplit44ToVector8 x) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    vectorQuadratic (realSplit44ToVector8 x) = (realQuadratic44 x : ℂ) ∧
    realClifford44Representation (CliffordAlgebra.ι realQuadratic44 x) =
      realGammaLinear x ∧
    realGammaLinear x * realGammaLinear x =
      algebraMap ℝ (Module.End ℝ DiracSpinor16) (realQuadratic44 x) := by
  exact ⟨realSplit44_projective_null x, realSplit44_vector_grade_plus x,
    vectorQuadratic_realSplit44ToVector8 x,
    realClifford44Representation_ι x, realGamma_sq x⟩

end CanonicalZornRealSpin44

end noncomputable section
