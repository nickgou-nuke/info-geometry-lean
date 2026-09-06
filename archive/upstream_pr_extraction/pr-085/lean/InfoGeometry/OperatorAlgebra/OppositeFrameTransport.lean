import InfoGeometry.OperatorAlgebra.CPTCommutantSpinFrame

/-!
# Opposite-frame transport

These are purely algebraic intertwining lemmas.  They transport products and
commutators through a map; they do not identify an arbitrary operator with a
geometric connection or curvature.
-/

namespace InfoGeometry.OperatorAlgebra.SpectralTriple

def intertwines {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (R L τ : EndR H) : Prop :=
  R.comp τ = τ.comp L

def intertwinerDefect {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (R L τ : EndR H) : EndR H :=
  R.comp τ - τ.comp L

theorem intertwinerDefect_eq_zero_of_intertwines
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {R L τ : EndR H}
    (h : intertwines R L τ) :
    intertwinerDefect R L τ = 0 := by
  dsimp [intertwinerDefect]
  rw [h, sub_self]

theorem oppositeRep_intertwinerDefect_zero
    {A H : Type*}
    [Ring A] [StarRing A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H} {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs) (b : A) :
    intertwinerDefect
      (oppositeRep ρ J b)
      (ρ.rep (star b))
      J.J.val = 0 := by
  apply intertwinerDefect_eq_zero_of_intertwines
  exact oppositeRep_comp_realStructure ρ J b

/-! The RingHom image is the opposite/commutant frame once the
order-zero law is supplied.  This is an inclusion statement; it does not
assert that the image exhausts the full commutant. -/
theorem oppositeRepRingHom_commutes_with_rep
    {A H : Type*}
    [Ring A] [StarRing A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H} {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs)
    (hzero : ∀ a b : A,
      (ρ.rep a).comp (oppositeRep ρ J b) =
        (oppositeRep ρ J b).comp (ρ.rep a))
    (a : A) (b : Aᵐᵒᵖ) :
    (ρ.rep a).comp ((oppositeRepRingHom ρ J) b) =
      ((oppositeRepRingHom ρ J) b).comp (ρ.rep a) := by
  change (ρ.rep a).comp (oppositeRep ρ J b.unop) =
    (oppositeRep ρ J b.unop).comp (ρ.rep a)
  exact hzero a b.unop

/-! Heterogeneous sheet transport.  The source and target carriers are kept
distinct in the type of the transport map, so this layer is an operator
intertwiner defect rather than a differential-geometric connection. -/
def relativeIntertwinerDefect
    {HL HR : Type*}
    [NormedAddCommGroup HL] [NormedSpace ℝ HL]
    [NormedAddCommGroup HR] [NormedSpace ℝ HR]
    (nablaL : HL →L[ℝ] HL)
    (nablaR : HR →L[ℝ] HR)
    (τ : HL →L[ℝ] HR) : HL →L[ℝ] HR :=
  nablaR.comp τ - τ.comp nablaL

theorem relativeIntertwinerDefect_eq_zero_iff
    {HL HR : Type*}
    [NormedAddCommGroup HL] [NormedSpace ℝ HL]
    [NormedAddCommGroup HR] [NormedSpace ℝ HR]
    (nablaL : HL →L[ℝ] HL)
    (nablaR : HR →L[ℝ] HR)
    (τ : HL →L[ℝ] HR) :
    relativeIntertwinerDefect nablaL nablaR τ = 0 ↔
      nablaR.comp τ = τ.comp nablaL := by
  simp [relativeIntertwinerDefect, sub_eq_zero]

def relativeCurvatureDefect
    {HL HR : Type*}
    [NormedAddCommGroup HL] [NormedSpace ℝ HL]
    [NormedAddCommGroup HR] [NormedSpace ℝ HR]
    (FL : HL →L[ℝ] HL)
    (FR : HR →L[ℝ] HR)
    (τ : HL →L[ℝ] HR) : HL →L[ℝ] HR :=
  FR.comp τ - τ.comp FL

theorem relativeCurvatureDefect_eq_zero_iff
    {HL HR : Type*}
    [NormedAddCommGroup HL] [NormedSpace ℝ HL]
    [NormedAddCommGroup HR] [NormedSpace ℝ HR]
    (FL : HL →L[ℝ] HL)
    (FR : HR →L[ℝ] HR)
    (τ : HL →L[ℝ] HR) :
    relativeCurvatureDefect FL FR τ = 0 ↔
      FR.comp τ = τ.comp FL := by
  simp [relativeCurvatureDefect, sub_eq_zero]

theorem relativeCurvatureDefect_sq
    {HL HR : Type*}
    [NormedAddCommGroup HL] [NormedSpace ℝ HL]
    [NormedAddCommGroup HR] [NormedSpace ℝ HR]
    (nablaL : HL →L[ℝ] HL)
    (nablaR : HR →L[ℝ] HR)
    (τ : HL →L[ℝ] HR) :
    relativeCurvatureDefect
        (nablaL.comp nablaL)
        (nablaR.comp nablaR)
        τ =
      nablaR.comp (relativeIntertwinerDefect nablaL nablaR τ) +
        (relativeIntertwinerDefect nablaL nablaR τ).comp nablaL := by
  ext x
  simp [relativeCurvatureDefect, relativeIntertwinerDefect]

theorem relativeCurvatureDefect_sq_eq_zero_of_parallel
    {HL HR : Type*}
    [NormedAddCommGroup HL] [NormedSpace ℝ HL]
    [NormedAddCommGroup HR] [NormedSpace ℝ HR]
    (nablaL : HL →L[ℝ] HL)
    (nablaR : HR →L[ℝ] HR)
    (τ : HL →L[ℝ] HR)
    (hτ : relativeIntertwinerDefect nablaL nablaR τ = 0) :
    relativeCurvatureDefect
        (nablaL.comp nablaL)
        (nablaR.comp nablaR)
        τ = 0 := by
  rw [relativeCurvatureDefect_sq nablaL nablaR τ, hτ]
  simp

theorem intertwines_comp
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {R₁ R₂ L₁ L₂ τ : EndR H}
    (h₁ : intertwines R₁ L₁ τ)
    (h₂ : intertwines R₂ L₂ τ) :
    intertwines (R₂.comp R₁) (L₂.comp L₁) τ := by
  ext x
  change R₂ (R₁ (τ x)) = τ (L₂ (L₁ x))
  change R₁.comp τ = τ.comp L₁ at h₁
  change R₂.comp τ = τ.comp L₂ at h₂
  have h₁x : R₁ (τ x) = τ (L₁ x) := by
    simpa using congrArg (fun T : EndR H => T x) h₁
  have h₂x : R₂ (τ (L₁ x)) = τ (L₂ (L₁ x)) := by
    simpa using congrArg (fun T : EndR H => T (L₁ x)) h₂
  calc
    R₂ (R₁ (τ x)) = R₂ (τ (L₁ x)) := congrArg R₂ h₁x
    _ = τ (L₂ (L₁ x)) := h₂x

def operatorCommutator {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (X Y : EndR H) : EndR H := X.comp Y - Y.comp X

theorem oppositeRep_sourceCommutator
    {A H : Type*}
    [Ring A] [StarRing A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H} {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs)
    (a b : A) :
    oppositeRep ρ J (a * b - b * a) =
      -operatorCommutator (oppositeRep ρ J a) (oppositeRep ρ J b) := by
  rw [oppositeRep_sub, oppositeRep_mul, oppositeRep_mul]
  ext x
  simp [operatorCommutator]

theorem intertwines_commutator
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {R₁ R₂ L₁ L₂ τ : EndR H}
    (h₁ : intertwines R₁ L₁ τ)
    (h₂ : intertwines R₂ L₂ τ) :
    intertwines (operatorCommutator R₂ R₁)
      (operatorCommutator L₂ L₁) τ := by
  change R₂.comp τ = τ.comp L₂ at h₂
  change R₁.comp τ = τ.comp L₁ at h₁
  ext x
  simp only [operatorCommutator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply]
  have h₂L₁x : R₂ (τ (L₁ x)) = τ (L₂ (L₁ x)) := by
    simpa using congrArg (fun T : EndR H => T (L₁ x)) h₂
  have h₁L₂x : R₁ (τ (L₂ x)) = τ (L₁ (L₂ x)) := by
    simpa using congrArg (fun T : EndR H => T (L₂ x)) h₁
  have h₁x : R₁ (τ x) = τ (L₁ x) := by
    simpa using congrArg (fun T : EndR H => T x) h₁
  have h₂x : R₂ (τ x) = τ (L₂ x) := by
    simpa using congrArg (fun T : EndR H => T x) h₂
  rw [h₁x, h₂L₁x, h₂x, h₁L₂x]
  rw [map_sub]

end InfoGeometry.OperatorAlgebra.SpectralTriple
