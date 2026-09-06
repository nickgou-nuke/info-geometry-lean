import InfoGeometry.Orthogonal.O55ContactMultiGrading

/-! The five contact-degree projections of an endomorphism. -/

noncomputable section
namespace InfoGeometry.Orthogonal.O55Contact

def gradeMinusTwoPart (A : End55) : End55 :=
  blockComponent ⟨Weight3.minus, Weight3.plus⟩ A

def gradeMinusOnePart (A : End55) : End55 :=
  blockComponent ⟨Weight3.minus, Weight3.zero⟩ A +
    blockComponent ⟨Weight3.zero, Weight3.plus⟩ A

def gradeZeroPart (A : End55) : End55 :=
  blockComponent ⟨Weight3.minus, Weight3.minus⟩ A +
    blockComponent ⟨Weight3.zero, Weight3.zero⟩ A +
    blockComponent ⟨Weight3.plus, Weight3.plus⟩ A

def gradePlusOnePart (A : End55) : End55 :=
  blockComponent ⟨Weight3.zero, Weight3.minus⟩ A +
    blockComponent ⟨Weight3.plus, Weight3.zero⟩ A

def gradePlusTwoPart (A : End55) : End55 :=
  blockComponent ⟨Weight3.plus, Weight3.minus⟩ A

def gradeMinusTwoLinear : End55 →ₗ[ℝ] End55 where
  toFun := gradeMinusTwoPart
  map_add' A B := by
    simpa [gradeMinusTwoPart] using
      blockComponent_add ⟨Weight3.minus, Weight3.plus⟩ A B
  map_smul' c A := by
    simpa [gradeMinusTwoPart] using
      blockComponent_smul ⟨Weight3.minus, Weight3.plus⟩ c A

def gradeMinusOneLinear : End55 →ₗ[ℝ] End55 where
  toFun := gradeMinusOnePart
  map_add' A B := by
    unfold gradeMinusOnePart
    rw [blockComponent_add, blockComponent_add]
    module
  map_smul' c A := by
    unfold gradeMinusOnePart
    rw [blockComponent_smul, blockComponent_smul]
    simp only [smul_add, RingHom.id_apply]

def gradeZeroLinear : End55 →ₗ[ℝ] End55 where
  toFun := gradeZeroPart
  map_add' A B := by
    unfold gradeZeroPart
    rw [blockComponent_add, blockComponent_add, blockComponent_add]
    module
  map_smul' c A := by
    unfold gradeZeroPart
    rw [blockComponent_smul, blockComponent_smul, blockComponent_smul]
    simp only [smul_add, RingHom.id_apply]

def gradePlusOneLinear : End55 →ₗ[ℝ] End55 where
  toFun := gradePlusOnePart
  map_add' A B := by
    unfold gradePlusOnePart
    rw [blockComponent_add, blockComponent_add]
    module
  map_smul' c A := by
    unfold gradePlusOnePart
    rw [blockComponent_smul, blockComponent_smul]
    simp only [smul_add, RingHom.id_apply]

def gradePlusTwoLinear : End55 →ₗ[ℝ] End55 where
  toFun := gradePlusTwoPart
  map_add' A B := by
    simpa [gradePlusTwoPart] using
      blockComponent_add ⟨Weight3.plus, Weight3.minus⟩ A B
  map_smul' c A := by
    simpa [gradePlusTwoPart] using
      blockComponent_smul ⟨Weight3.plus, Weight3.minus⟩ c A

theorem endCommutator_add (A B : End55) :
    endCommutator contactEulerEnd (A + B) =
      endCommutator contactEulerEnd A + endCommutator contactEulerEnd B := by
  unfold endCommutator
  noncomm_ring

theorem gradeMinusTwoPart_grade (A : End55) :
    endCommutator contactEulerEnd (gradeMinusTwoPart A) =
      (-2 : ℝ) • gradeMinusTwoPart A := by
  simpa [gradeMinusTwoPart, BlockDegree.contact, Weight3.valueR,
    Weight3.value] using blockComponent_grade
      (d := ⟨Weight3.minus, Weight3.plus⟩) A

theorem gradeMinusOnePart_grade (A : End55) :
    endCommutator contactEulerEnd (gradeMinusOnePart A) =
      (-1 : ℝ) • gradeMinusOnePart A := by
  unfold gradeMinusOnePart
  rw [endCommutator_add,
    blockComponent_grade (d := ⟨Weight3.minus, Weight3.zero⟩),
    blockComponent_grade (d := ⟨Weight3.zero, Weight3.plus⟩)]
  norm_num [BlockDegree.contact, Weight3.valueR, Weight3.value]
  module

theorem gradeZeroPart_grade (A : End55) :
    endCommutator contactEulerEnd (gradeZeroPart A) =
      (0 : ℝ) • gradeZeroPart A := by
  unfold gradeZeroPart
  rw [endCommutator_add, endCommutator_add,
    blockComponent_grade (d := ⟨Weight3.minus, Weight3.minus⟩),
    blockComponent_grade (d := ⟨Weight3.zero, Weight3.zero⟩),
    blockComponent_grade (d := ⟨Weight3.plus, Weight3.plus⟩)]
  norm_num [BlockDegree.contact, Weight3.valueR, Weight3.value]

theorem gradePlusOnePart_grade (A : End55) :
    endCommutator contactEulerEnd (gradePlusOnePart A) =
      (1 : ℝ) • gradePlusOnePart A := by
  unfold gradePlusOnePart
  rw [endCommutator_add,
    blockComponent_grade (d := ⟨Weight3.zero, Weight3.minus⟩),
    blockComponent_grade (d := ⟨Weight3.plus, Weight3.zero⟩)]
  norm_num [BlockDegree.contact, Weight3.valueR, Weight3.value]

theorem gradePlusTwoPart_grade (A : End55) :
    endCommutator contactEulerEnd (gradePlusTwoPart A) =
      (2 : ℝ) • gradePlusTwoPart A := by
  simpa [gradePlusTwoPart, BlockDegree.contact, Weight3.valueR,
    Weight3.value] using blockComponent_grade
      (d := ⟨Weight3.plus, Weight3.minus⟩) A

theorem endomorphism_grade_decomposition (A : End55) :
    A =
      gradeMinusTwoPart A + gradeMinusOnePart A + gradeZeroPart A +
        gradePlusOnePart A + gradePlusTwoPart A := by
  have hres := weightProjector_resolution
  unfold gradeMinusTwoPart gradeMinusOnePart gradeZeroPart
    gradePlusOnePart gradePlusTwoPart blockComponent
  calc
    A = (1 : End55) * A * 1 := by simp
    _ = (weightProjector Weight3.minus + weightProjector Weight3.zero +
          weightProjector Weight3.plus) * A *
        (weightProjector Weight3.minus + weightProjector Weight3.zero +
          weightProjector Weight3.plus) := by rw [hres]
    _ = _ := by noncomm_ring

theorem gradeMinusTwoPart_isSplitSkew
    {A : End55} (hA : IsSplitSkew A) :
    IsSplitSkew (gradeMinusTwoPart A) := by
  intro x y
  have h := blockComponent_pairing hA
    ⟨Weight3.minus, Weight3.plus⟩ x y
  simp [gradeMinusTwoPart, BlockDegree.adjointPartner, Weight3.opposite] at h
  change splitPairing (blockComponent ⟨Weight3.minus, Weight3.plus⟩ A x) y +
    splitPairing x (blockComponent ⟨Weight3.minus, Weight3.plus⟩ A y) = 0
  linarith

theorem gradeMinusOnePart_isSplitSkew
    {A : End55} (hA : IsSplitSkew A) :
    IsSplitSkew (gradeMinusOnePart A) := by
  intro x y
  have h₁ := blockComponent_pairing hA
    ⟨Weight3.minus, Weight3.zero⟩ x y
  have h₂ := blockComponent_pairing hA
    ⟨Weight3.zero, Weight3.plus⟩ x y
  simp [gradeMinusOnePart, BlockDegree.adjointPartner, Weight3.opposite,
    LinearMap.add_apply, splitPairing_add_left, splitPairing_add_right] at h₁ h₂ ⊢
  linarith

theorem gradeZeroPart_isSplitSkew
    {A : End55} (hA : IsSplitSkew A) :
    IsSplitSkew (gradeZeroPart A) := by
  intro x y
  have h₁ := blockComponent_pairing hA
    ⟨Weight3.minus, Weight3.minus⟩ x y
  have h₂ := blockComponent_pairing hA
    ⟨Weight3.zero, Weight3.zero⟩ x y
  have h₃ := blockComponent_pairing hA
    ⟨Weight3.plus, Weight3.plus⟩ x y
  simp [gradeZeroPart, BlockDegree.adjointPartner, Weight3.opposite,
    LinearMap.add_apply, splitPairing_add_left, splitPairing_add_right] at h₁ h₂ h₃ ⊢
  linarith

theorem gradePlusOnePart_isSplitSkew
    {A : End55} (hA : IsSplitSkew A) :
    IsSplitSkew (gradePlusOnePart A) := by
  intro x y
  have h₁ := blockComponent_pairing hA
    ⟨Weight3.zero, Weight3.minus⟩ x y
  have h₂ := blockComponent_pairing hA
    ⟨Weight3.plus, Weight3.zero⟩ x y
  simp [gradePlusOnePart, BlockDegree.adjointPartner, Weight3.opposite,
    LinearMap.add_apply, splitPairing_add_left, splitPairing_add_right] at h₁ h₂ ⊢
  linarith

theorem gradePlusTwoPart_isSplitSkew
    {A : End55} (hA : IsSplitSkew A) :
    IsSplitSkew (gradePlusTwoPart A) := by
  intro x y
  have h := blockComponent_pairing hA
    ⟨Weight3.plus, Weight3.minus⟩ x y
  simp [gradePlusTwoPart, BlockDegree.adjointPartner, Weight3.opposite] at h
  change splitPairing (blockComponent ⟨Weight3.plus, Weight3.minus⟩ A x) y +
    splitPairing x (blockComponent ⟨Weight3.plus, Weight3.minus⟩ A y) = 0
  linarith

def gradeMinusTwoProjection (A : O55Lie) : O55Lie :=
  ⟨gradeMinusTwoPart (A : End55), gradeMinusTwoPart_isSplitSkew A.property⟩
def gradeMinusOneProjection (A : O55Lie) : O55Lie :=
  ⟨gradeMinusOnePart (A : End55), gradeMinusOnePart_isSplitSkew A.property⟩
def gradeZeroProjection (A : O55Lie) : O55Lie :=
  ⟨gradeZeroPart (A : End55), gradeZeroPart_isSplitSkew A.property⟩
def gradePlusOneProjection (A : O55Lie) : O55Lie :=
  ⟨gradePlusOnePart (A : End55), gradePlusOnePart_isSplitSkew A.property⟩
def gradePlusTwoProjection (A : O55Lie) : O55Lie :=
  ⟨gradePlusTwoPart (A : End55), gradePlusTwoPart_isSplitSkew A.property⟩

def gradeMinusTwoProjectionLinear : O55Lie →ₗ[ℝ] O55Lie where
  toFun := gradeMinusTwoProjection
  map_add' A B := by
    apply Subtype.ext
    exact congrArg id (gradeMinusTwoLinear.map_add (A : End55) (B : End55))
  map_smul' c A := by
    apply Subtype.ext
    exact congrArg id (gradeMinusTwoLinear.map_smul c (A : End55))

def gradeMinusOneProjectionLinear : O55Lie →ₗ[ℝ] O55Lie where
  toFun := gradeMinusOneProjection
  map_add' A B := by
    apply Subtype.ext
    exact congrArg id (gradeMinusOneLinear.map_add (A : End55) (B : End55))
  map_smul' c A := by
    apply Subtype.ext
    exact congrArg id (gradeMinusOneLinear.map_smul c (A : End55))

def gradeZeroProjectionLinear : O55Lie →ₗ[ℝ] O55Lie where
  toFun := gradeZeroProjection
  map_add' A B := by
    apply Subtype.ext
    exact congrArg id (gradeZeroLinear.map_add (A : End55) (B : End55))
  map_smul' c A := by
    apply Subtype.ext
    exact congrArg id (gradeZeroLinear.map_smul c (A : End55))

def gradePlusOneProjectionLinear : O55Lie →ₗ[ℝ] O55Lie where
  toFun := gradePlusOneProjection
  map_add' A B := by
    apply Subtype.ext
    exact congrArg id (gradePlusOneLinear.map_add (A : End55) (B : End55))
  map_smul' c A := by
    apply Subtype.ext
    exact congrArg id (gradePlusOneLinear.map_smul c (A : End55))

def gradePlusTwoProjectionLinear : O55Lie →ₗ[ℝ] O55Lie where
  toFun := gradePlusTwoProjection
  map_add' A B := by
    apply Subtype.ext
    exact congrArg id (gradePlusTwoLinear.map_add (A : End55) (B : End55))
  map_smul' c A := by
    apply Subtype.ext
    exact congrArg id (gradePlusTwoLinear.map_smul c (A : End55))

theorem grade_projection_reconstruct (A : O55Lie) :
    A = gradeMinusTwoProjection A + gradeMinusOneProjection A +
      gradeZeroProjection A + gradePlusOneProjection A +
      gradePlusTwoProjection A := by
  apply Subtype.ext
  exact endomorphism_grade_decomposition (A : End55)

theorem grade_projection_linear_sum :
    gradeMinusTwoProjectionLinear + gradeMinusOneProjectionLinear +
        gradeZeroProjectionLinear + gradePlusOneProjectionLinear +
        gradePlusTwoProjectionLinear = LinearMap.id := by
  apply LinearMap.ext
  intro A
  apply Subtype.ext
  simpa [gradeMinusTwoProjectionLinear, gradeMinusOneProjectionLinear,
    gradeZeroProjectionLinear, gradePlusOneProjectionLinear,
    gradePlusTwoProjectionLinear] using
    congrArg (fun Z : O55Lie => (Z : End55))
      (grade_projection_reconstruct A).symm

theorem grade_projection_membership (A : O55Lie) :
    gradeMinusTwoProjection A ∈ realContactGradeSpace (-2) ∧
      gradeMinusOneProjection A ∈ realContactGradeSpace (-1) ∧
      gradeZeroProjection A ∈ realContactGradeSpace 0 ∧
      gradePlusOneProjection A ∈ realContactGradeSpace 1 ∧
      gradePlusTwoProjection A ∈ realContactGradeSpace 2 := by
  exact ⟨by
      change IsContactGrade (-2) (gradeMinusTwoProjection A)
      change endCommutator contactEulerEnd (gradeMinusTwoPart (A : End55)) =
        ((-2 : ℤ) : ℝ) • gradeMinusTwoPart (A : End55)
      simpa using gradeMinusTwoPart_grade (A : End55),
    by
      change IsContactGrade (-1) (gradeMinusOneProjection A)
      change endCommutator contactEulerEnd (gradeMinusOnePart (A : End55)) =
        ((-1 : ℤ) : ℝ) • gradeMinusOnePart (A : End55)
      simpa using gradeMinusOnePart_grade (A : End55),
    by
      change IsContactGrade 0 (gradeZeroProjection A)
      change endCommutator contactEulerEnd (gradeZeroPart (A : End55)) =
        ((0 : ℤ) : ℝ) • gradeZeroPart (A : End55)
      simpa using gradeZeroPart_grade (A : End55),
    by
      change IsContactGrade 1 (gradePlusOneProjection A)
      change endCommutator contactEulerEnd (gradePlusOnePart (A : End55)) =
        ((1 : ℤ) : ℝ) • gradePlusOnePart (A : End55)
      simpa using gradePlusOnePart_grade (A : End55),
    by
      change IsContactGrade 2 (gradePlusTwoProjection A)
      change endCommutator contactEulerEnd (gradePlusTwoPart (A : End55)) =
        ((2 : ℤ) : ℝ) • gradePlusTwoPart (A : End55)
      simpa using gradePlusTwoPart_grade (A : End55)⟩

end InfoGeometry.Orthogonal.O55Contact
