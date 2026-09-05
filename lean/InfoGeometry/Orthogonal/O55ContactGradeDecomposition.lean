import InfoGeometry.Orthogonal.O55ContactHeisenberg

/-!
# Exact five-term decomposition of `so(5,5)`

The nine source/target blocks group into five contact degrees.  For a
split-skew endomorphism, metric-adjoint blocks belong to the same contact
degree, so each grouped component is again in `so(5,5)`.  Their sum is the
original infinitesimal isometry.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

/-- Metric-adjoint partner of a block. -/
def BlockDegree.adjointPartner (d : BlockDegree) : BlockDegree :=
  ⟨d.source.opposite, d.target.opposite⟩

@[simp] theorem BlockDegree.adjointPartner_adjointPartner (d : BlockDegree) :
    d.adjointPartner.adjointPartner = d := by
  cases d
  simp [BlockDegree.adjointPartner]

@[simp] theorem BlockDegree.contact_adjointPartner (d : BlockDegree) :
    d.adjointPartner.contact = d.contact := by
  cases d
  simp [BlockDegree.adjointPartner, BlockDegree.contact]
  ring

/-- A weight projection is adjoint to the opposite weight projection. -/
theorem weightProjector_pairing_move
    (w : Weight3) (x y : Vector55) :
    splitPairing (weightProjector w x) y =
      splitPairing x (weightProjector w.opposite y) := by
  cases w <;>
    simp [splitPairing, weightProjector, weightOfIndex,
      Weight3.opposite]

/-- A source/target block is adjoint to its partner block. -/
theorem blockComponent_pairing
    {A : End55} (hA : IsSplitSkew A)
    (d : BlockDegree) (x y : Vector55) :
    splitPairing (blockComponent d A x) y =
      -splitPairing x (blockComponent d.adjointPartner A y) := by
  have hskew := hA (weightProjector d.source x)
    (weightProjector d.target.opposite y)
  calc
    splitPairing (blockComponent d A x) y =
        splitPairing
          (A (weightProjector d.source x))
          (weightProjector d.target.opposite y) := by
            simp [blockComponent, Module.End.mul_apply,
              weightProjector_pairing_move]
    _ = -splitPairing
          (weightProjector d.source x)
          (A (weightProjector d.target.opposite y)) := by
            linarith
    _ = -splitPairing x
          (weightProjector d.source.opposite
            (A (weightProjector d.target.opposite y))) := by
            rw [weightProjector_pairing_move]
    _ = -splitPairing x (blockComponent d.adjointPartner A y) := by
            rfl

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

theorem endCommutator_add (A B : End55) :
    endCommutator contactEulerEnd (A + B) =
      endCommutator contactEulerEnd A +
        endCommutator contactEulerEnd B := by
  unfold endCommutator
  noncomm_ring

theorem gradeMinusTwoPart_grade (A : End55) :
    endCommutator contactEulerEnd (gradeMinusTwoPart A) =
      (-2 : ℝ) • gradeMinusTwoPart A := by
  simpa [gradeMinusTwoPart, BlockDegree.contact,
    Weight3.value] using
    blockComponent_grade
      (d := BlockDegree.mk Weight3.minus Weight3.plus) A

theorem gradeMinusOnePart_grade (A : End55) :
    endCommutator contactEulerEnd (gradeMinusOnePart A) =
      (-1 : ℝ) • gradeMinusOnePart A := by
  unfold gradeMinusOnePart
  rw [endCommutator_add,
    blockComponent_grade
      (d := BlockDegree.mk Weight3.minus Weight3.zero),
    blockComponent_grade
      (d := BlockDegree.mk Weight3.zero Weight3.plus)]
  simp [BlockDegree.contact, Weight3.value]

theorem gradeZeroPart_grade (A : End55) :
    endCommutator contactEulerEnd (gradeZeroPart A) =
      (0 : ℝ) • gradeZeroPart A := by
  unfold gradeZeroPart
  rw [endCommutator_add, endCommutator_add,
    blockComponent_grade
      (d := BlockDegree.mk Weight3.minus Weight3.minus),
    blockComponent_grade
      (d := BlockDegree.mk Weight3.zero Weight3.zero),
    blockComponent_grade
      (d := BlockDegree.mk Weight3.plus Weight3.plus)]
  simp [BlockDegree.contact, Weight3.value]

theorem gradePlusOnePart_grade (A : End55) :
    endCommutator contactEulerEnd (gradePlusOnePart A) =
      (1 : ℝ) • gradePlusOnePart A := by
  unfold gradePlusOnePart
  rw [endCommutator_add,
    blockComponent_grade
      (d := BlockDegree.mk Weight3.zero Weight3.minus),
    blockComponent_grade
      (d := BlockDegree.mk Weight3.plus Weight3.zero)]
  simp [BlockDegree.contact, Weight3.value]

theorem gradePlusTwoPart_grade (A : End55) :
    endCommutator contactEulerEnd (gradePlusTwoPart A) =
      (2 : ℝ) • gradePlusTwoPart A := by
  simpa [gradePlusTwoPart, BlockDegree.contact,
    Weight3.value] using
    blockComponent_grade
      (d := BlockDegree.mk Weight3.plus Weight3.minus) A

theorem gradeMinusTwoPart_isSplitSkew
    {A : End55} (hA : IsSplitSkew A) :
    IsSplitSkew (gradeMinusTwoPart A) := by
  intro x y
  have h := blockComponent_pairing hA
    (BlockDegree.mk Weight3.minus Weight3.plus) x y
  simp [BlockDegree.adjointPartner, Weight3.opposite] at h
  unfold gradeMinusTwoPart
  linarith

theorem gradeMinusOnePart_isSplitSkew
    {A : End55} (hA : IsSplitSkew A) :
    IsSplitSkew (gradeMinusOnePart A) := by
  intro x y
  have h₁ := blockComponent_pairing hA
    (BlockDegree.mk Weight3.minus Weight3.zero) x y
  have h₂ := blockComponent_pairing hA
    (BlockDegree.mk Weight3.zero Weight3.plus) x y
  simp [BlockDegree.adjointPartner, Weight3.opposite] at h₁ h₂
  simp only [gradeMinusOnePart, LinearMap.add_apply,
    splitPairing_add_left, splitPairing_add_right]
  linarith

theorem gradeZeroPart_isSplitSkew
    {A : End55} (hA : IsSplitSkew A) :
    IsSplitSkew (gradeZeroPart A) := by
  intro x y
  have h₁ := blockComponent_pairing hA
    (BlockDegree.mk Weight3.minus Weight3.minus) x y
  have h₂ := blockComponent_pairing hA
    (BlockDegree.mk Weight3.zero Weight3.zero) x y
  have h₃ := blockComponent_pairing hA
    (BlockDegree.mk Weight3.plus Weight3.plus) x y
  simp [BlockDegree.adjointPartner, Weight3.opposite] at h₁ h₂ h₃
  simp only [gradeZeroPart, LinearMap.add_apply,
    splitPairing_add_left, splitPairing_add_right]
  linarith

theorem gradePlusOnePart_isSplitSkew
    {A : End55} (hA : IsSplitSkew A) :
    IsSplitSkew (gradePlusOnePart A) := by
  intro x y
  have h₁ := blockComponent_pairing hA
    (BlockDegree.mk Weight3.zero Weight3.minus) x y
  have h₂ := blockComponent_pairing hA
    (BlockDegree.mk Weight3.plus Weight3.zero) x y
  simp [BlockDegree.adjointPartner, Weight3.opposite] at h₁ h₂
  simp only [gradePlusOnePart, LinearMap.add_apply,
    splitPairing_add_left, splitPairing_add_right]
  linarith

theorem gradePlusTwoPart_isSplitSkew
    {A : End55} (hA : IsSplitSkew A) :
    IsSplitSkew (gradePlusTwoPart A) := by
  intro x y
  have h := blockComponent_pairing hA
    (BlockDegree.mk Weight3.plus Weight3.minus) x y
  simp [BlockDegree.adjointPartner, Weight3.opposite] at h
  unfold gradePlusTwoPart
  linarith

def gradeMinusTwoProjection (A : O55Lie) : O55Lie :=
  ⟨gradeMinusTwoPart (A : End55),
    gradeMinusTwoPart_isSplitSkew A.property⟩

def gradeMinusOneProjection (A : O55Lie) : O55Lie :=
  ⟨gradeMinusOnePart (A : End55),
    gradeMinusOnePart_isSplitSkew A.property⟩

def gradeZeroProjection (A : O55Lie) : O55Lie :=
  ⟨gradeZeroPart (A : End55),
    gradeZeroPart_isSplitSkew A.property⟩

def gradePlusOneProjection (A : O55Lie) : O55Lie :=
  ⟨gradePlusOnePart (A : End55),
    gradePlusOnePart_isSplitSkew A.property⟩

def gradePlusTwoProjection (A : O55Lie) : O55Lie :=
  ⟨gradePlusTwoPart (A : End55),
    gradePlusTwoPart_isSplitSkew A.property⟩

theorem grade_projection_membership (A : O55Lie) :
    gradeMinusTwoProjection A ∈ contactGradeSpace (-2) ∧
      gradeMinusOneProjection A ∈ contactGradeSpace (-1) ∧
      gradeZeroProjection A ∈ contactGradeSpace 0 ∧
      gradePlusOneProjection A ∈ contactGradeSpace 1 ∧
      gradePlusTwoProjection A ∈ contactGradeSpace 2 := by
  exact ⟨by
      change endCommutator contactEulerEnd (gradeMinusTwoPart (A : End55)) =
        ((-2 : ℤ) : ℝ) • gradeMinusTwoPart (A : End55)
      simpa using gradeMinusTwoPart_grade (A : End55),
    by
      change endCommutator contactEulerEnd (gradeMinusOnePart (A : End55)) =
        ((-1 : ℤ) : ℝ) • gradeMinusOnePart (A : End55)
      simpa using gradeMinusOnePart_grade (A : End55),
    by
      change endCommutator contactEulerEnd (gradeZeroPart (A : End55)) =
        ((0 : ℤ) : ℝ) • gradeZeroPart (A : End55)
      simpa using gradeZeroPart_grade (A : End55),
    by
      change endCommutator contactEulerEnd (gradePlusOnePart (A : End55)) =
        ((1 : ℤ) : ℝ) • gradePlusOnePart (A : End55)
      simpa using gradePlusOnePart_grade (A : End55),
    by
      change endCommutator contactEulerEnd (gradePlusTwoPart (A : End55)) =
        ((2 : ℤ) : ℝ) • gradePlusTwoPart (A : End55)
      simpa using gradePlusTwoPart_grade (A : End55)⟩

theorem five_grade_reconstruction (A : O55Lie) :
    A = gradeMinusTwoProjection A +
      gradeMinusOneProjection A + gradeZeroProjection A +
      gradePlusOneProjection A + gradePlusTwoProjection A := by
  apply Subtype.ext
  have h := full_block_decomposition (A : End55)
  unfold gradeMinusTwoProjection gradeMinusOneProjection gradeZeroProjection
    gradePlusOneProjection gradePlusTwoProjection gradeMinusTwoPart
    gradeMinusOnePart gradeZeroPart gradePlusOnePart gradePlusTwoPart
  rw [h]
  abel

theorem exact_five_grading_packet (A : O55Lie) :
    A = gradeMinusTwoProjection A +
        gradeMinusOneProjection A + gradeZeroProjection A +
        gradePlusOneProjection A + gradePlusTwoProjection A ∧
      gradeMinusTwoProjection A ∈ contactGradeSpace (-2) ∧
      gradeMinusOneProjection A ∈ contactGradeSpace (-1) ∧
      gradeZeroProjection A ∈ contactGradeSpace 0 ∧
      gradePlusOneProjection A ∈ contactGradeSpace 1 ∧
      gradePlusTwoProjection A ∈ contactGradeSpace 2 := by
  rcases grade_projection_membership A with ⟨h₂m, h₁m, h₀, h₁, h₂⟩
  exact ⟨five_grade_reconstruction A, h₂m, h₁m, h₀, h₁, h₂⟩

end InfoGeometry.Orthogonal.O55Contact
