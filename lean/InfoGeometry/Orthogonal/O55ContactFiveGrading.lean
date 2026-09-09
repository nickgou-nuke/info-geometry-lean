import InfoGeometry.Orthogonal.O55WittRootRepresentation

/-!
# Multiweight spaces and the `|2|` five-grading of split `O(5,5)`

The five diagonal Witt-Cartan operators define a simultaneous `ℤ⁵`
multigrading.  Their sum on the first two axes defines the contact Euler
operator and the collapsed grades `-2,-1,0,1,2`.

All grade-addition results are proved inside the associative matrix algebra;
therefore Jacobi and derivation identities are inherited rather than assumed.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

open scoped Matrix
open InfoGeometry.Orthogonal.O55D5
open InfoGeometry.Orthogonal.O55Witt

/-- Coefficient of the `a`th Cartan basis element. -/
def axisCartanCoefficient (a : Axis) : Axis → ℂ := fun b =>
  if b = a then 1 else 0

/-- The five commuting coordinate Cartan matrices. -/
def axisCartanMatrix (a : Axis) : Mat10 :=
  cartanMatrix (axisCartanCoefficient a)

@[simp] theorem axisCartanMatrix_mem_o55 (a : Axis) :
    IsSplitOrthogonal (axisCartanMatrix a) := by
  exact wittAdjoint_cartanMatrix _

/-- The root character against one coordinate Cartan is precisely the
corresponding integral multidegree. -/
theorem rootCharacter_axis (a : Axis) (r : Root) :
    rootCharacter (axisCartanCoefficient a) r =
      (r.multiDegree a : ℂ) := by
  by_cases hai : a = r.i
  · subst a
    have hne : r.i ≠ r.j := r.i_ne_j
    simp [rootCharacter, axisCartanCoefficient, Root.multiDegree, hne,
      hne.symm]
  · by_cases haj : a = r.j
    · subst a
      have hne : r.j ≠ r.i := r.i_ne_j.symm
      simp [rootCharacter, axisCartanCoefficient, Root.multiDegree,
        hai, hne]
    · simp [rootCharacter, axisCartanCoefficient, Root.multiDegree,
        hai, haj, Ne.symm hai, Ne.symm haj]

/-- Root matrices are simultaneous eigenvectors for all five Cartan
coordinates. -/
theorem axisCartan_rootMatrix (a : Axis) (r : Root) :
    axisCartanMatrix a * rootMatrix r -
        rootMatrix r * axisCartanMatrix a =
      (r.multiDegree a : ℂ) • rootMatrix r := by
  rw [axisCartanMatrix, cartan_commutator_rootMatrix,
    rootCharacter_axis]

/-- Simultaneous multigraded eigenspace in the full matrix algebra. -/
def multiWeightSpace (μ : Axis → ℂ) : Submodule ℂ Mat10 where
  carrier := {X | ∀ a,
    axisCartanMatrix a * X - X * axisCartanMatrix a = μ a • X}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY a
    calc
      axisCartanMatrix a * (X + Y) - (X + Y) * axisCartanMatrix a =
          (axisCartanMatrix a * X - X * axisCartanMatrix a) +
            (axisCartanMatrix a * Y - Y * axisCartanMatrix a) := by
              noncomm_ring
      _ = μ a • X + μ a • Y := by rw [hX a, hY a]
      _ = μ a • (X + Y) := by rw [smul_add]
  smul_mem' := by
    intro c X hX a
    calc
      axisCartanMatrix a * (c • X) - (c • X) * axisCartanMatrix a =
          c • (axisCartanMatrix a * X - X * axisCartanMatrix a) := by
            simp [sub_eq_add_neg]
      _ = c • (μ a • X) := by rw [hX a]
      _ = μ a • (c • X) := by simp [smul_smul, mul_comm]

/-- The collapsed contact-grade eigenspace in the full matrix algebra. -/
def contactGradeSpace (k : ℂ) : Submodule ℂ Mat10 where
  carrier := {X |
    contactGradingMatrix * X - X * contactGradingMatrix = k • X}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    calc
      contactGradingMatrix * (X + Y) - (X + Y) * contactGradingMatrix =
          (contactGradingMatrix * X - X * contactGradingMatrix) +
            (contactGradingMatrix * Y - Y * contactGradingMatrix) := by
              noncomm_ring
      _ = k • X + k • Y := by rw [hX, hY]
      _ = k • (X + Y) := by rw [smul_add]
  smul_mem' := by
    intro c X hX
    calc
      contactGradingMatrix * (c • X) - (c • X) * contactGradingMatrix =
          c • (contactGradingMatrix * X - X * contactGradingMatrix) := by
            simp [sub_eq_add_neg]
      _ = c • (k • X) := by rw [hX]
      _ = k • (c • X) := by simp [smul_smul, mul_comm]

/-- Root matrix in its exact `ℤ⁵` multiweight space. -/
theorem rootMatrix_mem_multiWeightSpace (r : Root) :
    rootMatrix r ∈ multiWeightSpace
      (fun a => (r.multiDegree a : ℂ)) := by
  intro a
  exact axisCartan_rootMatrix a r

/-- Root matrix in its collapsed contact grade. -/
theorem rootMatrix_mem_contactGradeSpace (r : Root) :
    rootMatrix r ∈ contactGradeSpace (r.contactDegree : ℂ) :=
  contactGrading_rootMatrix r

/-- Every Cartan matrix has contact degree zero. -/
theorem cartanMatrix_mem_contactGradeZero (h : Axis → ℂ) :
    cartanMatrix h ∈ contactGradeSpace 0 := by
  change contactGradingMatrix * cartanMatrix h -
      cartanMatrix h * contactGradingMatrix = 0 • cartanMatrix h
  change cartanMatrix _ * cartanMatrix h - cartanMatrix h * cartanMatrix _ = _
  rw [cartanMatrix_commute]
  simp

/-- Simultaneous multiweights add under the commutator. -/
theorem commutator_mem_multiWeightSpace
    {μ ν : Axis → ℂ} {X Y : Mat10}
    (hX : X ∈ multiWeightSpace μ)
    (hY : Y ∈ multiWeightSpace ν) :
    X * Y - Y * X ∈ multiWeightSpace (fun a => μ a + ν a) := by
  intro a
  have hx := hX a
  have hy := hY a
  calc
    axisCartanMatrix a * (X * Y - Y * X) -
        (X * Y - Y * X) * axisCartanMatrix a =
      (axisCartanMatrix a * X - X * axisCartanMatrix a) * Y +
        X * (axisCartanMatrix a * Y - Y * axisCartanMatrix a) -
      ((axisCartanMatrix a * Y - Y * axisCartanMatrix a) * X +
        Y * (axisCartanMatrix a * X - X * axisCartanMatrix a)) := by
          noncomm_ring
    _ = (μ a • X) * Y + X * (ν a • Y) -
      ((ν a • Y) * X + Y * (μ a • X)) := by rw [hx, hy]
    _ = (μ a + ν a) • (X * Y - Y * X) := by
      ext p q
      change
        (∑ x, (μ a * X p x) * Y x q) +
            ∑ x, X p x * (ν a * Y x q) -
              ((∑ x, (ν a * Y p x) * X x q) +
                ∑ x, Y p x * (μ a * X x q)) =
          (μ a + ν a) *
            ((∑ x, X p x * Y x q) - ∑ x, Y p x * X x q)
      have h1 : (∑ x, (μ a * X p x) * Y x q) =
          μ a * (∑ x, X p x * Y x q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      have h2 : (∑ x, X p x * (ν a * Y x q)) =
          ν a * (∑ x, X p x * Y x q) := by
        calc
          (∑ x, X p x * (ν a * Y x q)) =
              ∑ x, ν a * (X p x * Y x q) := by
                apply Finset.sum_congr rfl
                intro x hx
                ring
          _ = ν a * (∑ x, X p x * Y x q) := by rw [Finset.mul_sum]
      have h3 : (∑ x, (ν a * Y p x) * X x q) =
          ν a * (∑ x, Y p x * X x q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      have h4 : (∑ x, Y p x * (μ a * X x q)) =
          μ a * (∑ x, Y p x * X x q) := by
        calc
          (∑ x, Y p x * (μ a * X x q)) =
              ∑ x, μ a * (Y p x * X x q) := by
                apply Finset.sum_congr rfl
                intro x hx
                ring
          _ = μ a * (∑ x, Y p x * X x q) := by rw [Finset.mul_sum]
      rw [h1, h2, h3, h4]
      ring

/-- Contact degrees add under the commutator. -/
theorem commutator_mem_contactGradeSpace
    {k l : ℂ} {X Y : Mat10}
    (hX : X ∈ contactGradeSpace k)
    (hY : Y ∈ contactGradeSpace l) :
    X * Y - Y * X ∈ contactGradeSpace (k + l) := by
  have hx := hX
  have hy := hY
  calc
    contactGradingMatrix * (X * Y - Y * X) -
        (X * Y - Y * X) * contactGradingMatrix =
      (contactGradingMatrix * X - X * contactGradingMatrix) * Y +
        X * (contactGradingMatrix * Y - Y * contactGradingMatrix) -
      ((contactGradingMatrix * Y - Y * contactGradingMatrix) * X +
        Y * (contactGradingMatrix * X - X * contactGradingMatrix)) := by
          noncomm_ring
    _ = (k • X) * Y + X * (l • Y) -
      ((l • Y) * X + Y * (k • X)) := by rw [hx, hy]
    _ = (k + l) • (X * Y - Y * X) := by
      ext p q
      change
        (∑ x, (k * X p x) * Y x q) +
            ∑ x, X p x * (l * Y x q) -
              ((∑ x, (l * Y p x) * X x q) +
                ∑ x, Y p x * (k * X x q)) =
          (k + l) *
            ((∑ x, X p x * Y x q) - ∑ x, Y p x * X x q)
      have h1 : (∑ x, (k * X p x) * Y x q) =
          k * (∑ x, X p x * Y x q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      have h2 : (∑ x, X p x * (l * Y x q)) =
          l * (∑ x, X p x * Y x q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      have h3 : (∑ x, (l * Y p x) * X x q) =
          l * (∑ x, Y p x * X x q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      have h4 : (∑ x, Y p x * (k * X x q)) =
          k * (∑ x, Y p x * X x q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [h1, h2, h3, h4]
      ring

/-- Restriction of a contact grade to the native split-orthogonal Lie algebra. -/
def splitO55GradeSpace (k : ℂ) : Submodule ℂ splitO55Lie where
  carrier := {X |
    contactGradingMatrix * (X : Mat10) -
      (X : Mat10) * contactGradingMatrix = k • (X : Mat10)}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    change contactGradingMatrix * ((X : Mat10) + (Y : Mat10)) -
      ((X : Mat10) + (Y : Mat10)) * contactGradingMatrix =
        k • ((X : Mat10) + (Y : Mat10))
    calc
      contactGradingMatrix * ((X : Mat10) + (Y : Mat10)) -
          ((X : Mat10) + (Y : Mat10)) * contactGradingMatrix =
          (contactGradingMatrix * (X : Mat10) - (X : Mat10) * contactGradingMatrix) +
            (contactGradingMatrix * (Y : Mat10) - (Y : Mat10) * contactGradingMatrix) := by
              noncomm_ring
      _ = k • (X : Mat10) + k • (Y : Mat10) := by rw [hX, hY]
      _ = k • ((X : Mat10) + (Y : Mat10)) := by rw [smul_add]
  smul_mem' := by
    intro c X hX
    change contactGradingMatrix * (c • (X : Mat10)) -
      (c • (X : Mat10)) * contactGradingMatrix =
        k • (c • (X : Mat10))
    calc
      contactGradingMatrix * (c • (X : Mat10)) -
          (c • (X : Mat10)) * contactGradingMatrix =
          c • (contactGradingMatrix * (X : Mat10) -
            (X : Mat10) * contactGradingMatrix) := by
              simp [sub_eq_add_neg]
      _ = c • (k • (X : Mat10)) := by rw [hX]
      _ = k • (c • (X : Mat10)) := by simp [smul_smul, mul_comm]

/-- The native root element lies in the corresponding native `O(5,5)` grade. -/
theorem rootElement_mem_splitO55GradeSpace (r : Root) :
    rootElement r ∈ splitO55GradeSpace (r.contactDegree : ℂ) :=
  contactGrading_rootMatrix r

/-- Native split-orthogonal grade addition. -/
theorem splitO55_bracket_grade_add
    {k l : ℂ} {X Y : splitO55Lie}
    (hX : X ∈ splitO55GradeSpace k)
    (hY : Y ∈ splitO55GradeSpace l) :
    ⁅X, Y⁆ ∈ splitO55GradeSpace (k + l) := by
  change contactGradingMatrix *
      ((X : Mat10) * (Y : Mat10) - (Y : Mat10) * (X : Mat10)) -
      ((X : Mat10) * (Y : Mat10) - (Y : Mat10) * (X : Mat10)) *
        contactGradingMatrix =
    (k + l) •
      ((X : Mat10) * (Y : Mat10) - (Y : Mat10) * (X : Mat10))
  exact commutator_mem_contactGradeSpace hX hY

/-- Root brackets land in the sum of their collapsed degrees. -/
theorem rootBracket_contactDegree
    (r s : Root) :
    rootMatrix r * rootMatrix s - rootMatrix s * rootMatrix r ∈
      contactGradeSpace ((r.contactDegree + s.contactDegree : ℤ) : ℂ) := by
  have h := commutator_mem_contactGradeSpace
    (rootMatrix_mem_contactGradeSpace r)
    (rootMatrix_mem_contactGradeSpace s)
  simpa using h

/-- The full multigrading-to-five-grading theorem packet. -/
theorem o55_contact_five_grading_packet (r s : Root) :
    rootMatrix r ∈ multiWeightSpace
        (fun a => (r.multiDegree a : ℂ)) ∧
      rootMatrix r ∈ contactGradeSpace (r.contactDegree : ℂ) ∧
      IsSplitOrthogonal (rootMatrix r) ∧
      rootMatrix r * rootMatrix s - rootMatrix s * rootMatrix r ∈
        contactGradeSpace ((r.contactDegree + s.contactDegree : ℤ) : ℂ) := by
  exact ⟨rootMatrix_mem_multiWeightSpace r,
    rootMatrix_mem_contactGradeSpace r,
    wittAdjoint_rootMatrix r,
    rootBracket_contactDegree r s⟩

end InfoGeometry.Orthogonal.O55Contact

end noncomputable section
