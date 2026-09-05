import InfoGeometry.Orthogonal.O55ContactFiveGrading

/-!
# Full five-grade projection decomposition of split `O(5,5)`

The contact Euler operator has diagonal Witt weights `1,1,0,0,0` on the
positive sheet and their negatives on the opposite sheet.  Every matrix entry
therefore has degree in `{-2,-1,0,1,2}`.

Entrywise spectral projections give five pairwise orthogonal idempotent linear
maps whose sum is the identity on the entire Witt-skew Lie algebra.  This is
the actual direct-sum theorem behind the root count `(1,12,19,12,1)`.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55ContactDirectSum

open scoped Matrix BigOperators
open InfoGeometry.Orthogonal.O55D5
open InfoGeometry.Orthogonal.O55Witt
open InfoGeometry.Orthogonal.O55Contact

/-- Integral contact weight of one of the five axes. -/
def axisContactWeight (i : Axis) : ℤ :=
  if i = 0 ∨ i = 1 then 1 else 0

/-- Integral Euler weight on one Witt basis vector. -/
def indexContactWeight (p : Index) : ℤ :=
  if p.1 = 0 then axisContactWeight p.2 else -axisContactWeight p.2

/-- Degree of a matrix entry. -/
def entryDegree (p q : Index) : ℤ :=
  indexContactWeight p - indexContactWeight q

/-- The five allowed contact degrees. -/
def contactDegrees : Finset ℤ :=
  [-2, -1, 0, 1, 2].toFinset

@[simp] theorem indexWeight_contact (p : Index) :
    indexWeight contactCartanCoefficient p =
      (indexContactWeight p : ℂ) := by
  rcases p with ⟨s, i⟩
  fin_cases s <;> fin_cases i <;>
    norm_num [indexWeight, indexContactWeight, axisContactWeight,
      contactCartanCoefficient]

@[simp] theorem indexContactWeight_flip (p : Index) :
    indexContactWeight (flipIndex p) = -indexContactWeight p := by
  rcases p with ⟨s, i⟩
  fin_cases s <;> simp [indexContactWeight, flipIndex]

@[simp] theorem entryDegree_flip (p q : Index) :
    entryDegree (flipIndex q) (flipIndex p) = entryDegree p q := by
  simp [entryDegree]
  ring

/-- Every entry degree belongs to the five-element grading set. -/
theorem entryDegree_mem (p q : Index) :
    entryDegree p q ∈ contactDegrees := by
  native_decide

/-- Diagonal Cartan commutator evaluated entrywise. -/
theorem cartan_commutator_entry
    (h : Axis → ℂ) (X : Mat10) (p q : Index) :
    (cartanMatrix h * X - X * cartanMatrix h) p q =
      (indexWeight h p - indexWeight h q) * X p q := by
  classical
  simp [Matrix.mul_apply, cartanMatrix]
  ring

/-- Entrywise projection onto contact degree `k`. -/
def matrixGradeProjection (k : ℤ) (X : Mat10) : Mat10 := fun p q =>
  if entryDegree p q = k then X p q else 0

/-- Projection as a native linear map on all matrices. -/
def matrixGradeProjectionLinear (k : ℤ) : Mat10 →ₗ[ℂ] Mat10 where
  toFun := matrixGradeProjection k
  map_add' X Y := by
    ext p q
    simp [matrixGradeProjection]
  map_smul' c X := by
    ext p q
    simp [matrixGradeProjection]

@[simp] theorem matrixGradeProjectionLinear_apply
    (k : ℤ) (X : Mat10) :
    matrixGradeProjectionLinear k X = matrixGradeProjection k X := rfl

/-- Matrix-grade projections are idempotent. -/
theorem matrixGradeProjection_idempotent (k : ℤ) (X : Mat10) :
    matrixGradeProjection k (matrixGradeProjection k X) =
      matrixGradeProjection k X := by
  ext p q
  simp [matrixGradeProjection]

/-- Distinct grade projections annihilate one another. -/
theorem matrixGradeProjection_orthogonal
    {k l : ℤ} (hkl : k ≠ l) (X : Mat10) :
    matrixGradeProjection k (matrixGradeProjection l X) = 0 := by
  ext p q
  by_cases hk : entryDegree p q = k
  · have hl : entryDegree p q ≠ l := by
      intro h
      apply hkl
      exact hk.symm.trans h
    simp [matrixGradeProjection, hk, hl]
  · simp [matrixGradeProjection, hk]

/-- A projected matrix is an exact contact-grade eigenvector. -/
theorem matrixGradeProjection_mem_contactGradeSpace
    (k : ℤ) (X : Mat10) :
    matrixGradeProjection k X ∈ contactGradeSpace (k : ℂ) := by
  ext p q
  rw [cartan_commutator_entry, indexWeight_contact, indexWeight_contact]
  by_cases hdeg : entryDegree p q = k
  · simp [matrixGradeProjection, hdeg, entryDegree]
    push_cast
    rw [hdeg]
  · simp [matrixGradeProjection, hdeg]

/-- Projection preserves the Witt-skew condition. -/
theorem matrixGradeProjection_isSplitOrthogonal
    (k : ℤ) {X : Mat10} (hX : IsSplitOrthogonal X) :
    IsSplitOrthogonal (matrixGradeProjection k X) := by
  unfold IsSplitOrthogonal at hX ⊢
  ext p q
  have hx := congrArg (fun M : Mat10 => M p q) hX
  simp only [wittAdjoint] at hx ⊢
  by_cases hdeg : entryDegree p q = k
  · have hflip : entryDegree (flipIndex q) (flipIndex p) = k := by
      simpa using hdeg
    simp [matrixGradeProjection, hdeg, hflip, hx]
  · have hflip : entryDegree (flipIndex q) (flipIndex p) ≠ k := by
      simpa using hdeg
    simp [matrixGradeProjection, hdeg, hflip]

/-- Five-grade projector on the native split-orthogonal Lie carrier. -/
def o55GradeProjection (k : ℤ) : splitO55Lie →ₗ[ℂ] splitO55Lie where
  toFun X :=
    ⟨matrixGradeProjection k (X : Mat10),
      matrixGradeProjection_isSplitOrthogonal k X.property⟩
  map_add' X Y := by
    apply Subtype.ext
    ext p q
    simp [matrixGradeProjection]
  map_smul' c X := by
    apply Subtype.ext
    ext p q
    simp [matrixGradeProjection]

@[simp] theorem o55GradeProjection_apply_coe
    (k : ℤ) (X : splitO55Lie) :
    ((o55GradeProjection k X : splitO55Lie) : Mat10) =
      matrixGradeProjection k (X : Mat10) := rfl

/-- Every projected split-orthogonal element lies in its native grade space. -/
theorem o55GradeProjection_mem
    (k : ℤ) (X : splitO55Lie) :
    o55GradeProjection k X ∈ splitO55GradeSpace (k : ℂ) :=
  matrixGradeProjection_mem_contactGradeSpace k (X : Mat10)

/-- Native grade projectors are idempotent. -/
theorem o55GradeProjection_idempotent (k : ℤ) :
    o55GradeProjection k * o55GradeProjection k = o55GradeProjection k := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  exact matrixGradeProjection_idempotent k (X : Mat10)

/-- Native grade projectors are pairwise orthogonal. -/
theorem o55GradeProjection_orthogonal
    {k l : ℤ} (hkl : k ≠ l) :
    o55GradeProjection k * o55GradeProjection l = 0 := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  exact matrixGradeProjection_orthogonal hkl (X : Mat10)

private theorem sum_indicator_degree
    (d : ℤ) (hd : d ∈ contactDegrees) (z : ℂ) :
    ∑ k ∈ contactDegrees, (if d = k then z else 0) = z := by
  classical
  rw [Finset.sum_eq_single d]
  · simp
  · intro b hb hbd
    simp [hbd]
  · exact hd

/-- The five projections reconstruct every matrix. -/
theorem sum_matrixGradeProjection (X : Mat10) :
    ∑ k ∈ contactDegrees, matrixGradeProjection k X = X := by
  ext p q
  simp only [Finset.sum_apply]
  exact sum_indicator_degree (entryDegree p q) (entryDegree_mem p q) (X p q)

/-- Full direct-sum reconstruction on the native `O(5,5)` Lie carrier. -/
theorem sum_o55GradeProjection (X : splitO55Lie) :
    ∑ k ∈ contactDegrees, o55GradeProjection k X = X := by
  apply Subtype.ext
  exact sum_matrixGradeProjection (X : Mat10)

/-- No matrix entry survives projection to a degree outside the five-grade
support. -/
theorem matrixGradeProjection_eq_zero_of_not_mem
    {k : ℤ} (hk : k ∉ contactDegrees) (X : Mat10) :
    matrixGradeProjection k X = 0 := by
  ext p q
  have hne : entryDegree p q ≠ k := by
    intro h
    apply hk
    rw [← h]
    exact entryDegree_mem p q
  simp [matrixGradeProjection, hne]

/-- Full five-grade direct-sum packet. -/
theorem o55_five_grade_direct_sum_packet (X : splitO55Lie) :
    (∀ k, o55GradeProjection k X ∈
      splitO55GradeSpace (k : ℂ)) ∧
    (∀ k, o55GradeProjection k * o55GradeProjection k =
      o55GradeProjection k) ∧
    (∀ k l, k ≠ l →
      o55GradeProjection k * o55GradeProjection l = 0) ∧
    (∑ k ∈ contactDegrees, o55GradeProjection k X = X) ∧
    (∀ k, k ∉ contactDegrees → o55GradeProjection k X = 0) := by
  refine ⟨fun k => o55GradeProjection_mem k X,
    o55GradeProjection_idempotent,
    fun k l h => o55GradeProjection_orthogonal h,
    sum_o55GradeProjection X, ?_⟩
  intro k hk
  apply Subtype.ext
  exact matrixGradeProjection_eq_zero_of_not_mem hk (X : Mat10)

end InfoGeometry.Orthogonal.O55ContactDirectSum

end noncomputable section
