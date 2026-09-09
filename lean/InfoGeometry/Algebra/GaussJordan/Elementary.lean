import InfoGeometry.Algebra.GaussJordan.Rank

open Matrix

namespace InfoGeometry.Algebra.GaussJordan

section Elementary

variable {m n : ℕ}

/-- Left multiplication by the elementary swap matrix. -/
def swapRows (B : RatMatrix m n) (p q : Fin m) : RatMatrix m n :=
  Matrix.swap ℚ p q * B

@[simp] theorem swapRows_apply_left (B : RatMatrix m n) (p q : Fin m) (j : Fin n) :
    swapRows B p q p j = B q j := by
  simp [swapRows]

@[simp] theorem swapRows_apply_right (B : RatMatrix m n) (p q : Fin m) (j : Fin n) :
    swapRows B p q q j = B p j := by
  simp [swapRows]

theorem swapRows_apply_of_ne (B : RatMatrix m n) {p q i : Fin m} (j : Fin n)
    (hip : i ≠ p) (hiq : i ≠ q) :
    swapRows B p q i j = B i j := by
  exact Matrix.swap_mul_of_ne hip hiq B

/-- A diagonal elementary matrix scaling row `p` by `a`. -/
def scaleMultiplier (p : Fin m) (a : ℚ) : Matrix (Fin m) (Fin m) ℚ :=
  Matrix.diagonal fun i => if i = p then a else 1

/-- Scale row `p` of `B` by `a`. -/
def scaleRow (B : RatMatrix m n) (p : Fin m) (a : ℚ) : RatMatrix m n :=
  scaleMultiplier p a * B

@[simp] theorem scaleRow_apply_self (B : RatMatrix m n) (p : Fin m) (a : ℚ)
    (j : Fin n) :
    scaleRow B p a p j = a * B p j := by
  simp [scaleRow, scaleMultiplier]

theorem scaleRow_apply_of_ne (B : RatMatrix m n) {p i : Fin m} (a : ℚ)
    (j : Fin n) (hi : i ≠ p) :
    scaleRow B p a i j = B i j := by
  simp [scaleRow, scaleMultiplier, hi]

/-- A nonzero row scaling matrix is invertible. -/
theorem scaleMultiplier_isUnit {p : Fin m} {a : ℚ} (ha : a ≠ 0) :
    IsUnit (scaleMultiplier p a) := by
  let D := scaleMultiplier p a
  let Dinv := scaleMultiplier p a⁻¹
  have h_diag1 : (fun i => (if i = p then a else 1) * (if i = p then a⁻¹ else 1)) = fun _ => 1 := by
    ext i
    by_cases hi : i = p
    · subst hi; simp [ha]
    · simp [hi]
  have h_diag2 : (fun i => (if i = p then a⁻¹ else 1) * (if i = p then a else 1)) = fun _ => 1 := by
    ext i
    by_cases hi : i = p
    · subst hi; simp [ha]
    · simp [hi]
  have hvalInv : D * Dinv = 1 := by
    change Matrix.diagonal _ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_mul_diagonal, h_diag1, Matrix.diagonal_one]
  have hinvVal : Dinv * D = 1 := by
    change Matrix.diagonal _ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_mul_diagonal, h_diag2, Matrix.diagonal_one]
  exact ⟨⟨D, Dinv, hvalInv, hinvVal⟩, rfl⟩

/-- The swap matrix is a unit. -/
theorem swapMultiplier_isUnit (p q : Fin m) : IsUnit (Matrix.swap ℚ p q) :=
  ⟨Matrix.GeneralLinearGroup.swap ℚ p q, rfl⟩

/-- Coefficients used to clear a normalized pivot column. -/
def clearVector (B : RatMatrix m n) (p : Fin m) (j : Fin n) : Fin m → ℚ :=
  fun i => if i = p then 0 else -B i j

/-- The square-zero rank-one matrix encoding all row additions at once. -/
def clearNilpotent (B : RatMatrix m n) (p : Fin m) (j : Fin n) :
    Matrix (Fin m) (Fin m) ℚ :=
  Matrix.vecMulVec (clearVector B p j) (Pi.single p 1)

/-- The elementary matrix that clears a normalized pivot column. -/
def clearMultiplier (B : RatMatrix m n) (p : Fin m) (j : Fin n) :
    Matrix (Fin m) (Fin m) ℚ :=
  1 + clearNilpotent B p j

/-- Clear column `j` using normalized pivot row `p`. -/
def clearColumn (B : RatMatrix m n) (p : Fin m) (j : Fin n) : RatMatrix m n :=
  clearMultiplier B p j * B

@[simp] theorem clearColumn_apply (B : RatMatrix m n) (p : Fin m) (j c : Fin n)
    (i : Fin m) :
    clearColumn B p j i c = B i c + clearVector B p j i * B p c := by
  simp [clearColumn, clearMultiplier, clearNilpotent, Matrix.add_mul,
    Matrix.vecMulVec_mul, Matrix.vecMulVec_apply]

@[simp] theorem clearColumn_apply_self (B : RatMatrix m n) (p : Fin m) (j c : Fin n) :
    clearColumn B p j p c = B p c := by
  simp [clearVector]

theorem clearColumn_apply_of_ne (B : RatMatrix m n) {p i : Fin m} (j c : Fin n)
    (hi : i ≠ p) :
    clearColumn B p j i c = B i c - B i j * B p c := by
  rw [clearColumn_apply]
  simp [clearVector, hi, sub_eq_add_neg]

/-- The simultaneous clearing matrix has square-zero nilpotent part. -/
theorem clearNilpotent_sq (B : RatMatrix m n) (p : Fin m) (j : Fin n) :
    clearNilpotent B p j * clearNilpotent B p j = 0 := by
  simp [clearNilpotent, Matrix.vecMulVec_mul_vecMulVec, clearVector]

/-- The simultaneous clearing matrix is invertible, with inverse `1 - N`. -/
theorem clearMultiplier_isUnit (B : RatMatrix m n) (p : Fin m) (j : Fin n) :
    IsUnit (clearMultiplier B p j) := by
  let N := clearNilpotent B p j
  have hN : N * N = 0 := by
    simpa [N] using clearNilpotent_sq B p j
  refine ⟨⟨clearMultiplier B p j, 1 - N, ?_, ?_⟩, rfl⟩
  · change (1 + N) * (1 - N) = 1
    rw [mul_sub, mul_one, add_mul, one_mul, hN, add_zero, add_sub_cancel_right]
  · change (1 - N) * (1 + N) = 1
    rw [mul_add, mul_one, sub_mul, one_mul, hN, sub_zero, sub_add_cancel]

/-- Normalize the entry at `(p,j)` by scaling row `p`. -/
def normalizePivot (B : RatMatrix m n) (p : Fin m) (j : Fin n) : RatMatrix m n :=
  scaleRow B p (B p j)⁻¹

@[simp] theorem normalizePivot_pivot (B : RatMatrix m n) (p : Fin m) (j : Fin n)
    (h : B p j ≠ 0) :
    normalizePivot B p j p j = 1 := by
  simp [normalizePivot, h]

/-- One complete pivot operation: swap, normalize, and clear. -/
def pivotStep (B : RatMatrix m n) (p q : Fin m) (j : Fin n) : RatMatrix m n :=
  clearColumn (normalizePivot (swapRows B p q) p j) p j

/-- The single left multiplier implementing `pivotStep`. -/
def pivotMultiplier (B : RatMatrix m n) (p q : Fin m) (j : Fin n) :
    Matrix (Fin m) (Fin m) ℚ :=
  let S := Matrix.swap ℚ p q
  let B₁ := S * B
  let D := scaleMultiplier p (B₁ p j)⁻¹
  let B₂ := D * B₁
  clearMultiplier B₂ p j * D * S

/-- The executable pivot step is left multiplication by its elementary multiplier. -/
theorem pivotStep_eq_mul (B : RatMatrix m n) (p q : Fin m) (j : Fin n) :
    pivotStep B p q j = pivotMultiplier B p q j * B := by
  simp [pivotStep, pivotMultiplier, normalizePivot, scaleRow, swapRows, clearColumn,
    Matrix.mul_assoc]

/-- The selected pivot becomes `1`. -/
@[simp] theorem pivotStep_pivot_one (B : RatMatrix m n) (p q : Fin m) (j : Fin n)
    (hq : B q j ≠ 0) :
    pivotStep B p q j p j = 1 := by
  have hB₁ : swapRows B p q p j ≠ 0 := by
    simpa using hq
  rw [pivotStep, clearColumn_apply_self, normalizePivot_pivot _ _ _ hB₁]

/-- Every non-pivot entry in the selected column becomes `0`. -/
theorem pivotStep_pivot_zero (B : RatMatrix m n) (p q i : Fin m) (j : Fin n)
    (hq : B q j ≠ 0) (hi : i ≠ p) :
    pivotStep B p q j i j = 0 := by
  let B₁ := swapRows B p q
  let B₂ := normalizePivot B₁ p j
  have hB₁ : B₁ p j ≠ 0 := by
    simpa [B₁] using hq
  have hB₂ : B₂ p j = 1 := normalizePivot_pivot B₁ p j hB₁
  change clearColumn B₂ p j i j = 0
  rw [clearColumn_apply_of_ne B₂ j j hi, hB₂]
  ring

/-- Swapping two rows that are both zero in a column leaves that column unchanged. -/
theorem swapRows_apply_of_both_zero (B : RatMatrix m n) (p q i : Fin m) (c : Fin n)
    (hp : B p c = 0) (hq : B q c = 0) :
    swapRows B p q i c = B i c := by
  by_cases hip : i = p
  · subst i
    simp [hp, hq]
  · by_cases hiq : i = q
    · subst i
      simp [hp, hq]
    · exact swapRows_apply_of_ne B c hip hiq

/-- Scaling a row that is zero in a column leaves that column unchanged. -/
theorem scaleRow_apply_of_pivot_zero (B : RatMatrix m n) (p i : Fin m) (a : ℚ)
    (c : Fin n) (hp : B p c = 0) :
    scaleRow B p a i c = B i c := by
  by_cases hi : i = p
  · subst i
    simp [hp]
  · exact scaleRow_apply_of_ne B a c hi

/-- Clearing with a pivot row that is zero in another column leaves that column unchanged. -/
theorem clearColumn_apply_of_pivot_zero (B : RatMatrix m n) (p i : Fin m) (j c : Fin n)
    (hp : B p c = 0) :
    clearColumn B p j i c = B i c := by
  rw [clearColumn_apply]
  simp [hp]

/-- A pivot step preserves every column in which both swapped rows were zero. -/
theorem pivotStep_apply_of_both_zero (B : RatMatrix m n) (p q i : Fin m) (j c : Fin n)
    (hp : B p c = 0) (hq : B q c = 0) :
    pivotStep B p q j i c = B i c := by
  let B₁ := swapRows B p q
  let B₂ := normalizePivot B₁ p j
  have hB₁ : ∀ r, B₁ r c = B r c := by
    intro r
    exact swapRows_apply_of_both_zero B p q r c hp hq
  have hB₁p : B₁ p c = 0 := by rw [hB₁ p, hp]
  have hB₂ : ∀ r, B₂ r c = B₁ r c := by
    intro r
    exact scaleRow_apply_of_pivot_zero B₁ p r (B₁ p j)⁻¹ c hB₁p
  have hB₂p : B₂ p c = 0 := by rw [hB₂ p, hB₁p]
  change clearColumn B₂ p j i c = B i c
  rw [clearColumn_apply_of_pivot_zero B₂ p i j c hB₂p, hB₂ i, hB₁ i]

/-- The multiplier of a valid pivot step is invertible. -/
theorem pivotMultiplier_isUnit (B : RatMatrix m n) (p q : Fin m) (j : Fin n)
    (hq : B q j ≠ 0) :
    IsUnit (pivotMultiplier B p q j) := by
  let S := Matrix.swap ℚ p q
  let B₁ := S * B
  let D := scaleMultiplier p (B₁ p j)⁻¹
  let B₂ := D * B₁
  have hB₁ : B₁ p j ≠ 0 := by
    simpa [B₁, S] using hq
  have hD : IsUnit D := by
    exact scaleMultiplier_isUnit (inv_ne_zero hB₁)
  have hC : IsUnit (clearMultiplier B₂ p j) := clearMultiplier_isUnit B₂ p j
  have hS : IsUnit S := by
    simpa [S] using swapMultiplier_isUnit (m := m) p q
  simpa [pivotMultiplier, S, B₁, D, B₂] using (hC.mul hD).mul hS

/-- Left multiplication by an invertible square matrix preserves matrix rank. -/
theorem rank_mul_left_of_isUnit (E : Matrix (Fin m) (Fin m) ℚ) (B : RatMatrix m n)
    (hE : IsUnit E) :
    (E * B).rank = B.rank := by
  obtain ⟨u, rfl⟩ := hE
  apply Nat.le_antisymm
  · exact Matrix.rank_mul_le_right _ _
  · have h := Matrix.rank_mul_le_right (↑u⁻¹ : Matrix (Fin m) (Fin m) ℚ)
      ((u : Matrix (Fin m) (Fin m) ℚ) * B)
    simpa [← Matrix.mul_assoc] using h

end Elementary

end InfoGeometry.Algebra.GaussJordan
