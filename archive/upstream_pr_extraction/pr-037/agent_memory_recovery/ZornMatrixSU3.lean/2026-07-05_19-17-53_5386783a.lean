  simpa [norm, conjugate, dotProduct] using
    (InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm_conj (M.a, M.b, M.x, M.y))

theorem norm_mul (M N : ZornMatrix) :
    norm (M * N) = norm M * norm N := by
  change
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm
      (InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornMul
        (M.a, M.b, M.x, M.y) (N.a, N.b, N.x, N.y)) =
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm (M.a, M.b, M.x, M.y) *
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm (N.a, N.b, N.x, N.y)
  simpa [norm, dotProduct, crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornMul] using
    (InfoGeometry.Canonical.ZornVectorMatrixExplicit.zornNorm_mul
      (M.a, M.b, M.x, M.y) (N.a, N.b, N.x, N.y))


/-!
## 4. Diagonal Projectors and Color Decomposition
-/

/-- First diagonal projector (selects upper block) -/
def projector1 : ZornMatrix :=
  ⟨1, 0, fun _ => 0, fun _ => 0⟩

/-- Second diagonal projector (selects lower block) -/
def projector2 : ZornMatrix :=
  ⟨0, 1, fun _ => 0, fun _ => 0⟩

@[simp] lemma mul_projector1 (M : ZornMatrix) :
    projector1 * M = ⟨M.a, 0, M.x, fun _ : Fin 3 => 0⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector1, mul]
      · simp [projector1, mul]
      · simp [projector1, mul, dotProduct_zero_left, crossProduct_zero_left]
      · simp [projector1, mul, crossProduct_self]

@[simp] lemma mul_projector2 (M : ZornMatrix) :
    projector2 * M = ⟨0, M.b, fun _ : Fin 3 => 0, M.y⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector2, mul]
      · simp [projector2, mul]
      · simp [projector2, mul, crossProduct_self]
      · simp [projector2, mul, dotProduct_zero_left, crossProduct_zero_left]

@[simp] lemma projector1_mul (M : ZornMatrix) :
    M * projector1 = ⟨M.a, 0, fun _ : Fin 3 => 0, M.y⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector1, mul]
      · simp [projector1, mul]
      · simp [projector1, mul, crossProduct_self]
      · simp [projector1, mul, crossProduct_self]

@[simp] lemma projector2_mul (M : ZornMatrix) :
    M * projector2 = ⟨0, M.b, M.x, fun _ : Fin 3 => 0⟩ := by
  cases M with
  | mk a b x y =>
      ext
      · simp [projector2, mul]
      · simp [projector2, mul]
      · simp [projector2, mul, crossProduct_self]
      · simp [projector2, mul, dotProduct_zero_left, crossProduct_zero_left]

@[simp] theorem projector1_sq : projector1 * projector1 = projector1 := by
  ext
  · simp [projector1, mul]
  · simp [projector1, mul]
  · simp [projector1, mul, crossProduct_self]
  · simp [projector1, mul, crossProduct_self]

@[simp] theorem projector2_sq : projector2 * projector2 = projector2 := by
  ext
  · simp [projector2, mul]
  · simp [projector2, mul]
  · simp [projector2, mul, crossProduct_self]
  · simp [projector2, mul, crossProduct_self]

theorem projector1_projector2_orthogonal :
    projector1 * projector2 = zero ∧ projector2 * projector1 = zero := by
  constructor
  · ext
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero, dotProduct_zero_zero]
    · simp [projector1, projector2, zero, crossProduct_zero_zero]
  · ext
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero]
    · simp [projector1, projector2, zero, crossProduct_zero_zero]
    · simp [projector1, projector2, zero, crossProduct_zero_zero]

theorem projector1_add_projector2 : projector1 + projector2 = one := by
  ext i <;> simp [projector1, projector2, one, add]

@[simp] theorem zero_mul_zorn (M : ZornMatrix) : (0 : ZornMatrix) * M = 0 := by
  cases M <;> ext <;> simp [mul, zero, dotProduct_zero_left, dotProduct_zero_right,
    crossProduct_zero_left, crossProduct_zero_right]

@[simp] theorem mul_zero_zorn (M : ZornMatrix) : M * (0 : ZornMatrix) = 0 := by
  cases M <;> ext <;> simp [mul, zero, dotProduct_zero_left, dotProduct_zero_right,
    crossProduct_zero_left, crossProduct_zero_right]

theorem add_mul_zorn (M N P : ZornMatrix) : (M + N) * P = M * P + N * P := by
  cases M <;> cases N <;> cases P <;> ext <;>
    simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left,
      crossProduct_add_right, dotProduct_comm] <;> ring

theorem mul_add_zorn (M N P : ZornMatrix) : M * (N + P) = M * N + M * P := by
  cases M <;> cases N <;> cases P <;> ext <;>
    simp [add, mul, dotProduct_add_left, dotProduct_add_right, crossProduct_add_left,
      crossProduct_add_right, dotProduct_comm] <;> ring

theorem smul_mul_zorn (r : ℝ) (M N : ZornMatrix) : (r • M) * N = r • (M * N) := by
  cases M <;> cases N <;> ext <;>
    simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left,
      crossProduct_smul_right] <;> ring

theorem mul_smul_zorn (r : ℝ) (M N : ZornMatrix) : M * (r • N) = r • (M * N) := by
  cases M <;> cases N <;> ext <;>
    simp [smul, mul, dotProduct_smul_left, dotProduct_smul_right, crossProduct_smul_left,
      crossProduct_smul_right] <;> ring

@[simp] theorem one_mul_zorn (M : ZornMatrix) : (1 : ZornMatrix) * M = M := by
  cases M <;> ext <;> simp [mul, one, dotProduct_zero_left, dotProduct_zero_right,
    crossProduct_zero_left, crossProduct_zero_right]

@[simp] theorem mul_one_zorn (M : ZornMatrix) : M * (1 : ZornMatrix) = M := by
  cases M <;> ext <;> simp [mul, one, dotProduct_zero_left, dotProduct_zero_right,
    crossProduct_zero_left, crossProduct_zero_right]

/-- Color triplet extraction: OP₁ · M · OP₂ -/
def extractTriplet (M : ZornMatrix) : Fin 3 → ℝ :=
  (projector1 * M * projector2).x

/-- Color antitriplet extraction: OP₂ · M · OP₁ -/
def extractAntitriplet (M : ZornMatrix) : Fin 3 → ℝ :=
  (projector2 * M * projector1).y

/-- Diagonal scalar extraction -/
def extractScalars (M : ZornMatrix) : ℝ × ℝ :=
  ((projector1 * M * projector1).a, (projector2 * M * projector2).b)

@[simp] theorem extractTriplet_eq (M : ZornMatrix) : extractTriplet M = M.x := by
  cases M <;> simp [extractTriplet, mul, projector1, projector2]