import InfoGeometry.Physics.ZornMatrixSU3.ZornMatrixCore
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.KingdonSplitOctonion
import InfoGeometry.Clifford.Cl11CoordinateAlgebra
import InfoGeometry.Clifford.GammaMatrices

namespace InfoGeometry.Physics.ZornMatrixSU3

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
  · ext <;> simp [projector1, projector2, zero, mul]
  · ext <;> simp [projector1, projector2, zero, mul]

theorem projector1_add_projector2 : projector1 + projector2 = one := by
  ext i <;> simp [projector1, projector2, one, add]

/-- Color triplet extraction: OP₁ · M · OP₂ -/
def extractTriplet (M : ZornMatrix) : Fin 3 → ℝ :=
  (projector1 * M * projector2).x

/-- Color antitriplet extraction: OP₂ · M · OP₁ -/
def extractAntitriplet (M : ZornMatrix) : Fin 3 → ℝ :=
  (projector2 * M * projector1).y

/-- Diagonal scalar extraction -/
def extractScalars (M : ZornMatrix) : ℝ × ℝ :=
  ((projector1 * M * projector1).a, (projector2 * M * projector2).b)

theorem decomposition_theorem (M : ZornMatrix) :
    M = ⟨M.a, M.b, extractTriplet M, extractAntitriplet M⟩ := by
  have hx : extractTriplet M = M.x := by
    rw [extractTriplet, mul_projector1, projector2_mul]
  have hy : extractAntitriplet M = M.y := by
    rw [extractAntitriplet, mul_projector2, projector1_mul]
  simp [hx, hy]

/-- Peirce readback of the `1_+` sector. -/
theorem peirce_readback_plusplus (M : ZornMatrix) :
    projector1 * M * projector1 =
      ⟨M.a, 0, fun _ : Fin 3 => 0, fun _ : Fin 3 => 0⟩ := by
  rw [mul_projector1, projector1_mul]
/-- Peirce readback of the `3` sector. -/
theorem peirce_readback_plusminus (M : ZornMatrix) :
    projector1 * M * projector2 =
      ⟨0, 0, M.x, fun _ : Fin 3 => 0⟩ := by
  rw [mul_projector1, projector2_mul]
/-- Peirce readback of the `3*` sector. -/
theorem peirce_readback_minusplus (M : ZornMatrix) :
    projector2 * M * projector1 =
      ⟨0, 0, fun _ : Fin 3 => 0, M.y⟩ := by
  rw [mul_projector2, projector1_mul]
/-- Peirce readback of the `1_-` sector. -/
theorem peirce_readback_minusminus (M : ZornMatrix) :
    projector2 * M * projector2 =
      ⟨0, M.b, fun _ : Fin 3 => 0, fun _ : Fin 3 => 0⟩ := by
  rw [mul_projector2, projector2_mul]
/-- The canonical projector sandwich brackets agree for the color sector. -/
theorem peirce_bracketing (M : ZornMatrix) :
    (projector1 * M) * projector2 = projector1 * (M * projector2) := by
  rw [mul_projector1, projector2_mul, projector2_mul, mul_projector1]
/-- The Peirce decomposition reconstructs the original Zorn matrix. -/
theorem peirce_decomposition (M : ZornMatrix) :
    M =
      projector1 * M * projector1 +
      projector1 * M * projector2 +
      projector2 * M * projector1 +
      projector2 * M * projector2 := by
  simp only [mul_projector1, mul_projector2, projector1_mul, projector2_mul]
  ext i <;> simp [add]
/-- The production Zorn multiplication is left alternative. -/
theorem zorn_left_alternative (X Y : ZornMatrix) :
    (X * X) * Y = X * (X * Y) := by
  simpa using (InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.zorn_left_alternative X Y)

/-- The production Zorn multiplication is right alternative. -/
theorem zorn_right_alternative (X Y : ZornMatrix) :
    (Y * X) * X = Y * (X * X) := by
  simpa using (InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.zorn_right_alternative X Y)

/-!
## 5. Real cross-product stabilizer
-/

/-- 
A real linear map on `ℝ³` that preserves both the dot product and the cross
product. This is the exact finite real stabilizer property used by the Zorn
multiplication proofs below; it is not a complex `SU(3)` formalization.
-/
def IsRealCrossProductStabilizer (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) : Prop :=
  (∀ x y, dotProduct (R x) (R y) = dotProduct x y) ∧
  (∀ x y, R (crossProduct x y) = crossProduct (R x) (R y))

/-- 
Action of a real cross-product stabilizer on a Zorn matrix.
The transformation rotates the color triplet and antitriplet
while leaving the diagonal scalars invariant.
-/
def realCrossProductStabilizerAction
    (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (M : ZornMatrix) : ZornMatrix :=
  ⟨M.a, M.b, R M.x, R M.y⟩

theorem realCrossProductStabilizerAction_preserves_norm
    (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hR : IsRealCrossProductStabilizer R) (M : ZornMatrix) :
    norm (realCrossProductStabilizerAction R M) = norm M := by
  simp [realCrossProductStabilizerAction, norm, dotProduct]
  exact hR.1 M.x M.y

theorem realCrossProductStabilizerAction_preserves_multiplication
    (R : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hR : IsRealCrossProductStabilizer R) (M N : ZornMatrix) :
    realCrossProductStabilizerAction R (M * N) =
      (realCrossProductStabilizerAction R M) *
        (realCrossProductStabilizerAction R N) := by
  cases M with
  | mk a b x y =>
  cases N with
  | mk a' b' x' y' =>
      ext
      · simp [realCrossProductStabilizerAction, mul, hR.1]
      · simp [realCrossProductStabilizerAction, mul, hR.1]
      · simp [realCrossProductStabilizerAction, mul, hR.2]
      · simp [realCrossProductStabilizerAction, mul, hR.2]

/-!
## 6. Connection to Cl(1,1) Grading
-/

/-- 
Tripotent grading operator on Zorn matrices.
Extends the Cl(1,1) grading χ to the octonionic structure.
-/
def gradingOperator (M : ZornMatrix) : ZornMatrix :=
  ⟨0, 0, M.x, -M.y⟩

@[simp] theorem grading_sq (M : ZornMatrix) :
    gradingOperator (gradingOperator M) = ⟨0, 0, M.x, M.y⟩ := by
  simp [gradingOperator]

theorem grading_tripotent (M : ZornMatrix) :
    gradingOperator (gradingOperator (gradingOperator M)) = gradingOperator M := by
  ext <;> simp [gradingOperator, grading_sq]

/-- Eigenvalue +1 subspace: color triplets -/
def gradingEigenPlus : Set ZornMatrix := {M | gradingOperator M = M}

/-- Eigenvalue -1 subspace: color antitriplets -/
def gradingEigenMinus : Set ZornMatrix := {M | gradingOperator M = -M}

/-- Eigenvalue 0 subspace: diagonal scalars -/
def gradingEigenZero : Set ZornMatrix := {M | gradingOperator M = 0}

theorem eigenspace_decomposition (M : ZornMatrix) :
    ∃ (Mplus : ZornMatrix) (Mminus : ZornMatrix) (Mzero : ZornMatrix),
    Mplus ∈ gradingEigenPlus ∧ Mminus ∈ gradingEigenMinus ∧ Mzero ∈ gradingEigenZero ∧
    M = Mplus + Mminus + Mzero := by
  cases M with
  | mk a b x y =>
    refine
      ⟨⟨0, 0, x, fun _ : Fin 3 => 0⟩,
        ⟨0, 0, fun _ : Fin 3 => 0, y⟩,
        ⟨a, b, fun _ : Fin 3 => 0, fun _ : Fin 3 => 0⟩, ?_, ?_, ?_, ?_⟩
    · ext <;> simp [gradingOperator, neg]
    · ext <;> simp [gradingOperator, neg]
    · ext <;> simp [gradingOperator, neg]
    · ext <;> simp [add, zero, Pi.add_apply, add_assoc, add_left_comm, add_comm]

/-!
## 7. Mersenne Hierarchy Connection (TODO)
-/

/-- 
Associate Cl(n,n) tower levels with Mersenne primes:
- n=1: M₂ = 3 (dimension of color space)
- n=2: ???
- n=3: M₃ = 7 (dimension of imaginary octonions)
- n=7: M₇ = 127 (??? )

This connects the discrete arithmetic hierarchy to the continuous
geometric representation structure.
-/
def mersenneDimension (n : ℕ) : ℕ :=
  2^n - 1

-- TODO: Prove connections between mersenneDimension and:
-- - dim(SU(3)) = 8
-- - dim(G₂) = 14
-- - 137 = 3 + 7 + 127 decomposition

end InfoGeometry.Physics.ZornMatrixSU3
