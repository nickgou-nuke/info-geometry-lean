import InfoGeometry.Canonical.UHFInductiveColimitBoundary

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.FiniteCantorCuntzBranches

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
# Finite rectangular Cuntz branch maps

The matrix tower `MatStage n` cannot contain two Cuntz isometries: its finite
trace gives the obstruction proved by `FiniteMatrixCuntzObstruction`.  The
correct finite model is rectangular.  A branch maps functions on words of
length `n` to functions on words of length `n + 1`, and its adjoint removes the
chosen last bit.
-/

abbrev Stage (n : ℕ) : Type := BitWord n → ℝ

def lastBit (n : ℕ) (w : BitWord (n + 1)) : Bool :=
  w ⟨n, Nat.lt_succ_self n⟩

@[simp]
theorem lastBit_extendSucc (n : ℕ) (w : BitWord n) (b : Bool) :
    lastBit n (extendSucc n w b) = b := by
  simp [lastBit, extendSucc]

theorem extendSucc_prefixSucc_lastBit (n : ℕ) (w : BitWord (n + 1)) :
    extendSucc n (prefixSucc n w) (lastBit n w) = w := by
  ext i
  by_cases hi : i.1 < n
  · simp [extendSucc, prefixSucc, lastBit, hi]
  · have hin : i.1 = n := by omega
    have hi' : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hin
    rw [hi']
    simp [extendSucc, lastBit]

def branch (n : ℕ) (b : Bool) : Stage n →ₗ[ℝ] Stage (n + 1) where
  toFun f w := if lastBit n w = b then f (prefixSucc n w) else 0
  map_add' f g := by
    ext w
    by_cases h : lastBit n w = b <;> simp [h]
  map_smul' a f := by
    ext w
    by_cases h : lastBit n w = b <;> simp [h]

def branchAdjoint (n : ℕ) (b : Bool) : Stage (n + 1) →ₗ[ℝ] Stage n where
  toFun f w := f (extendSucc n w b)
  map_add' f g := by
    ext w
    rfl
  map_smul' a f := by
    ext w
    rfl

def diagonalEmbed (n : ℕ) : Stage n →ₗ[ℝ] Stage (n + 1) where
  toFun f w := f (prefixSucc n w)
  map_add' f g := by
    ext w
    rfl
  map_smul' a f := by
    ext w
    rfl

@[simp]
theorem branch_apply (n : ℕ) (b : Bool) (f : Stage n) (w : BitWord (n + 1)) :
    branch n b f w = if lastBit n w = b then f (prefixSucc n w) else 0 :=
  rfl

@[simp]
theorem branchAdjoint_apply (n : ℕ) (b : Bool) (f : Stage (n + 1))
    (w : BitWord n) :
    branchAdjoint n b f w = f (extendSucc n w b) :=
  rfl

@[simp]
theorem diagonalEmbed_apply (n : ℕ) (f : Stage n) (w : BitWord (n + 1)) :
    diagonalEmbed n f w = f (prefixSucc n w) :=
  rfl

theorem branch_add_eq_diagonalEmbed (n : ℕ) (f : Stage n) :
    branch n false f + branch n true f = diagonalEmbed n f := by
  ext w
  cases h : lastBit n w with
  | false =>
      simp [branch, diagonalEmbed, h]
  | true =>
      simp [branch, diagonalEmbed, h]

theorem branch_add_eq_diagonalEmbed_linear (n : ℕ) :
    branch n false + branch n true = diagonalEmbed n := by
  apply LinearMap.ext
  intro f
  exact branch_add_eq_diagonalEmbed n f

theorem branchAdjoint_diagonalEmbed (n : ℕ) (b : Bool) (f : Stage n) :
    branchAdjoint n b (diagonalEmbed n f) = f := by
  ext w
  simp [branchAdjoint, diagonalEmbed, prefixSucc_extendSucc]

theorem diagonalEmbed_injective (n : ℕ) :
    Function.Injective (diagonalEmbed n) := by
  intro f g h
  have h' := congrArg (branchAdjoint n false) h
  simpa [branchAdjoint_diagonalEmbed] using h'

theorem branchAdjoint_comp_branch (n : ℕ) (b : Bool) :
    (branchAdjoint n b).comp (branch n b) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  ext w
  simp [branch, branchAdjoint, lastBit_extendSucc,
    prefixSucc_extendSucc, extendSucc_prefixSucc_lastBit]

theorem branchAdjoint_false_comp_branch_true (n : ℕ) :
    (branchAdjoint n false).comp (branch n true) = 0 := by
  apply LinearMap.ext
  intro f
  ext w
  simp [branch, branchAdjoint, lastBit_extendSucc,
    prefixSucc_extendSucc, extendSucc_prefixSucc_lastBit]

theorem branchAdjoint_true_comp_branch_false (n : ℕ) :
    (branchAdjoint n true).comp (branch n false) = 0 := by
  apply LinearMap.ext
  intro f
  ext w
  simp [branch, branchAdjoint, lastBit_extendSucc,
    prefixSucc_extendSucc, extendSucc_prefixSucc_lastBit]

theorem branchAdjoint_comp_branch_of_ne (n : ℕ) {b c : Bool} (h : b ≠ c) :
    (branchAdjoint n b).comp (branch n c) = 0 := by
  cases b <;> cases c
  · exact (h rfl).elim
  · exact branchAdjoint_false_comp_branch_true n
  · exact branchAdjoint_true_comp_branch_false n
  · exact (h rfl).elim

theorem branch_range_partition (n : ℕ) :
    (branch n false).comp (branchAdjoint n false) +
        (branch n true).comp (branchAdjoint n true) =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  ext w
  cases h : lastBit n w with
  | false =>
      change
        (if lastBit n w = false then
            f (extendSucc n (prefixSucc n w) false) else 0) +
          (if lastBit n w = true then
            f (extendSucc n (prefixSucc n w) true) else 0) = f w
      rw [if_pos h]
      have hne : lastBit n w ≠ true := by simp [h]
      rw [if_neg hne]
      rw [← h]
      rw [extendSucc_prefixSucc_lastBit]
      simp
  | true =>
      change
        (if lastBit n w = false then
            f (extendSucc n (prefixSucc n w) false) else 0) +
          (if lastBit n w = true then
            f (extendSucc n (prefixSucc n w) true) else 0) = f w
      have hne : lastBit n w ≠ false := by simp [h]
      rw [if_neg hne, if_pos h]
      rw [← h]
      rw [extendSucc_prefixSucc_lastBit]
      simp

theorem branch_false_isometry (n : ℕ) :
    (branchAdjoint n false).comp (branch n false) = LinearMap.id :=
  branchAdjoint_comp_branch n false

theorem branch_true_isometry (n : ℕ) :
    (branchAdjoint n true).comp (branch n true) = LinearMap.id :=
  branchAdjoint_comp_branch n true

end InfoGeometry.Canonical.FiniteCantorCuntzBranches
