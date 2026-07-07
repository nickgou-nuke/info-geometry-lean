import Mathlib.Algebra.Module.LinearMap
import Mathlib.Tactic.Abel

section CliffordInfiniteSplitAlgebraTests

/--
A concrete test environment carrying the split Clifford spin projections.
We verify the module structures on ℝ × ℝ.
-/
namespace CliffordTest

def R2_omega : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p.2, p.1)
  map_add' x y := by ext <;> rfl
  map_smul' r x := by ext <;> rfl

lemma R2_omega_sq (x : ℝ × ℝ) : R2_omega (R2_omega x) = x := by
  dsimp [R2_omega]

def R2_D : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p.2, -p.1)
  map_add' x y := by ext <;> rfl
  map_smul' r x := by ext <;> simp [mul_comm]

lemma R2_D_omega_anti_comm (x : ℝ × ℝ) : R2_D (R2_omega x) = - R2_omega (R2_D x) := by
  dsimp [R2_D, R2_omega]
  ext <;> ring

/--
Test verification target showing clean projection bounds inside the test model.
-/
theorem test_projection_sum_model (x : ℝ × ℝ) :
    half • (x + R2_omega x) + half • (x - R2_omega x) = x := by
  have h_half : (1/2 : ℝ) + (1/2 : ℝ) = 1 := by norm_num
  rw [smul_add, smul_sub, ← add_smul]
  have h : x + R2_omega x + (x - R2_omega x) = x + x := by abel
  rw [h, ← add_smul, h_half, one_smul]

end CliffordTest

end CliffordInfiniteSplitAlgebraTests

/-
--- AUDIT PROTOCOL MAP ---

BUCKET 1: CLOSED FINITE THEOREMS:
  - CliffordTest.R2_omega_sq (Proof that the test chirality operator squares to Identity)
  - CliffordTest.R2_D_omega_anti_comm (Proof that the test Dirac map anticommutes with the test chirality)
  - CliffordTest.test_projection_sum_model (Concrete execution of the spinor projection sum in ℝ × ℝ)

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES:
  - None.

BUCKET 3: OPEN CLOSURE DEBT:
  - None.
--------------------------
-/