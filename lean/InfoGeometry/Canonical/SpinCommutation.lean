import Mathlib.Tactic
import Mathlib.Algebra.Quaternion

namespace InfoGeometry.Canonical.SpinCommutation

open Quaternion

/--
Standard Quaternions represent the Cl⁺(3,0; ℝ) subalgebra.
We map the geometric bivectors as:
e₂e₃ -> i
e₃e₁ -> j
e₁e₂ -> -k
-/
def e23 : Quaternion ℝ := ⟨0, 1, 0, 0⟩
def e31 : Quaternion ℝ := ⟨0, 0, 1, 0⟩
def e12 : Quaternion ℝ := ⟨0, 0, 0, -1⟩

/-- The standard commutator [A, B] = A * B - B * A -/
noncomputable def comm (A B : Quaternion ℝ) : Quaternion ℝ := A * B - B * A

/--
The geometric algebra commutator of the bivectors.
Notice that [e₂e₃, e₃e₁] = -2e₁e₂ exactly.
-/
theorem bivector_commutation : comm e23 e31 = -(2 : ℝ) • e12 := by
  ext <;> simp [comm, e23, e31, e12] <;> ring

/--
If we define spin operators as Sₖ = (1/2) * bivectorₖ
(Setting ħ=1 for algebraic clarity)
Then [S₁, S₂] = -S₃
-/
noncomputable def S1 : Quaternion ℝ := (1/2 : ℝ) • e23
noncomputable def S2 : Quaternion ℝ := (1/2 : ℝ) • e31
noncomputable def S3 : Quaternion ℝ := (1/2 : ℝ) • e12

theorem spin_commutation : comm S1 S2 = -S3 := by
  ext <;> simp [comm, S1, S2, S3, e23, e31, e12] <;> ring

/--
To recover the standard Quantum Mechanical commutation relation [S₁, S₂] = iS₃,
the mapping into M₂(ℂ) must insert the imaginary unit 'i_c', mapping
e₂e₃ ↦ -i_c σ₁, etc. In the pure geometric framework, the relation is exactly -S₃.
-/
theorem geometric_to_qm_clarification : comm S1 S2 = -S3 := spin_commutation

end InfoGeometry.Canonical.SpinCommutation
