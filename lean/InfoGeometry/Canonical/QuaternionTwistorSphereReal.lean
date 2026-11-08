import Mathlib.Algebra.Quaternion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.QuaternionicOperatorFrame

/-! The quaternionic twistor sphere as real-linear complex structures. -/

noncomputable section

namespace InfoGeometry.Canonical.QuaternionTwistorSphereReal

structure Point where
  a : ℝ
  b : ℝ
  c : ℝ
  unit : a ^ 2 + b ^ 2 + c ^ 2 = 1

def quaternion (p : Point) : Quaternion ℝ :=
  { re := 0, imI := p.a, imJ := p.b, imK := p.c }

@[simp] theorem quaternion_re (p : Point) : (quaternion p).re = 0 := rfl

theorem quaternion_sq (p : Point) : quaternion p ^ 2 = -(1 : Quaternion ℝ) := by
  rw [(Quaternion.sq_eq_neg_normSq).2 (quaternion_re p)]
  simp [quaternion, Quaternion.normSq_def', p.unit]

def leftAction (q : Quaternion ℝ) : Quaternion ℝ →ₗ[ℝ] Quaternion ℝ where
  toFun x := q * x
  map_add' x y := mul_add q x y
  map_smul' r x := by simp [mul_smul_comm]

theorem leftAction_mul (q r : Quaternion ℝ) :
    (leftAction q).comp (leftAction r) = leftAction (q * r) := by
  apply LinearMap.ext
  intro x
  simp [leftAction, LinearMap.comp_apply, mul_assoc]

def complexStructure (p : Point) : Quaternion ℝ →ₗ[ℝ] Quaternion ℝ :=
  leftAction (quaternion p)

theorem complexStructure_sq (p : Point) :
    (complexStructure p).comp (complexStructure p) =
      -(LinearMap.id : Quaternion ℝ →ₗ[ℝ] Quaternion ℝ) := by
  apply LinearMap.ext
  intro x
  change quaternion p * (quaternion p * x) = -x
  rw [← mul_assoc, ← pow_two, quaternion_sq p]
  simp

end InfoGeometry.Canonical.QuaternionTwistorSphereReal
