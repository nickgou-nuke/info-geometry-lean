import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionQuaternionPolar

noncomputable section

namespace SplitOctonion

instance : AddCommGroup SplitOctonion where
  add := HAdd.hAdd
  add_assoc := by
    intro x y z
    apply SplitOctonion.ext <;> simp [add_assoc]
  zero := 0
  zero_add := by
    intro x
    apply SplitOctonion.ext <;> simp
  add_zero := by
    intro x
    apply SplitOctonion.ext <;> simp
  nsmul := nsmulRec
  nsmul_zero := by
    intro x
    rfl
  nsmul_succ := by
    intro n x
    rfl
  neg := Neg.neg
  sub := Sub.sub
  sub_eq_add_neg := by
    intro x y
    rfl
  zsmul := zsmulRec
  zsmul_zero' := by
    intro x
    rfl
  zsmul_succ' := by
    intro n x
    rfl
  zsmul_neg' := by
    intro n x
    rfl
  neg_add_cancel := by
    intro x
    apply SplitOctonion.ext <;> simp
  add_comm := by
    intro x y
    apply SplitOctonion.ext <;> simp [add_comm]

instance : Module ℝ SplitOctonion where
  smul := HSMul.hSMul
  one_smul := by
    intro x
    apply SplitOctonion.ext <;> simp
  mul_smul := by
    intro r s x
    apply SplitOctonion.ext
    · exact (smul_smul r s x.a).symm
    · exact (smul_smul r s x.b).symm
  smul_zero := by
    intro r
    apply SplitOctonion.ext <;> simp
  smul_add := by
    intro r x y
    apply SplitOctonion.ext
    · exact smul_add r x.a y.a
    · exact smul_add r x.b y.b
  add_smul := by
    intro r s x
    apply SplitOctonion.ext
    · change (r + s) • x.a = r • x.a + s • x.a
      exact add_smul r s x.a
    · change (r + s) • x.b = r • x.b + s • x.b
      exact add_smul r s x.b
  zero_smul := by
    intro x
    apply SplitOctonion.ext
    · change (0 : ℝ) • x.a = 0
      exact zero_smul ℝ x.a
    · change (0 : ℝ) • x.b = 0
      exact zero_smul ℝ x.b

instance : NonUnitalNonAssocRing SplitOctonion where
  left_distrib := by
    intro x y z
    apply SplitOctonion.ext <;>
      simp [mul_a, mul_b, add_a, add_b, add_mul, mul_add] <;> abel
  right_distrib := by
    intro x y z
    apply SplitOctonion.ext <;>
      simp [mul_a, mul_b, add_a, add_b, add_mul, mul_add] <;> abel
  zero_mul := by
    intro x
    apply SplitOctonion.ext <;> simp [mul_a, mul_b]
  mul_zero := by
    intro x
    apply SplitOctonion.ext <;> simp [mul_a, mul_b]

def leftRegular (x : SplitOctonion) : Module.End ℝ SplitOctonion :=
  { toFun := fun y => x * y
    map_add' := by
      intro y z
      apply SplitOctonion.ext <;>
        simp [mul_a, mul_b, add_a, add_b, mul_add]
    map_smul' := by
      intro r y
      apply SplitOctonion.ext <;>
        simp [mul_a, mul_b, smul_a, smul_b, smul_mul, mul_smul] }

def rightRegular (x : SplitOctonion) : Module.End ℝ SplitOctonion :=
  { toFun := fun y => y * x
    map_add' := by
      intro y z
      apply SplitOctonion.ext <;>
        simp [mul_a, mul_b, add_a, add_b, add_mul]
    map_smul' := by
      intro r y
      apply SplitOctonion.ext <;>
        simp [mul_a, mul_b, smul_a, smul_b, smul_mul, mul_smul] }

@[simp] theorem leftRegular_apply (x y : SplitOctonion) :
    leftRegular x y = x * y := rfl

@[simp] theorem rightRegular_apply (x y : SplitOctonion) :
    rightRegular x y = y * x := rfl

theorem leftRegular_apply_one (x : SplitOctonion) :
    leftRegular x 1 = x := by
  apply SplitOctonion.ext <;> simp [mul_a, mul_b]

theorem leftRegular_injective :
    Function.Injective leftRegular := by
  intro x y h
  have h1 := LinearMap.congr_fun h 1
  rw [leftRegular_apply_one, leftRegular_apply_one] at h1
  exact h1

def associator (x y z : SplitOctonion) : SplitOctonion :=
  (x * y) * z - x * (y * z)

def leftRegularComp (x y : SplitOctonion) : Module.End ℝ SplitOctonion :=
  (leftRegular x).comp (leftRegular y)

def associatorOperator (x y : SplitOctonion) : Module.End ℝ SplitOctonion :=
  leftRegular (x * y) - leftRegularComp x y

theorem associatorOperator_apply (x y z : SplitOctonion) :
    associatorOperator x y z = associator x y z := by
  rfl

theorem leftRegular_comp_defect_apply (x y z : SplitOctonion) :
    associatorOperator x y z =
      associator x y z := by
  exact associatorOperator_apply x y z

theorem rightRegular_comp_defect_apply (x y z : SplitOctonion) :
    rightRegular z (rightRegular y x) - rightRegular (y * z) x =
      associator x y z := by
  simp [associator]

theorem leftRegular_comp_eq_iff_associator_zero (x y : SplitOctonion) :
    leftRegular (x * y) = (leftRegular x).comp (leftRegular y) ↔
      ∀ z, associator x y z = 0 := by
  constructor
  · intro h z
    have hz := leftRegular_comp_defect_apply x y z
    have hpoint := LinearMap.congr_fun h z
    change leftRegular (x * y) z -
      (leftRegular x).comp (leftRegular y) z = associator x y z at hz
    rw [hpoint] at hz
    simpa using hz.symm
  · intro h
    apply LinearMap.ext
    intro z
    change leftRegular (x * y) z = leftRegular x (leftRegular y z)
    have hz := leftRegular_comp_defect_apply x y z
    rw [h z] at hz
    exact sub_eq_zero.mp hz

end SplitOctonion
