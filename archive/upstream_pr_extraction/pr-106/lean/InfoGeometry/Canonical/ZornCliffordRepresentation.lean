import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Canonical.ZornSpinor

noncomputable section

namespace InfoGeometry.Canonical.ZornClifford

open InfoGeometry.Canonical.ZornMatrix

variable {R : Type*} [CommRing R]

lemma smul_a (c : R) (z : ZornMatrix R) : (c • z).a = c * z.a := rfl
lemma smul_b (c : R) (z : ZornMatrix R) : (c • z).b = c * z.b := rfl
lemma smul_x (c : R) (z : ZornMatrix R) : (c • z).x = c • z.x := rfl
lemma smul_y (c : R) (z : ZornMatrix R) : (c • z).y = c • z.y := rfl

lemma add_a (z1 z2 : ZornMatrix R) : (z1 + z2).a = z1.a + z2.a := rfl
lemma add_b (z1 z2 : ZornMatrix R) : (z1 + z2).b = z1.b + z2.b := rfl
lemma add_x (z1 z2 : ZornMatrix R) : (z1 + z2).x = z1.x + z2.x := rfl
lemma add_y (z1 z2 : ZornMatrix R) : (z1 + z2).y = z1.y + z2.y := rfl

lemma sub_a (z1 z2 : ZornMatrix R) : (z1 - z2).a = z1.a - z2.a := rfl
lemma sub_b (z1 z2 : ZornMatrix R) : (z1 - z2).b = z1.b - z2.b := rfl
lemma sub_x (z1 z2 : ZornMatrix R) : (z1 - z2).x = z1.x - z2.x := rfl
lemma sub_y (z1 z2 : ZornMatrix R) : (z1 - z2).y = z1.y - z2.y := rfl

attribute [local simp] smul_a smul_b smul_x smul_y add_a add_b add_x add_y sub_a sub_b sub_x sub_y Pi.smul_apply Pi.add_apply Pi.sub_apply Pi.neg_apply Matrix.vecHead Matrix.vecTail Matrix.cons_val_zero Matrix.cons_val_one Matrix.cons_val_two Matrix.cons_val_succ

/-- The canonical conjugation on Zorn matrices. -/
def zornConj (z : ZornMatrix R) : ZornMatrix R :=
  { a := z.b, b := z.a, x := -z.x, y := -z.y }

theorem zornConj_add (z1 z2 : ZornMatrix R) :
    zornConj (z1 + z2) = zornConj z1 + zornConj z2 := by
  ext <;> simp [zornConj] <;> try ring

theorem zornConj_smul (c : R) (z : ZornMatrix R) :
    zornConj (c • z) = c • zornConj z := by
  ext <;> simp [zornConj]

theorem mul_add' (z1 z2 z3 : ZornMatrix R) :
    z1 * (z2 + z3) = z1 * z2 + z1 * z3 := by
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, cross]; ring
  · simp [mul_def, mul, dot, cross]; ring
  · funext i; fin_cases i <;> simp [mul_def, mul, dot, cross] <;> ring
  · funext i; fin_cases i <;> simp [mul_def, mul, dot, cross] <;> ring

theorem add_mul' (z1 z2 z3 : ZornMatrix R) :
    (z1 + z2) * z3 = z1 * z3 + z2 * z3 := by
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, cross]; ring
  · simp [mul_def, mul, dot, cross]; ring
  · funext i; fin_cases i <;> simp [mul_def, mul, dot, cross] <;> ring
  · funext i; fin_cases i <;> simp [mul_def, mul, dot, cross] <;> ring

theorem smul_mul' (c : R) (z1 z2 : ZornMatrix R) :
    (c • z1) * z2 = c • (z1 * z2) := by
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, cross]; ring
  · simp [mul_def, mul, dot, cross]; ring
  · funext i; fin_cases i <;> simp [mul_def, mul, dot, cross] <;> ring
  · funext i; fin_cases i <;> simp [mul_def, mul, dot, cross] <;> ring

theorem mul_smul' (c : R) (z1 z2 : ZornMatrix R) :
    z1 * (c • z2) = c • (z1 * z2) := by
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, cross]; ring
  · simp [mul_def, mul, dot, cross]; ring
  · funext i; fin_cases i <;> simp [mul_def, mul, dot, cross] <;> ring
  · funext i; fin_cases i <;> simp [mul_def, mul, dot, cross] <;> ring

/-- The Zorn norm quadratic form mapping `z ↦ a * b - x ⋅ y`. -/
def zornNormFun (z : ZornMatrix R) : R :=
  z.a * z.b - dot z.x z.y

/-- The Zorn norm as a genuine quadratic form over `R`. -/
def zornNorm : QuadraticForm R (ZornMatrix R) :=
  QuadraticMap.ofPolar zornNormFun
    (by intro c z; simp [zornNormFun, dot]; ring)
    (by intro x x' y; simp [zornNormFun, dot, QuadraticMap.polar]; ring)
    (by intro c x y; simp [zornNormFun, dot, QuadraticMap.polar]; ring)

theorem zornNorm_apply (z : ZornMatrix R) :
    zornNorm z = zornNormFun z := rfl

/-! ## Carrier and Gamma Operators -/

/-- Direct sum of the two chiral Zorn carriers. -/
abbrev DiracSpinor16 := ZornMatrix R × ZornMatrix R

def cliffordMinus (V Ψ : ZornMatrix R) : ZornMatrix R :=
  V * Ψ

def cliffordPlus (V Ψ : ZornMatrix R) : ZornMatrix R :=
  zornConj V * Ψ

/-- Off-diagonal gamma action associated with a typed vector. -/
def diracGamma (V : ZornMatrix R) : Module.End R (DiracSpinor16 (R := R)) where
  toFun Ψ := (cliffordMinus V Ψ.2, cliffordPlus V Ψ.1)
  map_add' Ψ Φ := by
    apply Prod.ext
    · change V * (Ψ.2 + Φ.2) = V * Ψ.2 + V * Φ.2
      rw [mul_add']
    · change zornConj V * (Ψ.1 + Φ.1) = zornConj V * Ψ.1 + zornConj V * Φ.1
      rw [mul_add']
  map_smul' c Ψ := by
    apply Prod.ext
    · change V * (c • Ψ.2) = c • (V * Ψ.2)
      rw [mul_smul']
    · change zornConj V * (c • Ψ.1) = c • (zornConj V * Ψ.1)
      rw [mul_smul']

theorem mul_zornConj_mul (V Z : ZornMatrix R) :
    V * (zornConj V * Z) = zornNormFun V • Z := by
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, cross, zornConj, zornNormFun]; ring
  · simp [mul_def, mul, dot, cross, zornConj, zornNormFun]; ring
  · funext i; fin_cases i <;> simp [mul_def, mul, dot, cross, zornConj, zornNormFun] <;> ring
  · funext i; fin_cases i <;> simp [mul_def, mul, dot, cross, zornConj, zornNormFun] <;> ring

theorem zornConj_mul_mul (V Z : ZornMatrix R) :
    zornConj V * (V * Z) = zornNormFun V • Z := by
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, cross, zornConj, zornNormFun]; ring
  · simp [mul_def, mul, dot, cross, zornConj, zornNormFun]; ring
  · funext i; fin_cases i <;> simp [mul_def, mul, dot, cross, zornConj, zornNormFun] <;> ring
  · funext i; fin_cases i <;> simp [mul_def, mul, dot, cross, zornConj, zornNormFun] <;> ring

theorem diracGamma_sq_apply (V : ZornMatrix R) (Ψ : DiracSpinor16 (R := R)) :
    diracGamma V (diracGamma V Ψ) = zornNorm V • Ψ := by
  apply Prod.ext
  · change V * (zornConj V * Ψ.1) = zornNorm V • Ψ.1
    rw [zornNorm_apply]
    exact mul_zornConj_mul V Ψ.1
  · change zornConj V * (V * Ψ.2) = zornNorm V • Ψ.2
    rw [zornNorm_apply]
    exact zornConj_mul_mul V Ψ.2

theorem diracGamma_sq (V : ZornMatrix R) :
    diracGamma V * diracGamma V =
      algebraMap R (Module.End R (DiracSpinor16 (R := R))) (zornNorm V) := by
  apply LinearMap.ext
  intro Ψ
  exact diracGamma_sq_apply V Ψ

/-- Gamma depends linearly on its vector argument. -/
def diracGammaLinear : ZornMatrix R →ₗ[R] Module.End R (DiracSpinor16 (R := R)) where
  toFun := diracGamma
  map_add' V W := by
    apply LinearMap.ext
    intro Ψ
    apply Prod.ext
    · change (V + W) * Ψ.2 = V * Ψ.2 + W * Ψ.2
      apply add_mul'
    · change zornConj (V + W) * Ψ.1 = zornConj V * Ψ.1 + zornConj W * Ψ.1
      rw [zornConj_add, add_mul']
  map_smul' c V := by
    apply LinearMap.ext
    intro Ψ
    apply Prod.ext
    · change (c • V) * Ψ.2 = c • (V * Ψ.2)
      apply smul_mul'
    · change zornConj (c • V) * Ψ.1 = c • (zornConj V * Ψ.1)
      rw [zornConj_smul, smul_mul']

/-- The universal Clifford-algebra representation on the Zorn Dirac carrier. -/
def zornCliffordRepresentation :
    CliffordAlgebra (zornNorm (R := R)) →ₐ[R] Module.End R (DiracSpinor16 (R := R)) :=
  CliffordAlgebra.lift (zornNorm (R := R)) ⟨diracGammaLinear, diracGamma_sq⟩

@[simp] theorem zornCliffordRepresentation_ι (V : ZornMatrix R) :
    zornCliffordRepresentation (CliffordAlgebra.ι zornNorm V) =
      diracGamma V := by
  exact CliffordAlgebra.lift_ι_apply diracGammaLinear diracGamma_sq V

/-- The constructed representation restricts to the two chiral Zorn actions
on the Clifford generators. -/
theorem zornCliffordRepresentation_generator_action
    (V : ZornMatrix R) (S C : ZornMatrix R) :
    zornCliffordRepresentation (CliffordAlgebra.ι zornNorm V) (S, C) =
      (cliffordMinus V C, cliffordPlus V S) := by
  rw [zornCliffordRepresentation_ι]
  rfl

/-! ## Restriction to the complex spin group -/

/-- The universal Clifford representation sends Clifford units to invertible
linear operators.  Restricting along Mathlib's spin group gives a genuine
group representation on the sixteen-dimensional Dirac carrier. -/
def spinDiracRepresentation :
    spinGroup (zornNorm (R := R)) →* LinearMap.GeneralLinearGroup R (DiracSpinor16 (R := R)) :=
  (Units.map (zornCliffordRepresentation (R := R)).toRingHom.toMonoidHom).comp
    (spinGroup.toUnits)

theorem spinDiracRepresentation_val
    (g : spinGroup (zornNorm (R := R))) :
    ((spinDiracRepresentation (R := R) g :
      LinearMap.GeneralLinearGroup R (DiracSpinor16 (R := R))) :
        Module.End R (DiracSpinor16 (R := R))) =
      zornCliffordRepresentation (R := R) (g : CliffordAlgebra (zornNorm (R := R))) := by
  rfl

theorem spinDiracRepresentation_mul
    (g h : spinGroup (zornNorm (R := R))) :
    spinDiracRepresentation (R := R) (g * h) =
      spinDiracRepresentation (R := R) g * spinDiracRepresentation (R := R) h := by
  exact map_mul (spinDiracRepresentation (R := R)) g h

theorem spinDiracRepresentation_inv
    (g : spinGroup (zornNorm (R := R))) :
    spinDiracRepresentation (R := R) g⁻¹ =
      (spinDiracRepresentation (R := R) g)⁻¹ := by
  exact map_inv (spinDiracRepresentation (R := R)) g

end InfoGeometry.Canonical.ZornClifford
