import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Clifford

/-- Split quadratic form of signature `(1,1)` on `ℝ × ℝ`: `x₁² - x₂²`. -/
noncomputable def splitQ11 : QuadraticForm ℝ (ℝ × ℝ) :=
  QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ)
    - QuadraticMap.linMulLin (LinearMap.snd ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)

@[simp] lemma splitQ11_apply (x : ℝ × ℝ) : splitQ11 x = x.1 * x.1 - x.2 * x.2 := by simp [splitQ11]

noncomputable def splitB11 : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun q := {
    toFun := fun k => q.1 * k.1 - q.2 * k.2
    map_add' := by intros x y; simp; ring
    map_smul' := by intros m x; simp [RingHom.id_apply]; ring
  }
  map_add' := by intros x y; apply LinearMap.ext; intro k; simp; ring
  map_smul' := by intros m x; apply LinearMap.ext; intro k; simp [RingHom.id_apply]; ring

@[simp] lemma splitB11_apply (x y : ℝ × ℝ) : splitB11 x y = x.1 * y.1 - x.2 * y.2 := rfl
lemma splitB11_expand (q k : ℝ × ℝ) : splitB11 q k = q.1 * k.1 - q.2 * k.2 := rfl

@[simp] lemma splitB11_symm (x y : ℝ × ℝ) : splitB11 x y = splitB11 y x := by
  simp [splitB11_apply, mul_comm]

lemma splitQ11_eq_splitB11_diag (x : ℝ × ℝ) : splitQ11 x = splitB11 x x := by simp

@[simp] theorem splitQ11_add (x y : ℝ × ℝ) :
    splitQ11 (x + y) = splitQ11 x + splitQ11 y + 2 * splitB11 x y := by
  simp only [splitQ11_apply, splitB11_apply, Prod.fst_add, Prod.snd_add]
  ring

theorem splitQ11_sub (x y : ℝ × ℝ) :
    splitQ11 (x - y) = splitQ11 x + splitQ11 y - 2 * splitB11 x y := by
  simp only [splitQ11_apply, splitB11_apply, Prod.fst_sub, Prod.snd_sub]
  ring

theorem splitB11_eq_half_polarization (x y : ℝ × ℝ) :
    splitB11 x y = (splitQ11 (x + y) - splitQ11 x - splitQ11 y) / 2 := by
  rw [splitQ11_add]
  ring

def IsTimelike (v : ℝ × ℝ) : Prop := 0 < splitQ11 v
def IsSpacelike (v : ℝ × ℝ) : Prop := splitQ11 v < 0
def IsLightlike (v : ℝ × ℝ) : Prop := splitQ11 v = 0

end InfoGeometry.Clifford
