import InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.SplitSpinFactorTKKInjectivityNative

open InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66
open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
open InfoGeometry.Canonical.SplitSpinFactorHomothetySO55

abbrev V10 := SplitSpinFactorTKKConformalSO66.V10
abbrev End12 := V12 → V12

theorem B10_add_left (u v w : V10) :
    B10 (u + v) w = B10 u w + B10 v w := by
  rcases u with ⟨⟨u1, u2⟩, ux⟩
  rcases v with ⟨⟨v1, v2⟩, vx⟩
  rcases w with ⟨⟨w1, w2⟩, wx⟩
  simp [B10, zornPolar, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVectorMatrix.smul, ZornVec3.dot,
    Fin.sum_univ_three]
  ring

theorem B10_add_right (u v w : V10) :
    B10 u (v + w) = B10 u v + B10 u w := by
  rw [B10_symm, B10_add_left, B10_symm v u, B10_symm w u]

@[simp] theorem B10_neg_left (u v : V10) :
    B10 (-u) v = -B10 u v := by
  simpa using B10_smul_left (-1 : ℝ) u v

@[simp] theorem B10_neg_right (u v : V10) :
    B10 u (-v) = -B10 u v := by
  rw [B10_symm, B10_neg_left, B10_symm v u]

def B10SkewEnd : Submodule ℝ (Module.End ℝ V10) where
  carrier := {A | ∀ u v, B10 (A u) v + B10 u (A v) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A C hA hC u v
    simp only [LinearMap.add_apply, B10_add_left, B10_add_right]
    linarith [hA u v, hC u v]
  smul_mem' := by
    intro r A hA u v
    simp only [LinearMap.smul_apply, B10_smul_left, B10_smul_right]
    rw [← mul_add, hA u v, mul_zero]

def middleRotation (A : Module.End ℝ V10) : End12 :=
  fun x => (0, (A x.2.1, 0))

def tkkParamMap :
    (V10 × ((ℝ × B10SkewEnd) × V10)) →ₗ[ℝ] End12 where
  toFun p := pGen p.1 + dGen p.2.1.1 +
    middleRotation p.2.1.2.1 + kGen p.2.2
  map_add' p q := by
    funext x
    simp [pGen, dGen, kGen, middleRotation, B10_add_left, B10_add_right]
    constructor
    · ring
    · constructor
      · module
      · ring
  map_smul' r p := by
    funext x
    simp [pGen, dGen, kGen, middleRotation, smul_smul]
    constructor
    · ring
    · constructor
      · module
      · ring

theorem tkk_param_zero_components
    (u : V10) (a : ℝ) (A : Module.End ℝ V10) (v : V10)
    (hzero : pGen u + dGen a + middleRotation A + kGen v = 0) :
    u = 0 ∧ a = 0 ∧ A = 0 ∧ v = 0 := by
  have h1 :
      (pGen u + dGen a + middleRotation A + kGen v)
          (1, ((0 : V10), 0)) = 0 := by
    rw [hzero]
    rfl
  have ha : a = 0 := by
    have h := congrArg Prod.fst h1
    simpa [pGen, dGen, middleRotation, kGen] using h
  have hv : v = 0 := by
    have h := congrArg (fun p : V12 => p.2.1) h1
    simpa [pGen, dGen, middleRotation, kGen] using h
  have h2 :
      (pGen u + dGen a + middleRotation A + kGen v)
          (0, ((0 : V10), 1)) = 0 := by
    rw [hzero]
    rfl
  have hu : u = 0 := by
    have h := congrArg (fun p : V12 => p.2.1) h2
    simpa [pGen, dGen, middleRotation, kGen] using h
  have hA : A = 0 := by
    apply LinearMap.ext
    intro z
    have hz :
        (pGen u + dGen a + middleRotation A + kGen v)
            (0, (z, 0)) = 0 := by
      rw [hzero]
      rfl
    have h := congrArg (fun p : V12 => p.2.1) hz
    rw [hu, ha, hv] at h
    simpa [pGen, dGen, middleRotation, kGen] using h
  exact ⟨hu, ha, hA, hv⟩

theorem tkkParamMap_injective : Function.Injective tkkParamMap := by
  intro p q hpq
  rcases p with ⟨u, ⟨⟨a, A⟩, v⟩⟩
  rcases q with ⟨u', ⟨⟨a', A'⟩, v'⟩⟩
  have hzero : pGen (u - u') + dGen (a - a') +
      middleRotation (A.1 - A'.1) + kGen (v - v') = 0 := by
    have h := hpq
    change pGen u + dGen a + middleRotation A.1 + kGen v =
      pGen u' + dGen a' + middleRotation A'.1 + kGen v' at h
    have hz := sub_eq_zero.mpr h
    apply funext
    intro x
    have hx := congrFun hz x
    simp [sub_eq_add_neg, pGen, dGen, kGen, middleRotation,
      B10_sub_left, B10_sub_right] at hx ⊢
    rcases hx with ⟨hx₁, hx₂, hx₃⟩
    constructor
    · rw [B10_symm, B10_add_left, B10_neg_left]
      linear_combination hx₁
    · constructor
      · simpa [add_assoc, add_comm, add_left_comm] using hx₂
      · rw [B10_symm, B10_add_left, B10_neg_left]
        linear_combination hx₃
  rcases tkk_param_zero_components (u - u') (a - a')
      (A.1 - A'.1) (v - v') hzero with ⟨hu, ha, hA, hv⟩
  have hu' : u = u' := sub_eq_zero.mp hu
  have ha' : a = a' := sub_eq_zero.mp ha
  have hv' : v = v' := sub_eq_zero.mp hv
  have hAA' : A = A' := by
    apply Subtype.ext
    exact sub_eq_zero.mp hA
  cases hu'
  cases ha'
  cases hv'
  cases hAA'
  rfl

noncomputable def tkkParamRangeEquiv :
    (SplitSpinFactorTKKConformalSO66.V10 ×
      ((ℝ × B10SkewEnd) × SplitSpinFactorTKKConformalSO66.V10)) ≃ₗ[ℝ]
      LinearMap.range tkkParamMap :=
  LinearEquiv.ofInjective tkkParamMap tkkParamMap_injective

end InfoGeometry.Canonical.SplitSpinFactorTKKInjectivityNative
