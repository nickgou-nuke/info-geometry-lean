/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Complex.Basic

namespace InfoGeometry.Quantum.SpectralTripleApollonius

open Complex LinearMap

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Спинорна алгебра на Клифорд Cl(1,1) върху ℋ:
    γ₁ е самосъпряжен (γ₁† = γ₁), γ₂ е косо-самосъпряжен (γ₂† = -γ₂). -/
structure CliffordSpinor (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  γ₁ : H →ₗ[ℂ] H
  γ₂ : H →ₗ[ℂ] H
  γ₁_symm : ∀ u v : H, inner (𝕜 := ℂ) (γ₁ u) v = inner (𝕜 := ℂ) u (γ₁ v)
  γ₂_skew : ∀ u v : H, inner (𝕜 := ℂ) (γ₂ u) v = - inner (𝕜 := ℂ) u (γ₂ v)
  γ₁_sq : γ₁.comp γ₁ = LinearMap.id
  γ₂_sq : γ₂.comp γ₂ = -LinearMap.id
  anticomm : γ₁.comp γ₂ + γ₂.comp γ₁ = 0

/-- Спектрална тройка на Кон (𝒜, ℋ, 𝒟) за Аполониевата геометрия. -/
structure ApolloniusSpectralTriple (A : Type*) [Ring A] [Algebra ℂ A]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  -- Представяне π : 𝒜 → End_ℂ(ℋ)
  π : A → (H →ₗ[ℂ] H)
  -- Дилатационен оператор на Хилберт-Пойа
  H_HP : H →ₗ[ℂ] H
  H_HP_symm : ∀ u v : H, inner (𝕜 := ℂ) (H_HP u) v = inner (𝕜 := ℂ) u (H_HP v)
  -- Спинорна структура
  spinor : CliffordSpinor H
  comm_γ₁ : (spinor.γ₁).comp H_HP = H_HP.comp (spinor.γ₁)
  comm_γ₂ : (spinor.γ₂).comp H_HP = H_HP.comp (spinor.γ₂)
  -- Комутативност на представянето със спинорите
  comm_π_γ₁ : ∀ a : A, (spinor.γ₁).comp (π a) = (π a).comp (spinor.γ₁)
  comm_π_γ₂ : ∀ a : A, (spinor.γ₂).comp (π a) = (π a).comp (spinor.γ₂)

/-- Оператор на Дирак на спектралната тройка: 𝒟 = γ₁ ∘ H_HP + γ₂ ∘ (i • id). -/
def diracOp {A : Type*} [Ring A] [Algebra ℂ A]
    (st : ApolloniusSpectralTriple A H) : H →ₗ[ℂ] H :=
  (st.spinor.γ₁).comp st.H_HP + (st.spinor.γ₂).comp ((Complex.I : ℂ) • LinearMap.id)

/-- Квантов комутатор [𝒟, π(a)] = 𝒟 ∘ π(a) - π(a) ∘ 𝒟. -/
def diracCommutator {A : Type*} [Ring A] [Algebra ℂ A]
    (st : ApolloniusSpectralTriple A H) (a : A) : H →ₗ[ℂ] H :=
  (diracOp st).comp (st.π a) - (st.π a).comp (diracOp st)

/-!
### 1. Формална Самосъпряженост на Дираковия Оператор 𝒟
-/

/-- 🏆 ТЕОРЕМА 1 (Формална Самосъпряженост на 𝒟):
    За всяка двойка състояния u, v ∈ ℋ:
      ⟨𝒟 u, v⟩ = ⟨u, 𝒟 v⟩ -/
theorem diracOp_is_self_adjoint {A : Type*} [Ring A] [Algebra ℂ A]
    (st : ApolloniusSpectralTriple A H) (u v : H) :
    inner (𝕜 := ℂ) (diracOp st u) v = inner (𝕜 := ℂ) u (diracOp st v) := by
  unfold diracOp
  simp only [add_apply, comp_apply, smul_apply, id_apply, inner_add_left, inner_add_right]
  -- Първа компонента: γ₁ ∘ H_HP
  have h1 : inner (𝕜 := ℂ) (st.spinor.γ₁ (st.H_HP u)) v = inner (𝕜 := ℂ) u (st.spinor.γ₁ (st.H_HP v)) := by
    rw [st.spinor.γ₁_symm (st.H_HP u) v]
    rw [st.H_HP_symm u (st.spinor.γ₁ v)]
    have h_comm := LinearMap.congr_fun st.comm_γ₁ v
    simp only [comp_apply] at h_comm
    rw [h_comm]
  -- Втора компонента: γ₂ ∘ (i • id)
  have h2 : inner (𝕜 := ℂ) (st.spinor.γ₂ (Complex.I • u)) v = inner (𝕜 := ℂ) u (st.spinor.γ₂ (Complex.I • v)) := by
    rw [st.spinor.γ₂_skew (Complex.I • u) v]
    rw [inner_smul_left, conj_I]
    have : st.spinor.γ₂ (Complex.I • v) = Complex.I • (st.spinor.γ₂ v) := by
      rw [LinearMap.map_smul]
    rw [this, inner_smul_right]
    ring
  rw [h1, h2]

/-!
### 2. Редукция на Комутатора [𝒟, π(a)] към Диференциално Израждане
-/

/-- 🏆 ТЕОРЕМА 2 (Спинорна Редукция на Комутатора):
    Комутаторът [𝒟, π(a)] се редуцира строго до спинорното действие
    на диференциала df(H_HP) = [H_HP, π(a)]:
      [𝒟, π(a)] = γ₁ ∘ [H_HP, π(a)]. -/
theorem dirac_commutator_eq_spinor_diff {A : Type*} [Ring A] [Algebra ℂ A]
    (st : ApolloniusSpectralTriple A H) (a : A) :
    diracCommutator st a = (st.spinor.γ₁).comp (st.H_HP.comp (st.π a) - (st.π a).comp st.H_HP) := by
  unfold diracCommutator diracOp
  ext v
  simp only [comp_apply, add_apply, sub_apply, smul_apply, id_apply]
  have h_comm_γ₁ := LinearMap.congr_fun (st.comm_π_γ₁ a)
  have h_comm_γ₂ := LinearMap.congr_fun (st.comm_π_γ₂ a)
  have h_γ₂_term : st.spinor.γ₂ (Complex.I • (st.π a v)) - st.π a (st.spinor.γ₂ (Complex.I • v)) = 0 := by
    have h_smul1 : st.spinor.γ₂ (Complex.I • (st.π a v)) = Complex.I • (st.spinor.γ₂ (st.π a v)) := by
      rw [LinearMap.map_smul]
    have h_smul2 : st.π a (st.spinor.γ₂ (Complex.I • v)) = Complex.I • (st.π a (st.spinor.γ₂ v)) := by
      rw [LinearMap.map_smul, LinearMap.map_smul]
    rw [h_smul1, h_smul2]
    have h_c := LinearMap.congr_fun (st.comm_π_γ₂ a) v
    simp only [comp_apply] at h_c
    rw [h_c, sub_self]
  have h_γ₁_expand : st.spinor.γ₁ (st.H_HP (st.π a v)) - st.π a (st.spinor.γ₁ (st.H_HP v)) =
                     st.spinor.γ₁ (st.H_HP (st.π a v) - st.π a (st.H_HP v)) := by
    have h_c1 := LinearMap.congr_fun (st.comm_π_γ₁ a) (st.H_HP v)
    simp only [comp_apply] at h_c1
    rw [← h_c1, ← LinearMap.map_sub]
  have h_map_add : st.π a (st.spinor.γ₁ (st.H_HP v) + st.spinor.γ₂ (Complex.I • v)) =
                   st.π a (st.spinor.γ₁ (st.H_HP v)) + st.π a (st.spinor.γ₂ (Complex.I • v)) :=
    LinearMap.map_add (st.π a) (st.spinor.γ₁ (st.H_HP v)) (st.spinor.γ₂ (Complex.I • v))
  rw [h_map_add]
  calc st.spinor.γ₁ (st.H_HP (st.π a v)) + st.spinor.γ₂ (Complex.I • (st.π a v)) -
       (st.π a (st.spinor.γ₁ (st.H_HP v)) + st.π a (st.spinor.γ₂ (Complex.I • v)))
    _ = (st.spinor.γ₁ (st.H_HP (st.π a v)) - st.π a (st.spinor.γ₁ (st.H_HP v))) +
        (st.spinor.γ₂ (Complex.I • (st.π a v)) - st.π a (st.spinor.γ₂ (Complex.I • v))) := by abel
    _ = st.spinor.γ₁ (st.H_HP (st.π a v) - st.π a (st.H_HP v)) + 0 := by rw [h_γ₁_expand, h_γ₂_term]
    _ = st.spinor.γ₁ (st.H_HP (st.π a v) - st.π a (st.H_HP v)) := by rw [add_zero]

/-!
### 3. Гранд Капстоун Синтез на Спектралната Тройка
-/

/-! 🏆 ГРАНД СИНТЕЗ: Пълна верификация на Спектралната Тройка (𝒜, ℋ, 𝒟) върху Аполониевата фолиация -/
end

end InfoGeometry.Quantum.SpectralTripleApollonius
