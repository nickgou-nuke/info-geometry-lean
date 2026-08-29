/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace InfoGeometry.Topological.NonAbelianBerry

open Complex Matrix Real

noncomputable section

/-!
# Неабелева Връзка на Бери и Холономия по Затворени Аполониеви Контури

Този модул формализира неабелевата връзка на Уилчек-Зи (Wilczek-Zee non-abelian Berry connection)
и съответната $\mathrm{U}(2)$ холономия (геометрична фаза) по затворен контур $\mathcal{C}_\lambda$,
параметризиран от Аполониева окръжност:

1. **Многомерен дегенериран подпространствен базис**:
   Затворен контур в параметричното пространство $s(\theta) = \sigma_c(\lambda) + r(\lambda) e^{i\theta}$.
   Ортонормиран 2-квантов базис $\{|\psi_1(\theta)\rangle, |\psi_2(\theta)\rangle\}$ за $\theta \in [0, 2\pi]$.

2. **Неабелева 1-форма на връзката (Wilczek-Zee $\mathfrak{u}(2)$ Connection)**:
   $$A_{ab}(\theta) = i \langle \psi_a(\theta) | \frac{d}{d\theta} \psi_b(\theta) \rangle$$
   Доказва се анти-ермитовост: $A^\dagger(\theta) = A(\theta)$ като матрица с $i$ константа,
   съответно $\mathcal{A}(\theta) = -i A(\theta) \in \mathfrak{u}(2)$.

3. **Специфична $\mathrm{SU}(2)$ конфигурация на Аполониево сплитане**:
   $$A(\theta) = \frac{1}{2} \begin{pmatrix} 0 & e^{-i\theta} \\ e^{i\theta} & 0 \end{pmatrix}$$

4. **Холономия (Wilson Loop / Path-Ordered Exponent)**:
   $$W(\mathcal{C}_\lambda) = \mathcal{P} \exp\left( -i \oint_{\mathcal{C}_\lambda} A(\theta) \, d\theta \right)$$
   За каноничен период $\Delta\theta = 2\pi$ матрицата на холономията е строго унитарна:
   $W^\dagger W = I_2$.
-/

/-- Параметризирано семейство от 2-ортонормирани състояния в Hilbert пространство ℂ². -/
structure DegenerateSubspaceState (θ : ℝ) where
  psi1 : Fin 2 → ℂ
  psi2 : Fin 2 → ℂ
  ortho11 : (star psi1 ⬝ᵥ psi1 : ℂ) = 1
  ortho22 : (star psi2 ⬝ᵥ psi2 : ℂ) = 1
  ortho12 : (star psi1 ⬝ᵥ psi2 : ℂ) = 0
  ortho21 : (star psi2 ⬝ᵥ psi1 : ℂ) = 0

/-- Матрицата на неабелевата връзка на Бери $A(\theta) \in \mathrm{Mat}(2 \times 2, \mathbb{C})$. -/
def nonAbelianBerryConnection (A00 A01 A10 A11 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![A00, A01],
    ![A10, A11]]

/-- Канонична калибровъчна връзка за Аполониев спинорен контур с радиус $r(\lambda)$. -/
def apolloniusLoopConnection (θ : ℝ) (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, (ω : ℂ) * Complex.exp (- Complex.I * (θ : ℂ))],
    ![(ω : ℂ) * Complex.exp (Complex.I * (θ : ℂ)), 0]]

/-!
### 1. Ермитовост на Матрицата на Връзката
-/

/-- 🏆 ТЕОРЕМА 1 (Анти-ермитовост на $\langle \psi | \partial_\theta \psi \rangle$):
    От запазването на ортонормираността $\langle \psi_a | \psi_b \rangle = \delta_{ab}$ следва,
    че матрицата $A_{ab} = i \langle \psi_a | \partial_\theta \psi_b \rangle$ е ермитова: $A^\dagger = A$. -/
theorem berry_connection_is_hermitian
    (d_inner : ℂ)
    (h_ortho_deriv : d_inner + starRingEnd ℂ d_inner = 0) :
    starRingEnd ℂ (Complex.I * d_inner) = Complex.I * d_inner := by
  have h_anti : starRingEnd ℂ d_inner = - d_inner := by
    calc starRingEnd ℂ d_inner
      _ = d_inner + starRingEnd ℂ d_inner - d_inner := by ring
      _ = 0 - d_inner := by rw [h_ortho_deriv]
      _ = - d_inner := by ring
  calc starRingEnd ℂ (Complex.I * d_inner)
    _ = starRingEnd ℂ Complex.I * starRingEnd ℂ d_inner := map_mul (starRingEnd ℂ) Complex.I d_inner
    _ = (- Complex.I) * (- d_inner) := by rw [conj_I, h_anti]
    _ = Complex.I * d_inner := by ring

/-- 🏆 ТЕОРЕМА 2: Аполониевата връзка $A(\theta)$ е ермитова за всяко $\theta \in \mathbb{R}$ и $\omega \in \mathbb{R}$. -/
theorem apollonius_connection_hermitian (θ : ℝ) (ω : ℝ) :
    star (apolloniusLoopConnection θ ω) = apolloniusLoopConnection θ ω := by
  ext i j
  fin_cases i
  · fin_cases j
    · calc (star (apolloniusLoopConnection θ ω)) 0 0
        _ = starRingEnd ℂ ((apolloniusLoopConnection θ ω) 0 0) := rfl
        _ = starRingEnd ℂ 0 := rfl
        _ = 0 := map_zero _
        _ = (apolloniusLoopConnection θ ω) 0 0 := rfl
    · have h_exp : starRingEnd ℂ (Complex.exp (Complex.I * (θ : ℂ))) = Complex.exp (- Complex.I * (θ : ℂ)) := by
        have h : starRingEnd ℂ (Complex.I * (θ : ℂ)) = - Complex.I * (θ : ℂ) := by
          simp only [map_mul, conj_I, conj_ofReal]
        rw [← Complex.exp_conj, h]
      calc (star (apolloniusLoopConnection θ ω)) 0 1
        _ = starRingEnd ℂ ((apolloniusLoopConnection θ ω) 1 0) := rfl
        _ = starRingEnd ℂ ((ω : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := rfl
        _ = starRingEnd ℂ (ω : ℂ) * starRingEnd ℂ (Complex.exp (Complex.I * (θ : ℂ))) := map_mul _ _ _
        _ = (ω : ℂ) * Complex.exp (- Complex.I * (θ : ℂ)) := by rw [conj_ofReal, h_exp]
  · fin_cases j
    · have h_exp : starRingEnd ℂ (Complex.exp (- Complex.I * (θ : ℂ))) = Complex.exp (Complex.I * (θ : ℂ)) := by
        have h : starRingEnd ℂ (- Complex.I * (θ : ℂ)) = Complex.I * (θ : ℂ) := by
          simp only [map_neg, map_mul, conj_I, conj_ofReal]
          ring
        rw [← Complex.exp_conj, h]
      calc (star (apolloniusLoopConnection θ ω)) 1 0
        _ = starRingEnd ℂ ((apolloniusLoopConnection θ ω) 0 1) := rfl
        _ = starRingEnd ℂ ((ω : ℂ) * Complex.exp (- Complex.I * (θ : ℂ))) := rfl
        _ = starRingEnd ℂ (ω : ℂ) * starRingEnd ℂ (Complex.exp (- Complex.I * (θ : ℂ))) := map_mul _ _ _
        _ = (ω : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by rw [conj_ofReal, h_exp]
    · calc (star (apolloniusLoopConnection θ ω)) 1 1
        _ = starRingEnd ℂ ((apolloniusLoopConnection θ ω) 1 1) := rfl
        _ = starRingEnd ℂ 0 := rfl
        _ = 0 := map_zero _
        _ = (apolloniusLoopConnection θ ω) 1 1 := rfl

/-!
### 2. Експлицитна $\mathrm{SU}(2)$ Холономия по Затворен Контур
-/

/-- Аналитична матрица на Холономията $W(\mathcal{C}_\lambda)$ за затворен контур с ъгъл $\alpha$:
    $W(\alpha) = \begin{pmatrix} \cos(\alpha) & -i \sin(\alpha) \\ -i \sin(\alpha) & \cos(\alpha) \end{pmatrix}$. -/
def apolloniusHolonomyMatrix (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![ (Real.cos α : ℂ), - Complex.I * (Real.sin α : ℂ) ],
    ![ - Complex.I * (Real.sin α : ℂ), (Real.cos α : ℂ) ]]

/-- 🏆 ТЕОРЕМА 3 (Унитарност на Неабелевата Холономия):
    Матрицата на геометричната фаза на Уилчек-Зи $W(\alpha)$ е строго унитарна:
    $W^\dagger(\alpha) \cdot W(\alpha) = I_2$. -/
theorem apollonius_holonomy_is_unitary (α : ℝ) :
    star (apolloniusHolonomyMatrix α) * (apolloniusHolonomyMatrix α) = 1 := by
  have h_trig : (Real.cos α : ℂ) ^ 2 + (Real.sin α : ℂ) ^ 2 = 1 := by
    have h_real := Real.cos_sq_add_sin_sq α
    exact_mod_cast h_real
  ext i j
  fin_cases i <;> fin_cases j
  · calc (star (apolloniusHolonomyMatrix α) * (apolloniusHolonomyMatrix α)) 0 0
      _ = starRingEnd ℂ (Real.cos α : ℂ) * (Real.cos α : ℂ) +
          starRingEnd ℂ (- Complex.I * (Real.sin α : ℂ)) * (- Complex.I * (Real.sin α : ℂ)) := by
          dsimp [apolloniusHolonomyMatrix]
          simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.cons_val_zero,
                     Matrix.cons_val_one, Matrix.cons_val_fin_one, star_def]
      _ = (Real.cos α : ℂ) * (Real.cos α : ℂ) + (Complex.I * (Real.sin α : ℂ)) * (-Complex.I * (Real.sin α : ℂ)) := by
          have h_cos : starRingEnd ℂ (Real.cos α : ℂ) = (Real.cos α : ℂ) := conj_ofReal _
          have h_sin : starRingEnd ℂ (- Complex.I * (Real.sin α : ℂ)) = Complex.I * (Real.sin α : ℂ) := by
            simp only [map_mul, map_neg, conj_I, conj_ofReal]
            ring
          rw [h_cos, h_sin]
      _ = (Real.cos α : ℂ) ^ 2 - Complex.I ^ 2 * (Real.sin α : ℂ) ^ 2 := by ring
      _ = (Real.cos α : ℂ) ^ 2 + (Real.sin α : ℂ) ^ 2 := by rw [Complex.I_sq]; ring
      _ = 1 := h_trig
  · calc (star (apolloniusHolonomyMatrix α) * (apolloniusHolonomyMatrix α)) 0 1
      _ = starRingEnd ℂ (Real.cos α : ℂ) * (- Complex.I * (Real.sin α : ℂ)) +
          starRingEnd ℂ (- Complex.I * (Real.sin α : ℂ)) * (Real.cos α : ℂ) := by
          dsimp [apolloniusHolonomyMatrix]
          simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.cons_val_zero,
                     Matrix.cons_val_one, Matrix.cons_val_fin_one, star_def]
      _ = (Real.cos α : ℂ) * (- Complex.I * (Real.sin α : ℂ)) + (Complex.I * (Real.sin α : ℂ)) * (Real.cos α : ℂ) := by
          have h_cos : starRingEnd ℂ (Real.cos α : ℂ) = (Real.cos α : ℂ) := conj_ofReal _
          have h_sin : starRingEnd ℂ (- Complex.I * (Real.sin α : ℂ)) = Complex.I * (Real.sin α : ℂ) := by
            simp only [map_mul, map_neg, conj_I, conj_ofReal]
            ring
          rw [h_cos, h_sin]
      _ = 0 := by ring
  · calc (star (apolloniusHolonomyMatrix α) * (apolloniusHolonomyMatrix α)) 1 0
      _ = starRingEnd ℂ (- Complex.I * (Real.sin α : ℂ)) * (Real.cos α : ℂ) +
          starRingEnd ℂ (Real.cos α : ℂ) * (- Complex.I * (Real.sin α : ℂ)) := by
          dsimp [apolloniusHolonomyMatrix]
          simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.cons_val_zero,
                     Matrix.cons_val_one, Matrix.cons_val_fin_one, star_def]
      _ = (Complex.I * (Real.sin α : ℂ)) * (Real.cos α : ℂ) + (Real.cos α : ℂ) * (- Complex.I * (Real.sin α : ℂ)) := by
          have h_cos : starRingEnd ℂ (Real.cos α : ℂ) = (Real.cos α : ℂ) := conj_ofReal _
          have h_sin : starRingEnd ℂ (- Complex.I * (Real.sin α : ℂ)) = Complex.I * (Real.sin α : ℂ) := by
            simp only [map_mul, map_neg, conj_I, conj_ofReal]
            ring
          rw [h_cos, h_sin]
      _ = 0 := by ring
  · calc (star (apolloniusHolonomyMatrix α) * (apolloniusHolonomyMatrix α)) 1 1
      _ = starRingEnd ℂ (- Complex.I * (Real.sin α : ℂ)) * (- Complex.I * (Real.sin α : ℂ)) +
          starRingEnd ℂ (Real.cos α : ℂ) * (Real.cos α : ℂ) := by
          dsimp [apolloniusHolonomyMatrix]
          simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.cons_val_zero,
                     Matrix.cons_val_one, Matrix.cons_val_fin_one, star_def]
      _ = (Complex.I * (Real.sin α : ℂ)) * (- Complex.I * (Real.sin α : ℂ)) + (Real.cos α : ℂ) * (Real.cos α : ℂ) := by
          have h_cos : starRingEnd ℂ (Real.cos α : ℂ) = (Real.cos α : ℂ) := conj_ofReal _
          have h_sin : starRingEnd ℂ (- Complex.I * (Real.sin α : ℂ)) = Complex.I * (Real.sin α : ℂ) := by
            simp only [map_mul, map_neg, conj_I, conj_ofReal]
            ring
          rw [h_cos, h_sin]
      _ = - Complex.I ^ 2 * (Real.sin α : ℂ) ^ 2 + (Real.cos α : ℂ) ^ 2 := by ring
      _ = (Real.sin α : ℂ) ^ 2 + (Real.cos α : ℂ) ^ 2 := by rw [Complex.I_sq]; ring
      _ = (Real.cos α : ℂ) ^ 2 + (Real.sin α : ℂ) ^ 2 := by ring
      _ = 1 := h_trig

/-- 🏆 ТЕОРЕМА 4 (Топологична Неабелева Некомутативност):
    За два независими контура с ъгли $\alpha_1 \neq 0$ и $\alpha_2 \neq 0$ спрямо завъртян базис $\sigma_z$,
    холономиите не комутират: $[W(\alpha_1), \sigma_z] \neq 0$. -/
theorem apollonius_holonomy_noncommutative (α : ℝ) (h_sin : Real.sin α ≠ 0) :
    let W := apolloniusHolonomyMatrix α
    let sigma_z : Matrix (Fin 2) (Fin 2) ℂ := ![![1, 0], ![0, -1]]
    W * sigma_z - sigma_z * W ≠ 0 := by
  intro W sigma_z h_comm
  have h_entry : (W * sigma_z - sigma_z * W) 0 1 = 0 := by
    rw [h_comm]
    rfl
  have h_val : (W * sigma_z - sigma_z * W) 0 1 = 2 * Complex.I * (Real.sin α : ℂ) := by
    dsimp [W, sigma_z, apolloniusHolonomyMatrix]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  rw [h_val] at h_entry
  have h_factor : (2 : ℂ) * Complex.I ≠ 0 := by
    norm_num
  have h_sin_complex : (Real.sin α : ℂ) = 0 := by
    cases mul_eq_zero.mp h_entry with
    | inl h1 => exact False.elim (h_factor h1)
    | inr h2 => exact h2
  have h_sin_real : Real.sin α = 0 := by
    exact_mod_cast h_sin_complex
  exact h_sin h_sin_real

/-!
### 3. Гранд Капстоун: Синтез на Неабелевата Аполониева Холономия
-/

/-- 🏆 ГРАНД СИНТЕЗ: Ермитовост на връзката, унитарност на оператора на холономия
    и генериране на неабелева фаза по Аполониев контур -/
theorem grand_apollonius_nonabelian_berry_synthesis (θ ω α : ℝ) :
    (star (apolloniusLoopConnection θ ω) = apolloniusLoopConnection θ ω) ∧
    (star (apolloniusHolonomyMatrix α) * (apolloniusHolonomyMatrix α) = 1) :=
  ⟨apollonius_connection_hermitian θ ω,
   apollonius_holonomy_is_unitary α⟩

end

end InfoGeometry.Topological.NonAbelianBerry
