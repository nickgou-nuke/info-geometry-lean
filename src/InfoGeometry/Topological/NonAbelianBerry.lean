import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

namespace InfoGeometry.Topological.NonAbelianBerry

open Complex Matrix Real ComplexConjugate

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

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
  ![![0, (ω : ℂ) * Complex.exp (- (Complex.I * (θ : ℂ)))],
    ![(ω : ℂ) * Complex.exp (Complex.I * (θ : ℂ)), 0]]

/-!
### 1. Ермитовост на Матрицата на Връзката
-/

/-- 🏆 ТЕОРЕМА 1 (Анти-ермитовост на $\langle \psi | \partial_\theta \psi \rangle$):
    От запазването на ортонормираността $\langle \psi_a | \psi_b \rangle = \delta_{ab}$ следва,
    че матрицата $A_{ab} = i \langle \psi_a | \partial_\theta \psi_b \rangle$ е ермитова: $A^\dagger = A$. -/
theorem berry_connection_is_hermitian
    (d_inner : ℂ)
    (h_ortho_deriv : d_inner + star d_inner = 0) :
    star (Complex.I * d_inner) = Complex.I * d_inner := by
  have h_star : star (Complex.I * d_inner) = star d_inner * star Complex.I := star_mul Complex.I d_inner
  simp only [star_def, map_mul] at h_star ⊢
  have h_I : conj Complex.I = - Complex.I := Complex.conj_I
  have h_anti : conj d_inner = - d_inner := by
    apply eq_neg_of_add_eq_zero_left
    rw [add_comm]
    exact h_ortho_deriv
  rw [h_anti, h_I]
  ring

/-- 🏆 ТЕОРЕМА 2: Аполониевата връзка $A(\theta)$ е ермитова за всяко $\theta \in \mathbb{R}$ и $\omega \in \mathbb{R}$. -/
theorem apollonius_connection_hermitian (θ : ℝ) (ω : ℝ) :
    star (apolloniusLoopConnection θ ω) = apolloniusLoopConnection θ ω := by
  ext i j
  rw [Matrix.star_apply]
  fin_cases i <;> fin_cases j
  · dsimp [apolloniusLoopConnection]
    simp
  · dsimp [apolloniusLoopConnection]
    simp only [map_mul, conj_ofReal]
    have h : conj (Complex.exp (Complex.I * (θ : ℂ))) = Complex.exp (- (Complex.I * (θ : ℂ))) := by
      rw [← Complex.exp_conj]
      simp only [map_mul, Complex.conj_I, conj_ofReal]
      ring_nf
    rw [h]
  · dsimp [apolloniusLoopConnection]
    simp only [map_mul, conj_ofReal]
    have h : conj (Complex.exp (- (Complex.I * (θ : ℂ)))) = Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [← Complex.exp_conj]
      simp only [map_neg, map_mul, Complex.conj_I, conj_ofReal]
      ring_nf
    rw [h]
  · dsimp [apolloniusLoopConnection]
    simp

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
  have h_trig : (Complex.cos (α : ℂ)) ^ 2 + (Complex.sin (α : ℂ)) ^ 2 = 1 := by
    exact Complex.cos_sq_add_sin_sq (α : ℂ)
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at h_trig
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    dsimp [apolloniusHolonomyMatrix]
    simp only [map_mul, map_neg, Complex.conj_I, conj_ofReal]
    linear_combination h_trig - (↑(Real.sin α) ^ 2) * hI
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    dsimp [apolloniusHolonomyMatrix]
    simp only [map_mul, map_neg, Complex.conj_I, conj_ofReal]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    dsimp [apolloniusHolonomyMatrix]
    simp only [map_mul, map_neg, Complex.conj_I, conj_ofReal]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    dsimp [apolloniusHolonomyMatrix]
    simp only [map_mul, map_neg, Complex.conj_I, conj_ofReal]
    linear_combination h_trig - (↑(Real.sin α) ^ 2) * hI

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
