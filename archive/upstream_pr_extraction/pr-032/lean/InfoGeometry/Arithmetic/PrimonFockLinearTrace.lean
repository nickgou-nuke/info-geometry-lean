import Mathlib.LinearAlgebra.Trace
import InfoGeometry.Arithmetic.PrimonFockTraceFinite

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimonFockLinearTrace

open InfoGeometry.Arithmetic.PrimonFockTraceFinite

def numberProjectorLinear (n : ℕ) (i : Fin n) :
    FockVec n →ₗ[ℂ] FockVec n where
  toFun ψ := fun occ => (if occ i then (1 : ℂ) else 0) * ψ occ
  map_add' ψ φ := by
    funext occ
    simp only [Pi.add_apply]
    ring
  map_smul' c ψ := by
    funext occ
    simp only [Pi.smul_apply]
    change (if occ i then (1 : ℂ) else 0) * (c * ψ occ) =
      c * ((if occ i then (1 : ℂ) else 0) * ψ occ)
    ring

@[simp] theorem numberProjectorLinear_apply
    (n : ℕ) (i : Fin n) (ψ : FockVec n) (occ : FockState n) :
    numberProjectorLinear n i ψ occ =
      (if occ i then (1 : ℂ) else 0) * ψ occ :=
  rfl

theorem numberProjectorLinear_eq_linearization
    (n : ℕ) (i : Fin n) (ψ : FockVec n) :
    numberProjectorLinear n i ψ = numberProjector n i ψ :=
  rfl

theorem numberProjectorLinear_idempotent
    (n : ℕ) (i : Fin n) :
    (numberProjectorLinear n i).comp (numberProjectorLinear n i) =
      numberProjectorLinear n i := by
  apply LinearMap.ext
  intro ψ
  simpa [numberProjectorLinear_eq_linearization] using
    numberProjector_idempotent n i ψ

theorem numberProjectorLinear_commute
    (n : ℕ) (i j : Fin n) :
    (numberProjectorLinear n i).comp (numberProjectorLinear n j) =
      (numberProjectorLinear n j).comp (numberProjectorLinear n i) := by
  apply LinearMap.ext
  intro ψ
  simpa [numberProjectorLinear_eq_linearization] using
    numberProjector_commute n i j ψ

theorem trace_numberProjectorLinear
    (n : ℕ) (i : Fin n) :
    LinearMap.trace ℂ (FockVec n) (numberProjectorLinear n i) =
      ∑ occ : FockState n, (if occ i then (1 : ℂ) else 0) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (FockState n))]
  simp [numberProjectorLinear, Matrix.trace]

def fockHamiltonianLinear (n : ℕ) (ε : Fin n → ℝ) :
    FockVec n →ₗ[ℂ] FockVec n where
  toFun ψ := fun occ =>
    (fockEnergy n ε occ : ℂ) * ψ occ
  map_add' ψ φ := by
    funext occ
    simp only [Pi.add_apply]
    ring
  map_smul' c ψ := by
    funext occ
    simp only [Pi.smul_apply]
    change (fockEnergy n ε occ : ℂ) * (c * ψ occ) =
      c * ((fockEnergy n ε occ : ℂ) * ψ occ)
    ring

@[simp] theorem fockHamiltonianLinear_apply
    (n : ℕ) (ε : Fin n → ℝ) (ψ : FockVec n) (occ : FockState n) :
    fockHamiltonianLinear n ε ψ occ =
      (fockEnergy n ε occ : ℂ) * ψ occ :=
  rfl

theorem fockHamiltonianLinear_eq_linearization
    (n : ℕ) (ε : Fin n → ℝ) (ψ : FockVec n) :
    fockHamiltonianLinear n ε ψ =
      fockHamiltonian n ε ψ :=
  rfl

theorem fockHamiltonianLinear_eq_sum_numberProjector
    (n : ℕ) (ε : Fin n → ℝ) :
    fockHamiltonianLinear n ε =
      ∑ i : Fin n, (ε i : ℂ) • numberProjectorLinear n i := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp only [fockHamiltonianLinear_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  simp [numberProjectorLinear]
  change (fockEnergy n ε occ : ℂ) * ψ occ =
    ∑ i : Fin n, (if occ i then (ε i : ℂ) * ψ occ else 0)
  rw [show (fockEnergy n ε occ : ℂ) =
      ∑ i : Fin n, (if occ i then (ε i : ℂ) else 0) by
        simp only [fockEnergy]
        change Complex.ofRealHom (∑ i : Fin n,
          (if occ i then ε i else 0)) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases h : occ i <;> simp [h]]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases h : occ i <;> simp [h]

theorem fockHamiltonianLinear_commute_numberProjector
    (n : ℕ) (ε : Fin n → ℝ) (i : Fin n) :
    (fockHamiltonianLinear n ε).comp (numberProjectorLinear n i) =
      (numberProjectorLinear n i).comp (fockHamiltonianLinear n ε) := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp [fockHamiltonianLinear, numberProjectorLinear]

theorem trace_fockHamiltonianLinear_eq_sum_trace_numberProjector
    (n : ℕ) (ε : Fin n → ℝ) :
    LinearMap.trace ℂ (FockVec n) (fockHamiltonianLinear n ε) =
      ∑ i : Fin n, (ε i : ℂ) *
        LinearMap.trace ℂ (FockVec n) (numberProjectorLinear n i) := by
  rw [fockHamiltonianLinear_eq_sum_numberProjector]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul]
  simp [smul_eq_mul]

theorem trace_fockHamiltonianLinear
    (n : ℕ) (ε : Fin n → ℝ) :
    LinearMap.trace ℂ (FockVec n) (fockHamiltonianLinear n ε) =
      ∑ occ : FockState n, (fockEnergy n ε occ : ℂ) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (FockState n))]
  simp [fockHamiltonianLinear, Matrix.trace]

theorem fockHamiltonianLinear_on_basis
    (n : ℕ) (ε : Fin n → ℝ) (occ : FockState n) :
    fockHamiltonianLinear n ε (basisVector occ) =
      (fockEnergy n ε occ : ℂ) • basisVector occ := by
  simpa [fockHamiltonianLinear_eq_linearization] using
    fockHamiltonian_on_basis n ε occ

def fockGibbsLinear (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) :
    FockVec n →ₗ[ℂ] FockVec n where
  toFun ψ := fun occ =>
    (Real.exp (-β * fockEnergy n ε occ) : ℂ) * ψ occ
  map_add' ψ φ := by
    funext occ
    simp only [Pi.add_apply]
    ring
  map_smul' c ψ := by
    funext occ
    simp only [Pi.smul_apply]
    change (Real.exp (-β * fockEnergy n ε occ) : ℂ) * (c * ψ occ) =
      c * ((Real.exp (-β * fockEnergy n ε occ) : ℂ) * ψ occ)
    ring

@[simp] theorem fockGibbsLinear_apply
    (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) (ψ : FockVec n) (occ : FockState n) :
    fockGibbsLinear n ε β ψ occ =
      (Real.exp (-β * fockEnergy n ε occ) : ℂ) * ψ occ :=
  rfl

theorem fockGibbsLinear_commute_numberProjector
    (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    (fockGibbsLinear n ε β).comp (numberProjectorLinear n i) =
      (numberProjectorLinear n i).comp (fockGibbsLinear n ε β) := by
  apply LinearMap.ext
  intro ψ
  funext occ
  simp [fockGibbsLinear, numberProjectorLinear]

theorem trace_fockGibbsLinear
    (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) :
    LinearMap.trace ℂ (FockVec n) (fockGibbsLinear n ε β) =
      ∑ occ : FockState n, (Real.exp (-β * fockEnergy n ε occ) : ℂ) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (FockState n))]
  simp [fockGibbsLinear, Matrix.trace]

theorem trace_fockGibbsLinear_eq_complexification
    (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) :
    LinearMap.trace ℂ (FockVec n) (fockGibbsLinear n ε β) =
      (fockTraceExp n ε β : ℂ) := by
  rw [trace_fockGibbsLinear]
  simp [fockTraceExp]

theorem trace_fockGibbsLinear_ne_zero
    (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) :
    LinearMap.trace ℂ (FockVec n) (fockGibbsLinear n ε β) ≠ 0 := by
  rw [trace_fockGibbsLinear_eq_complexification]
  exact_mod_cast fockTraceExp_ne_zero n ε β

theorem trace_fockGibbsLinear_eq_local_product
    (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) :
    LinearMap.trace ℂ (FockVec n) (fockGibbsLinear n ε β) =
      ∏ i : Fin n, (1 + (localBoltzmann (ε i) β : ℂ)) := by
  rw [trace_fockGibbsLinear_eq_complexification,
    fockTraceExp_eq_product]
  norm_cast

end InfoGeometry.Arithmetic.PrimonFockLinearTrace
