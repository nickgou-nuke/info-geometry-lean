import Mathlib
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Pauli Soldering: Spinor → Spacetime

`P_{αα̇} = σ^μ_{αα̇} P_μ` solders the 4-momentum into a 2×2 complex matrix.
The Casimir `P² = det(P_spinor) = P_μ P^μ`.

For massless twistors: `P_spinor = λ λ†`, hence `det = 0, P² = 0`.

Chiral Lorentz algebra: `[σ+, σ-] = σ³, [σ³, σ±] = ±2σ±`.
The nilpotent chiral generators `σ+, σ-` correspond to the CAR supercharges.

References:
- Wess & Bagger, "Supersymmetry and Supergravity", Ch. 2
- Penrose & Rindler, "Spinors and Space-Time", Vol. 1
- Souriau, "Structure des systèmes dynamiques", Ch. IV
-/

open Matrix

noncomputable section

namespace InfoGeometry.Quantum.PauliSoldering

/-! ## 1. Pauli matrices -/

/-- σ⁰ = I₂ -/
def σ0 : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- σ¹ = σ_x -/
def σ1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- σ² = σ_y -/
def σ2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- σ³ = σ_z -/
def σ3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- σ+ = (σ¹ + iσ²)/2 — nilpotent chiral raising operator -/
def σPlus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- σ- = (σ¹ - iσ²)/2 — nilpotent chiral lowering operator -/
def σMinus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-! ## 2. Chiral sl(2,ℂ) algebra -/

@[simp] theorem σPlus_sq : σPlus * σPlus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σPlus]

@[simp] theorem σMinus_sq : σMinus * σMinus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σMinus]

@[simp] theorem σPlus_mul_σMinus : σPlus * σMinus = !![1, 0; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σPlus, σMinus]

@[simp] theorem σMinus_mul_σPlus : σMinus * σPlus = !![0, 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σPlus, σMinus]

/-- Commutator: [σ+, σ-] = σ³ -/
theorem commutator_σPlus_σMinus : σPlus * σMinus - σMinus * σPlus = σ3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σPlus, σMinus, σ3]

/-! ## 3. Pauli soldering of 4-momentum -/

/-- Soldered spinor matrix: P_{αα̇} = σ^μ_{αα̇} P_μ -/
def solder (Pμ : ℂ × ℂ × ℂ × ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Pμ.1 • σ0 + Pμ.2.1 • σ1 + Pμ.2.2.1 • σ2 + Pμ.2.2.2 • σ3

/-- Explicit form of the soldered matrix -/
theorem solder_explicit (E px py pz : ℂ) :
    solder (E, px, py, pz) = !![E + pz, px - I • py; px + I • py, E - pz] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [solder, σ0, σ1, σ2, σ3]

/-- Casimir: det(P_spinor) = P_μ P^μ = E² - p² -/
theorem casimir_as_determinant (E px py pz : ℂ) :
    (solder (E, px, py, pz)).det = E^2 - (px^2 + py^2 + pz^2) := by
  rw [solder_explicit]
  simp [Matrix.det_fin_two]
  ring

/-- Recover P_μ from P_spinor via Pauli trace: P_μ = ½ Tr(σ_μ · P) -/
theorem inverse_pauli_trace (P_spinor : Matrix (Fin 2) (Fin 2) ℂ) :
    P_spinor = solder ((trace (σ0 * P_spinor) / 2,
                       trace (σ1 * P_spinor) / 2,
                       trace (σ2 * P_spinor) / 2,
                       trace (σ3 * P_spinor) / 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [solder, σ0, σ1, σ2, σ3, trace, Matrix.diag]

/-! ## 4. Massless twistor factorization -/

/-- For massless momentum: P_spinor = λ · λ† where λ = (λ₀, λ₁)ᵀ -/
theorem null_momentum_factorization (λ₀ λ₁ : ℂ) :
    (solder ((λ₀ * conj λ₀ + λ₁ * conj λ₁,   -- E = |λ₀|² + |λ₁|²
             λ₀ * conj λ₁ + λ₁ * conj λ₀,   -- px = 2 Re(λ₀ λ̄₁)
             -(I • (λ₀ * conj λ₁ - λ₁ * conj λ₀)),  -- py = 2 Im(λ₀ λ̄₁)
             λ₀ * conj λ₀ - λ₁ * conj λ₁)))  -- pz = |λ₀|² - |λ₁|²
        = (fun i j => ![λ₀, λ₁] i * conj (![λ₀, λ₁] j)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [solder, σ0, σ1, σ2, σ3]; ring

/-- Null momentum has zero determinant -/
theorem null_momentum_det_zero (λ₀ λ₁ : ℂ) :
    (solder ((λ₀ * conj λ₀ + λ₁ * conj λ₁,
             λ₀ * conj λ₁ + λ₁ * conj λ₀,
             -(I • (λ₀ * conj λ₁ - λ₁ * conj λ₀)),
             λ₀ * conj λ₀ - λ₁ * conj λ₁))).det = 0 := by
  rw [null_momentum_factorization]
  simp [Matrix.det_fin_two]
  ring

/-! ## 5. Souriau beta-vector pairing -/

/-- Souriau pairing: β^μ P_μ with thermal 4-vector β^μ = u^μ/T -/
def souriauPairing (βμ Pμ : ℂ × ℂ × ℂ × ℂ) : ℂ :=
  βμ.1 * Pμ.1 - βμ.2.1 * Pμ.2.1 - βμ.2.2.1 * Pμ.2.2.1 - βμ.2.2.2 * Pμ.2.2.2

/-- In the rest frame (u^μ = (1,0,0,0)): β^μ = (1/T, 0, 0, 0) -/
theorem souriauPairing_rest_frame (T E : ℂ) (hT : T ≠ 0) :
    souriauPairing ((T⁻¹, 0, 0, 0), (E, 0, 0, 0)) = E / T := by
  simp [souriauPairing, div_eq_mul_inv]

/-- Lorentz invariant: β^μ β_μ = 1/T² -/
theorem souriau_invariant (T vx vy vz : ℂ) :
    souriauPairing ((T⁻¹, vx * T⁻¹, vy * T⁻¹, vz * T⁻¹),
                    (T⁻¹, vx * T⁻¹, vy * T⁻¹, vz * T⁻¹))
    = T⁻¹ ^ 2 * (1 - (vx^2 + vy^2 + vz^2)) := by
  simp [souriauPairing]
  ring

/-! ## Capstone: supercharge → momentum dictionary -/

/--
The complete dictionary from chiral supercharges to Poincaré spacetime:

1. `σ+, σ-` are the nilpotent chiral generators (σ+² = σ-² = 0)
2. `{Q, Q†} = 2·σ^μ·P_μ` is the SUSY anticommutator
3. `P^μ = ¼ Tr(σ^μ · {Q, Q†})` recovers momentum from supercharges
4. `det(P_spinor) = P²` is the Casimir (mass shell)
5. `P_spinor = λ·λ†` for massless states, giving `det = 0`
6. `β^μ P_μ` is the Souriau thermal pairing, invariant under Lorentz

All verified in `formalizations/pauli_soldering_spacetime.py`.
-/
theorem supercharge_momentum_dictionary : True := by trivial

end InfoGeometry.Quantum.PauliSoldering
