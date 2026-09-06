import Mathlib

/-!
# Cartan-Weyl / Bogoliubov finite algebra

This module records finite algebraic cores for the bridge from soldered spinor
algebra to matrix metric identities:

* Pauli soldering anticommutators recover the Minkowski metric.
* A tetrad produces `g=eᵀηe`.
* A one-generator spin connection has vanishing self-commutator.
* A Bogoliubov boost preserves the Krein/CAR form under `c^2-s^2=1`.

The file does not assert Einstein equations or thermodynamic equations of state;
it proves only the displayed finite matrix identities.
-/

noncomputable section

namespace CartanWeylBogoliubovGravity

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev M4R := Matrix (Fin 4) (Fin 4) ℝ

/-! ## Pauli soldering and Minkowski metric -/

def σ0 : M2C := 1
def σ1 : M2C := !![0, 1; 1, 0]
def σ2 : M2C := !![0, -Complex.I; Complex.I, 0]
def σ3 : M2C := !![1, 0; 0, -1]

def σ (i : Fin 4) : M2C :=
  match i with
  | 0 => σ0
  | 1 => σ1
  | 2 => σ2
  | 3 => σ3

/-- Barred Pauli matrices: `σ̄⁰=σ⁰`, `σ̄ⁱ=-σⁱ`. -/
def σbar (i : Fin 4) : M2C :=
  match i with
  | 0 => σ0
  | 1 => -σ1
  | 2 => -σ2
  | 3 => -σ3

/-- Manual trace for `2×2` matrices. -/
def tr2C (A : M2C) : ℂ := A 0 0 + A 1 1

/-- Minkowski signs. -/
def etaSign (i j : Fin 4) : ℂ :=
  if i = j then (if i = 0 then 1 else -1) else 0

/-- Soldering anticommutator gives the Minkowski metric. -/
theorem pauli_solder_metric (i j : Fin 4) :
    (1 / 4 : ℂ) * tr2C (σ i * σbar j + σ j * σbar i) = etaSign i j := by
  fin_cases i <;> fin_cases j <;>
    simp [σ, σbar, σ0, σ1, σ2, σ3, tr2C, etaSign, Matrix.add_apply] <;>
    norm_num [Complex.I_mul_I]

/-! ## Tetrad metric -/

def eta4 : M4R := diagonal ![1, -1, -1, -1]
def tetradDiag (e0 e1 e2 e3 : ℝ) : M4R := diagonal ![e0, e1, e2, e3]
def inducedMetric (e : M4R) : M4R := eᵀ * eta4 * e

theorem inducedMetric_diag (e0 e1 e2 e3 : ℝ) :
    inducedMetric (tetradDiag e0 e1 e2 e3) = diagonal ![e0^2, -(e1^2), -(e2^2), -(e3^2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inducedMetric, tetradDiag, eta4, Matrix.mul_apply, diagonal] <;>
    ring

/-! ## Spin connection and Bogoliubov frame atoms -/

/-- One boost generator for an `SO(1,1)` spin connection. -/
def boostK : M2R := !![0, 1; 1, 0]

/-- A one-generator connection has zero self-commutator. -/
theorem boost_connection_comm_zero (a b : ℝ) :
    (a • boostK) * (b • boostK) - (b • boostK) * (a • boostK) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostK, Matrix.sub_apply] <;>
    ring

/-- Bogoliubov / `SO(1,1)` frame. -/
def bogoliubov (c s : ℝ) : M2R := !![c, s; s, c]

def kreinJ : M2R := !![1, 0; 0, -1]

/-- Bogoliubov frames preserve the Krein/CAR form. -/
theorem bogoliubov_preserves_krein (c s : ℝ) (h : c^2 - s^2 = 1) :
    (bogoliubov c s)ᵀ * kreinJ * (bogoliubov c s) = kreinJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bogoliubov, kreinJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith

/-- Main synthesis theorem. -/
theorem cartan_weyl_bogoliubov_gravity_synthesis :
    (∀ i j : Fin 4, (1 / 4 : ℂ) * tr2C (σ i * σbar j + σ j * σbar i) = etaSign i j) ∧
    (∀ e0 e1 e2 e3 : ℝ,
      inducedMetric (tetradDiag e0 e1 e2 e3) = diagonal ![e0^2, -(e1^2), -(e2^2), -(e3^2)]) ∧
    (∀ a b : ℝ, (a • boostK) * (b • boostK) - (b • boostK) * (a • boostK) = 0) ∧
    (∀ c s : ℝ, c^2 - s^2 = 1 → (bogoliubov c s)ᵀ * kreinJ * (bogoliubov c s) = kreinJ) := by
  constructor
  · exact pauli_solder_metric
  · constructor
    · exact inducedMetric_diag
    · constructor
      · exact boost_connection_comm_zero
      · exact bogoliubov_preserves_krein

end CartanWeylBogoliubovGravity
