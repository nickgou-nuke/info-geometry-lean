import Mathlib

/-!
# Exact two-level BdG algebra

This file isolates the finite traceless two-channel matrix

`H(ξ,Δ) = [[ξ, Δ], [Δ, -ξ]]`.

It proves Hermiticity, the Clifford square law, the exact characteristic
polynomial, an explicit spectral intertwiner, and a conjugate-linear
particle--hole map with square `-1` which anticommutes with the complexified
matrix.  These are finite algebraic theorems; no microscopic mean-field model
or topological classification is inferred.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearBdGTwoLevelExact

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev V2R := Fin 2 → ℝ
abbrev V2C := Fin 2 → ℂ

/-- Real symmetric traceless BdG block. -/
def bdgBlock (ξ Δ : ℝ) : M2R :=
  !![ξ, Δ; Δ, -ξ]

/-- Positive spectral radius. -/
def bdgEnergy (ξ Δ : ℝ) : ℝ :=
  Real.sqrt (ξ ^ 2 + Δ ^ 2)

@[simp] theorem bdgEnergy_nonneg (ξ Δ : ℝ) :
    0 ≤ bdgEnergy ξ Δ := Real.sqrt_nonneg _

/-- Exact energy square. -/
theorem bdgEnergy_sq (ξ Δ : ℝ) :
    (bdgEnergy ξ Δ) ^ 2 = ξ ^ 2 + Δ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

/-- The block is real symmetric. -/
theorem bdgBlock_transpose (ξ Δ : ℝ) :
    (bdgBlock ξ Δ)ᵀ = bdgBlock ξ Δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bdgBlock]

/-- Tracelessness. -/
theorem bdgBlock_trace (ξ Δ : ℝ) :
    (bdgBlock ξ Δ).trace = 0 := by
  simp [bdgBlock]

/-- Determinant equals minus the squared gap. -/
theorem bdgBlock_det (ξ Δ : ℝ) :
    (bdgBlock ξ Δ).det = -(ξ ^ 2 + Δ ^ 2) := by
  simp [bdgBlock, Matrix.det_fin_two]
  ring

/-- Clifford square law. -/
theorem bdgBlock_sq (ξ Δ : ℝ) :
    bdgBlock ξ Δ * bdgBlock ξ Δ =
      (ξ ^ 2 + Δ ^ 2) • (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgBlock, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Exact characteristic polynomial. -/
theorem bdg_characteristic (ξ Δ λ : ℝ) :
    (bdgBlock ξ Δ - λ • (1 : M2R)).det =
      λ ^ 2 - (ξ ^ 2 + Δ ^ 2) := by
  simp [bdgBlock, Matrix.det_fin_two]
  ring

/-- Both formal spectral roots annihilate the characteristic determinant. -/
theorem bdg_characteristic_at_energy (ξ Δ : ℝ) :
    (bdgBlock ξ Δ - bdgEnergy ξ Δ • (1 : M2R)).det = 0 := by
  rw [bdg_characteristic, bdgEnergy_sq]
  ring

/-- Negative spectral root. -/
theorem bdg_characteristic_at_neg_energy (ξ Δ : ℝ) :
    (bdgBlock ξ Δ - (-bdgEnergy ξ Δ) • (1 : M2R)).det = 0 := by
  rw [bdg_characteristic, bdgEnergy_sq]
  ring

/-- Two explicit, generally unnormalised, eigenvector columns. -/
def bdgEigenbasis (ξ Δ : ℝ) : M2R :=
  let E := bdgEnergy ξ Δ
  !![Δ, Δ; E - ξ, -(E + ξ)]

/-- Diagonal spectral matrix. -/
def bdgSpectrum (ξ Δ : ℝ) : M2R :=
  let E := bdgEnergy ξ Δ
  !![E, 0; 0, -E]

/-- Exact spectral intertwining equation `H U = U diag(E,-E)`. -/
theorem bdg_eigenbasis_intertwines (ξ Δ : ℝ) :
    bdgBlock ξ Δ * bdgEigenbasis ξ Δ =
      bdgEigenbasis ξ Δ * bdgSpectrum ξ Δ := by
  have hE := bdgEnergy_sq ξ Δ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgBlock, bdgEigenbasis, bdgSpectrum,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith

/-- Determinant of the explicit spectral basis. -/
theorem bdgEigenbasis_det (ξ Δ : ℝ) :
    (bdgEigenbasis ξ Δ).det =
      -2 * Δ * bdgEnergy ξ Δ := by
  simp [bdgEigenbasis, Matrix.det_fin_two]
  ring

/-- Nonzero pairing makes the explicit spectral basis invertible. -/
theorem bdgEigenbasis_det_ne_zero
    {ξ Δ : ℝ} (hΔ : Δ ≠ 0) :
    (bdgEigenbasis ξ Δ).det ≠ 0 := by
  rw [bdgEigenbasis_det]
  have hE : 0 < bdgEnergy ξ Δ := by
    apply Real.sqrt_pos.2
    nlinarith [sq_nonneg ξ, sq_pos_of_ne_zero hΔ]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hΔ) (ne_of_gt hE)

/-! ## Complexification and conjugate-linear particle--hole symmetry -/

/-- Complexified matrix. -/
def bdgBlockC (ξ Δ : ℝ) : M2C :=
  !![(ξ : ℂ), (Δ : ℂ); (Δ : ℂ), -(ξ : ℂ)]

/-- The complexified block is Hermitian. -/
theorem bdgBlockC_hermitian (ξ Δ : ℝ) :
    (bdgBlockC ξ Δ)ᴴ = bdgBlockC ξ Δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bdgBlockC]

/-- Conjugate-linear particle--hole map `C = τ_y K`. -/
def particleHole (ψ : V2C) : V2C :=
  ![-Complex.I * Complex.conj (ψ 1),
      Complex.I * Complex.conj (ψ 0)]

/-- Additivity of the anti-linear map. -/
theorem particleHole_add (ψ φ : V2C) :
    particleHole (ψ + φ) = particleHole ψ + particleHole φ := by
  ext i
  fin_cases i <;> simp [particleHole] <;> ring

/-- Conjugate scalar law. -/
theorem particleHole_smul (c : ℂ) (ψ : V2C) :
    particleHole (c • ψ) = Complex.conj c • particleHole ψ := by
  ext i
  fin_cases i <;> simp [particleHole] <;> ring

/-- Quaternionic square of the chosen particle--hole map. -/
theorem particleHole_sq (ψ : V2C) :
    particleHole (particleHole ψ) = -ψ := by
  ext i
  fin_cases i <;> simp [particleHole] <;> ring

/-- Exact particle--hole anticommutation with the real BdG block. -/
theorem particleHole_anticommutes (ξ Δ : ℝ) (ψ : V2C) :
    particleHole (mulVec (bdgBlockC ξ Δ) ψ) =
      -mulVec (bdgBlockC ξ Δ) (particleHole ψ) := by
  ext i
  fin_cases i <;>
    simp [particleHole, bdgBlockC, mulVec, dotProduct,
      Fin.sum_univ_two] <;>
    ring

/-- Compact finite BdG packet. -/
theorem bdg_two_level_packet (ξ Δ : ℝ) (ψ : V2C) :
    (bdgBlock ξ Δ)ᵀ = bdgBlock ξ Δ ∧
      bdgBlock ξ Δ * bdgBlock ξ Δ =
        (ξ ^ 2 + Δ ^ 2) • (1 : M2R) ∧
      (bdgBlock ξ Δ - bdgEnergy ξ Δ • (1 : M2R)).det = 0 ∧
      bdgBlock ξ Δ * bdgEigenbasis ξ Δ =
        bdgEigenbasis ξ Δ * bdgSpectrum ξ Δ ∧
      particleHole (particleHole ψ) = -ψ ∧
      particleHole (mulVec (bdgBlockC ξ Δ) ψ) =
        -mulVec (bdgBlockC ξ Δ) (particleHole ψ) := by
  exact ⟨bdgBlock_transpose ξ Δ,
    bdgBlock_sq ξ Δ,
    bdg_characteristic_at_energy ξ Δ,
    bdg_eigenbasis_intertwines ξ Δ,
    particleHole_sq ψ,
    particleHole_anticommutes ξ Δ ψ⟩

end InfoGeometry.Physics.NuclearBdGTwoLevelExact
