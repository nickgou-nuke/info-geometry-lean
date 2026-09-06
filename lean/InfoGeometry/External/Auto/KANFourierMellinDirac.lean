import Mathlib.Tactic

/-!
# KAN / Fourier--Mellin / Dirac-Hodge synthesis

A finite matrix formalization of the KAN decomposition viewpoint on the
biquaternion group and the Fourier--Mellin diagonalization of Dirac-Hodge
symbols:

* `K,A,N` are determinant-one factors in `SL(2,ℂ)`;
* Fourier on the nilpotent factor `N≃ℂ` maps the tangential Dirac term to `i(k·σ)`;
* Mellin on the radial group `A≃ℝ₊ˣ` maps `r∂ᵣ` to a scalar `-s`;
* the combined symbol `σ₃(-sI+i k·σ)` stays inside the Pauli/biquaternion basis;
* the tripotent scale defect has poles at `s=+1,-1,0`;
* Cantor/Cuntz radial discretization is represented by binary cylinder doubling.
-/

noncomputable section

namespace KANFourierMellinDirac

open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ

/-! ## 1. KAN finite factors -/

/-- Compact subgroup factor `K=SU(2)` represented here by determinant one. -/
structure KFactor where
  mat : M2C
  det_one : mat.det = 1

/-- Abelian radial factor `A≃ℝ₊ˣ`. -/
structure AFactor where
  mat : M2C
  radialScale : ℝ
  positive : 0 < radialScale
  det_one : mat.det = 1

/-- Nilpotent translation factor `N≃ℂ`. -/
structure NFactor where
  mat : M2C
  nilCoordinate : ℂ
  det_one : mat.det = 1

/-- Product of determinant-one KAN factors remains determinant one. -/
theorem KAN_det_one (K : KFactor) (A : AFactor) (N : NFactor) :
    (K.mat * A.mat * N.mat).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_mul, K.det_one, A.det_one, N.det_one]
  norm_num

/-! ## 2. Pauli/Dirac Fourier-Mellin symbols -/

/-- Pauli σ₁. -/
def σ₁ : M2C := !![0, 1; 1, 0]
/-- Pauli σ₂. -/
def σ₂ : M2C := !![0, -I; I, 0]
/-- Pauli σ₃, used as radial Clifford generator. -/
def σ₃ : M2C := !![1, 0; 0, -1]

/-- Nilpotent-factor Dirac Fourier symbol `i(kx σ₁ + ky σ₂)`. -/
def nilDiracFourierSymbol (kx ky : ℂ) : M2C := I • (kx • σ₁ + ky • σ₂)

/-- Fourier symbol square: `(i k·σ)² = - (kx²+ky²) I`. -/
theorem nilDiracFourierSymbol_sq (kx ky : ℂ) :
    nilDiracFourierSymbol kx ky * nilDiracFourierSymbol kx ky =
      (-(kx * kx + ky * ky)) • (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [nilDiracFourierSymbol, σ₁, σ₂, Matrix.smul_apply, Matrix.add_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, Complex.I_mul_I] <;>
    (ring_nf; try simp [Complex.I_mul_I]; try ring)

/-- Mellin radial symbol for `r∂ᵣ`: by convention it is `-s`. -/
def mellinRadialSymbol (s : ℂ) : ℂ := -s

/-- Combined KAN-separated Dirac-Hodge symbol `σᵣ(-sI+i k·σ)`. -/
def KANDiracSymbol (s kx ky : ℂ) : M2C :=
  σ₃ * (mellinRadialSymbol s • (1 : M2C) + nilDiracFourierSymbol kx ky)

/-- Any `2×2` complex matrix has a Pauli-basis decomposition. -/
theorem pauli_decompose (M : M2C) :
    M = ((M 0 0 + M 1 1) / 2) • (1 : M2C) +
        ((M 0 1 + M 1 0) / 2) • σ₁ +
        ((I * (M 0 1 - M 1 0)) / 2) • σ₂ +
        ((M 0 0 - M 1 1) / 2) • σ₃ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₂, σ₃, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply] <;>
    (ring_nf; try simp [Complex.I_mul_I]; try ring)

/-- The KAN Dirac symbol is closed in the biquaternion/Pauli algebra. -/
theorem KANDiracSymbol_biquaternion_closed (s kx ky : ℂ) :
    ∃ a₀ a₁ a₂ a₃ : ℂ,
      KANDiracSymbol s kx ky =
        a₀ • (1 : M2C) + a₁ • σ₁ + a₂ • σ₂ + a₃ • σ₃ := by
  refine ⟨((KANDiracSymbol s kx ky) 0 0 + (KANDiracSymbol s kx ky) 1 1) / 2,
    ((KANDiracSymbol s kx ky) 0 1 + (KANDiracSymbol s kx ky) 1 0) / 2,
    (I * ((KANDiracSymbol s kx ky) 0 1 - (KANDiracSymbol s kx ky) 1 0)) / 2,
    ((KANDiracSymbol s kx ky) 0 0 - (KANDiracSymbol s kx ky) 1 1) / 2, ?_⟩
  exact pauli_decompose (KANDiracSymbol s kx ky)

/-! ## 3. Tripotent scale poles and Cantor discretization -/

/-- Tripotent scale defect with sectors `+1,-1,0`. -/
def Trip : M3C := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

/-- `Trip³=Trip`. -/
theorem Trip_tripotent : Trip * Trip * Trip = Trip := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Trip, Matrix.mul_apply, Fin.sum_univ_three]

/-- Scale matrix `sI-Trip`. -/
def scaleMatrix (s : ℂ) : M3C := s • (1 : M3C) - Trip

/-- Determinant of `sI-Trip`, hence poles at `s=1,-1,0`. -/
theorem scaleMatrix_det (s : ℂ) :
    (scaleMatrix s).det = (s - 1) * (s + 1) * s := by
  simp [scaleMatrix, Trip, Matrix.det_fin_three, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply]

/-- Cantor/Cuntz cylinder count. -/
def cantorCylinderCount (n : ℕ) : ℕ := 2 ^ n

/-- Discretizing radial scale on a binary Cantor tree doubles cylinders. -/
theorem cantorCylinder_refines (n : ℕ) :
    cantorCylinderCount (n + 1) = 2 * cantorCylinderCount n := by
  simp [cantorCylinderCount, pow_succ]
  ring

/-- Synthesis theorem for the KAN/Fourier-Mellin/Dirac framework. -/
theorem kan_fourier_mellin_dirac_synthesis :
    (∀ K : KFactor, ∀ A : AFactor, ∀ N : NFactor, (K.mat * A.mat * N.mat).det = 1) ∧
    (∀ kx ky : ℂ, nilDiracFourierSymbol kx ky * nilDiracFourierSymbol kx ky =
      (-(kx * kx + ky * ky)) • (1 : M2C)) ∧
    (∀ s kx ky : ℂ, ∃ a₀ a₁ a₂ a₃ : ℂ,
      KANDiracSymbol s kx ky = a₀ • (1 : M2C) + a₁ • σ₁ + a₂ • σ₂ + a₃ • σ₃) ∧
    Trip * Trip * Trip = Trip ∧
    (∀ s : ℂ, (scaleMatrix s).det = (s - 1) * (s + 1) * s) ∧
    (∀ n, cantorCylinderCount (n + 1) = 2 * cantorCylinderCount n) := by
  constructor
  · intro K A N
    exact KAN_det_one K A N
  constructor
  · intro kx ky
    exact nilDiracFourierSymbol_sq kx ky
  constructor
  · intro s kx ky
    exact KANDiracSymbol_biquaternion_closed s kx ky
  constructor
  · exact Trip_tripotent
  constructor
  · intro s
    exact scaleMatrix_det s
  · intro n
    exact cantorCylinder_refines n

#check KAN_det_one
#check nilDiracFourierSymbol_sq
#check KANDiracSymbol_biquaternion_closed
#check scaleMatrix_det
#check cantorCylinder_refines
#check kan_fourier_mellin_dirac_synthesis

end KANFourierMellinDirac
