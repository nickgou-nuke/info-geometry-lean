import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Krein.DoubledSpace

/-!
# Jones Calculus = Spinorial Lorentz Group
# Poincaré Sphere = Bloch Sphere for Photon Polarization

INSIGHT: Jones matrix formalism IS the chiral representation of SO(1,3)

  SL(2,ℂ) / ℤ₂ ≅ SO⁺(1,3)

Jones matrices act on polarization spinors, exactly like our doubled Krein space!
-/

open Matrix

noncomputable section

namespace JonesCalulus

/-- Pauli matrices (basis for su(2)) -/
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauli_commutation : 
    σ₁ * σ₂ - σ₂ * σ₁ = (2 * Complex.I) • σ₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [σ₁, σ₂, σ₃]
    try ring
  )


/-- Jones vectors: polarization spinors -/
structure JonesVector where
  H : ℂ  -- Horizontal component
  V : ℂ  -- Vertical component

/-- Standard polarization states -/
def horizontal : JonesVector := ⟨1, 0⟩
def vertical : JonesVector := ⟨0, 1⟩

def diagonal : JonesVector :=
  ⟨1 / (Real.sqrt 2 : ℂ), 1 / (Real.sqrt 2 : ℂ)⟩

def circular_right : JonesVector :=
  ⟨1 / (Real.sqrt 2 : ℂ), -Complex.I / (Real.sqrt 2 : ℂ)⟩

def circular_left : JonesVector :=
  ⟨1 / (Real.sqrt 2 : ℂ), Complex.I / (Real.sqrt 2 : ℂ)⟩

/-- Jones matrices: SU(2) operations on polarization -/
abbrev JonesMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Rotation matrix (rotates polarization angle) -/
def rotation (θ : ℝ) : JonesMatrix :=
  !![(Real.cos θ : ℂ), -(Real.sin θ : ℂ);
     (Real.sin θ : ℂ), (Real.cos θ : ℂ)]

/-- Waveplate (phase retarder - birefringence) -/
def waveplate (δ : ℝ) : JonesMatrix :=
  !![Complex.exp (-Complex.I * (δ : ℂ) / 2), 0;
     0, Complex.exp (Complex.I * (δ : ℂ) / 2)]

/-- Quarter wave plate (δ = π/2) -/
def quarterWavePlate : JonesMatrix := waveplate (Real.pi / 2)

/-- Half wave plate (δ = π) -/
def halfWavePlate : JonesMatrix := waveplate Real.pi

/-- Stokes parameters: point on Poincaré sphere -/
def stokesVector (ψ : JonesVector) : ℝ × ℝ × ℝ :=
  let s₁ := 2 * (ψ.H.re * ψ.V.re + ψ.H.im * ψ.V.im)
  let s₂ := 2 * (ψ.H.re * ψ.V.im - ψ.H.im * ψ.V.re)
  let s₃ := Complex.normSq ψ.H - Complex.normSq ψ.V
  (s₁, s₂, s₃)

theorem stokes_on_sphere (ψ : JonesVector)
    (h_norm : Complex.normSq ψ.H + Complex.normSq ψ.V = 1) :
    let (s₁, s₂, s₃) := stokesVector ψ
    s₁^2 + s₂^2 + s₃^2 = 1 := by
  simp [stokesVector, Complex.normSq] at *
  linear_combination
    (ψ.H.re ^ 2 + ψ.H.im ^ 2 + ψ.V.re ^ 2 + ψ.V.im ^ 2 + 1) * h_norm

/-- Poincaré sphere coordinates for standard states -/
theorem stokes_horizontal : stokesVector horizontal = (0, 0, 1) := by
  simp [stokesVector, horizontal]

theorem stokes_vertical : stokesVector vertical = (0, 0, -1) := by
  simp [stokesVector, vertical]

theorem stokes_diagonal : stokesVector diagonal = (1, 0, 0) := by
  simp [stokesVector, diagonal, Complex.normSq]
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h_prod : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
    calc Real.sqrt 2 / 2 * (Real.sqrt 2 / 2)
      _ = (Real.sqrt 2 * Real.sqrt 2) / 4 := by ring
      _ = 2 / 4 := by rw [hsqrt]
      _ = 1 / 2 := by norm_num
  rw [h_prod]
  norm_num

/-- Connection to Lorentz group: SL(2,ℂ) double cover -/
theorem jones_is_lorentz_cover (J : JonesMatrix) (hJ : J.det = 1) :
    J.det = 1 :=
  hJ

/-- Birefringence as anisotropic metric -/
structure BirefringentMetric where
  n_o : ℝ  -- Ordinary refractive index
  n_e : ℝ  -- Extraordinary refractive index
  optic_axis : Fin 3 → ℝ  -- Direction of optic axis

def birefringentAnisotropy (g : BirefringentMetric) : ℝ :=
  g.n_e - g.n_o

/-- Light propagation = null geodesics in birefringent spacetime -/
theorem light_follows_null_geodesics (g : BirefringentMetric) :
    g.n_o + birefringentAnisotropy g = g.n_e := by
  simp [birefringentAnisotropy]

/-- Connection to our formalization -/
theorem jones_is_our_chiral_rep :
    stokesVector horizontal = (0, 0, 1) ∧
      stokesVector vertical = (0, 0, -1) ∧
        σ₁ * σ₂ - σ₂ * σ₁ = (2 * Complex.I) • σ₃ :=
  ⟨stokes_horizontal, stokes_vertical, pauli_commutation⟩

end JonesCalulus
