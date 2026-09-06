import InfoGeometry.Canonical.BoundaryBraidRepresentation
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Fibonacci.FibAnyonSpectralObstruction
import InfoGeometry.Physics.B3PresentedGroup
import Mathlib.Tactic

/-!
# Direct boundary/Fibonacci intertwiner obstruction

The native eight-dimensional boundary braid representation and the native
Fibonacci two-dimensional representation are not identified here.

This owner records the first compatibility condition for a candidate direct
intertwiner.  If a matrix `Φ : ℂ⁸ → ℂ²` intertwines the first Artin generator,
`Φ s₀ = R Φ`, then the relation `s₀² = -I` forces
`(R² + I) Φ = 0`.

No projection, fibre equivalence, or nonzero intertwiner is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction

open Matrix
open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Canonical.YangBaxterProof

local notation "s₀" => _root_.InfoGeometry.Physics.JonesBraidB3.s0
local notation "s₁" => _root_.InfoGeometry.Physics.JonesBraidB3.s1
local notation "R_Fib" => _root_.InfoGeometry.Canonical.YangBaxterProof.R
local notation "B_Fib" => _root_.InfoGeometry.Canonical.YangBaxterProof.B

/-- Matrix form of intertwining the first Artin generator. -/
def IntertwinesFirstGenerator (Φ : Matrix (Fin 2) (Fin 8) ℂ) : Prop :=
  Φ * s₀ = R_Fib * Φ

/-- The linear defect whose kernel is the space of first-generator
intertwiners. -/
def firstGeneratorDefect :
    Matrix (Fin 2) (Fin 8) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 8) ℂ where
  toFun Φ := Φ * s₀ - R_Fib * Φ
  map_add' Φ Ψ := by
    change (Φ + Ψ) * s₀ - R_Fib * (Φ + Ψ) =
      (Φ * s₀ - R_Fib * Φ) + (Ψ * s₀ - R_Fib * Ψ)
    rw [Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' c Φ := by
    change (c • Φ) * s₀ - R_Fib * (c • Φ) =
      c • (Φ * s₀ - R_Fib * Φ)
    rw [smul_sub, Matrix.smul_mul, Matrix.mul_smul]

theorem mem_firstGeneratorDefect_ker_iff (Φ : Matrix (Fin 2) (Fin 8) ℂ) :
    Φ ∈ LinearMap.ker firstGeneratorDefect ↔
      IntertwinesFirstGenerator Φ := by
  change Φ * s₀ - R_Fib * Φ = 0 ↔ _
  exact sub_eq_zero

/-- The second Artin-generator defect for a direct boundary/Fibonacci map. -/
def secondGeneratorDefect :
    Matrix (Fin 2) (Fin 8) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 8) ℂ where
  toFun Φ := Φ * s₁ - B_Fib * Φ
  map_add' Φ Ψ := by
    change (Φ + Ψ) * s₁ - B_Fib * (Φ + Ψ) =
      (Φ * s₁ - B_Fib * Φ) + (Ψ * s₁ - B_Fib * Ψ)
    rw [Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' c Φ := by
    change (c • Φ) * s₁ - B_Fib * (c • Φ) =
      c • (Φ * s₁ - B_Fib * Φ)
    rw [smul_sub, Matrix.smul_mul, Matrix.mul_smul]

theorem mem_secondGeneratorDefect_ker_iff
    (Φ : Matrix (Fin 2) (Fin 8) ℂ) :
    Φ ∈ LinearMap.ker secondGeneratorDefect ↔
      Φ * s₁ = B_Fib * Φ := by
  change Φ * s₁ - B_Fib * Φ = 0 ↔ _
  exact sub_eq_zero

/-- The simultaneous two-generator matrix defect. -/
def simultaneousGeneratorDefect :
    Matrix (Fin 2) (Fin 8) ℂ →ₗ[ℂ]
      (Matrix (Fin 2) (Fin 8) ℂ × Matrix (Fin 2) (Fin 8) ℂ) where
  toFun Φ := (firstGeneratorDefect Φ, secondGeneratorDefect Φ)
  map_add' Φ Ψ := by
    exact Prod.ext (map_add (firstGeneratorDefect) Φ Ψ)
      (map_add (secondGeneratorDefect) Φ Ψ)
  map_smul' c Φ := by
    exact Prod.ext (map_smul (firstGeneratorDefect) c Φ)
      (map_smul (secondGeneratorDefect) c Φ)

theorem mem_simultaneousGeneratorDefect_ker_iff
    (Φ : Matrix (Fin 2) (Fin 8) ℂ) :
    Φ ∈ LinearMap.ker simultaneousGeneratorDefect ↔
      Φ ∈ LinearMap.ker firstGeneratorDefect ∧
        Φ ∈ LinearMap.ker secondGeneratorDefect := by
  change simultaneousGeneratorDefect Φ = 0 ↔ _
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h₀, h₁⟩
    exact Prod.ext h₀ h₁

/-- Any direct first-generator intertwiner is annihilated by `R² + I`.
This is the spectral obstruction forced by `s₀² = -I`. -/
theorem fibonacci_square_obstruction
    (Φ : Matrix (Fin 2) (Fin 8) ℂ)
    (hΦ : IntertwinesFirstGenerator Φ) :
    (R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Φ = 0 := by
  have hstep :
      Φ * (s₀ * s₀) =
        (R_Fib * R_Fib) * Φ := by
    calc
      Φ * (s₀ * s₀)
          = (Φ * s₀) * s₀ := by
              rw [Matrix.mul_assoc]
      _ = (R_Fib * Φ) * s₀ := by rw [hΦ]
      _ = R_Fib * (Φ * s₀) := by rw [Matrix.mul_assoc]
      _ = R_Fib * (R_Fib * Φ) := by rw [hΦ]
      _ = (R_Fib * R_Fib) * Φ := by rw [Matrix.mul_assoc]
  have hneg : -(Φ : Matrix (Fin 2) (Fin 8) ℂ) = (R_Fib * R_Fib) * Φ := by
    calc
      -Φ = Φ * (-(1 : Matrix (Fin 8) (Fin 8) ℂ)) := by simp
      _ = Φ * (s₀ * s₀) := by
            rw [s0_sq_eq_neg_one]
      _ = (R_Fib * R_Fib) * Φ := hstep
  calc
    (R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Φ
        = (R_Fib * R_Fib) * Φ + Φ := by
            rw [Matrix.add_mul, Matrix.one_mul]
    _ = -Φ + Φ := by rw [← hneg]
    _ = 0 := by simp

/-- A left inverse for `R² + I` forces every direct candidate intertwiner to
vanish. -/
theorem direct_intertwiner_eq_zero_of_left_inverse
    (Φ : Matrix (Fin 2) (Fin 8) ℂ)
    (hΦ : IntertwinesFirstGenerator Φ)
    (L : Matrix (Fin 2) (Fin 2) ℂ)
    (hL : L * (R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1) :
    Φ = 0 := by
  have hobs := fibonacci_square_obstruction Φ hΦ
  calc
    Φ = (1 : Matrix (Fin 2) (Fin 2) ℂ) * Φ := by simp
    _ = (L * (R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ))) * Φ := by rw [hL]
    _ = L * ((R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Φ) := by
          rw [Matrix.mul_assoc]
    _ = L * (0 : Matrix (Fin 2) (Fin 8) ℂ) := by rw [hobs]
    _ = (0 : Matrix (Fin 2) (Fin 8) ℂ) := by simp

/-- The concrete Fibonacci phase has a nonsingular spectral obstruction. -/
theorem obstruction_det_ne_zero :
    Matrix.det (R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ)) ≠ 0 := by
  simpa [InfoGeometry.Canonical.YangBaxterProof.R,
    InfoGeometry.Fibonacci.FibAnyonThm3.R] using
    InfoGeometry.Fibonacci.FibAnyonSpectralObstruction.R_sq_add_one_det_ne_zero

/-- No nonzero direct intertwiner exists for the concrete first-generator
representations. -/
theorem direct_intertwiner_eq_zero
    (Φ : Matrix (Fin 2) (Fin 8) ℂ)
    (hΦ : IntertwinesFirstGenerator Φ) :
    Φ = 0 := by
  apply direct_intertwiner_eq_zero_of_left_inverse Φ hΦ
    (R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹
  exact Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr obstruction_det_ne_zero)

/-- The first-generator intertwiner kernel is genuinely zero. -/
theorem firstGeneratorDefect_ker_eq_bot :
    LinearMap.ker firstGeneratorDefect = ⊥ := by
  apply le_antisymm
  · intro Φ hΦ
    rw [mem_firstGeneratorDefect_ker_iff] at hΦ
    exact (direct_intertwiner_eq_zero Φ hΦ)
  · exact bot_le

/-- No nonzero direct map intertwines both concrete Artin generators. -/
theorem simultaneousGeneratorDefect_ker_eq_bot :
    LinearMap.ker simultaneousGeneratorDefect = ⊥ := by
  apply le_antisymm
  · intro Φ hΦ
    have h₀ : Φ ∈ LinearMap.ker firstGeneratorDefect :=
      (mem_simultaneousGeneratorDefect_ker_iff Φ).mp hΦ |>.1
    exact (firstGeneratorDefect_ker_eq_bot ▸ h₀)
  · exact bot_le

/-- The simultaneous generator-intertwiner space has no finite-dimensional
dimension: its kernel is the zero submodule. -/
theorem simultaneousGeneratorDefect_ker_finrank_eq_zero :
    Module.finrank ℂ (LinearMap.ker simultaneousGeneratorDefect) = 0 := by
  rw [simultaneousGeneratorDefect_ker_eq_bot, finrank_bot]

end InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction
