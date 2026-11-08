/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.RelativeDeterminantScatteringSocket

Constructive finite-dimensional **Weinstein–Aronszajn / Birman–Krein Relative Perturbation
Determinant and Cayley Scattering** owner over `Matrix n n ℂ`:

#### BUCKET 1: CLOSED FINITE THEOREMS
- `weinsteinAronszajnMatrix_self_and_relative_determinant_self`
- `second_resolvent_identity`
- `weinstein_aronszajn_factorization`
- `relative_determinant_zero_iff_perturbed_eigenvalue`
- `birman_krein_cayley_scattering_det_identity`
- `resolvent_difference_trace_identity`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `second_resolvent_identity` (conditional on `R₀ * (H₀ - Z) = 1` and `(H - Z) * R = 1`)
- `weinstein_aronszajn_factorization` and `relative_determinant_zero_iff_perturbed_eigenvalue`
  (conditional on two-sided free resolvent invertibility `(H₀ - z • 1) * R₀ = 1` and
  `R₀ * (H₀ - z • 1) = 1`)
- `birman_krein_cayley_scattering_det_identity` (conditional on `R z * (H - z • 1) = 1`)
- `resolvent_difference_trace_identity` (conditional on `R₀ * (H₀ - z • 1) = 1` and
  `(H - z • 1) * R = 1`)

#### BUCKET 3: OPEN CLOSURE DEBT
- Infinite-dimensional trace-class Fredholm determinants `det₁(1 + V R₀(z))` and continuum
  spectral shift measures `ξ(λ)` on unbounded self-adjoint operators remain external analytic
  context beyond finite matrix algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.RelativeDeterminantScatteringSocket

/-! ## Constructive Finite-Dimensional Weinstein–Aronszajn & Birman–Krein Theorems -/

section FiniteMatrixRelativeDeterminant

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Weinstein–Aronszajn relative perturbation matrix `W(z) = 1 + (H - H₀) * R₀`. -/
def weinsteinAronszajnMatrix (H₀ H R₀ : Matrix n n ℂ) : Matrix n n ℂ :=
  1 + (H - H₀) * R₀

/-- Finite-dimensional relative perturbation determinant `det(1 + (H - H₀) * R₀)`. -/
def matrixRelativeDeterminant (H₀ H : Matrix n n ℂ) (R₀ : ℂ → Matrix n n ℂ) (z : ℂ) : ℂ :=
  Matrix.det (weinsteinAronszajnMatrix H₀ H (R₀ z))

/-- Finite-dimensional Cayley / Jost scattering matrix `S(z) = (H + z • 1) * R(z)`. -/
def matrixCayleyScattering (H : Matrix n n ℂ) (R : ℂ → Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  (H + z • (1 : Matrix n n ℂ)) * R z

/-- At zero perturbation (`H = H₀`), the Weinstein–Aronszajn matrix is the identity matrix `1`
and the relative perturbation determinant is identically `1`. -/
theorem weinsteinAronszajnMatrix_self_and_relative_determinant_self
    (H₀ : Matrix n n ℂ) (R₀ : ℂ → Matrix n n ℂ) (z : ℂ) :
    weinsteinAronszajnMatrix H₀ H₀ (R₀ z) = 1 ∧
    matrixRelativeDeterminant H₀ H₀ R₀ z = 1 := by
  have hWA : weinsteinAronszajnMatrix H₀ H₀ (R₀ z) = 1 := by
    dsimp [weinsteinAronszajnMatrix]
    rw [sub_self, zero_mul, add_zero]
  refine ⟨hWA, ?_⟩
  dsimp [matrixRelativeDeterminant]
  rw [hWA, Matrix.det_one]

/-- **Second Resolvent Identity (`second_resolvent_identity`)**:
In any associative ring `B`, if `R₀ * (H₀ - Z) = 1` and `(H - Z) * R = 1`, then
`R₀ - R = R₀ * (H - H₀) * R`. -/
theorem second_resolvent_identity
    {B : Type*} [Ring B] (H₀ H Z R₀ R : B)
    (hR₀_left : R₀ * (H₀ - Z) = 1)
    (hR_right : (H - Z) * R = 1) :
    R₀ - R = R₀ * (H - H₀) * R := by
  calc
    R₀ - R = R₀ * ((H - Z) * R) - (R₀ * (H₀ - Z)) * R := by
      rw [hR_right, hR₀_left, mul_one, one_mul]
    _ = R₀ * (H - H₀) * R := by noncomm_ring

/-- **Weinstein–Aronszajn Factorization (`weinstein_aronszajn_factorization`)**:
Whenever `(H₀ - z • 1) * R₀ = 1`, the relative perturbation matrix satisfies
`weinsteinAronszajnMatrix H₀ H R₀ = (H - z • 1) * R₀` and
`Matrix.det (weinsteinAronszajnMatrix H₀ H R₀) * Matrix.det (H₀ - z • 1) = Matrix.det (H - z • 1)`. -/
theorem weinstein_aronszajn_factorization
    (H₀ H R₀ : Matrix n n ℂ) (z : ℂ)
    (hR₀_right : (H₀ - z • (1 : Matrix n n ℂ)) * R₀ = 1)
    (hR₀_left : R₀ * (H₀ - z • (1 : Matrix n n ℂ)) = 1) :
    weinsteinAronszajnMatrix H₀ H R₀ = (H - z • (1 : Matrix n n ℂ)) * R₀ ∧
    Matrix.det (weinsteinAronszajnMatrix H₀ H R₀) *
      Matrix.det (H₀ - z • (1 : Matrix n n ℂ)) =
      Matrix.det (H - z • (1 : Matrix n n ℂ)) := by
  have hWA : weinsteinAronszajnMatrix H₀ H R₀ = (H - z • (1 : Matrix n n ℂ)) * R₀ := by
    calc
      weinsteinAronszajnMatrix H₀ H R₀
        = (H₀ - z • (1 : Matrix n n ℂ)) * R₀ + (H - H₀) * R₀ := by
            dsimp [weinsteinAronszajnMatrix]
            rw [hR₀_right]
      _ = (H - z • (1 : Matrix n n ℂ)) * R₀ := by
            rw [← add_mul]
            congr 1
            abel
  refine ⟨hWA, ?_⟩
  rw [hWA, ← Matrix.det_mul, mul_assoc, hR₀_left, mul_one]

/-- **Relative Perturbation Determinant Zero ↔ Perturbed Eigenvalue Theorem
(`relative_determinant_zero_iff_perturbed_eigenvalue`)**:
At any spectral parameter `z : ℂ` where `R₀ z` is a two-sided inverse of `H₀ - z • 1`,
the relative perturbation determinant `matrixRelativeDeterminant H₀ H R₀ z` vanishes if and only if
`z` is an eigenvalue/resonance of `H` (`Matrix.det (H - z • 1) = 0`). -/
theorem relative_determinant_zero_iff_perturbed_eigenvalue
    (H₀ H : Matrix n n ℂ) (R₀ : ℂ → Matrix n n ℂ) (z : ℂ)
    (hR₀_right : (H₀ - z • (1 : Matrix n n ℂ)) * R₀ z = 1)
    (hR₀_left : R₀ z * (H₀ - z • (1 : Matrix n n ℂ)) = 1) :
    matrixRelativeDeterminant H₀ H R₀ z = 0 ↔
      Matrix.det (H - z • (1 : Matrix n n ℂ)) = 0 := by
  dsimp [matrixRelativeDeterminant]
  have hDetProd := (weinstein_aronszajn_factorization H₀ H (R₀ z) z hR₀_right hR₀_left).2
  have hDetFreeNe : Matrix.det (H₀ - z • (1 : Matrix n n ℂ)) ≠ 0 := by
    intro hZero
    have hOne : Matrix.det ((H₀ - z • (1 : Matrix n n ℂ)) * R₀ z) = 1 := by
      rw [hR₀_right, Matrix.det_one]
    rw [Matrix.det_mul, hZero, zero_mul] at hOne
    exact zero_ne_one hOne
  rw [← hDetProd, mul_eq_zero]
  exact ⟨fun h => Or.inl h, fun h => h.resolve_right hDetFreeNe⟩

/-- **Birman–Krein Cayley Scattering Determinant Identity
(`birman_krein_cayley_scattering_det_identity`)**:
Whenever `R z * (H - z • 1) = 1`, the Cayley scattering matrix `matrixCayleyScattering H R z`
satisfies `Matrix.det (matrixCayleyScattering H R z) * Matrix.det (H - z • 1) = Matrix.det (H + z • 1)`. -/
theorem birman_krein_cayley_scattering_det_identity
    (H : Matrix n n ℂ) (R : ℂ → Matrix n n ℂ) (z : ℂ)
    (hR_left : R z * (H - z • (1 : Matrix n n ℂ)) = 1) :
    Matrix.det (matrixCayleyScattering H R z) *
      Matrix.det (H - z • (1 : Matrix n n ℂ)) =
      Matrix.det (H + z • (1 : Matrix n n ℂ)) := by
  dsimp [matrixCayleyScattering]
  rw [← Matrix.det_mul, mul_assoc, hR_left, mul_one]

/-- **Resolvent Difference & Krein Spectral-Shift Trace Identity
(`resolvent_difference_trace_identity`)**:
Whenever `R₀ * (H₀ - z • 1) = 1` and `(H - z • 1) * R = 1`:
1. `Matrix.trace (R₀ - R) = Matrix.trace (R₀ * (H - H₀) * R)`,
2. `Matrix.trace (R₀ - R) = Matrix.trace ((H - H₀) * R * R₀)` (cyclic trace reduction),
3. `Matrix.trace (R - R₀) = - Matrix.trace ((H - H₀) * R * R₀)`,
4. `Matrix.trace (weinsteinAronszajnMatrix H₀ H R₀ - 1) = Matrix.trace ((H - H₀) * R₀)`. -/
theorem resolvent_difference_trace_identity
    (H₀ H R₀ R : Matrix n n ℂ) (z : ℂ)
    (hR₀_left : R₀ * (H₀ - z • (1 : Matrix n n ℂ)) = 1)
    (hR_right : (H - z • (1 : Matrix n n ℂ)) * R = 1) :
    Matrix.trace (R₀ - R) = Matrix.trace (R₀ * (H - H₀) * R) ∧
    Matrix.trace (R₀ - R) = Matrix.trace ((H - H₀) * R * R₀) ∧
    Matrix.trace (R - R₀) = - Matrix.trace ((H - H₀) * R * R₀) ∧
    Matrix.trace (weinsteinAronszajnMatrix H₀ H R₀ - 1) =
      Matrix.trace ((H - H₀) * R₀) := by
  have hRes := second_resolvent_identity H₀ H (z • (1 : Matrix n n ℂ)) R₀ R hR₀_left hR_right
  have hTr1 : Matrix.trace (R₀ - R) = Matrix.trace (R₀ * (H - H₀) * R) :=
    congrArg Matrix.trace hRes
  have hTr2 : Matrix.trace (R₀ - R) = Matrix.trace ((H - H₀) * R * R₀) := by
    rw [hTr1, mul_assoc R₀ (H - H₀) R, Matrix.trace_mul_comm R₀ ((H - H₀) * R)]
  have hTr3 : Matrix.trace (R - R₀) = - Matrix.trace ((H - H₀) * R * R₀) := by
    have hNeg : R - R₀ = -(R₀ - R) := by abel
    rw [hNeg, Matrix.trace_neg, hTr2]
  have hTrWA :
      Matrix.trace (weinsteinAronszajnMatrix H₀ H R₀ - 1) =
        Matrix.trace ((H - H₀) * R₀) := by
    have hSub : weinsteinAronszajnMatrix H₀ H R₀ - 1 = (H - H₀) * R₀ := by
      dsimp [weinsteinAronszajnMatrix]
      abel
    rw [hSub]
  exact ⟨hTr1, hTr2, hTr3, hTrWA⟩

end FiniteMatrixRelativeDeterminant

end InfoGeometry.Canonical.RelativeDeterminantScatteringSocket
