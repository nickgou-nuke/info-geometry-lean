/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
import InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis
import InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction
import InfoGeometry.Algebra.NoncommutativeKramersCompassHallSynthesis
import InfoGeometry.Quantum.QuaternionSpinTimeReversal
import InfoGeometry.Canonical.FiniteCompassBraidedChain
import Mathlib.Tactic

/-!
# Intertwining Bridge: Noncommutative Kramers–Compass–Dirac–Zorn Synthesis

Connects the noncommutative `M₂(B)` / `M₂(M₂(B))` operator-algebraic modules
(`NoncommutativeKramersCompassHallSynthesis`, `NoncommutativeInherentZornGaugeSynthesis`,
`NoncommutativeYangMillsHiggsSpectralAction`) with the existing spinor/compass owners:

1. `InfoGeometry.Quantum.QuaternionSpinTimeReversal`:
   Proves `timeReverse ψ = (-omegaOp) *ᵥ (star ψ)` and
   `timeReverse (H *ᵥ ψ) = (sympTimeRev Hᵀ) *ᵥ (timeReverse ψ)`, deriving
   the Kramers eigenpair theorem directly from `sympTimeRev Hᵀ = H`.
2. `InfoGeometry.Canonical.FiniteCompassBraidedChain`:
   Constructs `zornCompassTriple B : CompassTriple (Matrix (Fin 2) (Fin 2) B)`
   over an arbitrary `[Ring B]` using `omegaOp` (elliptic), `gamma1Op` (hyperbolic),
   and `mat2 0 1 0 0` (parabolic nilpotent).
3. `NoncommutativeInherentZornGaugeSynthesis` / `NoncommutativeYangMillsHiggsSpectralAction`:
   Defines `blockwiseSympTimeRev` on `NestedMat B` and proves that `bareDiracZorn`
   is `Θ`-even for self-adjoint mass and skew-adjoint covariant derivatives,
   `Θ`-odd for zero mass and self-adjoint Zeeman fields, and that the quartic
   spectral action `trace4 ((D_cov * D_cov)ᴴ * (D_cov * D_cov))` is self-adjoint.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
open InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis
open InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction
open InfoGeometry.Algebra.NoncommutativeKramersCompassHallSynthesis
open InfoGeometry.Quantum.QuaternionSpinTimeReversal
open InfoGeometry.Canonical.FiniteCompassBraidedChain

namespace InfoGeometry.Algebra.NoncommutativeKramersCompassBridge

/-! ## Bridge 1: `QuaternionSpinTimeReversal` ↔ `sympTimeRev` -/

section QuaternionSpinBridge

/-- `QuaternionSpinTimeReversal.timeReverse` on `TwoSpinor` is left-multiplication
by `-omegaOp` composed with entrywise conjugation `star`. -/
theorem timeReverse_eq_neg_omegaOp_mulVec (ψ : TwoSpinor) :
    timeReverse ψ = (-(omegaOp : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ (star ψ) := by
  ext i
  fin_cases i <;>
    simp [timeReverse, omegaOp, mat2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Intertwining of matrix action with `timeReverse` via `sympTimeRev` on `Hᵀ`. -/
theorem timeReverse_mulVec_eq_sympTimeRev_transpose
    (H : Matrix (Fin 2) (Fin 2) ℂ) (ψ : TwoSpinor) :
    timeReverse (H *ᵥ ψ) = (sympTimeRev Hᵀ) *ᵥ (timeReverse ψ) := by
  rw [timeReverse_eq_neg_omegaOp_mulVec, timeReverse_eq_neg_omegaOp_mulVec]
  ext i
  fin_cases i <;>
    (simp [sympTimeRev, omegaOp, mat2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
     try ring)

/-- Kramers eigenpair derived from `sympTimeRev Hᵀ = H` and real eigenvalue. -/
theorem kramers_sympTimeRev_eigenpair
    (H : Matrix (Fin 2) (Fin 2) ℂ) (eigenvalue : ℝ) (ψ : TwoSpinor)
    (hH : sympTimeRev Hᵀ = H)
    (heig : H *ᵥ ψ = (eigenvalue : ℂ) • ψ) :
    H *ᵥ (timeReverse ψ) = (eigenvalue : ℂ) • (timeReverse ψ) ∧
      spinorPair ψ (timeReverse ψ) = 0 := by
  refine ⟨?_, timeReverse_orthogonal ψ⟩
  calc
    H *ᵥ (timeReverse ψ)
      = (sympTimeRev Hᵀ) *ᵥ (timeReverse ψ) := by rw [hH]
    _ = timeReverse (H *ᵥ ψ) := (timeReverse_mulVec_eq_sympTimeRev_transpose H ψ).symm
    _ = timeReverse ((eigenvalue : ℂ) • ψ) := by rw [heig]
    _ = star (eigenvalue : ℂ) • timeReverse ψ := timeReverse_smul _ ψ
    _ = (eigenvalue : ℂ) • timeReverse ψ := by simp

end QuaternionSpinBridge

/-! ## Bridge 2: `FiniteCompassBraidedChain.CompassTriple` in `M₂(B)` -/

section CompassBridge

/-- Parabolic nilpotent generator in `M₂(B)` (`(1/2)(sigmaOp - omegaOp)` without requiring `2⁻¹`). -/
def parabolicShearOp {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B :=
  mat2 0 1 0 0

lemma parabolicShearOp_sq {B : Type*} [Ring B] :
    (parabolicShearOp : Matrix (Fin 2) (Fin 2) B) * parabolicShearOp = 0 := by
  apply ext_fin2 <;> simp [parabolicShearOp]

/-- Realization of `FiniteCompassBraidedChain.CompassTriple` in `M₂(B)` over any `[Ring B]`. -/
def zornCompassTriple (B : Type*) [Ring B] :
    CompassTriple (Matrix (Fin 2) (Fin 2) B) where
  elliptic := omegaOp
  hyperbolic := gamma1Op
  parabolic := parabolicShearOp
  elliptic_sq_neg_one := omegaOp_sq
  hyperbolic_sq_one := gamma1Op_sq
  parabolic_sq_zero := parabolicShearOp_sq

theorem zornCompassTriple_elliptic_hyperbolic_anticomm {B : Type*} [Ring B] :
    (zornCompassTriple B).elliptic * (zornCompassTriple B).hyperbolic +
      (zornCompassTriple B).hyperbolic * (zornCompassTriple B).elliptic = 0 := by
  dsimp [zornCompassTriple]
  rw [add_comm]
  exact gamma1_omega_anticomm

end CompassBridge

/-! ## Bridge 3: Blockwise `sympTimeRev` on `bareDiracZorn` & Self-Adjoint Spectral Action -/

section DiracZornTimeReversalBridge

variable {B : Type*} [Ring B] [StarRing B]

/-- Blockwise symplectic time-reversal on `NestedMat B = M₂(M₂(B))`. -/
def blockwiseSympTimeRev (M : NestedMat B) : NestedMat B :=
  mat2 (sympTimeRev (M 0 0)) (sympTimeRev (M 0 1))
       (sympTimeRev (M 1 0)) (sympTimeRev (M 1 1))

/-- With self-adjoint mass `star m = m` and skew-adjoint covariant derivatives
`star Dₖ = -Dₖ`, `bareDiracZorn m D₁ D₂ D₃` is `blockwiseSympTimeRev`-invariant. -/
theorem blockwiseSympTimeRev_bareDiracZorn_covariant
    (m D₁ D₂ D₃ : B)
    (hm : star m = m)
    (h1 : star D₁ = -D₁) (h2 : star D₂ = -D₂) (h3 : star D₃ = -D₃) :
    blockwiseSympTimeRev (bareDiracZorn m D₁ D₂ D₃) =
      bareDiracZorn m D₁ D₂ D₃ := by
  apply ext_fin2
  · simp [blockwiseSympTimeRev, bareDiracZorn, diracZornOp, sympTimeRev_fiberEmbed, hm]
  · simp [blockwiseSympTimeRev, bareDiracZorn, diracZornOp, sympTimeRev_vecOp,
      h1, h2, h3]
    apply ext_fin2 <;> simp <;> abel
  · simp [blockwiseSympTimeRev, bareDiracZorn, diracZornOp, sympTimeRev_vecOp,
      h1, h2, h3]
    apply ext_fin2 <;> simp <;> abel
  · simp [blockwiseSympTimeRev, bareDiracZorn, diracZornOp, sympTimeRev_fiberEmbed, hm,
      star_neg]

/-- With zero mass and self-adjoint Zeeman fields `star Mₖ = Mₖ`,
`bareDiracZorn 0 M₁ M₂ M₃` is `blockwiseSympTimeRev`-odd. -/
theorem blockwiseSympTimeRev_bareDiracZorn_zeeman_odd
    (M₁ M₂ M₃ : B)
    (h1 : star M₁ = M₁) (h2 : star M₂ = M₂) (h3 : star M₃ = M₃) :
    blockwiseSympTimeRev (bareDiracZorn 0 M₁ M₂ M₃) =
      -bareDiracZorn 0 M₁ M₂ M₃ := by
  apply ext_fin2
  · simp [blockwiseSympTimeRev, bareDiracZorn, diracZornOp, sympTimeRev_fiberEmbed]
    apply ext_fin2 <;> simp [fiberEmbed]
  · simp [blockwiseSympTimeRev, bareDiracZorn, diracZornOp, sympTimeRev_vecOp, h1, h2, h3]
  · simp [blockwiseSympTimeRev, bareDiracZorn, diracZornOp, sympTimeRev_vecOp, h1, h2, h3]
  · simp [blockwiseSympTimeRev, bareDiracZorn, diracZornOp, sympTimeRev_fiberEmbed]
    apply ext_fin2 <;> simp [fiberEmbed]

/-- Every term in `unified_yang_mills_higgs_dirac_spectral_action` is a Hermitian
square `star x * x`, so the quartic `trace4` spectral action is self-adjoint in `B`. -/
theorem unified_spectral_action_selfAdjoint
    (m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁ := d₁ + A₁
    let D₂ := d₂ + A₂
    let D₃ := d₃ + A₃
    let D_cov := bareDiracZorn m D₁ D₂ D₃
    star (trace4 ((D_cov * D_cov)ᴴ * (D_cov * D_cov))) =
      trace4 ((D_cov * D_cov)ᴴ * (D_cov * D_cov)) := by
  intro D₁ D₂ D₃ D_cov
  have hact := unified_yang_mills_higgs_dirac_spectral_action m d₁ d₂ d₃ A₁ A₂ A₃ h23 h31 h12
  dsimp only at hact
  rw [show D_cov * D_cov = (diracZornOp m (-m) D₁ D₂ D₃ D₁ D₂ D₃ : NestedMat B) ^ 2 by
    simp only [D_cov, bareDiracZorn, pow_two]]
  rw [hact]
  rw [star_nsmul]
  simp only [star_add, star_mul, star_star]

end DiracZornTimeReversalBridge

/-- Explicit non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem mat2C_basis_noncommuting :
    ∃ A C : Matrix (Fin 2) (Fin 2) ℂ, A * C ≠ C * A := by
  refine ⟨!![1, 0; 0, 0], !![0, 1; 0, 0], ?_⟩
  intro h
  have h01 := congrArg (fun M => M 0 1) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01

end InfoGeometry.Algebra.NoncommutativeKramersCompassBridge
