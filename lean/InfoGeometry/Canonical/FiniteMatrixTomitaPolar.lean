/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Finite-Matrix Tomita–Takesaki Polar Decomposition & Modular Flow (`D20`)

This module constructs the finite-dimensional real matrix Tomita–Takesaki theory on
`Matrix (Fin n) (Fin n) ℝ` equipped with a strictly positive density square-root factor
`r = ρ^{1/2}` (`PositiveRealDensityFactor n`):

1. **Hilbert–Schmidt Inner Product** `hsInner X Y = (Xᵀ * Y).trace`, proved symmetric and
   strictly positive-definite (`hsInner X X = 0 ↔ X = 0`).
2. **Tomita Operator & Exact Polar Decomposition**:
   - `tomitaOp F X = F.rInv * Xᵀ * F.r`, satisfying `tomitaOp F (X * F.r) = Xᵀ * F.r`,
     `tomitaOp_involution : S(S(X)) = X`.
   - `modularOp F X = F.rho * X * F.rhoInv` and `modularSqrt F X = F.r * X * F.rInv`, proved
     equal to `F_adj ∘ S` and `Δ^{1/2} ∘ Δ^{1/2}`, symmetric and strictly positive for `hsInner`.
   - `modularConj X = Xᵀ`, proved involutive and `hsInner`-isometric.
   - `tomita_polar_decomposition : tomitaOp F X = modularConj (modularSqrt F X)` (`S = J Δ^{1/2}`).
   - `modularConj_modularOp_conj : J (Δ (J X)) = Δ⁻¹ X`.
3. **CommutantConjugation, Exact KMS Identity & Causal Wedge Invariance**:
   - `modularConj_leftMul_conj : J (leftMul A (J X)) = rightMul Aᵀ X`.
   - `modularOp_kms_identity : state F (A * modularOp F B) = state F (B * A)`.
   - `modularOp_preserves_causalWedge` for any symmetric idempotent `PeirceCut` commuting with `F.rho`.
4. **Exponential Flow & Umegaki Generator Derivative**:
   - Over any real Banach algebra, `expAdFlow H t X = exp((-t) • H) * X * exp(t • H)` forms a
     homomorphic 1-parameter automorphism group whose negative derivative at `t = 0` is `[H, X]`.
5. **OpenGauss T16 Witness**:
   - Explicit non-commuting `2 × 2` matrix units `matE01 * matE10 ≠ matE10 * matE01` and
     non-trivial modular scaling under `diag2Density41`.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteMatrixTomitaPolar

open Matrix
open scoped BigOperators

section HilbertSchmidt

variable {n : ℕ}

/-- Real Hilbert–Schmidt inner product `⟨X, Y⟩_HS = Tr(Xᵀ Y)` on `M_n(ℝ)`. -/
def hsInner (X Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (Xᵀ * Y).trace

/-- Symmetry of the real Hilbert–Schmidt inner product. -/
theorem hsInner_symm (X Y : Matrix (Fin n) (Fin n) ℝ) :
    hsInner X Y = hsInner Y X := by
  unfold hsInner
  rw [← Matrix.trace_transpose (Xᵀ * Y), Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Explicit coordinate sum-of-squares formula for `hsInner X X`. -/
theorem hsInner_self_eq_sum_sq (X : Matrix (Fin n) (Fin n) ℝ) :
    hsInner X X = ∑ i : Fin n, ∑ j : Fin n, (X j i) ^ 2 := by
  unfold hsInner
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, sq]

/-- Nonnegativity of `hsInner X X`. -/
theorem hsInner_self_nonneg (X : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ hsInner X X := by
  rw [hsInner_self_eq_sum_sq]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Strict positivity / faithfulness of `hsInner`. -/
theorem hsInner_self_eq_zero_iff (X : Matrix (Fin n) (Fin n) ℝ) :
    hsInner X X = 0 ↔ X = 0 := by
  rw [hsInner_self_eq_sum_sq]
  constructor
  · intro h
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
    ext j i
    have hi := h i (Finset.mem_univ i)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at hi
    exact sq_eq_zero_iff.mp (hi j (Finset.mem_univ j))
  · rintro rfl
    simp

/-- Scaling law for `hsInner`. -/
theorem hsInner_smul (c : ℝ) (X Y : Matrix (Fin n) (Fin n) ℝ) :
    hsInner (c • X) (c • Y) = c ^ 2 * hsInner X Y := by
  unfold hsInner
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq]

end HilbertSchmidt

section TomitaPolar

variable {n : ℕ}

/-- Symmetric invertible density square-root factor `r = ρ^{1/2}` on `M_n(ℝ)`. -/
structure PositiveRealDensityFactor (n : ℕ) where
  r : Matrix (Fin n) (Fin n) ℝ
  rInv : Matrix (Fin n) (Fin n) ℝ
  r_symm : rᵀ = r
  rInv_symm : rInvᵀ = rInv
  r_mul_rInv : r * rInv = 1
  rInv_mul_r : rInv * r = 1

namespace PositiveRealDensityFactor

/-- Density matrix `ρ = r * r`. -/
def rho (F : PositiveRealDensityFactor n) : Matrix (Fin n) (Fin n) ℝ :=
  F.r * F.r

/-- Inverse density matrix `ρ⁻¹ = r⁻¹ * r⁻¹`. -/
def rhoInv (F : PositiveRealDensityFactor n) : Matrix (Fin n) (Fin n) ℝ :=
  F.rInv * F.rInv

theorem rho_symm (F : PositiveRealDensityFactor n) : F.rhoᵀ = F.rho := by
  unfold rho
  rw [Matrix.transpose_mul, F.r_symm]

theorem rhoInv_symm (F : PositiveRealDensityFactor n) : F.rhoInvᵀ = F.rhoInv := by
  unfold rhoInv
  rw [Matrix.transpose_mul, F.rInv_symm]

theorem rho_mul_rhoInv (F : PositiveRealDensityFactor n) : F.rho * F.rhoInv = 1 := by
  unfold rho rhoInv
  calc
    F.r * F.r * (F.rInv * F.rInv)
        = F.r * (F.r * F.rInv) * F.rInv := by simp only [Matrix.mul_assoc]
    _ = F.r * 1 * F.rInv := by rw [F.r_mul_rInv]
    _ = F.r * F.rInv := by rw [Matrix.mul_one]
    _ = 1 := F.r_mul_rInv

theorem rhoInv_mul_rho (F : PositiveRealDensityFactor n) : F.rhoInv * F.rho = 1 := by
  unfold rho rhoInv
  calc
    F.rInv * F.rInv * (F.r * F.r)
        = F.rInv * (F.rInv * F.r) * F.r := by simp only [Matrix.mul_assoc]
    _ = F.rInv * 1 * F.r := by rw [F.rInv_mul_r]
    _ = F.rInv * F.r := by rw [Matrix.mul_one]
    _ = 1 := F.rInv_mul_r

end PositiveRealDensityFactor

/-- Expectation functional `ω(X) = Tr(ρ X)`. -/
def state (F : PositiveRealDensityFactor n) (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (F.rho * X).trace

/-- Cyclic vector identity `ω(X) = ⟨r, X r⟩_HS` with cyclic vector `Ω = r = ρ^{1/2}`. -/
theorem state_eq_hsInner_cyclic (F : PositiveRealDensityFactor n) (X : Matrix (Fin n) (Fin n) ℝ) :
    state F X = hsInner F.r (X * F.r) := by
  unfold state PositiveRealDensityFactor.rho hsInner
  rw [F.r_symm, Matrix.mul_assoc, Matrix.trace_mul_comm F.r (F.r * X)]
  simp only [Matrix.mul_assoc]

/-- Tomita operator `S_ρ(X) = r⁻¹ Xᵀ r` in GNS coordinates. -/
def tomitaOp (F : PositiveRealDensityFactor n) (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  F.rInv * Xᵀ * F.r

/-- Action on the dense cyclic subspace: `S_ρ(X r) = Xᵀ r`. -/
theorem tomitaOp_on_cyclic (F : PositiveRealDensityFactor n) (X : Matrix (Fin n) (Fin n) ℝ) :
    tomitaOp F (X * F.r) = Xᵀ * F.r := by
  unfold tomitaOp
  rw [Matrix.transpose_mul, F.r_symm]
  calc
    F.rInv * (F.r * Xᵀ) * F.r
        = (F.rInv * F.r) * Xᵀ * F.r := by simp only [Matrix.mul_assoc]
    _ = 1 * Xᵀ * F.r := by rw [F.rInv_mul_r]
    _ = Xᵀ * F.r := by rw [Matrix.one_mul]

theorem tomitaOp_add (F : PositiveRealDensityFactor n) (X Y : Matrix (Fin n) (Fin n) ℝ) :
    tomitaOp F (X + Y) = tomitaOp F X + tomitaOp F Y := by
  unfold tomitaOp
  rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem tomitaOp_smul (F : PositiveRealDensityFactor n) (c : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    tomitaOp F (c • X) = c • tomitaOp F X := by
  unfold tomitaOp
  rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- `S_ρ` is an involution: `S_ρ(S_ρ(X)) = X`. -/
theorem tomitaOp_involution (F : PositiveRealDensityFactor n) (X : Matrix (Fin n) (Fin n) ℝ) :
    tomitaOp F (tomitaOp F X) = X := by
  unfold tomitaOp
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    F.r_symm, F.rInv_symm]
  calc
    F.rInv * (F.r * (X * F.rInv)) * F.r
        = (F.rInv * F.r) * X * (F.rInv * F.r) := by simp only [Matrix.mul_assoc]
    _ = 1 * X * 1 := by rw [F.rInv_mul_r]
    _ = X := by simp

/-- Hilbert–Schmidt adjoint of `S_ρ`: `F_ρ(X) = r Xᵀ r⁻¹`. -/
def tomitaAdjOp (F : PositiveRealDensityFactor n) (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  F.r * Xᵀ * F.rInv

/-- Exact Hilbert–Schmidt adjointness `⟨X, S_ρ Y⟩_HS = ⟨Y, F_ρ X⟩_HS`. -/
theorem hsInner_tomitaOp_eq (F : PositiveRealDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    hsInner X (tomitaOp F Y) = hsInner Y (tomitaAdjOp F X) := by
  unfold hsInner tomitaOp tomitaAdjOp
  calc
    (Xᵀ * (F.rInv * Yᵀ * F.r)).trace
        = ((Xᵀ * F.rInv) * (Yᵀ * F.r)).trace := by simp only [Matrix.mul_assoc]
    _ = ((Yᵀ * F.r) * (Xᵀ * F.rInv)).trace := Matrix.trace_mul_comm _ _
    _ = (Yᵀ * (F.r * Xᵀ * F.rInv)).trace := by simp only [Matrix.mul_assoc]

/-- Modular operator `Δ_ρ(X) = ρ X ρ⁻¹`. -/
def modularOp (F : PositiveRealDensityFactor n) (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  F.rho * X * F.rhoInv

/-- Square root of modular operator `Δ_ρ^{1/2}(X) = r X r⁻¹`. -/
def modularSqrt (F : PositiveRealDensityFactor n) (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  F.r * X * F.rInv

/-- Fundamental Tomita–Takesaki identity `F_ρ ∘ S_ρ = Δ_ρ`. -/
theorem modularOp_eq_adj_comp_tomita (F : PositiveRealDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    tomitaAdjOp F (tomitaOp F X) = modularOp F X := by
  unfold tomitaAdjOp tomitaOp modularOp PositiveRealDensityFactor.rho PositiveRealDensityFactor.rhoInv
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    F.r_symm, F.rInv_symm]
  simp only [Matrix.mul_assoc]

/-- Square-root property `Δ_ρ^{1/2} ∘ Δ_ρ^{1/2} = Δ_ρ`. -/
theorem modularSqrt_comp_self (F : PositiveRealDensityFactor n) (X : Matrix (Fin n) (Fin n) ℝ) :
    modularSqrt F (modularSqrt F X) = modularOp F X := by
  unfold modularSqrt modularOp PositiveRealDensityFactor.rho PositiveRealDensityFactor.rhoInv
  simp only [Matrix.mul_assoc]

/-- Symmetry (self-adjointness) of `Δ_ρ` with respect to `hsInner`. -/
theorem modularOp_hsSelfAdjoint (F : PositiveRealDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    hsInner X (modularOp F Y) = hsInner (modularOp F X) Y := by
  unfold hsInner modularOp
  have hL :
      (Xᵀ * (F.rho * Y * F.rhoInv)).trace =
        (F.rhoInv * Xᵀ * F.rho * Y).trace := by
    calc
      (Xᵀ * (F.rho * Y * F.rhoInv)).trace
          = ((Xᵀ * F.rho * Y) * F.rhoInv).trace := by simp only [Matrix.mul_assoc]
      _ = (F.rhoInv * (Xᵀ * F.rho * Y)).trace := Matrix.trace_mul_comm _ _
      _ = (F.rhoInv * Xᵀ * F.rho * Y).trace := by simp only [Matrix.mul_assoc]
  have hR :
      ((F.rho * X * F.rhoInv)ᵀ * Y).trace =
        (F.rhoInv * Xᵀ * F.rho * Y).trace := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, F.rho_symm, F.rhoInv_symm]
    simp only [Matrix.mul_assoc]
  exact hL.trans hR.symm

/-- `⟨X, Δ_ρ X⟩_HS = ‖Δ_ρ^{1/2} X‖_HS²`. -/
theorem hsInner_modularOp_eq_hsInner_sqrt (F : PositiveRealDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    hsInner X (modularOp F X) = hsInner (modularSqrt F X) (modularSqrt F X) := by
  unfold hsInner modularOp modularSqrt PositiveRealDensityFactor.rho PositiveRealDensityFactor.rhoInv
  have htrans : (F.r * X * F.rInv)ᵀ = F.rInv * Xᵀ * F.r := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, F.r_symm, F.rInv_symm]
    exact (Matrix.mul_assoc F.rInv Xᵀ F.r).symm
  rw [htrans]
  calc
    (Xᵀ * (F.r * F.r * X * (F.rInv * F.rInv))).trace
        = ((Xᵀ * F.r * F.r * X * F.rInv) * F.rInv).trace := by simp only [Matrix.mul_assoc]
    _ = (F.rInv * (Xᵀ * F.r * F.r * X * F.rInv)).trace := Matrix.trace_mul_comm _ _
    _ = (F.rInv * Xᵀ * F.r * (F.r * X * F.rInv)).trace := by simp only [Matrix.mul_assoc]

/-- Positivity of `Δ_ρ` in `hsInner`. -/
theorem modularOp_hsPos (F : PositiveRealDensityFactor n) (X : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ hsInner X (modularOp F X) := by
  rw [hsInner_modularOp_eq_hsInner_sqrt]
  exact hsInner_self_nonneg _

/-- Strict positivity of `Δ_ρ`: `⟨X, Δ_ρ X⟩_HS = 0 ↔ X = 0`. -/
theorem modularOp_hsPos_eq_zero_iff (F : PositiveRealDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    hsInner X (modularOp F X) = 0 ↔ X = 0 := by
  rw [hsInner_modularOp_eq_hsInner_sqrt, hsInner_self_eq_zero_iff]
  constructor
  · intro h
    calc
      X = 1 * X * 1 := by simp
      _ = (F.rInv * F.r) * X * (F.rInv * F.r) := by rw [F.rInv_mul_r]
      _ = F.rInv * (modularSqrt F X) * F.r := by
            unfold modularSqrt
            simp only [Matrix.mul_assoc]
      _ = F.rInv * 0 * F.r := by rw [h]
      _ = 0 := by simp
  · rintro rfl
    unfold modularSqrt
    simp

/-- `Δ_ρ` fixes the cyclic vector `r`. -/
theorem modularOp_fixes_cyclic (F : PositiveRealDensityFactor n) :
    modularOp F F.r = F.r := by
  unfold modularOp PositiveRealDensityFactor.rho PositiveRealDensityFactor.rhoInv
  calc
    F.r * F.r * F.r * (F.rInv * F.rInv)
        = F.r * F.r * (F.r * F.rInv) * F.rInv := by simp only [Matrix.mul_assoc]
    _ = F.r * F.r * 1 * F.rInv := by rw [F.r_mul_rInv]
    _ = F.r * (F.r * F.rInv) := by simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = F.r := by rw [F.r_mul_rInv, Matrix.mul_one]

/-- Modular conjugation `J(X) = Xᵀ` on real matrices. -/
def modularConj (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Xᵀ

/-- `J² = id`. -/
theorem modularConj_involution (X : Matrix (Fin n) (Fin n) ℝ) :
    modularConj (modularConj X) = X :=
  Matrix.transpose_transpose X

/-- `J` is an `hsInner` isometry. -/
theorem modularConj_isometry (X Y : Matrix (Fin n) (Fin n) ℝ) :
    hsInner (modularConj X) (modularConj Y) = hsInner X Y := by
  unfold modularConj hsInner
  rw [Matrix.transpose_transpose, ← Matrix.trace_transpose (X * Yᵀ),
    Matrix.transpose_mul, Matrix.transpose_transpose]
  exact Matrix.trace_mul_comm Y Xᵀ

/-- Exact finite-matrix Tomita polar decomposition: `S_ρ = J ∘ Δ_ρ^{1/2}`. -/
theorem tomita_polar_decomposition (F : PositiveRealDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    tomitaOp F X = modularConj (modularSqrt F X) := by
  unfold tomitaOp modularConj modularSqrt
  rw [Matrix.transpose_mul, Matrix.transpose_mul, F.r_symm, F.rInv_symm]
  exact Matrix.mul_assoc F.rInv Xᵀ F.r

/-- Tomita inversion law: `J Δ_ρ J = Δ_ρ⁻¹`. -/
theorem modularConj_modularOp_conj (F : PositiveRealDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    modularConj (modularOp F (modularConj X)) = F.rhoInv * X * F.rho := by
  unfold modularConj modularOp
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    F.rho_symm, F.rhoInv_symm]
  exact (Matrix.mul_assoc F.rhoInv X F.rho).symm

end TomitaPolar

section CommutantKMSAndWedge

variable {n : ℕ}

/-- Left multiplication representation `L_A(X) = A * X`. -/
def leftMul (A X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := A * X

/-- Right multiplication commutant representation `R_B(X) = X * B`. -/
def rightMul (B X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := X * B

/-- Left and right multiplication commute identically. -/
theorem leftMul_comm_rightMul (A B X : Matrix (Fin n) (Fin n) ℝ) :
    leftMul A (rightMul B X) = rightMul B (leftMul A X) := by
  unfold leftMul rightMul
  exact (Matrix.mul_assoc A X B).symm

/-- Tomita commutant theorem: `J L_A J = R_{Aᵀ}`. -/
theorem modularConj_leftMul_conj (A X : Matrix (Fin n) (Fin n) ℝ) :
    modularConj (leftMul A (modularConj X)) = rightMul Aᵀ X := by
  unfold modularConj leftMul rightMul
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Algebraic KMS boundary condition: `ω(A Δ_ρ(B)) = ω(B A)`. -/
theorem modularOp_kms_identity (F : PositiveRealDensityFactor n)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    state F (A * modularOp F B) = state F (B * A) := by
  unfold state modularOp
  calc
    (F.rho * (A * (F.rho * B * F.rhoInv))).trace
        = ((F.rho * A * F.rho * B) * F.rhoInv).trace := by simp only [Matrix.mul_assoc]
    _ = (F.rhoInv * (F.rho * A * F.rho * B)).trace := Matrix.trace_mul_comm _ _
    _ = ((F.rhoInv * F.rho) * (A * (F.rho * B))).trace := by simp only [Matrix.mul_assoc]
    _ = (A * (F.rho * B)).trace := by rw [F.rhoInv_mul_rho, Matrix.one_mul]
    _ = (F.rho * (B * A)).trace := by
          rw [Matrix.trace_mul_comm A (F.rho * B), Matrix.mul_assoc]

/-- Modular invariance of the state: `ω(Δ_ρ(A)) = ω(A)`. -/
theorem modularOp_state_invariant (F : PositiveRealDensityFactor n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    state F (modularOp F A) = state F A := by
  simpa using modularOp_kms_identity F 1 A

/-- Symmetric Peirce cut projection defining a finite causal wedge `P 𝒜 P`. -/
structure PeirceCut (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) ℝ
  idempotent : mat * mat = mat
  symm : matᵀ = mat

/-- Concrete diagonal Peirce cut `E₀₀` on `M₂(ℝ)`. -/
def diag2PeirceE00 : PeirceCut 2 where
  mat := !![1, 0; 0, 0]
  idempotent := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  symm := by ext i j; fin_cases i <;> fin_cases j <;> simp

instance : Inhabited (PeirceCut 2) := ⟨diag2PeirceE00⟩

/-- Causal wedge subalgebra `P 𝒜 P = { P Y P | Y ∈ M_n(ℝ) }`. -/
def causalWedge (P : PeirceCut n) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  { X | ∃ Y : Matrix (Fin n) (Fin n) ℝ, X = P.mat * Y * P.mat }

/-- Membership characterization for `causalWedge P`. -/
theorem mem_causalWedge_iff (P : PeirceCut n) (X : Matrix (Fin n) (Fin n) ℝ) :
    X ∈ causalWedge P ↔ P.mat * X * P.mat = X := by
  constructor
  · rintro ⟨Y, rfl⟩
    calc
      P.mat * (P.mat * Y * P.mat) * P.mat
          = (P.mat * P.mat) * Y * (P.mat * P.mat) := by simp only [Matrix.mul_assoc]
      _ = P.mat * Y * P.mat := by rw [P.idempotent]
  · intro h
    exact ⟨X, h.symm⟩

/-- When `P` commutes with `ρ`, the modular operator preserves the causal wedge `P 𝒜 P`. -/
theorem modularOp_preserves_causalWedge (F : PositiveRealDensityFactor n) (P : PeirceCut n)
    (hcomm : Commute F.rho P.mat) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ causalWedge P) :
    modularOp F X ∈ causalWedge P := by
  have hcommInv : Commute F.rhoInv P.mat := by
    calc
      F.rhoInv * P.mat = F.rhoInv * (P.mat * (F.rho * F.rhoInv)) := by
        rw [F.rho_mul_rhoInv, Matrix.mul_one]
      _ = F.rhoInv * ((P.mat * F.rho) * F.rhoInv) := by simp only [Matrix.mul_assoc]
      _ = F.rhoInv * ((F.rho * P.mat) * F.rhoInv) := by rw [hcomm.eq]
      _ = (F.rhoInv * F.rho) * (P.mat * F.rhoInv) := by simp only [Matrix.mul_assoc]
      _ = P.mat * F.rhoInv := by rw [F.rhoInv_mul_rho, Matrix.one_mul]
  rcases hX with ⟨Y, rfl⟩
  refine ⟨modularOp F Y, ?_⟩
  unfold modularOp
  calc
    F.rho * (P.mat * Y * P.mat) * F.rhoInv
        = (F.rho * P.mat) * Y * (P.mat * F.rhoInv) := by simp only [Matrix.mul_assoc]
    _ = (P.mat * F.rho) * Y * (F.rhoInv * P.mat) := by rw [hcomm.eq, hcommInv.eq]
    _ = P.mat * (F.rho * Y * F.rhoInv) * P.mat := by simp only [Matrix.mul_assoc]

end CommutantKMSAndWedge

section BanachExpModularFlow

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Exponential adjoint modular flow `σ_t^H(X) = exp(-t H) * X * exp(t H)` in a Banach algebra. -/
def expAdFlow (H : A) (t : ℝ) (X : A) : A :=
  NormedSpace.exp ((-t) • H) * X * NormedSpace.exp (t • H)

omit [CompleteSpace A] in
@[simp]
theorem expAdFlow_zero (H X : A) : expAdFlow H 0 X = X := by
  unfold expAdFlow
  simp

/-- Additive group law for `expAdFlow`. -/
theorem expAdFlow_add (H : A) (s t : ℝ) (X : A) :
    expAdFlow H (s + t) X = expAdFlow H s (expAdFlow H t X) := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have h1 : Commute ((-s) • H) ((-t) • H) := ((Commute.refl H).smul_left _).smul_right _
  have h2 : Commute (t • H) (s • H) := ((Commute.refl H).smul_left _).smul_right _
  unfold expAdFlow
  rw [show -(s + t) = -s + -t by ring, add_smul, NormedSpace.exp_add_of_commute h1]
  rw [add_smul, add_comm (s • H) (t • H), NormedSpace.exp_add_of_commute h2]
  simp only [mul_assoc]

/-- Multiplicative homomorphism law for `expAdFlow`. -/
theorem expAdFlow_mul (H : A) (t : ℝ) (X Y : A) :
    expAdFlow H t (X * Y) = expAdFlow H t X * expAdFlow H t Y := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hcomm : Commute (t • H) ((-t) • H) := ((Commute.refl H).smul_left _).smul_right _
  have hinv : NormedSpace.exp (t • H) * NormedSpace.exp ((-t) • H) = 1 := by
    rw [← NormedSpace.exp_add_of_commute hcomm, ← add_smul, add_neg_cancel, zero_smul,
      NormedSpace.exp_zero]
  unfold expAdFlow
  calc
    NormedSpace.exp ((-t) • H) * (X * Y) * NormedSpace.exp (t • H)
        = NormedSpace.exp ((-t) • H) * X * 1 * Y * NormedSpace.exp (t • H) := by
            simp only [mul_assoc, mul_one]
    _ = NormedSpace.exp ((-t) • H) * X * (NormedSpace.exp (t • H) * NormedSpace.exp ((-t) • H)) *
          Y * NormedSpace.exp (t • H) := by rw [hinv]
    _ = (NormedSpace.exp ((-t) • H) * X * NormedSpace.exp (t • H)) *
          (NormedSpace.exp ((-t) • H) * Y * NormedSpace.exp (t • H)) := by
          simp only [mul_assoc]

/-- Derivative of `t ↦ expAdFlow H t X` at `t = 0` equals `-[H, X]`. -/
theorem hasDerivAt_expAdFlow_zero (H X : A) :
    HasDerivAt (fun t : ℝ => expAdFlow H t X) (-(H * X - X * H)) 0 := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have h_pos :
      HasDerivAt (fun u : ℝ => NormedSpace.exp (u • H)) (H * NormedSpace.exp ((0 : ℝ) • H)) 0 :=
    (hasStrictDerivAt_exp_smul_const' H 0).hasDerivAt
  have h_pos_simpl : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • H)) H 0 := by
    simpa using h_pos
  have h_neg_base :
      HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (-H)))
        ((-H) * NormedSpace.exp ((0 : ℝ) • (-H))) 0 :=
    (hasStrictDerivAt_exp_smul_const' (-H) 0).hasDerivAt
  have h_neg_simpl : HasDerivAt (fun t : ℝ => NormedSpace.exp ((-t) • H)) (-H) 0 := by
    have hfun : (fun t : ℝ => NormedSpace.exp ((-t) • H)) =
        (fun t : ℝ => NormedSpace.exp (t • (-H))) := by
      ext t
      rw [neg_smul, smul_neg]
    rw [hfun]
    simpa using h_neg_base
  have hprod := (h_neg_simpl.mul_const X).mul h_pos_simpl
  have hval :
      (-H * X) * NormedSpace.exp ((0 : ℝ) • H) +
        (NormedSpace.exp ((-0 : ℝ) • H) * X) * H = -(H * X - X * H) := by
    simp only [zero_smul, neg_zero, NormedSpace.exp_zero, mul_one, one_mul]
    noncomm_ring
  rw [hval] at hprod
  exact hprod

/-- Umegaki modular Hamiltonian commutator formula: `-(d/dt)|_{t=0} expAdFlow H t X = [H, X]`. -/
theorem neg_deriv_expAdFlow_zero (H X : A) :
    -(deriv (fun t : ℝ => expAdFlow H t X) 0) = H * X - X * H := by
  rw [(hasDerivAt_expAdFlow_zero H X).deriv, neg_neg]

end BanachExpModularFlow

section NonCommWitness

/-- Concrete `2 × 2` positive density square-root factor `diag(2, 1)`, giving `ρ = diag(4, 1)`. -/
def diag2Density41 : PositiveRealDensityFactor 2 where
  r := !![2, 0; 0, 1]
  rInv := !![1 / 2, 0; 0, 1]
  r_symm := by ext i j; fin_cases i <;> fin_cases j <;> simp
  rInv_symm := by ext i j; fin_cases i <;> fin_cases j <;> simp
  r_mul_rInv := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  rInv_mul_r := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

def matE01 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def matE10 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- OpenGauss T16 explicit non-commutativity witness on `M₂(ℝ)`. -/
theorem matE01_matE10_noncomm : matE01 * matE10 ≠ matE10 * matE01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [matE01, matE10, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Non-trivial modular operator eigen-action `Δ(E₀₁) = 4 • E₀₁`. -/
theorem modularOp_diag2Density41_matE01 :
    modularOp diag2Density41 matE01 = (4 : ℝ) • matE01 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularOp, diag2Density41, PositiveRealDensityFactor.rho,
      PositiveRealDensityFactor.rhoInv, matE01, Matrix.mul_apply, Fin.sum_univ_two]

/-- Witness that `modularOp` is strictly non-identity on non-commuting matrix units. -/
theorem modularOp_diag2Density41_nontrivial :
    modularOp diag2Density41 matE01 ≠ matE01 := by
  rw [modularOp_diag2Density41_matE01]
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [matE01] at h01

end NonCommWitness

end InfoGeometry.Canonical.FiniteMatrixTomitaPolar
