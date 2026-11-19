/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Core
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Clifford8BdGHorizon
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Supertwistor16AndRealBloch
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# KMS Bath Coupling, Finite-Matrix Relaxation, & Spin Information Geometry

This module proves several distinct finite-dimensional statements:
1. Inter-sector sandwich vanishing for the listed finite matrix jump operators.
2. The real linear map `partialTraceKKT : M₈(ℝ) →ₗ[ℝ] M₂(ℝ)` preserves trace and
   positive semidefiniteness and has the stated Gibbs marginal. Complete positivity is
   not established here, so the map is not called CPTP.
3. A two-rate generator and closed-form propagator on the full carrier `M₂(ℝ)` with
   proved matrix-valued ODE, composition, trace preservation, and Gibbs relaxation under
   the stated hypotheses. Complete positivity, positivity preservation of the propagator,
   and a `CStarAlgebra` quantum Markov semigroup structure are not established here.
4. The spin-cumulant, Legendre, Kubo-Mori-bound, boundary-limit, and Lyapunov results are
   stated on `EuclideanSpace ℝ (Fin d)` and are not matrix Umegaki relative-entropy results.
5. A concrete noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceBiSandwich

open Matrix Filter Set
open scoped RealInnerProductSpace

/-! ### Part I: Inter-Sector Kraus Refeeding Vanishing -/

/-- Inter-sector Kraus jump operators map from `Q₊` into `P₀`, so the inter-sector refeeding
    sandwich `Lᵀ (Q₊ X Q₊) L` vanishes identically for all jump operators at `K₈` and `Ω₈`
    and any matrix `X ∈ M₈(ℤ)`. -/
theorem inter_sector_kraus_refeeding_vanishing_Z (X : Matrix (Fin 8) (Fin 8) ℤ) :
    let Qp := Qplus P8_Z A8_Z A8_Z
    -- K₈ polarization basis
    (twoL_up_plus K8_Z).transpose * (Qp * X * Qp) * twoL_up_plus K8_Z = 0 ∧
    (twoL_dn_plus K8_Z).transpose * (Qp * X * Qp) * twoL_dn_plus K8_Z = 0 ∧
    (twoL_up_minus K8_Z).transpose * (Qp * X * Qp) * twoL_up_minus K8_Z = 0 ∧
    (twoL_dn_minus K8_Z).transpose * (Qp * X * Qp) * twoL_dn_minus K8_Z = 0 ∧
    -- Ω₈ polarization basis
    (twoL_up_plus Omega8_Z).transpose * (Qp * X * Qp) * twoL_up_plus Omega8_Z = 0 ∧
    (twoL_dn_plus Omega8_Z).transpose * (Qp * X * Qp) * twoL_dn_plus Omega8_Z = 0 ∧
    (twoL_up_minus Omega8_Z).transpose * (Qp * X * Qp) * twoL_up_minus Omega8_Z = 0 ∧
    (twoL_dn_minus Omega8_Z).transpose * (Qp * X * Qp) * twoL_dn_minus Omega8_Z = 0 := by
  intro Qp
  have hK_up_p : Qp * twoL_up_plus K8_Z = 0 := by decide
  have hK_dn_p : Qp * twoL_dn_plus K8_Z = 0 := by decide
  have hK_up_m : Qp * twoL_up_minus K8_Z = 0 := by decide
  have hK_dn_m : Qp * twoL_dn_minus K8_Z = 0 := by decide
  have hO_up_p : Qp * twoL_up_plus Omega8_Z = 0 := by decide
  have hO_dn_p : Qp * twoL_dn_plus Omega8_Z = 0 := by decide
  have hO_up_m : Qp * twoL_up_minus Omega8_Z = 0 := by decide
  have hO_dn_m : Qp * twoL_dn_minus Omega8_Z = 0 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (twoL_up_plus K8_Z).transpose * (Qp * X * Qp) * twoL_up_plus K8_Z
        = (twoL_up_plus K8_Z).transpose * (Qp * X) * (Qp * twoL_up_plus K8_Z) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hK_up_p, mul_zero]
  · calc (twoL_dn_plus K8_Z).transpose * (Qp * X * Qp) * twoL_dn_plus K8_Z
        = (twoL_dn_plus K8_Z).transpose * (Qp * X) * (Qp * twoL_dn_plus K8_Z) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hK_dn_p, mul_zero]
  · calc (twoL_up_minus K8_Z).transpose * (Qp * X * Qp) * twoL_up_minus K8_Z
        = (twoL_up_minus K8_Z).transpose * (Qp * X) * (Qp * twoL_up_minus K8_Z) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hK_up_m, mul_zero]
  · calc (twoL_dn_minus K8_Z).transpose * (Qp * X * Qp) * twoL_dn_minus K8_Z
        = (twoL_dn_minus K8_Z).transpose * (Qp * X) * (Qp * twoL_dn_minus K8_Z) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hK_dn_m, mul_zero]
  · calc (twoL_up_plus Omega8_Z).transpose * (Qp * X * Qp) * twoL_up_plus Omega8_Z
        = (twoL_up_plus Omega8_Z).transpose * (Qp * X) * (Qp * twoL_up_plus Omega8_Z) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hO_up_p, mul_zero]
  · calc (twoL_dn_plus Omega8_Z).transpose * (Qp * X * Qp) * twoL_dn_plus Omega8_Z
        = (twoL_dn_plus Omega8_Z).transpose * (Qp * X) * (Qp * twoL_dn_plus Omega8_Z) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hO_dn_p, mul_zero]
  · calc (twoL_up_minus Omega8_Z).transpose * (Qp * X * Qp) * twoL_up_minus Omega8_Z
        = (twoL_up_minus Omega8_Z).transpose * (Qp * X) * (Qp * twoL_up_minus Omega8_Z) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hO_up_m, mul_zero]
  · calc (twoL_dn_minus Omega8_Z).transpose * (Qp * X * Qp) * twoL_dn_minus Omega8_Z
        = (twoL_dn_minus Omega8_Z).transpose * (Qp * X) * (Qp * twoL_dn_minus Omega8_Z) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hO_dn_m, mul_zero]

/-- Real version: inter-sector Kraus refeeding vanishing for arbitrary real observables `X ∈ M₈(ℝ)`. -/
theorem inter_sector_kraus_refeeding_vanishing_R (X : Matrix (Fin 8) (Fin 8) ℝ)
    (S_pol : Matrix (Fin 8) (Fin 8) ℤ) (hS : S_pol = K8_Z ∨ S_pol = Omega8_Z) :
    let Qp := toMat8R (Qplus P8_Z A8_Z A8_Z)
    let L1 := toMat8R (twoL_up_plus S_pol)
    let L2 := toMat8R (twoL_dn_plus S_pol)
    let L3 := toMat8R (twoL_up_minus S_pol)
    let L4 := toMat8R (twoL_dn_minus S_pol)
    L1.transpose * (Qp * X * Qp) * L1 = 0 ∧
    L2.transpose * (Qp * X * Qp) * L2 = 0 ∧
    L3.transpose * (Qp * X * Qp) * L3 = 0 ∧
    L4.transpose * (Qp * X * Qp) * L4 = 0 := by
  intro Qp L1 L2 L3 L4
  rcases hS with rfl | rfl
  · have h1 : Qp * L1 = 0 := by
      dsimp [Qp, L1]; rw [← map_mul, show (Qplus P8_Z A8_Z A8_Z) * twoL_up_plus K8_Z = 0 by decide, map_zero]
    have h2 : Qp * L2 = 0 := by
      dsimp [Qp, L2]; rw [← map_mul, show (Qplus P8_Z A8_Z A8_Z) * twoL_dn_plus K8_Z = 0 by decide, map_zero]
    have h3 : Qp * L3 = 0 := by
      dsimp [Qp, L3]; rw [← map_mul, show (Qplus P8_Z A8_Z A8_Z) * twoL_up_minus K8_Z = 0 by decide, map_zero]
    have h4 : Qp * L4 = 0 := by
      dsimp [Qp, L4]; rw [← map_mul, show (Qplus P8_Z A8_Z A8_Z) * twoL_dn_minus K8_Z = 0 by decide, map_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc L1.transpose * (Qp * X * Qp) * L1 = L1.transpose * (Qp * X) * (Qp * L1) := by simp only [mul_assoc]
        _ = 0 := by rw [h1, mul_zero]
    · calc L2.transpose * (Qp * X * Qp) * L2 = L2.transpose * (Qp * X) * (Qp * L2) := by simp only [mul_assoc]
        _ = 0 := by rw [h2, mul_zero]
    · calc L3.transpose * (Qp * X * Qp) * L3 = L3.transpose * (Qp * X) * (Qp * L3) := by simp only [mul_assoc]
        _ = 0 := by rw [h3, mul_zero]
    · calc L4.transpose * (Qp * X * Qp) * L4 = L4.transpose * (Qp * X) * (Qp * L4) := by simp only [mul_assoc]
        _ = 0 := by rw [h4, mul_zero]
  · have h1 : Qp * L1 = 0 := by
      dsimp [Qp, L1]; rw [← map_mul, show (Qplus P8_Z A8_Z A8_Z) * twoL_up_plus Omega8_Z = 0 by decide, map_zero]
    have h2 : Qp * L2 = 0 := by
      dsimp [Qp, L2]; rw [← map_mul, show (Qplus P8_Z A8_Z A8_Z) * twoL_dn_plus Omega8_Z = 0 by decide, map_zero]
    have h3 : Qp * L3 = 0 := by
      dsimp [Qp, L3]; rw [← map_mul, show (Qplus P8_Z A8_Z A8_Z) * twoL_up_minus Omega8_Z = 0 by decide, map_zero]
    have h4 : Qp * L4 = 0 := by
      dsimp [Qp, L4]; rw [← map_mul, show (Qplus P8_Z A8_Z A8_Z) * twoL_dn_minus Omega8_Z = 0 by decide, map_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc L1.transpose * (Qp * X * Qp) * L1 = L1.transpose * (Qp * X) * (Qp * L1) := by simp only [mul_assoc]
        _ = 0 := by rw [h1, mul_zero]
    · calc L2.transpose * (Qp * X * Qp) * L2 = L2.transpose * (Qp * X) * (Qp * L2) := by simp only [mul_assoc]
        _ = 0 := by rw [h2, mul_zero]
    · calc L3.transpose * (Qp * X * Qp) * L3 = L3.transpose * (Qp * X) * (Qp * L3) := by simp only [mul_assoc]
        _ = 0 := by rw [h3, mul_zero]
    · calc L4.transpose * (Qp * X * Qp) * L4 = L4.transpose * (Qp * X) * (Qp * L4) := by simp only [mul_assoc]
        _ = 0 := by rw [h4, mul_zero]

/-! ### Part II: Trace- and PSD-Preserving Partial Trace `partialTraceKKT` -/

/-- Componentwise embedding from integer matrices to real matrices. -/
def toMatR {m n : Type*} (M : Matrix m n ℤ) : Matrix m n ℝ :=
  fun i j => (M i j : ℝ)

@[simp]
lemma toMatR_apply {m n : Type*} (M : Matrix m n ℤ) (i : m) (j : n) :
    toMatR M i j = (M i j : ℝ) := rfl

lemma toMatR_mul {m n k : Type*} [Fintype k] (A : Matrix m k ℤ) (B : Matrix k n ℤ) :
    toMatR (A * B) = toMatR A * toMatR B := by
  ext i j
  dsimp [toMatR]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  push_cast
  rfl

lemma toMatR_add {m n : Type*} (A B : Matrix m n ℤ) :
    toMatR (A + B) = toMatR A + toMatR B := by
  ext i j
  dsimp [toMatR]
  simp only [Int.cast_add]

lemma toMatR_transpose {m n : Type*} (A : Matrix m n ℤ) :
    toMatR A.transpose = (toMatR A).transpose := by
  ext i j
  rfl

lemma toMatR_one {n : Type*} [DecidableEq n] [Fintype n] :
    toMatR (1 : Matrix n n ℤ) = (1 : Matrix n n ℝ) := by
  ext i j
  dsimp [toMatR]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

/-- Integer Kraus blocks for the 4 KKT sectors embedding into `M₈(ℤ)`. -/
def V_KKT_Z (a : Fin 4) : Matrix (Fin 8) (Fin 2) ℤ :=
  Matrix.of fun i j => if i.val = 2 * a.val + j.val then 1 else 0

lemma kkt_kraus_isometric_Z (a : Fin 4) : (V_KKT_Z a).transpose * (V_KKT_Z a) = 1 := by
  fin_cases a <;> decide

lemma kkt_kraus_completeness_Z :
    V_KKT_Z 0 * (V_KKT_Z 0).transpose +
    V_KKT_Z 1 * (V_KKT_Z 1).transpose +
    V_KKT_Z 2 * (V_KKT_Z 2).transpose +
    V_KKT_Z 3 * (V_KKT_Z 3).transpose = 1 := by
  decide

/-- Four isometric injection blocks `V_a : M_{8×2}(ℝ)` embedding the 4 KKT sectors into `M₈(ℝ)`. -/
def V_KKT (a : Fin 4) : Matrix (Fin 8) (Fin 2) ℝ :=
  toMatR (V_KKT_Z a)

/-- Kraus completeness and isometry of the 4 KKT sector blocks. -/
theorem kkt_kraus_isometric_and_completeness :
    (∀ a : Fin 4, (V_KKT a).transpose * (V_KKT a) = 1) ∧
    (V_KKT 0 * (V_KKT 0).transpose +
     V_KKT 1 * (V_KKT 1).transpose +
     V_KKT 2 * (V_KKT 2).transpose +
     V_KKT 3 * (V_KKT 3).transpose = 1) := by
  constructor
  · intro a
    dsimp [V_KKT]
    rw [← toMatR_transpose, ← toMatR_mul, kkt_kraus_isometric_Z a, toMatR_one]
  · dsimp [V_KKT]
    rw [← toMatR_transpose, ← toMatR_transpose, ← toMatR_transpose, ← toMatR_transpose,
        ← toMatR_mul, ← toMatR_mul, ← toMatR_mul, ← toMatR_mul,
        ← toMatR_add, ← toMatR_add, ← toMatR_add,
        kkt_kraus_completeness_Z, toMatR_one]

/-- The finite partial-trace map `M₈(ℝ) →ₗ[ℝ] M₂(ℝ)`. Trace and positive-semidefinite preservation are proved below; complete positivity (arbitrary finite ancilla amplification) is established in `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.KMSCompletePositivityAndKrausSemigroup`. -/
noncomputable def partialTraceKKT : Matrix (Fin 8) (Fin 8) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun M := (V_KKT 0).transpose * M * (V_KKT 0) +
             (V_KKT 1).transpose * M * (V_KKT 1) +
             (V_KKT 2).transpose * M * (V_KKT 2) +
             (V_KKT 3).transpose * M * (V_KKT 3)
  map_add' M N := by
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c M := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply]

/-- Integer-coefficient formula for the finite partial-trace map. -/
def partialTraceKKT_Z (M : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  (V_KKT_Z 0).transpose * M * (V_KKT_Z 0) +
  (V_KKT_Z 1).transpose * M * (V_KKT_Z 1) +
  (V_KKT_Z 2).transpose * M * (V_KKT_Z 2) +
  (V_KKT_Z 3).transpose * M * (V_KKT_Z 3)

lemma partialTraceKKT_toMatR (M : Matrix (Fin 8) (Fin 8) ℤ) :
    partialTraceKKT (toMatR M) = toMatR (partialTraceKKT_Z M) := by
  show (V_KKT 0).transpose * toMatR M * (V_KKT 0) +
       (V_KKT 1).transpose * toMatR M * (V_KKT 1) +
       (V_KKT 2).transpose * toMatR M * (V_KKT 2) +
       (V_KKT 3).transpose * toMatR M * (V_KKT 3) =
       toMatR (partialTraceKKT_Z M)
  dsimp [partialTraceKKT_Z, V_KKT]
  rw [toMatR_add, toMatR_add, toMatR_add,
      toMatR_mul, toMatR_mul, toMatR_transpose,
      toMatR_mul, toMatR_mul, toMatR_transpose,
      toMatR_mul, toMatR_mul, toMatR_transpose,
      toMatR_mul, toMatR_mul, toMatR_transpose]

/-- `partialTraceKKT` preserves total trace: `Tr(Tr_KKT(M)) = Tr(M)`. -/
theorem partialTraceKKT_preserves_trace (M : Matrix (Fin 8) (Fin 8) ℝ) :
    (partialTraceKKT M).trace = M.trace := by
  show ((V_KKT 0).transpose * M * (V_KKT 0) +
        (V_KKT 1).transpose * M * (V_KKT 1) +
        (V_KKT 2).transpose * M * (V_KKT 2) +
        (V_KKT 3).transpose * M * (V_KKT 3)).trace = M.trace
  rw [trace_add, trace_add, trace_add,
      trace_mul_comm ((V_KKT 0).transpose * M) (V_KKT 0),
      trace_mul_comm ((V_KKT 1).transpose * M) (V_KKT 1),
      trace_mul_comm ((V_KKT 2).transpose * M) (V_KKT 2),
      trace_mul_comm ((V_KKT 3).transpose * M) (V_KKT 3)]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← trace_add, ← trace_add, ← trace_add,
      ← add_mul, ← add_mul, ← add_mul]
  have h_comp := kkt_kraus_isometric_and_completeness.2
  rw [h_comp, one_mul]

/-- `partialTraceKKT` preserves positive semidefiniteness: `M ≥ 0 → Tr_KKT(M) ≥ 0`. -/
theorem partialTraceKKT_preserves_posSemidef {M : Matrix (Fin 8) (Fin 8) ℝ} (hM : M.PosSemidef) :
    (partialTraceKKT M).PosSemidef := by
  dsimp [partialTraceKKT]
  have h0 : ((V_KKT 0).transpose * M * V_KKT 0).PosSemidef := by
    have hconj : (V_KKT 0).transpose = (V_KKT 0)ᴴ := by
      rw [conjTranspose_eq_transpose_of_trivial]
    rw [hconj]
    exact hM.conjTranspose_mul_mul_same (V_KKT 0)
  have h1 : ((V_KKT 1).transpose * M * V_KKT 1).PosSemidef := by
    have hconj : (V_KKT 1).transpose = (V_KKT 1)ᴴ := by
      rw [conjTranspose_eq_transpose_of_trivial]
    rw [hconj]
    exact hM.conjTranspose_mul_mul_same (V_KKT 1)
  have h2 : ((V_KKT 2).transpose * M * V_KKT 2).PosSemidef := by
    have hconj : (V_KKT 2).transpose = (V_KKT 2)ᴴ := by
      rw [conjTranspose_eq_transpose_of_trivial]
    rw [hconj]
    exact hM.conjTranspose_mul_mul_same (V_KKT 2)
  have h3 : ((V_KKT 3).transpose * M * V_KKT 3).PosSemidef := by
    have hconj : (V_KKT 3).transpose = (V_KKT 3)ᴴ := by
      rw [conjTranspose_eq_transpose_of_trivial]
    rw [hconj]
    exact hM.conjTranspose_mul_mul_same (V_KKT 3)
  exact ((h0.add h1).add h2).add h3

lemma toMat8R_eq_toMatR (M : Matrix (Fin 8) (Fin 8) ℤ) :
    toMat8R M = toMatR M := by
  ext i j
  rfl

/-- Marginal of `ρ_Gibbs8(χ)` under `partialTraceKKT` is the exact diagonal qubit state
    `diag [cos²(χ), sin²(χ)]` with unit trace and positive semidefiniteness. -/
theorem partialTraceKKT_rhoGibbs8 (χ : ℝ) :
    partialTraceKKT (rho_Gibbs8 χ) =
      Matrix.diagonal ![Real.cos χ ^ 2, Real.sin χ ^ 2] ∧
    (partialTraceKKT (rho_Gibbs8 χ)).trace = 1 ∧
    (partialTraceKKT (rho_Gibbs8 χ)).PosSemidef := by
  let E00_Z : Matrix (Fin 8) (Fin 8) ℤ := Matrix.diagonal ![1, 0, 0, 0, 0, 0, 0, 0]
  let E11_Z : Matrix (Fin 8) (Fin 8) ℤ := Matrix.diagonal ![0, 1, 0, 0, 0, 0, 0, 0]
  have h_rho := (polarized_fermi_sea_unit_trace_state χ).2.2.2.1
  have hE00 : partialTraceKKT (toMat8R E00_Z) = Matrix.diagonal ![1, 0] := by
    rw [toMat8R_eq_toMatR, partialTraceKKT_toMatR]
    have : partialTraceKKT_Z E00_Z = Matrix.diagonal ![1, 0] := by decide
    rw [this]
    ext i j
    dsimp [toMatR]
    fin_cases i <;> fin_cases j <;> simp
  have hE11 : partialTraceKKT (toMat8R E11_Z) = Matrix.diagonal ![0, 1] := by
    rw [toMat8R_eq_toMatR, partialTraceKKT_toMatR]
    have : partialTraceKKT_Z E11_Z = Matrix.diagonal ![0, 1] := by decide
    rw [this]
    ext i j
    dsimp [toMatR]
    fin_cases i <;> fin_cases j <;> simp
  have h_pt : partialTraceKKT (rho_Gibbs8 χ) =
      Matrix.diagonal ![Real.cos χ ^ 2, Real.sin χ ^ 2] := by
    rw [h_rho, map_add, map_smul, map_smul, hE00, hE11]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  refine ⟨h_pt, ?_, ?_⟩
  · rw [h_pt, trace_diagonal, Fin.sum_univ_two]
    simp only [cons_val_zero, cons_val_one, Real.cos_sq_add_sin_sq]
  · rw [h_pt]
    refine PosSemidef.diagonal (fun i => ?_)
    fin_cases i
    · exact sq_nonneg _
    · exact sq_nonneg _

/-! ### Part III: KMS Detailed-Balance Generator, Matrix Propagator, & Gibbs Relaxation -/

/-- Spin-lowering ladder operator in `M₂(ℝ)`. -/
noncomputable def M_down : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i.val = 1 ∧ j.val = 0 then 1 else 0

/-- Spin-raising ladder operator in `M₂(ℝ)`. -/
noncomputable def M_up : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i.val = 0 ∧ j.val = 1 then 1 else 0

/-- KMS detailed-balance Markov GKSL generator on `M₂(ℝ)`. -/
noncomputable def gkslGenerator (γ_up γ_down : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  γ_down • (M_down * ρ * M_down.transpose -
    (1 / 2 : ℝ) • (M_down.transpose * M_down * ρ + ρ * M_down.transpose * M_down)) +
  γ_up • (M_up * ρ * M_up.transpose -
    (1 / 2 : ℝ) • (M_up.transpose * M_up * ρ + ρ * M_up.transpose * M_up))

/-- Two-level KMS Gibbs equilibrium density matrix at inverse temperature `β` and frequency `ω`. -/
noncomputable def gibbsState2 (β ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let z := 1 + Real.exp (-β * ω)
  Matrix.diagonal ![Real.exp (-β * ω) / z, 1 / z]

lemma gibbsState2_00 (β ω : ℝ) :
    gibbsState2 β ω 0 0 = Real.exp (-β * ω) / (1 + Real.exp (-β * ω)) := by
  dsimp [gibbsState2]; simp

lemma gibbsState2_01 (β ω : ℝ) :
    gibbsState2 β ω 0 1 = 0 := by
  dsimp [gibbsState2]; simp

lemma gibbsState2_10 (β ω : ℝ) :
    gibbsState2 β ω 1 0 = 0 := by
  dsimp [gibbsState2]; simp

lemma gibbsState2_11 (β ω : ℝ) :
    gibbsState2 β ω 1 1 = 1 / (1 + Real.exp (-β * ω)) := by
  dsimp [gibbsState2]; simp

lemma matrix_trace_fin2 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M.trace = M 0 0 + M 1 1 := by
  rw [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply, Matrix.diag_apply]

/-- The stationary Gibbs state satisfies `Tr(ρ_KMS) = 1` and `L(ρ_KMS) = 0` under detailed balance. -/
theorem kms_detailed_balance_gksl_stationary {β ω γ_up γ_down : ℝ}
    (h_rates : γ_up / γ_down = Real.exp (-β * ω)) (h_down : 0 < γ_down) :
    (gibbsState2 β ω).trace = 1 ∧
    gkslGenerator γ_up γ_down (gibbsState2 β ω) = 0 := by
  have hz_pos : 0 < 1 + Real.exp (-β * ω) := by positivity
  constructor
  · dsimp [gibbsState2]
    rw [trace_diagonal, Fin.sum_univ_two]
    simp only [cons_val_zero, cons_val_one]
    rw [← add_div, add_comm]
    exact div_self hz_pos.ne'
  · have h_up_eq : γ_up = γ_down * Real.exp (-β * ω) := by
      rw [← h_rates, mul_div_cancel₀ _ h_down.ne']
    ext i j
    rw [h_up_eq]
    dsimp [gkslGenerator, gibbsState2, M_down, M_up]
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, Fin.sum_univ_two, Matrix.of_apply]
      ring
    · simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, Fin.sum_univ_two, Matrix.of_apply]
    · simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, Fin.sum_univ_two, Matrix.of_apply]
    · simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, Fin.sum_univ_two, Matrix.of_apply]
      ring

/-- Closed-form propagator on the full real matrix carrier for the displayed two-rate generator.
The matrix ODE, composition law, trace preservation, and asymptotic fixed-point limit
are proved below. Complete positivity and the 4-channel Kraus representation (at $\omega = 0$)
are established in `InfoGeometry.OperatorAlgebra.PeirceBiSandwich.KMSCompletePositivityAndKrausSemigroup`. -/
noncomputable def gkslPropagator (γ_up γ_down t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  let Γ := γ_down + γ_up
  let p0 := if Γ = 0 then 0 else γ_up / Γ
  let p1 := if Γ = 0 then 0 else γ_down / Γ
  let tr := ρ.trace
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then
      p0 * tr + (ρ 0 0 - p0 * tr) * Real.exp (-Γ * t)
    else if i = 1 ∧ j = 1 then
      p1 * tr + (ρ 1 1 - p1 * tr) * Real.exp (-Γ * t)
    else
      ρ i j * Real.exp (-(1 / 2 : ℝ) * Γ * t)

lemma gksl_propagator_00 (γ_up γ_down t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ)
    (h_pos : 0 < γ_down + γ_up) :
    gkslPropagator γ_up γ_down t ρ 0 0 =
      (γ_up / (γ_down + γ_up)) * ρ.trace +
        (ρ 0 0 - (γ_up / (γ_down + γ_up)) * ρ.trace) * Real.exp (-(γ_down + γ_up) * t) := by
  dsimp [gkslPropagator]; rw [ite_eq_right h_pos.ne']

lemma gksl_propagator_01 (γ_up γ_down t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ) :
    gkslPropagator γ_up γ_down t ρ 0 1 =
      ρ 0 1 * Real.exp (-(1 / 2 : ℝ) * (γ_down + γ_up) * t) := by
  dsimp [gkslPropagator]

lemma gksl_propagator_10 (γ_up γ_down t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ) :
    gkslPropagator γ_up γ_down t ρ 1 0 =
      ρ 1 0 * Real.exp (-(1 / 2 : ℝ) * (γ_down + γ_up) * t) := by
  dsimp [gkslPropagator]

lemma gksl_propagator_11 (γ_up γ_down t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ)
    (h_pos : 0 < γ_down + γ_up) :
    gkslPropagator γ_up γ_down t ρ 1 1 =
      (γ_down / (γ_down + γ_up)) * ρ.trace +
        (ρ 1 1 - (γ_down / (γ_down + γ_up)) * ρ.trace) * Real.exp (-(γ_down + γ_up) * t) := by
  dsimp [gkslPropagator]; rw [ite_eq_right h_pos.ne']

/-- `gkslPropagator` at `t = 0` is the identity map: `P(0) ρ = ρ`. -/
theorem gksl_propagator_zero (γ_up γ_down : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ) :
    gkslPropagator γ_up γ_down 0 ρ = ρ := by
  ext i j
  dsimp [gkslPropagator]
  simp only [mul_zero, Real.exp_zero, mul_one]
  fin_cases i <;> fin_cases j <;> simp

/-- `gkslPropagator` preserves trace for all `t`: `Tr(P(t) ρ) = Tr(ρ)`. -/
theorem gksl_propagator_preserves_trace (γ_up γ_down t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ)
    (h_pos : 0 < γ_down + γ_up) :
    (gkslPropagator γ_up γ_down t ρ).trace = ρ.trace := by
  let Γ := γ_down + γ_up
  have hΓ_ne : Γ ≠ 0 := h_pos.ne'
  have hp_sum : γ_up / Γ + γ_down / Γ = 1 := by
    rw [← add_div, add_comm]
    exact div_self hΓ_ne
  have htr_def : ρ 0 0 + ρ 1 1 = ρ.trace := (matrix_trace_fin2 ρ).symm
  rw [matrix_trace_fin2, gksl_propagator_00 _ _ _ _ h_pos, gksl_propagator_11 _ _ _ _ h_pos]
  calc (γ_up / Γ * ρ.trace + (ρ 0 0 - γ_up / Γ * ρ.trace) * Real.exp (-Γ * t)) +
       (γ_down / Γ * ρ.trace + (ρ 1 1 - γ_down / Γ * ρ.trace) * Real.exp (-Γ * t))
      = (γ_up / Γ + γ_down / Γ) * ρ.trace +
        ((ρ 0 0 + ρ 1 1) - (γ_up / Γ + γ_down / Γ) * ρ.trace) * Real.exp (-Γ * t) := by ring
    _ = 1 * ρ.trace + (ρ.trace - 1 * ρ.trace) * Real.exp (-Γ * t) := by rw [hp_sum, htr_def]
    _ = ρ.trace := by ring

/-- The propagator satisfies the algebraic composition law `P(s + t) = P(s) ∘ P(t)` for real `s,t`. This does not assert positivity for negative times. -/
theorem gksl_propagator_semigroup (γ_up γ_down s t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ)
    (h_pos : 0 < γ_down + γ_up) :
    gkslPropagator γ_up γ_down (s + t) ρ =
      gkslPropagator γ_up γ_down s (gkslPropagator γ_up γ_down t ρ) := by
  let Γ := γ_down + γ_up
  have htr : (gkslPropagator γ_up γ_down t ρ).trace = ρ.trace :=
    gksl_propagator_preserves_trace γ_up γ_down t ρ h_pos
  have h_exp1 : Real.exp (-Γ * (s + t)) = Real.exp (-Γ * s) * Real.exp (-Γ * t) := by
    rw [mul_add, neg_add, Real.exp_add]
  have h_exp2 : Real.exp (-(1 / 2 : ℝ) * Γ * (s + t)) =
      Real.exp (-(1 / 2 : ℝ) * Γ * s) * Real.exp (-(1 / 2 : ℝ) * Γ * t) := by
    calc Real.exp (-(1 / 2 : ℝ) * Γ * (s + t))
        = Real.exp (-(1 / 2 : ℝ) * Γ * s + -(1 / 2 : ℝ) * Γ * t) := by ring_nf
      _ = Real.exp (-(1 / 2 : ℝ) * Γ * s) * Real.exp (-(1 / 2 : ℝ) * Γ * t) := Real.exp_add _ _
  ext i j
  fin_cases i <;> fin_cases j
  · change gkslPropagator γ_up γ_down (s + t) ρ 0 0 = gkslPropagator γ_up γ_down s (gkslPropagator γ_up γ_down t ρ) 0 0
    rw [gksl_propagator_00 _ _ _ _ h_pos, gksl_propagator_00 _ _ _ _ h_pos, htr,
        gksl_propagator_00 _ _ _ _ h_pos, h_exp1]
    ring
  · change gkslPropagator γ_up γ_down (s + t) ρ 0 1 = gkslPropagator γ_up γ_down s (gkslPropagator γ_up γ_down t ρ) 0 1
    rw [gksl_propagator_01, gksl_propagator_01, gksl_propagator_01, h_exp2]
    ring
  · change gkslPropagator γ_up γ_down (s + t) ρ 1 0 = gkslPropagator γ_up γ_down s (gkslPropagator γ_up γ_down t ρ) 1 0
    rw [gksl_propagator_10, gksl_propagator_10, gksl_propagator_10, h_exp2]
    ring
  · change gkslPropagator γ_up γ_down (s + t) ρ 1 1 = gkslPropagator γ_up γ_down s (gkslPropagator γ_up γ_down t ρ) 1 1
    rw [gksl_propagator_11 _ _ _ _ h_pos, gksl_propagator_11 _ _ _ _ h_pos, htr,
        gksl_propagator_11 _ _ _ _ h_pos, h_exp1]
    ring

/-- `gkslPropagator` entrywise derivative satisfies `HasDerivAt` matching `gkslGenerator`. -/
lemma gksl_propagator_hasDerivAt_00 (γ_up γ_down : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ)
    (h_pos : 0 < γ_down + γ_up) (t : ℝ) :
    HasDerivAt (fun s => gkslPropagator γ_up γ_down s ρ 0 0)
      (gkslGenerator γ_up γ_down (gkslPropagator γ_up γ_down t ρ) 0 0) t := by
  let Γ := γ_down + γ_up
  have hΓ_ne : Γ ≠ 0 := h_pos.ne'
  have h_fun : (fun s => gkslPropagator γ_up γ_down s ρ 0 0) =
      fun s => (γ_up / Γ) * ρ.trace + (ρ 0 0 - (γ_up / Γ) * ρ.trace) * Real.exp (-Γ * s) := by
    ext s; dsimp [gkslPropagator]; rw [ite_eq_right h_pos.ne']
  have h_der : HasDerivAt (fun s => Real.exp (-Γ * s)) (-Γ * Real.exp (-Γ * t)) t := by
    have h1 : HasDerivAt (fun s => -Γ * s) (-Γ) t := by simpa using (hasDerivAt_id t).const_mul (-Γ)
    have h2 := h1.exp
    have : Real.exp (-Γ * t) * -Γ = -Γ * Real.exp (-Γ * t) := mul_comm _ _
    rwa [this] at h2
  have h_all : HasDerivAt (fun s => (γ_up / Γ) * ρ.trace + (ρ 0 0 - (γ_up / Γ) * ρ.trace) * Real.exp (-Γ * s))
      ((ρ 0 0 - (γ_up / Γ) * ρ.trace) * (-Γ * Real.exp (-Γ * t))) t := by
    have h := (hasDerivAt_const t ((γ_up / Γ) * ρ.trace)).add (h_der.const_mul (ρ 0 0 - (γ_up / Γ) * ρ.trace))
    rw [zero_add] at h
    exact h
  have h_gen : gkslGenerator γ_up γ_down (gkslPropagator γ_up γ_down t ρ) 0 0 =
      ((ρ 0 0 - (γ_up / Γ) * ρ.trace) * (-Γ * Real.exp (-Γ * t))) := by
    dsimp [gkslGenerator, gkslPropagator, M_down, M_up]
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.of_apply, ite_eq_right h_pos.ne']
    have htr : ρ.trace = ρ 0 0 + ρ 1 1 := by dsimp [Matrix.trace]; rw [Fin.sum_univ_two]
    dsimp [Γ]
    rw [htr]
    have h_exp_eq : ((-γ_up + -γ_down) * t) = -((γ_down + γ_up) * t) := by ring
    rw [h_exp_eq]
    field_simp [hΓ_ne]
    ring
  rw [h_gen]
  exact h_all.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => by rw [← h_fun]))

lemma gksl_propagator_hasDerivAt_01 (γ_up γ_down : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ)
    (h_pos : 0 < γ_down + γ_up) (t : ℝ) :
    HasDerivAt (fun s => gkslPropagator γ_up γ_down s ρ 0 1)
      (gkslGenerator γ_up γ_down (gkslPropagator γ_up γ_down t ρ) 0 1) t := by
  let Γ := γ_down + γ_up
  have h_fun : (fun s => gkslPropagator γ_up γ_down s ρ 0 1) =
      fun s => ρ 0 1 * Real.exp (-(1 / 2 : ℝ) * Γ * s) := by
    ext s; dsimp [gkslPropagator]
  have h_der : HasDerivAt (fun s => Real.exp (-(1 / 2 : ℝ) * Γ * s))
      (-(1 / 2 : ℝ) * Γ * Real.exp (-(1 / 2 : ℝ) * Γ * t)) t := by
    have h1 : HasDerivAt (fun s => -(1 / 2 : ℝ) * Γ * s) (-(1 / 2 : ℝ) * Γ) t := by
      simpa using (hasDerivAt_id t).const_mul (-(1 / 2 : ℝ) * Γ)
    have h2 := h1.exp
    have : Real.exp (-(1 / 2 : ℝ) * Γ * t) * (-(1 / 2 : ℝ) * Γ) =
        -(1 / 2 : ℝ) * Γ * Real.exp (-(1 / 2 : ℝ) * Γ * t) := mul_comm _ _
    rwa [this] at h2
  have h_all := h_der.const_mul (ρ 0 1)
  have h_gen : gkslGenerator γ_up γ_down (gkslPropagator γ_up γ_down t ρ) 0 1 =
      ρ 0 1 * (-(1 / 2 : ℝ) * Γ * Real.exp (-(1 / 2 : ℝ) * Γ * t)) := by
    dsimp [gkslGenerator, gkslPropagator, M_down, M_up]
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.of_apply, ite_eq_right h_pos.ne']
    dsimp [Γ]
    ring
  rw [h_gen]
  exact h_all.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => by rw [← h_fun]))

lemma gksl_propagator_hasDerivAt_10 (γ_up γ_down : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ)
    (h_pos : 0 < γ_down + γ_up) (t : ℝ) :
    HasDerivAt (fun s => gkslPropagator γ_up γ_down s ρ 1 0)
      (gkslGenerator γ_up γ_down (gkslPropagator γ_up γ_down t ρ) 1 0) t := by
  let Γ := γ_down + γ_up
  have h_fun : (fun s => gkslPropagator γ_up γ_down s ρ 1 0) =
      fun s => ρ 1 0 * Real.exp (-(1 / 2 : ℝ) * Γ * s) := by
    ext s; dsimp [gkslPropagator]
  have h_der : HasDerivAt (fun s => Real.exp (-(1 / 2 : ℝ) * Γ * s))
      (-(1 / 2 : ℝ) * Γ * Real.exp (-(1 / 2 : ℝ) * Γ * t)) t := by
    have h1 : HasDerivAt (fun s => -(1 / 2 : ℝ) * Γ * s) (-(1 / 2 : ℝ) * Γ) t := by
      simpa using (hasDerivAt_id t).const_mul (-(1 / 2 : ℝ) * Γ)
    have h2 := h1.exp
    have : Real.exp (-(1 / 2 : ℝ) * Γ * t) * (-(1 / 2 : ℝ) * Γ) =
        -(1 / 2 : ℝ) * Γ * Real.exp (-(1 / 2 : ℝ) * Γ * t) := mul_comm _ _
    rwa [this] at h2
  have h_all := h_der.const_mul (ρ 1 0)
  have h_gen : gkslGenerator γ_up γ_down (gkslPropagator γ_up γ_down t ρ) 1 0 =
      ρ 1 0 * (-(1 / 2 : ℝ) * Γ * Real.exp (-(1 / 2 : ℝ) * Γ * t)) := by
    dsimp [gkslGenerator, gkslPropagator, M_down, M_up]
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.of_apply, ite_eq_right h_pos.ne']
    dsimp [Γ]
    ring
  rw [h_gen]
  exact h_all.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => by rw [← h_fun]))

lemma gksl_propagator_hasDerivAt_11 (γ_up γ_down : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ)
    (h_pos : 0 < γ_down + γ_up) (t : ℝ) :
    HasDerivAt (fun s => gkslPropagator γ_up γ_down s ρ 1 1)
      (gkslGenerator γ_up γ_down (gkslPropagator γ_up γ_down t ρ) 1 1) t := by
  let Γ := γ_down + γ_up
  have hΓ_ne : Γ ≠ 0 := h_pos.ne'
  have h_fun : (fun s => gkslPropagator γ_up γ_down s ρ 1 1) =
      fun s => (γ_down / Γ) * ρ.trace + (ρ 1 1 - (γ_down / Γ) * ρ.trace) * Real.exp (-Γ * s) := by
    ext s; dsimp [gkslPropagator]; rw [ite_eq_right h_pos.ne']
  have h_der : HasDerivAt (fun s => Real.exp (-Γ * s)) (-Γ * Real.exp (-Γ * t)) t := by
    have h1 : HasDerivAt (fun s => -Γ * s) (-Γ) t := by simpa using (hasDerivAt_id t).const_mul (-Γ)
    have h2 := h1.exp
    have : Real.exp (-Γ * t) * -Γ = -Γ * Real.exp (-Γ * t) := mul_comm _ _
    rwa [this] at h2
  have h_all : HasDerivAt (fun s => (γ_down / Γ) * ρ.trace + (ρ 1 1 - (γ_down / Γ) * ρ.trace) * Real.exp (-Γ * s))
      ((ρ 1 1 - (γ_down / Γ) * ρ.trace) * (-Γ * Real.exp (-Γ * t))) t := by
    have h := (hasDerivAt_const t ((γ_down / Γ) * ρ.trace)).add (h_der.const_mul (ρ 1 1 - (γ_down / Γ) * ρ.trace))
    rw [zero_add] at h
    exact h
  have h_gen : gkslGenerator γ_up γ_down (gkslPropagator γ_up γ_down t ρ) 1 1 =
      ((ρ 1 1 - (γ_down / Γ) * ρ.trace) * (-Γ * Real.exp (-Γ * t))) := by
    dsimp [gkslGenerator, gkslPropagator, M_down, M_up]
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.of_apply, ite_eq_right h_pos.ne']
    have htr : ρ.trace = ρ 0 0 + ρ 1 1 := by dsimp [Matrix.trace]; rw [Fin.sum_univ_two]
    dsimp [Γ]
    rw [htr]
    have h_exp_eq : ((-γ_up + -γ_down) * t) = -((γ_down + γ_up) * t) := by ring
    rw [h_exp_eq]
    field_simp [hΓ_ne]
    ring
  rw [h_gen]
  exact h_all.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => by rw [← h_fun]))

/-- `gkslPropagator` entrywise derivative satisfies `HasDerivAt` matching `gkslGenerator`. -/
theorem gksl_propagator_hasDerivAt (γ_up γ_down : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ)
    (h_pos : 0 < γ_down + γ_up) (t : ℝ) :
    ∀ i j : Fin 2,
      HasDerivAt (fun s => gkslPropagator γ_up γ_down s ρ i j)
        (gkslGenerator γ_up γ_down (gkslPropagator γ_up γ_down t ρ) i j) t := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact gksl_propagator_hasDerivAt_00 γ_up γ_down ρ h_pos t
  · exact gksl_propagator_hasDerivAt_01 γ_up γ_down ρ h_pos t
  · exact gksl_propagator_hasDerivAt_10 γ_up γ_down ρ h_pos t
  · exact gksl_propagator_hasDerivAt_11 γ_up γ_down ρ h_pos t

/-- Full matrix `HasDerivAt` for the GKSL propagator. -/
theorem gksl_propagator_hasDerivAt_matrix (γ_up γ_down : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℝ)
    (h_pos : 0 < γ_down + γ_up) (t : ℝ) :
    HasDerivAt (fun s => gkslPropagator γ_up γ_down s ρ)
      (gkslGenerator γ_up γ_down (gkslPropagator γ_up γ_down t ρ)) t := by
  refine hasDerivAt_pi.2 (fun i => hasDerivAt_pi.2 (fun j => ?_))
  exact gksl_propagator_hasDerivAt γ_up γ_down ρ h_pos t i j

/-- Asymptotic relaxation: `lim_{t → ∞} P(t) ρ = ρ_KMS` for any unit-trace real matrix `ρ`. -/
theorem gksl_propagator_relaxation {β ω γ_up γ_down : ℝ}
    (h_rates : γ_up / γ_down = Real.exp (-β * ω)) (h_down : 0 < γ_down)
    (ρ : Matrix (Fin 2) (Fin 2) ℝ) (h_tr : ρ.trace = 1) :
    Tendsto (fun t => gkslPropagator γ_up γ_down t ρ) atTop
      (nhds (gibbsState2 β ω)) := by
  let Γ := γ_down + γ_up
  have h_exp_pos : 0 < Real.exp (-β * ω) := Real.exp_pos _
  have h_up_pos : 0 < γ_up := by
    have : γ_up = γ_down * Real.exp (-β * ω) := by
      rw [← h_rates, mul_div_cancel₀ _ h_down.ne']
    rw [this]
    exact mul_pos h_down h_exp_pos
  have hΓ_pos : 0 < Γ := add_pos h_down h_up_pos
  have hΓ_ne : Γ ≠ 0 := hΓ_pos.ne'
  have h_exp_tendsto : Tendsto (fun t => Real.exp (-Γ * t)) atTop (nhds 0) := by
    have h_pos : Tendsto (fun t : ℝ => Γ * t) atTop atTop :=
      Tendsto.const_mul_atTop hΓ_pos tendsto_id
    have h_neg : Tendsto (fun t : ℝ => -(Γ * t)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp h_pos
    have heq : (fun t : ℝ => Real.exp (-Γ * t)) = (fun x => Real.exp x) ∘ (fun t : ℝ => -(Γ * t)) := by
      ext t; dsimp; rw [neg_mul_eq_neg_mul]
    rw [heq]
    exact Real.tendsto_exp_atBot.comp h_neg
  have h_exp_half_tendsto : Tendsto (fun t => Real.exp (-(1 / 2 : ℝ) * Γ * t)) atTop (nhds 0) := by
    have h_half_pos : 0 < (1 / 2 : ℝ) * Γ := mul_pos (by norm_num) hΓ_pos
    have h_pos : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * Γ * t) atTop atTop :=
      Tendsto.const_mul_atTop h_half_pos tendsto_id
    have h_neg : Tendsto (fun t : ℝ => -((1 / 2 : ℝ) * Γ * t)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp h_pos
    have heq : (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * Γ * t)) =
        (fun x => Real.exp x) ∘ (fun t : ℝ => -((1 / 2 : ℝ) * Γ * t)) := by
      ext t; dsimp; congr 1; ring
    rw [heq]
    exact Real.tendsto_exp_atBot.comp h_neg
  have hp0_eq : γ_up / Γ = Real.exp (-β * ω) / (1 + Real.exp (-β * ω)) := by
    dsimp [Γ]
    have h_up : γ_up = γ_down * Real.exp (-β * ω) := by
      rw [← h_rates, mul_div_cancel₀ _ h_down.ne']
    rw [h_up]
    have : γ_down + γ_down * Real.exp (-β * ω) = γ_down * (1 + Real.exp (-β * ω)) := by ring
    rw [this, mul_div_mul_left _ _ h_down.ne']
  have hp1_eq : γ_down / Γ = 1 / (1 + Real.exp (-β * ω)) := by
    dsimp [Γ]
    have h_up : γ_up = γ_down * Real.exp (-β * ω) := by
      rw [← h_rates, mul_div_cancel₀ _ h_down.ne']
    rw [h_up]
    have : γ_down + γ_down * Real.exp (-β * ω) = γ_down * (1 + Real.exp (-β * ω)) := by ring
    rw [this]
    have : γ_down = γ_down * 1 := by ring
    nth_rw 1 [this]
    exact mul_div_mul_left 1 _ h_down.ne'
  refine tendsto_pi_nhds.2 (fun i => tendsto_pi_nhds.2 (fun j => ?_))
  fin_cases i <;> fin_cases j
  · change Tendsto (fun t => gkslPropagator γ_up γ_down t ρ 0 0) atTop (nhds (gibbsState2 β ω 0 0))
    rw [gibbsState2_00]
    have h_fun : (fun t => gkslPropagator γ_up γ_down t ρ 0 0) =
        fun t => Real.exp (-β * ω) / (1 + Real.exp (-β * ω)) +
                 (ρ 0 0 - Real.exp (-β * ω) / (1 + Real.exp (-β * ω))) * Real.exp (-Γ * t) := by
      ext t
      rw [gksl_propagator_00 _ _ _ _ hΓ_pos, hp0_eq, h_tr, mul_one]
    rw [h_fun]
    have h_tend := (tendsto_const_nhds (x := Real.exp (-β * ω) / (1 + Real.exp (-β * ω)))).add
      (h_exp_tendsto.const_mul (ρ 0 0 - Real.exp (-β * ω) / (1 + Real.exp (-β * ω))))
    simp only [mul_zero, add_zero] at h_tend
    exact h_tend
  · change Tendsto (fun t => gkslPropagator γ_up γ_down t ρ 0 1) atTop (nhds (gibbsState2 β ω 0 1))
    rw [gibbsState2_01]
    have h_fun : (fun t => gkslPropagator γ_up γ_down t ρ 0 1) = fun t => ρ 0 1 * Real.exp (-(1 / 2 : ℝ) * Γ * t) := by
      ext t; rw [gksl_propagator_01]
    rw [h_fun]
    have h_tend := h_exp_half_tendsto.const_mul (ρ 0 1)
    simp only [mul_zero] at h_tend
    exact h_tend
  · change Tendsto (fun t => gkslPropagator γ_up γ_down t ρ 1 0) atTop (nhds (gibbsState2 β ω 1 0))
    rw [gibbsState2_10]
    have h_fun : (fun t => gkslPropagator γ_up γ_down t ρ 1 0) = fun t => ρ 1 0 * Real.exp (-(1 / 2 : ℝ) * Γ * t) := by
      ext t; rw [gksl_propagator_10]
    rw [h_fun]
    have h_tend := h_exp_half_tendsto.const_mul (ρ 1 0)
    simp only [mul_zero] at h_tend
    exact h_tend
  · change Tendsto (fun t => gkslPropagator γ_up γ_down t ρ 1 1) atTop (nhds (gibbsState2 β ω 1 1))
    rw [gibbsState2_11]
    have h_fun : (fun t => gkslPropagator γ_up γ_down t ρ 1 1) =
        fun t => 1 / (1 + Real.exp (-β * ω)) +
                 (ρ 1 1 - 1 / (1 + Real.exp (-β * ω))) * Real.exp (-Γ * t) := by
      ext t
      rw [gksl_propagator_11 _ _ _ _ hΓ_pos, hp1_eq, h_tr, mul_one]
    rw [h_fun]
    have h_tend := (tendsto_const_nhds (x := 1 / (1 + Real.exp (-β * ω)))).add
      (h_exp_tendsto.const_mul (ρ 1 1 - 1 / (1 + Real.exp (-β * ω))))
    simp only [mul_zero, add_zero] at h_tend
    exact h_tend

/-! ### Part IV: Dually Flat Spin Cumulant, Legendre Duality, Anisotropic Kubo-Mori & Nernst Barrier -/

variable {d : ℕ}

/-- Dually flat spin cumulant potential `ψ(θ) = ln(2 cosh ‖θ‖)` on `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def spinCumulant (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.log (2 * Real.cosh ‖θ‖)

/-- Dual Legendre spin entropy `φ(η) = ((1+‖η‖)/2) ln((1+‖η‖)/2) + ((1-‖η‖)/2) ln((1-‖η‖)/2)`. -/
noncomputable def spinDualEntropy (η : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((1 + ‖η‖) / 2) * Real.log ((1 + ‖η‖) / 2) + ((1 - ‖η‖) / 2) * Real.log ((1 - ‖η‖) / 2)

/-- Bloch ball gradient coordinate map `η = ∇ψ(θ) = (tanh ‖θ‖ / ‖θ‖) • θ`. -/
noncomputable def blochCoord (θ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if ‖θ‖ = 0 then 0 else (Real.tanh ‖θ‖ / ‖θ‖) • θ

/-- Inverse Bloch coordinate map from the open ball `‖η‖ < 1` to `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def invBlochCoord (η : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if ‖η‖ = 0 then 0 else (Real.artanh ‖η‖ / ‖η‖) • η

theorem tanh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le

theorem bloch_coord_norm (θ : EuclideanSpace ℝ (Fin d)) :
    ‖blochCoord θ‖ = Real.tanh ‖θ‖ := by
  dsimp [blochCoord]
  split_ifs with h
  · simp [h, Real.tanh_zero]
  · rw [norm_smul, Real.norm_of_nonneg, div_mul_cancel₀ _ h]
    have h_tanh_nonneg : 0 ≤ Real.tanh ‖θ‖ := tanh_nonneg_of_nonneg (norm_nonneg θ)
    exact div_nonneg h_tanh_nonneg (norm_nonneg θ)

/-- The image of `blochCoord` lies strictly inside the open Bloch unit ball `‖η‖ < 1`. -/
theorem bloch_coord_lt_one (θ : EuclideanSpace ℝ (Fin d)) :
    ‖blochCoord θ‖ < 1 := by
  rw [bloch_coord_norm]
  exact Real.tanh_lt_one ‖θ‖

/-- Legendre bijection and Young equality: `ψ(θ) + φ(η) = ⟨θ, η⟩` for `η = blochCoord θ`. -/
theorem bloch_legendre_bijection_and_young_equality (θ : EuclideanSpace ℝ (Fin d)) :
    -- 1. Young equality holds identically
    spinCumulant θ + spinDualEntropy (blochCoord θ) =
      @inner ℝ (EuclideanSpace ℝ (Fin d)) _ θ (blochCoord θ) ∧
    -- 2. Left inverse: invBlochCoord (blochCoord θ) = θ
    invBlochCoord (blochCoord θ) = θ := by
  constructor
  · by_cases h : ‖θ‖ = 0
    · have hθ : θ = 0 := norm_eq_zero.mp h
      subst hθ
      have h_bloch : blochCoord (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
        dsimp [blochCoord]; split_ifs; rfl
      rw [h_bloch]
      dsimp [spinCumulant, spinDualEntropy]
      simp only [norm_zero, Real.cosh_zero, mul_one, inner_zero_right]
      have hlog1 : Real.log ((1 + 0) / 2) = -Real.log 2 := by
        rw [add_zero, one_div, Real.log_inv]
      have hlog2 : Real.log ((1 - 0) / 2) = -Real.log 2 := by
        rw [sub_zero, one_div, Real.log_inv]
      rw [hlog1, hlog2]
      ring
    · have h_norm := bloch_coord_norm θ
      let r := ‖θ‖
      have hr_pos : 0 < r := lt_of_le_of_ne (norm_nonneg θ) (Ne.symm h)
      let s := Real.tanh r
      have hs_lt : s < 1 := Real.tanh_lt_one r
      have hs_nonneg : 0 ≤ s := tanh_nonneg_of_nonneg hr_pos.le
      have hcosh_pos : 0 < Real.cosh r := Real.cosh_pos r
      have h2cosh_pos : 0 < 2 * Real.cosh r := by linarith
      have h_plus : (1 + s) / 2 = Real.exp r / (2 * Real.cosh r) := by
        dsimp [s]; rw [Real.tanh_eq_sinh_div_cosh]
        have : 1 + Real.sinh r / Real.cosh r = (Real.cosh r + Real.sinh r) / Real.cosh r := by
          rw [add_div, div_self hcosh_pos.ne']
        rw [this, Real.cosh_add_sinh]
        ring
      have h_minus : (1 - s) / 2 = Real.exp (-r) / (2 * Real.cosh r) := by
        dsimp [s]; rw [Real.tanh_eq_sinh_div_cosh]
        have : 1 - Real.sinh r / Real.cosh r = (Real.cosh r - Real.sinh r) / Real.cosh r := by
          rw [sub_div, div_self hcosh_pos.ne']
        rw [this, Real.cosh_sub_sinh]
        ring
      have h_log_plus : Real.log ((1 + s) / 2) = r - Real.log (2 * Real.cosh r) := by
        rw [h_plus, Real.log_div (Real.exp_pos r).ne' h2cosh_pos.ne', Real.log_exp]
      have h_log_minus : Real.log ((1 - s) / 2) = -r - Real.log (2 * Real.cosh r) := by
        rw [h_minus, Real.log_div (Real.exp_pos (-r)).ne' h2cosh_pos.ne', Real.log_exp]
      have h_entropy : spinDualEntropy (blochCoord θ) =
          r * Real.tanh r - Real.log (2 * Real.cosh r) := by
        dsimp [spinDualEntropy]
        rw [h_norm]
        change ((1 + s) / 2) * Real.log ((1 + s) / 2) + ((1 - s) / 2) * Real.log ((1 - s) / 2) =
               r * s - Real.log (2 * Real.cosh r)
        rw [h_log_plus, h_log_minus]
        ring
      have h_inner : @inner ℝ (EuclideanSpace ℝ (Fin d)) _ θ (blochCoord θ) = r * Real.tanh r := by
        have h_bc : blochCoord θ = (Real.tanh ‖θ‖ / ‖θ‖) • θ := by
          dsimp [blochCoord]; rw [ite_eq_right h]
        rw [h_bc, inner_smul_right, real_inner_self_eq_norm_mul_norm]
        dsimp [r]
        calc (Real.tanh ‖θ‖ / ‖θ‖) * (‖θ‖ * ‖θ‖)
            = (Real.tanh ‖θ‖ / ‖θ‖ * ‖θ‖) * ‖θ‖ := by ring
          _ = Real.tanh ‖θ‖ * ‖θ‖ := by rw [div_mul_cancel₀ _ h]
          _ = ‖θ‖ * Real.tanh ‖θ‖ := by ring
      dsimp [spinCumulant]
      rw [h_entropy, h_inner]
      ring
  · by_cases h : ‖θ‖ = 0
    · have hθ : θ = 0 := norm_eq_zero.mp h
      subst hθ
      dsimp [blochCoord, invBlochCoord]
      split_ifs; rfl
    · have h_norm := bloch_coord_norm θ
      have h_s_ne : ‖blochCoord θ‖ ≠ 0 := by
        rw [h_norm]
        have h_pos : 0 < ‖θ‖ := lt_of_le_of_ne (norm_nonneg θ) (Ne.symm h)
        have h_tanh_pos : 0 < Real.tanh ‖θ‖ := by
          rw [Real.tanh_eq_sinh_div_cosh]
          exact div_pos (Real.sinh_pos_iff.mpr h_pos) (Real.cosh_pos ‖θ‖)
        exact h_tanh_pos.ne'
      have h_bc : blochCoord θ = (Real.tanh ‖θ‖ / ‖θ‖) • θ := by
        dsimp [blochCoord]; rw [ite_eq_right h]
      dsimp [invBlochCoord]
      rw [ite_eq_right h_s_ne, h_norm, Real.artanh_tanh, h_bc, smul_smul]
      have h_canc : (‖θ‖ / Real.tanh ‖θ‖) * (Real.tanh ‖θ‖ / ‖θ‖) = 1 := by
        have ht_ne : Real.tanh ‖θ‖ ≠ 0 := by
          rw [← h_norm]; exact h_s_ne
        rw [div_mul_div_cancel₀ ht_ne, div_self h]
      rw [h_canc, one_smul]

/-- Derivative of `artanh(s)` on `(-1, 1)`. -/
theorem hasDerivAt_artanh {s : ℝ} (hs : s ∈ Ioo (-1) 1) :
    HasDerivAt Real.artanh (1 / (1 - s ^ 2)) s := by
  have hs1 : -1 < s := hs.1
  have hs2 : s < 1 := hs.2
  have h_pos : 0 < 1 - s ^ 2 := by nlinarith
  have h_ne : 1 - s ^ 2 ≠ 0 := h_pos.ne'
  have h_tanh_deriv : HasDerivAt Real.tanh (1 - s ^ 2) (Real.artanh s) := by
    have h1 : HasDerivAt Real.sinh (Real.cosh (Real.artanh s)) (Real.artanh s) :=
      Real.hasDerivAt_sinh (Real.artanh s)
    have h2 : HasDerivAt Real.cosh (Real.sinh (Real.artanh s)) (Real.artanh s) :=
      Real.hasDerivAt_cosh (Real.artanh s)
    have hcosh_pos : 0 < Real.cosh (Real.artanh s) := Real.cosh_pos (Real.artanh s)
    have h_quot := h1.div h2 hcosh_pos.ne'
    have h_eq : (Real.cosh (Real.artanh s) * Real.cosh (Real.artanh s) -
                 Real.sinh (Real.artanh s) * Real.sinh (Real.artanh s)) /
                (Real.cosh (Real.artanh s) ^ 2) = 1 - s ^ 2 := by
      rw [← sq, ← sq, Real.cosh_sq_sub_sinh_sq]
      rw [one_div, Real.cosh_artanh hs]
      have h_sq : (1 / √(1 - s ^ 2)) ^ 2 = 1 / (1 - s ^ 2) := by
        rw [div_pow, one_pow, Real.sq_sqrt (by linarith)]
      rw [h_sq, inv_div, div_one]
    have h_tanh_fun : Real.sinh / Real.cosh = Real.tanh := by
      ext x; exact (Real.tanh_eq_sinh_div_cosh x).symm
    rw [h_tanh_fun] at h_quot
    rw [h_eq] at h_quot
    exact h_quot
  have h_cont : ContinuousAt Real.artanh s := by
    have h_log_eq : (fun y => (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y))) =ᶠ[nhds s] Real.artanh := by
      have h_nhds : Ioo (-1 : ℝ) 1 ∈ nhds s := isOpen_Ioo.mem_nhds hs
      filter_upwards [h_nhds] with y hy
      exact (Real.artanh_eq_half_log (Ioo_subset_Icc_self hy)).symm
    have h_target : ContinuousAt (fun y => (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y))) s := by
      apply ContinuousAt.mul continuousAt_const
      have h_div_pos : 0 < (1 + s) / (1 - s) := div_pos (by linarith) (by linarith)
      have h_denom : (fun y : ℝ => 1 - y) s ≠ 0 := by dsimp; linarith
      have h_div : ContinuousAt (fun y => (1 + y) / (1 - y)) s :=
        (continuousAt_const.add continuousAt_id).div
        (continuousAt_const.sub continuousAt_id) h_denom
      exact ContinuousAt.comp (g := Real.log) (f := fun y => (1 + y) / (1 - y))
            (Real.continuousAt_log h_div_pos.ne') h_div
    exact h_target.congr h_log_eq
  have h_ev : ∀ᶠ y in nhds s, Real.tanh (Real.artanh y) = y := by
    have h_nhds : Ioo (-1 : ℝ) 1 ∈ nhds s := isOpen_Ioo.mem_nhds hs
    filter_upwards [h_nhds] with y hy
    exact Real.tanh_artanh hy
  have h_inv := HasDerivAt.of_local_left_inverse h_cont h_tanh_deriv h_ne h_ev
  rw [one_div]
  exact h_inv

theorem artanh_strictMono_sub_id : StrictMonoOn (fun x => Real.artanh x - x) (Ico 0 1) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun x => 1 / (1 - x ^ 2) - 1)
         (convex_Ico 0 1) ?_ ?_ ?_
  · refine ContinuousOn.sub ?_ continuousOn_id
    intro x hx
    have hx_ioo : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    exact (hasDerivAt_artanh hx_ioo).continuousAt.continuousWithinAt
  · rw [interior_Ico]
    intro x hx
    have hx_ioo : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have h_der := (hasDerivAt_artanh hx_ioo).sub (hasDerivAt_id x)
    exact h_der.hasDerivWithinAt
  · rw [interior_Ico]
    intro x hx
    have hx1 : 0 < x := hx.1
    have hx2 : x < 1 := hx.2
    have h_div : 1 < 1 / (1 - x ^ 2) := one_lt_one_div (by nlinarith) (by nlinarith)
    linarith

theorem artanh_strictMono_div_sub_artanh :
    StrictMonoOn (fun x => x / (1 - x ^ 2) - Real.artanh x) (Ico 0 1) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos
         (f' := fun x => (1 + x ^ 2) / (1 - x ^ 2) ^ 2 - 1 / (1 - x ^ 2))
         (convex_Ico 0 1) ?_ ?_ ?_
  · refine ContinuousOn.sub ?_ ?_
    · intro x hx
      have h_ne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
      exact (continuousAt_id.div
             (continuousAt_const.sub (continuousAt_id.pow 2)) h_ne).continuousWithinAt
    · intro x hx
      have hx_ioo : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
      exact (hasDerivAt_artanh hx_ioo).continuousAt.continuousWithinAt
  · rw [interior_Ico]
    intro x hx
    have hx_ioo : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have h_ne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
    have h1 : HasDerivAt (fun y => y) 1 x := hasDerivAt_id x
    have hmul : HasDerivAt (fun y => y * y) (1 * x + x * 1) x := (hasDerivAt_id x).mul (hasDerivAt_id x)
    have hsq : HasDerivAt (fun y => y ^ 2) (2 * x) x := by
      simpa [sq, two_mul] using hmul
    have h2 : HasDerivAt (fun y => 1 - y ^ 2) (-2 * x) x := by
      have hsub := (hasDerivAt_const x 1).sub hsq
      have h_neg : 0 - 2 * x = -2 * x := by ring
      rw [h_neg] at hsub
      exact hsub
    have h_quot := h1.div h2 h_ne
    have h_alg : (1 * (1 - x ^ 2) - x * (-2 * x)) / (1 - x ^ 2) ^ 2 = (1 + x ^ 2) / (1 - x ^ 2) ^ 2 := by
      ring
    rw [h_alg] at h_quot
    have h_der := h_quot.sub (hasDerivAt_artanh hx_ioo)
    exact h_der.hasDerivWithinAt
  · rw [interior_Ico]
    intro x hx
    have hx1 : 0 < x := hx.1
    have hx2 : x < 1 := hx.2
    have h_pos : 0 < 1 - x ^ 2 := by nlinarith
    have h_alg : (1 + x ^ 2) / (1 - x ^ 2) ^ 2 - 1 / (1 - x ^ 2) = (2 * x ^ 2) / (1 - x ^ 2) ^ 2 := by
      have h_ne : 1 - x ^ 2 ≠ 0 := h_pos.ne'
      field_simp; ring
    rw [h_alg]
    exact div_pos (by nlinarith) (by nlinarith)

/-- Strict anisotropic Kubo-Mori Hessian metric bounds on `(0, 1)`:
    `1 < artanh(s)/s < 1 / (1 - s²)` and `artanh'(s) = 1 / (1 - s²)`. -/
theorem artanh_deriv_and_anisotropic_kubo_mori_bounds {s : ℝ} (hs : s ∈ Ioo 0 1) :
    HasDerivAt Real.artanh (1 / (1 - s ^ 2)) s ∧
    1 < Real.artanh s / s ∧
    Real.artanh s / s < 1 / (1 - s ^ 2) := by
  have hs_ioo : s ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
  have h_der := hasDerivAt_artanh hs_ioo
  have hs_ico : s ∈ Ico 0 1 := ⟨by linarith [hs.1], hs.2⟩
  have h0_ico : (0 : ℝ) ∈ Ico 0 1 := ⟨le_rfl, by linarith [hs.2]⟩
  -- Lower bound
  have h_lt_low := artanh_strictMono_sub_id h0_ico hs_ico hs.1
  simp only [Real.artanh_zero, sub_self] at h_lt_low
  have hs_pos : s < Real.artanh s := by linarith
  have h_low : 1 < Real.artanh s / s := by
    rw [lt_div_iff₀ hs.1]; linarith
  -- Upper bound
  have h_lt_up := artanh_strictMono_div_sub_artanh h0_ico hs_ico hs.1
  simp only [Real.artanh_zero, zero_div, sub_self] at h_lt_up
  have hs_up_pos : Real.artanh s < s / (1 - s ^ 2) := by linarith
  have h_div : Real.artanh s / s < (s / (1 - s ^ 2)) / s :=
    (div_lt_div_iff_of_pos_right hs.1).mpr hs_up_pos
  have h_canc : (s / (1 - s ^ 2)) / s = 1 / (1 - s ^ 2) := by
    rw [div_div, mul_comm, ← div_div, div_self hs.1.ne', one_div]
  rw [h_canc] at h_div
  exact ⟨h_der, h_low, h_div⟩

/-- Nernst horizon third-law boundary theorem: `artanh(s) → +∞` as `s → 1⁻`. -/
theorem nernst_boundary_divergence :
    Tendsto Real.artanh (nhdsWithin 1 (Iio 1)) atTop := by
  rw [tendsto_atTop]
  intro M
  let s₀ := Real.tanh (M + 1)
  have hs₀_lt : s₀ < 1 := Real.tanh_lt_one (M + 1)
  have hs₀_gt : -1 < s₀ := Real.neg_one_lt_tanh (M + 1)
  have h_mem : Ioo s₀ 1 ∈ nhdsWithin 1 (Iio 1) := by
    rw [nhdsWithin, mem_inf_iff]
    refine ⟨Ioi s₀, isOpen_Ioi.mem_nhds hs₀_lt, Iio 1, mem_principal_self _, ?_⟩
    ext x; simp [Ioo, Ioi, Iio, and_comm]
  filter_upwards [h_mem] with s hs
  have h_lt : s₀ < s := hs.1
  have hs_lt : s < 1 := hs.2
  have h_art : Real.artanh s₀ < Real.artanh s :=
    Real.artanh_lt_artanh (by linarith) hs_lt h_lt
  rw [Real.artanh_tanh] at h_art
  linarith

lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hsinh := Real.hasDerivAt_sinh x
  have hcosh := Real.hasDerivAt_cosh x
  have hdiv := hsinh.div hcosh (Real.cosh_pos x).ne'
  have heq : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 =
      1 / Real.cosh x ^ 2 := by
    rw [← sq, ← sq, Real.cosh_sq_sub_sinh_sq]
  have h_tanh_fun : Real.sinh / Real.cosh = Real.tanh := by
    ext y; exact (Real.tanh_eq_sinh_div_cosh y).symm
  rw [h_tanh_fun, heq] at hdiv
  exact hdiv

lemma strictMono_tanh : StrictMono Real.tanh := by
  intro a b hab
  refine strictMono_of_hasDerivAt_pos (f' := fun x => 1 / Real.cosh x ^ 2)
    (fun x => hasDerivAt_tanh x)
    (fun x => one_div_pos.mpr (sq_pos_of_ne_zero (Real.cosh_pos x).ne'))
    hab

/-- Radial 1D spin Bregman divergence `D_ψ(r₁, r₂) = ψ(r₁) - ψ(r₂) - tanh(r₂) (r₁ - r₂)`. -/
noncomputable def spinBregman1D (r₁ r₂ : ℝ) : ℝ :=
  Real.log (2 * Real.cosh r₁) - Real.log (2 * Real.cosh r₂) - Real.tanh r₂ * (r₁ - r₂)

/-- Bregman nonnegativity: `D_ψ(r₁, r₂) ≥ 0`, and strictly positive for `r₁ ≠ r₂`. -/
theorem spin_bregman_nonneg (r₁ r₂ : ℝ) :
    0 ≤ spinBregman1D r₁ r₂ ∧
    (spinBregman1D r₁ r₂ = 0 ↔ r₁ = r₂) := by
  have h_conv := strictMono_tanh
  constructor
  · rcases lt_trichotomy r₁ r₂ with hlt | heq | hgt
    · have h_mvt : ∃ c ∈ Ioo r₁ r₂, Real.tanh c =
          (Real.log (2 * Real.cosh r₂) - Real.log (2 * Real.cosh r₁)) / (r₂ - r₁) := by
        have h_der : ∀ x ∈ Icc r₁ r₂, HasDerivAt (fun y => Real.log (2 * Real.cosh y)) (Real.tanh x) x := by
          intro x _
          have h2c : HasDerivAt (fun y => 2 * Real.cosh y) (2 * Real.sinh x) x :=
            (Real.hasDerivAt_cosh x).const_mul 2
          have hlog := h2c.log (by linarith [Real.cosh_pos x])
          have heq : 2 * Real.sinh x / (2 * Real.cosh x) = Real.tanh x := by
            rw [mul_div_mul_left _ _ (by norm_num), Real.tanh_eq_sinh_div_cosh]
          rw [heq] at hlog
          exact hlog
        have h_cont : ContinuousOn (fun y => Real.log (2 * Real.cosh y)) (Icc r₁ r₂) :=
          fun x hx => (h_der x hx).continuousAt.continuousWithinAt
        exact exists_hasDerivAt_eq_slope (fun y => Real.log (2 * Real.cosh y))
              Real.tanh hlt h_cont (fun x hx => h_der x (Ioo_subset_Icc_self hx))
      rcases h_mvt with ⟨c, hc, hc_eq⟩
      dsimp [spinBregman1D]
      have hc_lt : Real.tanh c < Real.tanh r₂ := h_conv hc.2
      have h_slope : Real.log (2 * Real.cosh r₂) - Real.log (2 * Real.cosh r₁) =
          Real.tanh c * (r₂ - r₁) := by
        rw [hc_eq, div_mul_cancel₀ _ (by linarith)]
      have : Real.log (2 * Real.cosh r₁) - Real.log (2 * Real.cosh r₂) = -Real.tanh c * (r₂ - r₁) := by
        linarith
      rw [this]
      have : -Real.tanh c * (r₂ - r₁) - Real.tanh r₂ * (r₁ - r₂) =
             (Real.tanh r₂ - Real.tanh c) * (r₂ - r₁) := by ring
      rw [this]
      exact mul_nonneg (by linarith) (by linarith)
    · subst heq
      dsimp [spinBregman1D]
      simp only [sub_self, mul_zero, le_refl]
    · have h_mvt : ∃ c ∈ Ioo r₂ r₁, Real.tanh c =
          (Real.log (2 * Real.cosh r₁) - Real.log (2 * Real.cosh r₂)) / (r₁ - r₂) := by
        have h_der : ∀ x ∈ Icc r₂ r₁, HasDerivAt (fun y => Real.log (2 * Real.cosh y)) (Real.tanh x) x := by
          intro x _
          have h2c : HasDerivAt (fun y => 2 * Real.cosh y) (2 * Real.sinh x) x :=
            (Real.hasDerivAt_cosh x).const_mul 2
          have hlog := h2c.log (by linarith [Real.cosh_pos x])
          have heq : 2 * Real.sinh x / (2 * Real.cosh x) = Real.tanh x := by
            rw [mul_div_mul_left _ _ (by norm_num), Real.tanh_eq_sinh_div_cosh]
          rw [heq] at hlog
          exact hlog
        have h_cont : ContinuousOn (fun y => Real.log (2 * Real.cosh y)) (Icc r₂ r₁) :=
          fun x hx => (h_der x hx).continuousAt.continuousWithinAt
        exact exists_hasDerivAt_eq_slope (fun y => Real.log (2 * Real.cosh y))
              Real.tanh hgt h_cont (fun x hx => h_der x (Ioo_subset_Icc_self hx))
      rcases h_mvt with ⟨c, hc, hc_eq⟩
      dsimp [spinBregman1D]
      have hc_gt : Real.tanh r₂ < Real.tanh c := h_conv hc.1
      have h_slope : Real.log (2 * Real.cosh r₁) - Real.log (2 * Real.cosh r₂) =
          Real.tanh c * (r₁ - r₂) := by
        rw [hc_eq, div_mul_cancel₀ _ (by linarith)]
      rw [h_slope]
      have : Real.tanh c * (r₁ - r₂) - Real.tanh r₂ * (r₁ - r₂) =
             (Real.tanh c - Real.tanh r₂) * (r₁ - r₂) := by ring
      rw [this]
      exact mul_nonneg (by linarith) (by linarith)
  · constructor
    · intro h_zero
      rcases lt_trichotomy r₁ r₂ with hlt | heq | hgt
      · exfalso
        have h_mvt : ∃ c ∈ Ioo r₁ r₂, Real.tanh c =
            (Real.log (2 * Real.cosh r₂) - Real.log (2 * Real.cosh r₁)) / (r₂ - r₁) := by
          have h_der : ∀ x ∈ Icc r₁ r₂, HasDerivAt (fun y => Real.log (2 * Real.cosh y)) (Real.tanh x) x := by
            intro x _
            have h2c : HasDerivAt (fun y => 2 * Real.cosh y) (2 * Real.sinh x) x :=
              (Real.hasDerivAt_cosh x).const_mul 2
            have hlog := h2c.log (by linarith [Real.cosh_pos x])
            have heq : 2 * Real.sinh x / (2 * Real.cosh x) = Real.tanh x := by
              rw [mul_div_mul_left _ _ (by norm_num), Real.tanh_eq_sinh_div_cosh]
            rw [heq] at hlog
            exact hlog
          have h_cont : ContinuousOn (fun y => Real.log (2 * Real.cosh y)) (Icc r₁ r₂) :=
            fun x hx => (h_der x hx).continuousAt.continuousWithinAt
          exact exists_hasDerivAt_eq_slope (fun y => Real.log (2 * Real.cosh y))
                Real.tanh hlt h_cont (fun x hx => h_der x (Ioo_subset_Icc_self hx))
        rcases h_mvt with ⟨c, hc, hc_eq⟩
        dsimp [spinBregman1D] at h_zero
        have hc_lt : Real.tanh c < Real.tanh r₂ := h_conv hc.2
        have h_slope : Real.log (2 * Real.cosh r₂) - Real.log (2 * Real.cosh r₁) =
            Real.tanh c * (r₂ - r₁) := by
          rw [hc_eq, div_mul_cancel₀ _ (by linarith)]
        have : Real.log (2 * Real.cosh r₁) - Real.log (2 * Real.cosh r₂) = -Real.tanh c * (r₂ - r₁) := by
          linarith
        rw [this] at h_zero
        have : -Real.tanh c * (r₂ - r₁) - Real.tanh r₂ * (r₁ - r₂) =
               (Real.tanh r₂ - Real.tanh c) * (r₂ - r₁) := by ring
        rw [this] at h_zero
        have h_pos : 0 < (Real.tanh r₂ - Real.tanh c) * (r₂ - r₁) :=
          mul_pos (by linarith) (by linarith)
        linarith
      · exact heq
      · exfalso
        have h_mvt : ∃ c ∈ Ioo r₂ r₁, Real.tanh c =
            (Real.log (2 * Real.cosh r₁) - Real.log (2 * Real.cosh r₂)) / (r₁ - r₂) := by
          have h_der : ∀ x ∈ Icc r₂ r₁, HasDerivAt (fun y => Real.log (2 * Real.cosh y)) (Real.tanh x) x := by
            intro x _
            have h2c : HasDerivAt (fun y => 2 * Real.cosh y) (2 * Real.sinh x) x :=
              (Real.hasDerivAt_cosh x).const_mul 2
            have hlog := h2c.log (by linarith [Real.cosh_pos x])
            have heq : 2 * Real.sinh x / (2 * Real.cosh x) = Real.tanh x := by
              rw [mul_div_mul_left _ _ (by norm_num), Real.tanh_eq_sinh_div_cosh]
            rw [heq] at hlog
            exact hlog
          have h_cont : ContinuousOn (fun y => Real.log (2 * Real.cosh y)) (Icc r₂ r₁) :=
            fun x hx => (h_der x hx).continuousAt.continuousWithinAt
          exact exists_hasDerivAt_eq_slope (fun y => Real.log (2 * Real.cosh y))
                Real.tanh hgt h_cont (fun x hx => h_der x (Ioo_subset_Icc_self hx))
        rcases h_mvt with ⟨c, hc, hc_eq⟩
        dsimp [spinBregman1D] at h_zero
        have hc_gt : Real.tanh r₂ < Real.tanh c := h_conv hc.1
        have h_slope : Real.log (2 * Real.cosh r₁) - Real.log (2 * Real.cosh r₂) =
            Real.tanh c * (r₁ - r₂) := by
          rw [hc_eq, div_mul_cancel₀ _ (by linarith)]
        rw [h_slope] at h_zero
        have : Real.tanh c * (r₁ - r₂) - Real.tanh r₂ * (r₁ - r₂) =
               (Real.tanh c - Real.tanh r₂) * (r₁ - r₂) := by ring
        rw [this] at h_zero
        have h_pos : 0 < (Real.tanh c - Real.tanh r₂) * (r₁ - r₂) :=
          mul_pos (by linarith) (by linarith)
        linarith
    · rintro rfl
      dsimp [spinBregman1D]
      simp only [sub_self, mul_zero]

/-- Lyapunov monotonic decay along the GKSL exponential relaxation trajectory:
    `d/dt D_ψ(r(t), r_eq) ≤ 0`. -/
theorem spin_bregman_lyapunov_decay {r_eq r₀ Γ : ℝ} (hΓ : 0 < Γ) (t : ℝ) :
    let r := fun s => r_eq + (r₀ - r_eq) * Real.exp (-Γ * s)
    HasDerivAt (fun s => spinBregman1D (r s) r_eq)
      (-Γ * (Real.tanh (r t) - Real.tanh r_eq) * (r t - r_eq)) t ∧
    -Γ * (Real.tanh (r t) - Real.tanh r_eq) * (r t - r_eq) ≤ 0 := by
  dsimp only
  let r := fun s => r_eq + (r₀ - r_eq) * Real.exp (-Γ * s)
  have h_exp_der : HasDerivAt (fun s => Real.exp (-Γ * s)) (-Γ * Real.exp (-Γ * t)) t := by
    have h1 : HasDerivAt (fun s => -Γ * s) (-Γ) t := by simpa using (hasDerivAt_id t).const_mul (-Γ)
    have h2 := h1.exp
    have : Real.exp (-Γ * t) * -Γ = -Γ * Real.exp (-Γ * t) := mul_comm _ _
    rwa [this] at h2
  have h_r_der : HasDerivAt r ((r₀ - r_eq) * (-Γ * Real.exp (-Γ * t))) t := by
    have h := (hasDerivAt_const t r_eq).add (h_exp_der.const_mul (r₀ - r_eq))
    rw [zero_add] at h
    exact h
  have h_r_dot : (r₀ - r_eq) * (-Γ * Real.exp (-Γ * t)) = -Γ * (r t - r_eq) := by
    dsimp [r]; ring
  have h_r_der2 : HasDerivAt r (-Γ * (r t - r_eq)) t := by
    rwa [← h_r_dot]
  have h_log_der : HasDerivAt (fun s => Real.log (2 * Real.cosh (r s)))
      (Real.tanh (r t) * (-Γ * (r t - r_eq))) t := by
    have h_cosh := (Real.hasDerivAt_cosh (r t)).const_mul 2
    have h_comp := h_cosh.comp t h_r_der2
    have h_pos : 0 < 2 * Real.cosh (r t) := by linarith [Real.cosh_pos (r t)]
    have h_log := h_comp.log h_pos.ne'
    have h_alg : 2 * Real.sinh (r t) * (-Γ * (r t - r_eq)) / (2 * Real.cosh (r t)) =
        Real.tanh (r t) * (-Γ * (r t - r_eq)) := by
      have h2ne : (2 : ℝ) ≠ 0 := by norm_num
      calc 2 * Real.sinh (r t) * (-Γ * (r t - r_eq)) / (2 * Real.cosh (r t))
          = (2 * (Real.sinh (r t) * (-Γ * (r t - r_eq)))) / (2 * Real.cosh (r t)) := by ring
        _ = (Real.sinh (r t) * (-Γ * (r t - r_eq))) / Real.cosh (r t) := mul_div_mul_left _ _ h2ne
        _ = (Real.sinh (r t) / Real.cosh (r t)) * (-Γ * (r t - r_eq)) := by ring
        _ = Real.tanh (r t) * (-Γ * (r t - r_eq)) := by rw [Real.tanh_eq_sinh_div_cosh]
    change HasDerivAt (fun s => Real.log (2 * Real.cosh (r s)))
      (2 * Real.sinh (r t) * (-Γ * (r t - r_eq)) / (2 * Real.cosh (r t))) t at h_log
    rw [h_alg] at h_log
    exact h_log
  have h_breg_fun : (fun s => spinBregman1D (r s) r_eq) =
      fun s => Real.log (2 * Real.cosh (r s)) - Real.log (2 * Real.cosh r_eq) -
               Real.tanh r_eq * (r s - r_eq) := by
    ext s; rfl
  rw [h_breg_fun]
  have h_sub_der : HasDerivAt (fun s => Real.tanh r_eq * (r s - r_eq))
      (Real.tanh r_eq * (-Γ * (r t - r_eq))) t := by
    have h1 := h_r_der2.sub_const r_eq
    exact h1.const_mul (Real.tanh r_eq)
  have h_tot_der := (h_log_der.sub_const (Real.log (2 * Real.cosh r_eq))).sub h_sub_der
  have h_tot_alg : Real.tanh (r t) * (-Γ * (r t - r_eq)) - Real.tanh r_eq * (-Γ * (r t - r_eq)) =
      -Γ * (Real.tanh (r t) - Real.tanh r_eq) * (r t - r_eq) := by ring
  rw [h_tot_alg] at h_tot_der
  refine ⟨h_tot_der, ?_⟩
  · have h_conv := strictMono_tanh
    have h_prod_nonneg : 0 ≤ (Real.tanh (r t) - Real.tanh r_eq) * (r t - r_eq) := by
      rcases lt_trichotomy (r t) r_eq with hlt | heq | hgt
      · have : Real.tanh (r t) < Real.tanh r_eq := h_conv hlt
        have h1 : Real.tanh (r t) - Real.tanh r_eq < 0 := by linarith
        have h2 : r t - r_eq < 0 := by linarith
        nlinarith
      · rw [heq]; simp
      · have : Real.tanh r_eq < Real.tanh (r t) := h_conv hgt
        have h1 : 0 < Real.tanh (r t) - Real.tanh r_eq := by linarith
        have h2 : 0 < r t - r_eq := by linarith
        nlinarith
    have h_neg_gamma : -Γ < 0 := neg_lt_zero.mpr hΓ
    have : -Γ * (Real.tanh (r t) - Real.tanh r_eq) * (r t - r_eq) =
           -Γ * ((Real.tanh (r t) - Real.tanh r_eq) * (r t - r_eq)) := by ring
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg h_neg_gamma.le h_prod_nonneg

/-- Combined Bregman nonnegativity and Lyapunov monotonic decay theorem. -/
theorem spin_bregman_nonneg_and_lyapunov_decay {r_eq r₀ Γ : ℝ} (hΓ : 0 < Γ) (t : ℝ) :
    let r := fun s => r_eq + (r₀ - r_eq) * Real.exp (-Γ * s)
    0 ≤ spinBregman1D (r t) r_eq ∧
    -Γ * (Real.tanh (r t) - Real.tanh r_eq) * (r t - r_eq) ≤ 0 := by
  dsimp only
  exact ⟨(spin_bregman_nonneg (r_eq + (r₀ - r_eq) * Real.exp (-Γ * t)) r_eq).1,
         (spin_bregman_lyapunov_decay hΓ t).2⟩

/-! ### Part V: OpenGauss T16 Non-Commutativity Witness -/

/-- OpenGauss T16 non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`:
    the spin ladder operators `M_up` and `M_down` do not commute. -/
lemma kms_bath_matrix_noncomm : ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨M_up, M_down, ?_⟩
  intro h
  have h00 : (M_up * M_down) 0 0 = (M_down * M_up) 0 0 := by rw [h]
  have h1 : (M_up * M_down) 0 0 = 1 := by
    dsimp [M_up, M_down]
    simp [Matrix.mul_apply, Matrix.of_apply]
  have h2 : (M_down * M_up) 0 0 = 0 := by
    dsimp [M_up, M_down]
    simp [Matrix.mul_apply, Matrix.of_apply]
  rw [h1, h2] at h00
  norm_num at h00

end InfoGeometry.OperatorAlgebra.PeirceBiSandwich
