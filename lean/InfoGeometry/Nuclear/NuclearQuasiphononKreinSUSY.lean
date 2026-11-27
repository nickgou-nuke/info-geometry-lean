/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases
import InfoGeometry.Canonical.ComplexMatrixModularFlowAndCStarPolar
import InfoGeometry.Modular.MatrixConnesRadonNikodymCocycle
import InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Matrix

/-!
# Nuclear Quasiphonon Krein SUSY

This module formalizes Target 1 (Section 80):
Nuclear Quasiphonon Krein SUSY: Quasiparticle-Phonon Coupling, Doubled Real Krein Space,
Real Pseudo-SUSY Supercharges, and Affine Soloviev-BdG Identification.

## Mathematical Architecture:
1. **The Doubled Real Krein Supercarrier & Fundamental Involutions**:
   Graded Krein carrier `Matrix (V_b ⊕ V_f) (V_b ⊕ V_f) R` equipped with the fundamental
   grading metric `J = diag(I, -I) = fromBlocks 1 0 0 (-1)`, involutive `J² = 1`, and the
   paracomplex sheet swap `S = fromBlocks 0 1 1 0` with `S² = 1` and `{J, S} = 0`.
2. **Real Pseudo-SUSY Supercharges and SUSY Hamiltonian**:
   Nilpotent off-diagonal supercharges `Q` and `Q†` constructed from particle-phonon coupling
   matrix `V_coup : Matrix V_b V_f R`, satisfying `Q² = 0` and `(Q†)² = 0`. The supersymmetric
   Hamiltonian `H = {Q, Q†}` is block-diagonal `fromBlocks (V Vᵀ) 0 0 (Vᵀ V)` and satisfies exact
   SUSY conservation `[H, Q] = 0` and `[H, Q†] = 0`.
3. **Exact Affine Soloviev QPNM to BdG Decomposition**:
   Affine decomposition of Soloviev Quasiparticle-Phonon Nuclear Model (QPNM) matrix into
   a scalar center and a traceless Bogoliubov-de Gennes (BdG) Hamiltonian block, satisfying
   the characteristic polynomial `H_BdG² = (δ² + V²) I`, Andreev reflection reversal,
   `Tr(H_BdG) = 0`, and `det(H_BdG) = -(δ² + V²)`.
-/

namespace InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY

/-! ### Section 1: The Doubled Real Krein Supercarrier & Fundamental Involutions -/

/-- Fundamental Krein metric on the graded supercarrier `Matrix (V_b ⊕ V_f) (V_b ⊕ V_f) R`. -/
def kreinMetric (V_b V_f : Type*) [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    (R : Type*) [Ring R] : Matrix (V_b ⊕ V_f) (V_b ⊕ V_f) R :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Involutive property of the fundamental Krein metric: `J² = 1`. -/
theorem kreinMetric_sq (V_b V_f : Type*) [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    (R : Type*) [Ring R] :
    (kreinMetric V_b V_f R) * (kreinMetric V_b V_f R) = 1 := by
  rw [kreinMetric, Matrix.fromBlocks_multiply]
  simp

/-- Paracomplex sheet-swap operator on the balanced doubled carrier `(V ⊕ V)`. -/
def sheetSwap (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [Ring R] :
    Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 1 1 0

/-- Involutive property of the paracomplex sheet swap: `S² = 1`. -/
theorem sheetSwap_sq (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [Ring R] :
    (sheetSwap V R) * (sheetSwap V R) = 1 := by
  rw [sheetSwap, Matrix.fromBlocks_multiply]
  simp

/-- Exact anticommutation between the Krein metric and the sheet-swap operator: `{J, S} = 0`. -/
theorem krein_sheetSwap_anticomm (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [Ring R] :
    (kreinMetric V V R) * (sheetSwap V R) + (sheetSwap V R) * (kreinMetric V V R) = 0 := by
  rw [kreinMetric, sheetSwap, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp

/-! ### Section 2: Real Pseudo-SUSY Supercharges and SUSY Hamiltonian -/

/-- Real supercharge Q mapping fermionic phonons to bosonic quasiparticles. -/
def superchargeQ {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [Ring R] (V_coup : Matrix V_b V_f R) : Matrix (V_b ⊕ V_f) (V_b ⊕ V_f) R :=
  Matrix.fromBlocks 0 V_coup 0 0

/-- Transposed conjugate supercharge Q† mapping bosonic quasiparticles to fermionic phonons. -/
def superchargeQ_dag {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [Ring R] (V_coup : Matrix V_b V_f R) : Matrix (V_b ⊕ V_f) (V_b ⊕ V_f) R :=
  Matrix.fromBlocks 0 0 V_coupᵀ 0

/-- Nilpotence of the real supercharge: `Q² = 0`. -/
theorem superchargeQ_sq {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [Ring R] (V_coup : Matrix V_b V_f R) :
    (superchargeQ V_coup) * (superchargeQ V_coup) = 0 := by
  rw [superchargeQ, Matrix.fromBlocks_multiply]
  simp

/-- Nilpotence of the conjugate supercharge: `(Q†)² = 0`. -/
theorem superchargeQ_dag_sq {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [Ring R] (V_coup : Matrix V_b V_f R) :
    (superchargeQ_dag V_coup) * (superchargeQ_dag V_coup) = 0 := by
  rw [superchargeQ_dag, Matrix.fromBlocks_multiply]
  simp

/-- Supersymmetric Hamiltonian defined by anticommutator `{Q, Q†} = Q Q† + Q† Q`. -/
def susyHamiltonian {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [Ring R] (V_coup : Matrix V_b V_f R) : Matrix (V_b ⊕ V_f) (V_b ⊕ V_f) R :=
  (superchargeQ V_coup) * (superchargeQ_dag V_coup) + (superchargeQ_dag V_coup) * (superchargeQ V_coup)

/-- Exact block diagonal decomposition of the supersymmetric Hamiltonian. -/
theorem susyHamiltonian_blocks {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [Ring R] (V_coup : Matrix V_b V_f R) :
    susyHamiltonian V_coup = Matrix.fromBlocks (V_coup * V_coupᵀ) 0 0 (V_coupᵀ * V_coup) := by
  rw [susyHamiltonian, superchargeQ, superchargeQ_dag, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp

/-- Commutation and conservation of supercharge Q with the SUSY Hamiltonian: `[H, Q] = 0`. -/
theorem susyHamiltonian_comm_Q {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [Ring R] (V_coup : Matrix V_b V_f R) :
    (susyHamiltonian V_coup) * (superchargeQ V_coup) - (superchargeQ V_coup) * (susyHamiltonian V_coup) = 0 := by
  rw [susyHamiltonian_blocks, superchargeQ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [Matrix.mul_assoc]

/-- Commutation and conservation of conjugate supercharge Q† with the SUSY Hamiltonian: `[H, Q†] = 0`. -/
theorem susyHamiltonian_comm_Q_dag {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [Ring R] (V_coup : Matrix V_b V_f R) :
    (susyHamiltonian V_coup) * (superchargeQ_dag V_coup) - (superchargeQ_dag V_coup) * (susyHamiltonian V_coup) = 0 := by
  rw [susyHamiltonian_blocks, superchargeQ_dag, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [Matrix.mul_assoc]

/-! ### Section 3: Exact Affine Soloviev QPNM to BdG Decomposition -/

/-- 2x2 Soloviev Quasiparticle-Phonon Nuclear Model (QPNM) Hamiltonian matrix. -/
def qpnmMatrix {R : Type*} [Ring R] (Eqp omega V : R) : Matrix (Fin 2) (Fin 2) R :=
  !![Eqp, V; V, Eqp + omega]

/-- Central scalar shift of the Soloviev Hamiltonian: `Eqp + ω / 2`. -/
def solovievCenter {R : Type*} [Ring R] [Invertible (2 : R)] (Eqp omega : R) : R :=
  Eqp + ⅟(2 : R) * omega

/-- Traceless Bogoliubov-de Gennes (BdG) Hamiltonian block. -/
def bdgBlock {R : Type*} [Ring R] (delta V : R) : Matrix (Fin 2) (Fin 2) R :=
  !![delta, V; V, -delta]

/-- Exact affine decomposition of the Soloviev QPNM Hamiltonian into scalar center and BdG block. -/
theorem qpnm_affine_bdg {R : Type*} [Ring R] [Invertible (2 : R)] (Eqp omega V : R) :
    qpnmMatrix Eqp omega V = (solovievCenter Eqp omega) • (1 : Matrix (Fin 2) (Fin 2) R) + bdgBlock (- ⅟(2 : R) * omega) V := by
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  ext i j
  fin_cases i <;> fin_cases j
  · simp [qpnmMatrix, solovievCenter, bdgBlock]
  · simp [qpnmMatrix, solovievCenter, bdgBlock]
  · simp [qpnmMatrix, solovievCenter, bdgBlock]
  · simp [qpnmMatrix, solovievCenter, bdgBlock]
    calc Eqp + omega = Eqp + (⅟(2 : R) * 2) * omega := by rw [h2, one_mul]
    _ = Eqp + ⅟(2 : R) * omega + ⅟(2 : R) * omega := by noncomm_ring

/-- Squaring of the BdG Hamiltonian block yielding the relativistic dispersion scalar: `H_BdG² = (δ² + V²) I`. -/
theorem bdgBlock_sq {R : Type*} [CommRing R] (delta V : R) :
    (bdgBlock delta V) * (bdgBlock delta V) = (delta^2 + V^2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [bdgBlock, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  }

/-- Pauli tau_1 matrix representing the particle-hole / Andreev reflection generator. -/
def tau1 (R : Type*) [Ring R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

/-- Involutive property of the Andreev generator: `τ₁² = 1`. -/
theorem tau1_sq (R : Type*) [Ring R] : (tau1 R) * (tau1 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tau1, Matrix.mul_apply, Fin.sum_univ_two]

/-- Andreev particle-hole sign reversal of the BdG block under τ₁ conjugation: `τ₁ H(δ, V) τ₁ = - H(δ, -V)`. -/
theorem andreev_bdg_sign_reversal {R : Type*} [Ring R] (delta V : R) :
    (tau1 R) * (bdgBlock delta V) * (tau1 R) = - bdgBlock delta (-V) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tau1, bdgBlock, Matrix.mul_apply, Fin.sum_univ_two]

/-- Andreev particle-hole swap of the energy gap under τ₁ conjugation: `τ₁ H(δ, V) τ₁ = H(-δ, V)`. -/
theorem andreev_bdg_swap {R : Type*} [Ring R] (delta V : R) :
    (tau1 R) * (bdgBlock delta V) * (tau1 R) = bdgBlock (-delta) V := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tau1, bdgBlock, Matrix.mul_apply, Fin.sum_univ_two]

/-- Tracelessness of the BdG block: `Tr(H_BdG) = 0`. -/
theorem bdgBlock_traceless {R : Type*} [Ring R] (delta V : R) :
    Matrix.trace (bdgBlock delta V) = 0 := by
  simp [Matrix.trace, Matrix.diag, bdgBlock, Fin.sum_univ_two]

/-- Exact determinant of the BdG block: `det(H_BdG) = -(δ² + V²)`. -/
theorem bdgBlock_det {R : Type*} [CommRing R] (delta V : R) :
    Matrix.det (bdgBlock delta V) = - (delta^2 + V^2) := by
  rw [bdgBlock, Matrix.det_fin_two_of]
  ring


/-- Closed noncommutativity witness for `Matrix (Fin 2) (Fin 2) R` (Trap T16):
the elementary upper and lower shear matrices do not commute. -/
def ncShearA (R : Type*) [Ring R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]
def ncShearB (R : Type*) [Ring R] : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, 0]

theorem qpnm_noncommutativity_witness {R : Type*} [Ring R] [Nontrivial R] :
    ncShearA (R := R) * ncShearB (R := R) ≠ ncShearB (R := R) * ncShearA (R := R) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  simp [ncShearA, ncShearB, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-! ### Section 4: Dynamic Modular Two-Sheeted SUSY Flow & Connes Cocycle Intertwining -/

section DynamicModularSUSY

open Complex
open scoped Matrix.Norms.L2Operator
open InfoGeometry.Canonical.ComplexMatrixModularFlowAndCStarPolar
open InfoGeometry.Modular.ConnesCocycle
open InfoGeometry.Modular.MatrixConnesRadonNikodymCocycle
open InfoGeometry.SuperGrassmannian.NuclearQuasiphononSuperGrassmannian

section CommuteExp

variable {n : ℕ}

/-- Any matrix `X` commuting with `H` commutes with the unitary exponential `uExp H t`. -/
theorem commute_uExp_of_commute (H X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hcomm : Commute H X) : Commute (uExp H t) X := by
  let _ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  unfold uExp Commute SemiconjBy
  set A : Matrix (Fin n) (Fin n) ℂ := (Complex.I * (t : ℂ)) • H
  have hA : Commute A X := hcomm.smul_left (Complex.I * (t : ℂ))
  have hs : Summable (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • A ^ k) := by
    simpa [NormedSpace.expSeries_apply_eq] using NormedSpace.expSeries_summable (𝕂 := ℂ) A
  have hexp : NormedSpace.exp A = ∑' k : ℕ, (Nat.factorial k : ℂ)⁻¹ • A ^ k := by
    simpa [NormedSpace.expSeries_apply_eq] using congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℂ)) A
  have hL : HasSum (fun k : ℕ => ((Nat.factorial k : ℂ)⁻¹ • A ^ k) * X) (NormedSpace.exp A * X) := by
    rw [hexp]
    exact hs.hasSum.mul_right X
  have hR : HasSum (fun k : ℕ => X * ((Nat.factorial k : ℂ)⁻¹ • A ^ k)) (X * NormedSpace.exp A) := by
    rw [hexp]
    exact hs.hasSum.mul_left X
  have hterm : (fun k : ℕ => ((Nat.factorial k : ℂ)⁻¹ • A ^ k) * X) =
      (fun k : ℕ => X * ((Nat.factorial k : ℂ)⁻¹ • A ^ k)) := by
    funext k
    rw [smul_mul_assoc, mul_smul_comm, (hA.pow_left k).eq]
  rw [hterm] at hL
  exact hL.unique hR

/-- Any matrix `X` commuting with `H` is fixed by the modular automorphism flow `σ_t^H`. -/
theorem matrixModularFlow_eq_self_of_commute (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (hcomm : Commute H X) :
    matrixModularFlow H hH t X = X := by
  rw [matrixModularFlow_apply, (commute_uExp_of_commute H X t hcomm).eq, Matrix.mul_assoc,
    ← uExp_add, add_neg_cancel, uExp_zero, Matrix.mul_one]

end CommuteExp

section ArbitraryIndexSUSYFlow

variable {ι₀ ι₁ : Type*} [DecidableEq ι₀] [Fintype ι₀] [DecidableEq ι₁] [Fintype ι₁]

/-- Canonical finite index equivalence `ι₀ ⊕ ι₁ ≃ Fin (|ι₀| + |ι₁|)`. -/
noncomputable def sumFinEquiv (ι₀ ι₁ : Type*) [Fintype ι₀] [Fintype ι₁] :
    ι₀ ⊕ ι₁ ≃ Fin (Fintype.card ι₀ + Fintype.card ι₁) :=
  ((Fintype.equivFin ι₀).sumCongr (Fintype.equivFin ι₁)).trans finSumFinEquiv

/-- Star-algebra equivalence reindexing `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ` onto
`Matrix (Fin (|ι₀| + |ι₁|)) (Fin (|ι₀| + |ι₁|)) ℂ`. -/
noncomputable def sumMatEquiv (ι₀ ι₁ : Type*) [DecidableEq ι₀] [Fintype ι₀]
    [DecidableEq ι₁] [Fintype ι₁] :
    Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ ≃⋆ₐ[ℂ]
      Matrix (Fin (Fintype.card ι₀ + Fintype.card ι₁))
        (Fin (Fintype.card ι₀ + Fintype.card ι₁)) ℂ where
  toFun := Matrix.reindex (sumFinEquiv ι₀ ι₁) (sumFinEquiv ι₀ ι₁)
  invFun := Matrix.reindex (sumFinEquiv ι₀ ι₁).symm (sumFinEquiv ι₀ ι₁).symm
  left_inv M := by simp
  right_inv M := by simp
  map_mul' M N := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.reindex_apply]
    exact (Fintype.sum_equiv (sumFinEquiv ι₀ ι₁).symm _ _ (fun _ => rfl)).symm
  map_add' M N := by ext i j; rfl
  map_smul' c M := by ext i j; rfl
  map_star' M := by ext i j; rfl

/-- Complexified supercharge `Q(V)` on `ι₀ ⊕ ι₁` for a real coupling `V : Matrix ι₀ ι₁ ℝ`. -/
def susyQ_ℂ (V : Matrix ι₀ ι₁ ℝ) : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ :=
  superchargeQ (V.map Complex.ofReal)

/-- Complexified conjugate supercharge `Q†(V)` on `ι₀ ⊕ ι₁`. -/
def susyQ_dag_ℂ (V : Matrix ι₀ ι₁ ℝ) : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ :=
  superchargeQ_dag (V.map Complex.ofReal)

/-- Complexified SUSY Hamiltonian `H(V) = {Q(V), Q†(V)}` on `ι₀ ⊕ ι₁`. -/
def susyH_ℂ (V : Matrix ι₀ ι₁ ℝ) : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ :=
  susyHamiltonian (V.map Complex.ofReal)

/-- Reindexed supercharge `Q(V)` on `Fin (|ι₀| + |ι₁|)`. -/
noncomputable def susyQ_fin (V : Matrix ι₀ ι₁ ℝ) :
    Matrix (Fin (Fintype.card ι₀ + Fintype.card ι₁))
      (Fin (Fintype.card ι₀ + Fintype.card ι₁)) ℂ :=
  sumMatEquiv ι₀ ι₁ (susyQ_ℂ V)

/-- Reindexed conjugate supercharge `Q†(V)` on `Fin (|ι₀| + |ι₁|)`. -/
noncomputable def susyQ_dag_fin (V : Matrix ι₀ ι₁ ℝ) :
    Matrix (Fin (Fintype.card ι₀ + Fintype.card ι₁))
      (Fin (Fintype.card ι₀ + Fintype.card ι₁)) ℂ :=
  sumMatEquiv ι₀ ι₁ (susyQ_dag_ℂ V)

/-- Reindexed SUSY Hamiltonian `H(V)` on `Fin (|ι₀| + |ι₁|)`. -/
noncomputable def susyH_fin (V : Matrix ι₀ ι₁ ℝ) :
    Matrix (Fin (Fintype.card ι₀ + Fintype.card ι₁))
      (Fin (Fintype.card ι₀ + Fintype.card ι₁)) ℂ :=
  sumMatEquiv ι₀ ι₁ (susyH_ℂ V)

/-- Reindexed Krein grading metric `J = diag(I, -I)` on `Fin (|ι₀| + |ι₁|)`. -/
noncomputable def kreinMetric_fin (ι₀ ι₁ : Type*) [DecidableEq ι₀] [Fintype ι₀]
    [DecidableEq ι₁] [Fintype ι₁] :
    Matrix (Fin (Fintype.card ι₀ + Fintype.card ι₁))
      (Fin (Fintype.card ι₀ + Fintype.card ι₁)) ℂ :=
  sumMatEquiv ι₀ ι₁ (kreinMetric ι₀ ι₁ ℂ)

private theorem real_map_conjTranspose (V : Matrix ι₀ ι₁ ℝ) :
    (V.map Complex.ofReal)ᴴ = (V.map Complex.ofReal)ᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]

private theorem real_map_transpose_conjTranspose (V : Matrix ι₀ ι₁ ℝ) :
    ((V.map Complex.ofReal)ᵀ)ᴴ = V.map Complex.ofReal := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]

/-- `susyH_fin V` is Hermitian for every real coupling matrix `V : Matrix ι₀ ι₁ ℝ`. -/
theorem susyH_fin_isHermitian (V : Matrix ι₀ ι₁ ℝ) : (susyH_fin V).IsHermitian := by
  change star (sumMatEquiv ι₀ ι₁ (susyH_ℂ V)) = sumMatEquiv ι₀ ι₁ (susyH_ℂ V)
  rw [← map_star]
  congr 1
  change (susyH_ℂ V)ᴴ = susyH_ℂ V
  unfold susyH_ℂ
  rw [susyHamiltonian_blocks, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, real_map_conjTranspose,
    real_map_transpose_conjTranspose]
  simp only [Matrix.conjTranspose_zero]

private theorem susyH_ℂ_comm_kreinMetric (V : Matrix ι₀ ι₁ ℝ) :
    Commute (susyH_ℂ V) (kreinMetric ι₀ ι₁ ℂ) := by
  unfold Commute SemiconjBy susyH_ℂ kreinMetric
  rw [susyHamiltonian_blocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- The modular flow generated by `susyH_fin V` leaves `susyH_fin V` invariant. -/
theorem matrixModularFlow_susyH_fin_self (V : Matrix ι₀ ι₁ ℝ) (t : ℝ) :
    matrixModularFlow (susyH_fin V) (susyH_fin_isHermitian V) t (susyH_fin V) = susyH_fin V := by
  apply matrixModularFlow_eq_self_of_commute
  exact Commute.refl _

/-- The modular flow generated by `susyH_fin V` leaves `susyQ_fin V` invariant. -/
theorem matrixModularFlow_susyH_fin_Q (V : Matrix ι₀ ι₁ ℝ) (t : ℝ) :
    matrixModularFlow (susyH_fin V) (susyH_fin_isHermitian V) t (susyQ_fin V) = susyQ_fin V := by
  apply matrixModularFlow_eq_self_of_commute
  unfold Commute SemiconjBy susyH_fin susyQ_fin susyH_ℂ susyQ_ℂ
  rw [← map_mul, ← map_mul]
  congr 1
  exact sub_eq_zero.mp (susyHamiltonian_comm_Q (V.map Complex.ofReal))

/-- The modular flow generated by `susyH_fin V` leaves `susyQ_dag_fin V` invariant. -/
theorem matrixModularFlow_susyH_fin_Q_dag (V : Matrix ι₀ ι₁ ℝ) (t : ℝ) :
    matrixModularFlow (susyH_fin V) (susyH_fin_isHermitian V) t (susyQ_dag_fin V) =
      susyQ_dag_fin V := by
  apply matrixModularFlow_eq_self_of_commute
  unfold Commute SemiconjBy susyH_fin susyQ_dag_fin susyH_ℂ susyQ_dag_ℂ
  rw [← map_mul, ← map_mul]
  congr 1
  exact sub_eq_zero.mp (susyHamiltonian_comm_Q_dag (V.map Complex.ofReal))

/-- The modular flow generated by `susyH_fin V` leaves `kreinMetric_fin ι₀ ι₁` invariant. -/
theorem matrixModularFlow_susyH_fin_kreinMetric (V : Matrix ι₀ ι₁ ℝ) (t : ℝ) :
    matrixModularFlow (susyH_fin V) (susyH_fin_isHermitian V) t (kreinMetric_fin ι₀ ι₁) =
      kreinMetric_fin ι₀ ι₁ := by
  apply matrixModularFlow_eq_self_of_commute
  unfold Commute SemiconjBy susyH_fin kreinMetric_fin
  rw [← map_mul, ← map_mul]
  congr 1
  exact (susyH_ℂ_comm_kreinMetric V).eq

/-- Exact representation of `superTrace` as `Tr(kreinMetric * M)`. -/
theorem superTrace_eq_trace_kreinMetric (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    superTrace M = (kreinMetric ι₀ ι₁ ℂ * M).trace := by
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks M).symm
  conv_rhs => rw [hM]
  unfold kreinMetric superTrace
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.neg_mul, zero_add]
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, sub_eq_add_neg]

private theorem sumMatEquiv_trace (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    (sumMatEquiv ι₀ ι₁ M).trace = M.trace := by
  change ∑ i, Matrix.reindex (sumFinEquiv ι₀ ι₁) (sumFinEquiv ι₀ ι₁) M i i = ∑ j, M j j
  simp only [Matrix.reindex_apply]
  exact Fintype.sum_equiv (sumFinEquiv ι₀ ι₁).symm _ _ (fun _ => rfl)

private theorem commute_kreinMetric_fin_of_uExp (V : Matrix ι₀ ι₁ ℝ) (t : ℝ) :
    Commute (uExp (susyH_fin V) t) (kreinMetric_fin ι₀ ι₁) := by
  apply commute_uExp_of_commute
  unfold Commute SemiconjBy susyH_fin kreinMetric_fin
  rw [← map_mul, ← map_mul]
  congr 1
  exact (susyH_ℂ_comm_kreinMetric V).eq

/-- Exact supertrace invariance under the dynamic modular flow `matrixModularFlow (susyH_fin V) _ t`. -/
theorem matrixModularFlow_susyH_fin_preserves_superTrace (V : Matrix ι₀ ι₁ ℝ) (t : ℝ)
    (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    superTrace ((sumMatEquiv ι₀ ι₁).symm
      (matrixModularFlow (susyH_fin V) (susyH_fin_isHermitian V) t (sumMatEquiv ι₀ ι₁ M))) =
      superTrace M := by
  rw [superTrace_eq_trace_kreinMetric, superTrace_eq_trace_kreinMetric]
  rw [← sumMatEquiv_trace, ← sumMatEquiv_trace]
  rw [map_mul, map_mul]
  change (kreinMetric_fin ι₀ ι₁ *
    (sumMatEquiv ι₀ ι₁ ((sumMatEquiv ι₀ ι₁).symm
      (matrixModularFlow (susyH_fin V) (susyH_fin_isHermitian V) t (sumMatEquiv ι₀ ι₁ M))))).trace =
    (kreinMetric_fin ι₀ ι₁ * sumMatEquiv ι₀ ι₁ M).trace
  rw [(sumMatEquiv ι₀ ι₁).apply_symm_apply, matrixModularFlow_apply]
  have hcomm := (commute_kreinMetric_fin_of_uExp V t).eq
  have hcommNeg := (commute_kreinMetric_fin_of_uExp V (-t)).eq
  calc
    (kreinMetric_fin ι₀ ι₁ * (uExp (susyH_fin V) t * sumMatEquiv ι₀ ι₁ M * uExp (susyH_fin V) (-t))).trace
        = ((kreinMetric_fin ι₀ ι₁ * uExp (susyH_fin V) t * sumMatEquiv ι₀ ι₁ M) *
            uExp (susyH_fin V) (-t)).trace := by
          simp only [Matrix.mul_assoc]
    _ = (uExp (susyH_fin V) (-t) *
          (kreinMetric_fin ι₀ ι₁ * uExp (susyH_fin V) t * sumMatEquiv ι₀ ι₁ M)).trace :=
        Matrix.trace_mul_comm _ _
    _ = ((uExp (susyH_fin V) (-t) * uExp (susyH_fin V) t) *
          kreinMetric_fin ι₀ ι₁ * sumMatEquiv ι₀ ι₁ M).trace := by
        rw [← hcomm]
        simp only [Matrix.mul_assoc]
    _ = (kreinMetric_fin ι₀ ι₁ * sumMatEquiv ι₀ ι₁ M).trace := by
        rw [← uExp_add, neg_add_cancel, uExp_zero, Matrix.one_mul]

/-- Constructive Connes 1-cocycle between two coupling matrices `V₁, V₂ : Matrix ι₀ ι₁ ℝ`. -/
noncomputable def susyConnesOneCocycle (V₁ V₂ : Matrix ι₀ ι₁ ℝ) :
    ConnesOneCocycle (matrixModularFlow (susyH_fin V₂) (susyH_fin_isHermitian V₂)) :=
  matrixConnesOneCocycle (susyH_fin V₁) (susyH_fin V₂)
    (susyH_fin_isHermitian V₁) (susyH_fin_isHermitian V₂)

/-- The Connes Radon–Nikodym cocycle between any two couplings `V₁, V₂` is grading-even
(commutes with `kreinMetric_fin`). -/
theorem commute_connesCocycleMatrix_kreinMetric_fin (V₁ V₂ : Matrix ι₀ ι₁ ℝ) (t : ℝ) :
    Commute (connesCocycleMatrix (susyH_fin V₁) (susyH_fin V₂) t) (kreinMetric_fin ι₀ ι₁) := by
  unfold connesCocycleMatrix
  exact (commute_kreinMetric_fin_of_uExp V₁ t).mul_left (commute_kreinMetric_fin_of_uExp V₂ (-t))

/-- Conjugation by the Connes cocycle `(D_{V₁} : D_{V₂})_t` strictly preserves `superTrace`. -/
theorem connesCocycleMatrix_susy_preserves_superTrace (V₁ V₂ : Matrix ι₀ ι₁ ℝ) (t : ℝ)
    (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    let u := connesCocycleMatrix (susyH_fin V₁) (susyH_fin V₂) t
    superTrace ((sumMatEquiv ι₀ ι₁).symm (u * sumMatEquiv ι₀ ι₁ M * uᴴ)) = superTrace M := by
  intro u
  rw [superTrace_eq_trace_kreinMetric, superTrace_eq_trace_kreinMetric]
  rw [← sumMatEquiv_trace, ← sumMatEquiv_trace, map_mul]
  conv_rhs => rw [map_mul]
  rw [(sumMatEquiv ι₀ ι₁).apply_symm_apply]
  change (kreinMetric_fin ι₀ ι₁ * (u * sumMatEquiv ι₀ ι₁ M * uᴴ)).trace =
    (kreinMetric_fin ι₀ ι₁ * sumMatEquiv ι₀ ι₁ M).trace
  have hcomm := (commute_connesCocycleMatrix_kreinMetric_fin V₁ V₂ t).eq
  have hunit : uᴴ * u = 1 :=
    (susyConnesOneCocycle V₁ V₂).unitary_right t
  calc
    (kreinMetric_fin ι₀ ι₁ * (u * sumMatEquiv ι₀ ι₁ M * uᴴ)).trace
        = ((kreinMetric_fin ι₀ ι₁ * u * sumMatEquiv ι₀ ι₁ M) * uᴴ).trace := by
          simp only [Matrix.mul_assoc]
    _ = (uᴴ * (kreinMetric_fin ι₀ ι₁ * u * sumMatEquiv ι₀ ι₁ M)).trace :=
        Matrix.trace_mul_comm _ _
    _ = ((uᴴ * u) * kreinMetric_fin ι₀ ι₁ * sumMatEquiv ι₀ ι₁ M).trace := by
        rw [show u = connesCocycleMatrix (susyH_fin V₁) (susyH_fin V₂) t from rfl]
        rw [← hcomm]
        simp only [Matrix.mul_assoc]
    _ = (kreinMetric_fin ι₀ ι₁ * sumMatEquiv ι₀ ι₁ M).trace := by
        rw [hunit, Matrix.one_mul]

/-- The Connes cocycle `connesCocycleMatrix (susyH_fin V₁) (susyH_fin V₂) t` intertwines
the two dynamic SUSY modular flows `matrixModularFlow (susyH_fin V₁)` and
`matrixModularFlow (susyH_fin V₂)`. -/
theorem connesCocycleMatrix_susy_intertwines (V₁ V₂ : Matrix ι₀ ι₁ ℝ) (t : ℝ)
    (X : Matrix (Fin (Fintype.card ι₀ + Fintype.card ι₁))
      (Fin (Fintype.card ι₀ + Fintype.card ι₁)) ℂ) :
    matrixModularFlow (susyH_fin V₁) (susyH_fin_isHermitian V₁) t X *
        connesCocycleMatrix (susyH_fin V₁) (susyH_fin V₂) t =
      connesCocycleMatrix (susyH_fin V₁) (susyH_fin V₂) t *
        matrixModularFlow (susyH_fin V₂) (susyH_fin_isHermitian V₂) t X := by
  have h := matrixConnesCocycleData_intertwines (susyH_fin V₁) (susyH_fin V₂)
    (susyH_fin_isHermitian V₁) (susyH_fin_isHermitian V₂) t X
  exact h

theorem perturbedFlow_susyConnesOneCocycle_eq (V₁ V₂ : Matrix ι₀ ι₁ ℝ) (t : ℝ)
    (X : Matrix (Fin (Fintype.card ι₀ + Fintype.card ι₁))
      (Fin (Fintype.card ι₀ + Fintype.card ι₁)) ℂ) :
    perturbedFlow (susyConnesOneCocycle V₁ V₂) t X =
      matrixModularFlow (susyH_fin V₁) (susyH_fin_isHermitian V₁) t X := by
  have h := matrixConnes_perturbedFlow_eq (susyH_fin V₁) (susyH_fin V₂)
    (susyH_fin_isHermitian V₁) (susyH_fin_isHermitian V₂) t X
  exact h

end ArbitraryIndexSUSYFlow

end DynamicModularSUSY

end InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY
