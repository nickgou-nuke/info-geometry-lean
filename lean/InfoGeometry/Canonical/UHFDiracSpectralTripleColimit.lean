/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.UHFColimitCStarCompletion
import InfoGeometry.Canonical.UHFTracialStateCore
import InfoGeometry.Canonical.Cl11DiracGeneratorCore
import InfoGeometry.Canonical.ConnesInfimumDistance
import InfoGeometry.Prequantum.GNSQuotientStrictPositivity

/-!
# Jaynesian Inductive UHF Dirac Spectral-Triple Colimit & Tracial GNS Bridge (`D19`)

Constructively discharges the inductive bounded Dirac operator tower,
commutator-norm transport, Connes spectral-distance colimit transport, and
tracial-state / GNS strict-positivity faithfulness bridge purely in the
`2^∞` Jaynesian inductive colimit (`UHFStage n → UHFAlg`), without positing
any `UniformSpace.Completion` / Cauchy completion or non-inductive Hilbert
continuum.

Specifically:
1. `uhfDirac n : UHFStage (n + 1)` embeds `diracGenerator` (Pauli `X`) along
   the block-doubling embeddings `uhfStep`, satisfying `uhfDirac_compat`,
   `uhfDirac_selfAdjoint`, `uhfDirac_sq`, `uhfDirac_norm`, and an explicit
   unit-commutator non-commutativity witness `uhfDirac_noncomm`.
2. `uhfCommutatorNorm_bound`, `uhfCommutatorNorm_transport`, and
   `uhfLipschitzBall_transport` prove the uniform bound `‖[Dₙ, A]‖ ≤ 2‖A‖`
   and exact invariance under `uhfStep`.
3. `uhfColimitDirac : UHFAlg` lifts the inductive Dirac family into the
   pure directed Jaynesian colimit algebra `UHFAlg`.
4. `uhfStateDistanceBound_step`, `uhfConnesInfDistance_step_le`,
   `uhfStateDistanceBound_colimit`, and `uhfConnesInfDistance_stage_le_colimit`
   transport Connes Lipschitz distance bounds across stages and `UHFAlg`.
5. `uhfTracialState_compat`, `uhfColimitTrace`,
   `stageOne_connesInfDistance_topLeft_trace` (`= 1 / 2`), and
   `uhfStageRealState_gns_strict_positivity` / `uhfColimitTrace_faithful`
   close the compatible tracial-state net and GNS quotient faithfulness lane.

Note on scope: under the repository's colimit-continuum law, the directed
colimit `UHFAlg` is the Jaynesian inductive colimit — the sole admissible
infinite limit here — with no `UniformSpace.Completion`, Cauchy completion, or
postulated non-inductive unbounded Hilbert space continuum.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFDiracSpectralTripleColimit

open Matrix
open scoped Matrix.Norms.L2Operator
open InfoGeometry.Algebra.UHFColimitCStarCompletion
open InfoGeometry.Canonical.UHFTracialStateCore
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.Cl11DiracGeneratorCore
open InfoGeometry.Canonical.CuntzConnesSpectralDistance
open InfoGeometry.Canonical.ConnesInfimumDistance
open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Prequantum.AlgebraicGNSState.GNSQuotientStrictPositivity

/-!
## 1. Inductive UHF Dirac Tower & Commutator Transport
-/

/-- Inductive bounded UHF Dirac operator built from `diracGenerator` (Pauli `X`)
at stage `1` (`2^(0+1) = 2`) and propagated via the unital block-doubling
embedding `uhfStep`. -/
def uhfDirac : (n : ℕ) → UHFStage (n + 1)
  | 0 => diracGenerator
  | n + 1 => uhfStep (n + 1) (uhfDirac n)

/-- Inductive compatibility under `uhfStep`. -/
theorem uhfDirac_compat (n : ℕ) :
    uhfStep (n + 1) (uhfDirac n) = uhfDirac (n + 1) :=
  rfl

/-- Every finite stage `uhfDirac n` is self-adjoint. -/
theorem uhfDirac_selfAdjoint (n : ℕ) : star (uhfDirac n) = uhfDirac n := by
  induction n with
  | zero => exact diracGenerator_selfAdjoint
  | succ n ih =>
      unfold uhfDirac
      rw [← uhfStep_star, ih]

/-- Every finite stage `uhfDirac n` squares to the identity. -/
theorem uhfDirac_sq (n : ℕ) : uhfDirac n * uhfDirac n = 1 := by
  induction n with
  | zero => exact diracGenerator_sq
  | succ n ih =>
      unfold uhfDirac
      rw [← uhfStep_mul, ih, uhfStep_one]

/-- Exact L2 operator norm of the stage-1 generator `diracGenerator`. -/
theorem diracGenerator_norm : ‖(diracGenerator : UHFStage 1)‖ = 1 := by
  have hnonneg : 0 ≤ ‖(diracGenerator : UHFStage 1)‖ := norm_nonneg _
  have hmul_sq : ‖(diracGenerator : UHFStage 1)‖ * ‖(diracGenerator : UHFStage 1)‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self (diracGenerator : UHFStage 1)]
    have hct : (diracGenerator : UHFStage 1)ᴴ = diracGenerator :=
      diracGenerator_selfAdjoint
    rw [hct, diracGenerator_sq, norm_one]
  have hsq : ‖(diracGenerator : UHFStage 1)‖ ^ 2 = (1 : ℝ) ^ 2 := by
    rw [sq, hmul_sq, one_pow]
  exact (sq_eq_sq₀ hnonneg (by norm_num)).mp hsq

/-- Every finite stage `uhfDirac n` has unit L2 operator norm. -/
theorem uhfDirac_norm (n : ℕ) : ‖uhfDirac n‖ = 1 := by
  induction n with
  | zero => exact diracGenerator_norm
  | succ n ih =>
      unfold uhfDirac
      rw [uhfStep_isometry, ih]

/-- Uniform boundedness of the finite-stage Dirac commutator: `‖[Dₙ, A]‖ ≤ 2‖A‖`. -/
theorem uhfCommutatorNorm_bound (n : ℕ) (A : UHFStage (n + 1)) :
    commutatorNorm (uhfDirac n) A ≤ 2 * ‖A‖ := by
  have hle := (ConnesSpectral.SpectralTriple.mk (uhfDirac n)).commutatorNorm_le A
  change commutatorNorm (uhfDirac n) A ≤ 2 * ‖uhfDirac n‖ * ‖A‖ at hle
  rw [uhfDirac_norm n, mul_one] at hle
  exact hle

/-- Isometric transport of the commutator norm along `uhfStep (n + 1)`. -/
theorem uhfCommutatorNorm_transport (n : ℕ) (A : UHFStage (n + 1)) :
    commutatorNorm (uhfDirac (n + 1)) (uhfStep (n + 1) A) = commutatorNorm (uhfDirac n) A :=
  CuntzConnesSpectralDistance.commutatorNorm_transport
    (uhfStepHom (n + 1)).toRingHom (uhfDirac n) (uhfDirac (n + 1)) rfl
    (uhfStep_isometry (n + 1)) A

/-- The Connes Lipschitz ball is preserved and reflected by `uhfStep`. -/
theorem uhfLipschitzBall_transport (n : ℕ) (A : UHFStage (n + 1)) :
    LipschitzBall (uhfDirac (n + 1)) (uhfStep (n + 1) A) ↔ LipschitzBall (uhfDirac n) A := by
  unfold LipschitzBall
  rw [uhfCommutatorNorm_transport]

/-!
## 2. Explicit Non-Commutativity & Unit-Commutator Witness (OpenGauss T16)
-/

/-- Stage-1 diagonal projection `diag(1, 0)`. -/
def stageOneProj0 : UHFStage 1 := !![1, 0; 0, 0]

/-- Propagated diagonal projection across all finite stages `n + 1`. -/
def stageProj0 : (n : ℕ) → UHFStage (n + 1)
  | 0 => stageOneProj0
  | n + 1 => uhfStep (n + 1) (stageProj0 n)

theorem commutator_diracGenerator_proj0_unitary :
    star (CuntzConnesSpectralDistance.commutator (uhfDirac 0) stageOneProj0) *
      CuntzConnesSpectralDistance.commutator (uhfDirac 0) stageOneProj0 = 1 := by
  have hC :
      CuntzConnesSpectralDistance.commutator (uhfDirac 0) stageOneProj0 = !![0, -1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CuntzConnesSpectralDistance.commutator, uhfDirac, diracGenerator, stageOneProj0]
  rw [hC]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.star_apply]

/-- At every stage `n`, `[uhfDirac n, stageProj0 n]` has exact commutator norm `1`. -/
theorem commutatorNorm_uhfDirac_stageProj0 (n : ℕ) :
    commutatorNorm (uhfDirac n) (stageProj0 n) = 1 := by
  induction n with
  | zero =>
      dsimp [stageProj0, commutatorNorm]
      set C := CuntzConnesSpectralDistance.commutator (uhfDirac 0) stageOneProj0
      have hnonneg : 0 ≤ ‖C‖ := norm_nonneg _
      have hmul : ‖C‖ * ‖C‖ = 1 := by
        rw [← Matrix.l2_opNorm_conjTranspose_mul_self C]
        have hs : Cᴴ * C = star C * C := rfl
        rw [hs, commutator_diracGenerator_proj0_unitary, norm_one]
      have hsq : ‖C‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [sq, hmul, one_pow]
      exact (sq_eq_sq₀ hnonneg (by norm_num)).mp hsq
  | succ n ih =>
      change commutatorNorm (uhfDirac (n + 1)) (uhfStep (n + 1) (stageProj0 n)) = 1
      rw [uhfCommutatorNorm_transport, ih]

/-- `stageProj0 n` belongs to the Connes Lipschitz ball of `uhfDirac n`. -/
theorem uhfDirac_stageProj0_lipschitz (n : ℕ) :
    LipschitzBall (uhfDirac n) (stageProj0 n) := by
  unfold LipschitzBall
  rw [commutatorNorm_uhfDirac_stageProj0]

/-- OpenGauss T16 non-commutativity witness at every finite stage `n`:
`uhfDirac n` does not commute with `stageProj0 n`. -/
theorem uhfDirac_noncomm (n : ℕ) :
    uhfDirac n * stageProj0 n ≠ stageProj0 n * uhfDirac n := by
  intro h
  have hzero : commutatorNorm (uhfDirac n) (stageProj0 n) = 0 := by
    unfold commutatorNorm CuntzConnesSpectralDistance.commutator
    rw [h, sub_self, norm_zero]
  have hone := commutatorNorm_uhfDirac_stageProj0 n
  linarith

/-!
## 3. Jaynesian Colimit Dirac Operator on `UHFAlg`
-/

/-- Canonical `RingHom` inclusion `UHFStage n →+* UHFAlg`. -/
def toUHFStageRingHom (n : ℕ) : UHFStage n →+* UHFAlg where
  toFun := toUHF n
  map_one' := toUHF_one n
  map_mul' X Y := (mul_toUHF n X Y).symm
  map_zero' := toUHF_zero n
  map_add' X Y := (add_toUHF n X Y).symm

/-- Exact isometry of the canonical colimit inclusion `UHFStage n → UHFAlg`. -/
theorem norm_toUHF_stage (n : ℕ) (X : UHFStage n) : ‖toUHF n X‖ = ‖X‖ :=
  rfl

/-- Canonical Dirac element inside the directed colimit algebra `UHFAlg`. -/
def uhfColimitDirac : UHFAlg := toUHF 1 diracGenerator

/-- Every finite-stage Dirac operator `uhfDirac n` projects to `uhfColimitDirac`. -/
theorem toUHF_uhfDirac (n : ℕ) :
    toUHF (n + 1) (uhfDirac n) = uhfColimitDirac := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change toUHF (n + 2) (uhfStep (n + 1) (uhfDirac n)) = uhfColimitDirac
      rw [toUHF_uhfStep, ih]

theorem uhfColimitDirac_selfAdjoint : star uhfColimitDirac = uhfColimitDirac := by
  unfold uhfColimitDirac
  rw [star_toUHF, diracGenerator_selfAdjoint]

theorem uhfColimitDirac_sq : uhfColimitDirac * uhfColimitDirac = 1 := by
  unfold uhfColimitDirac
  rw [mul_toUHF, diracGenerator_sq, toUHF_one]

theorem uhfColimitDirac_norm : ‖uhfColimitDirac‖ = 1 := by
  unfold uhfColimitDirac
  rw [norm_toUHF_stage, diracGenerator_norm]

/-- The colimit commutator norm on any stage representative equals its finite-stage
commutator norm. -/
theorem uhfColimitCommutatorNorm_eq (n : ℕ) (A : UHFStage (n + 1)) :
    commutatorNorm uhfColimitDirac (toUHF (n + 1) A) = commutatorNorm (uhfDirac n) A :=
  CuntzConnesSpectralDistance.commutatorNorm_transport
    (toUHFStageRingHom (n + 1)) (uhfDirac n) uhfColimitDirac (toUHF_uhfDirac n)
    (norm_toUHF_stage (n + 1)) A

theorem uhfColimitCommutatorNorm_bound (x : UHFAlg) :
    commutatorNorm uhfColimitDirac x ≤ 2 * ‖x‖ := by
  have hle := (ConnesSpectral.SpectralTriple.mk uhfColimitDirac).commutatorNorm_le x
  change commutatorNorm uhfColimitDirac x ≤ 2 * ‖uhfColimitDirac‖ * ‖x‖ at hle
  rw [uhfColimitDirac_norm, mul_one] at hle
  exact hle

theorem uhfColimitLipschitzBall_iff (n : ℕ) (A : UHFStage (n + 1)) :
    LipschitzBall uhfColimitDirac (toUHF (n + 1) A) ↔ LipschitzBall (uhfDirac n) A := by
  unfold LipschitzBall
  rw [uhfColimitCommutatorNorm_eq]

/-!
## 4. Connes Spectral-Distance Colimit Transport (`uhfStateDistanceBound_colimit`)
-/

/-- Every element of `UHFAlg` has a representative at some positive stage `n + 1`. -/
theorem exists_toUHF_succ (x : UHFAlg) :
    ∃ (n : ℕ) (A : UHFStage (n + 1)), x = toUHF (n + 1) A := by
  rcases exists_toUHF x with ⟨m, X, rfl⟩
  cases m with
  | zero => exact ⟨0, uhfStep 0 X, (toUHF_uhfStep 0 X).symm⟩
  | succ n => exact ⟨n, X, rfl⟩

/-- One-step downward transport of `StateDistanceBound` along compatible functionals. -/
theorem uhfStateDistanceBound_step {n : ℕ}
    (μₙ νₙ : UHFStage (n + 1) → ℝ)
    (μₛ νₛ : UHFStage (n + 2) → ℝ)
    (hμ : ∀ A : UHFStage (n + 1), μₛ (uhfStep (n + 1) A) = μₙ A)
    (hν : ∀ A : UHFStage (n + 1), νₛ (uhfStep (n + 1) A) = νₙ A)
    {d : ℝ} (hd : StateDistanceBound (uhfDirac (n + 1)) μₛ νₛ d) :
    StateDistanceBound (uhfDirac n) μₙ νₙ d := by
  refine ⟨fun A hA => ?_, hd.2⟩
  have hstep : LipschitzBall (uhfDirac (n + 1)) (uhfStep (n + 1) A) :=
    (uhfLipschitzBall_transport n A).mpr hA
  simpa only [hμ A, hν A] using hd.1 (uhfStep (n + 1) A) hstep

/-- One-step monotonicity of Connes infimum distance along compatible functionals. -/
theorem uhfConnesInfDistance_step_le {n : ℕ}
    (μₙ νₙ : UHFStage (n + 1) → ℝ)
    (μₛ νₛ : UHFStage (n + 2) → ℝ)
    (hμ : ∀ A : UHFStage (n + 1), μₛ (uhfStep (n + 1) A) = μₙ A)
    (hν : ∀ A : UHFStage (n + 1), νₛ (uhfStep (n + 1) A) = νₙ A)
    (hnonempty : ( {d : ℝ | StateDistanceBound (uhfDirac (n + 1)) μₛ νₛ d} ).Nonempty) :
    connesInfDistance (uhfDirac n) μₙ νₙ ≤ connesInfDistance (uhfDirac (n + 1)) μₛ νₛ := by
  unfold connesInfDistance
  refine csInf_le_csInf ⟨0, fun _ hd => hd.2⟩ hnonempty ?_
  intro d hd
  exact uhfStateDistanceBound_step μₙ νₙ μₛ νₛ hμ hν hd

/-- Colimit equivalence: a Connes state-distance bound holds on `UHFAlg` with
respect to `uhfColimitDirac` iff it holds uniformly on every finite stage `n`. -/
theorem uhfStateDistanceBound_colimit (μ ν : UHFAlg → ℝ) (d : ℝ) :
    StateDistanceBound uhfColimitDirac μ ν d ↔
      ∀ n : ℕ, StateDistanceBound (uhfDirac n)
        (fun A => μ (toUHF (n + 1) A)) (fun A => ν (toUHF (n + 1) A)) d := by
  constructor
  · intro ⟨hbound, hd0⟩ n
    refine ⟨fun A hA => ?_, hd0⟩
    exact hbound (toUHF (n + 1) A) ((uhfColimitLipschitzBall_iff n A).mpr hA)
  · intro hstages
    refine ⟨fun x hx => ?_, (hstages 0).2⟩
    rcases exists_toUHF_succ x with ⟨n, A, rfl⟩
    exact (hstages n).1 A ((uhfColimitLipschitzBall_iff n A).mp hx)

/-- Every finite-stage Connes infimum distance is bounded above by the colimit
Connes infimum distance on `UHFAlg`. -/
theorem uhfConnesInfDistance_stage_le_colimit (μ ν : UHFAlg → ℝ)
    (hnonempty : ({d : ℝ | StateDistanceBound uhfColimitDirac μ ν d}).Nonempty) (n : ℕ) :
    connesInfDistance (uhfDirac n)
      (fun A => μ (toUHF (n + 1) A)) (fun A => ν (toUHF (n + 1) A)) ≤
      connesInfDistance uhfColimitDirac μ ν := by
  unfold connesInfDistance
  refine csInf_le_csInf ⟨0, fun _ hd => hd.2⟩ hnonempty ?_
  intro d hd
  exact (uhfStateDistanceBound_colimit μ ν d).mp hd n

/-!
## 5. Tracial State Compatibility, Colimit Trace, Exact Stage-1 Distance, and GNS Bridge
-/

/-- Entrywise bound `‖A i j‖ ≤ ‖A‖` for the L2 operator norm on `UHFStage n`. -/
theorem uhfStage_entry_norm_le {n : ℕ} (A : UHFStage n) (i j : Fin (2 ^ n)) :
    ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ (Fin (2 ^ n)) := EuclideanSpace.single j (1 : ℂ)
  have he_norm : ‖e‖ = 1 :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Fin (2 ^ n))).1 j
  have hmulvec : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)) A e) i = A i j := by
    have heval := Matrix.toEuclideanCLM_toLp A (Pi.single j (1 : ℂ))
    change (Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 (Pi.single j (1 : ℂ)))) i = A i j
    rw [heval]
    change (A *ᵥ Pi.single j (1 : ℂ)) i = A i j
    rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_single j]
    · simp
    · intro k hk
      simp [Pi.single_eq_of_ne hk]
  have hle1 : ‖A i j‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)) A e‖ := by
    rw [← hmulvec]
    exact PiLp.norm_apply_le _ i
  have hle2 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)) A e‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)) A‖ * ‖e‖ :=
    ContinuousLinearMap.le_opNorm _ e
  rw [Matrix.l2_opNorm_toEuclideanCLM, he_norm, mul_one] at hle2
  exact hle1.trans hle2

/-- Exact trace doubling under the block-doubling step `uhfStep n`. -/
theorem matrixTrace_uhfStep (n : ℕ) (A : UHFStage n) :
    Matrix.trace (uhfStep n A) = 2 * Matrix.trace A := by
  unfold uhfStep Matrix.trace Matrix.diag
  rw [← Equiv.sum_comp (finSumTwoPow n)]
  have hsum : (∑ s : Fin (2 ^ n) ⊕ Fin (2 ^ n),
      (reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks A 0 0 A))
        (finSumTwoPow n s) (finSumTwoPow n s)) =
      ∑ s : Fin (2 ^ n) ⊕ Fin (2 ^ n), fromBlocks A 0 0 A s s := by
    apply Finset.sum_congr rfl
    intro s _
    change (reindex (finSumTwoPow n) (finSumTwoPow n) (fromBlocks A 0 0 A))
      (finSumTwoPow n s) (finSumTwoPow n s) = fromBlocks A 0 0 A s s
    rw [reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [hsum, Fintype.sum_sum_type]
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₂]
  ring

/-- Compatibility of the normalized tracial state across one block-doubling step:
`ω_{n+1}(uhfStep n A) = ωₙ(A)`. -/
theorem uhfTracialState_compat (n : ℕ) (A : UHFStage n) :
    uhfTracialState (n + 1) (uhfStep n A) = uhfTracialState n A := by
  unfold uhfTracialState
  rw [matrixTraceState_apply, matrixTraceState_apply, matrixTrace_uhfStep]
  have hpow : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  rw [pow_succ']
  field_simp [hpow, htwo]

/-- Iterated compatibility of the normalized tracial state across `k` steps. -/
theorem uhfTracialState_compat_iter {n : ℕ} (k : ℕ) (A : UHFStage n) :
    uhfTracialState (n + k) (uhfStepIter k A) = uhfTracialState n A := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp [uhfStepIter]
      change uhfTracialState ((n + k) + 1) (uhfStep (n + k) (uhfStepIter k A)) = uhfTracialState n A
      rw [uhfTracialState_compat, ih]

/-- Operator-norm bound `‖ωₙ(A)‖ ≤ ‖A‖` at every finite stage `n`. -/
theorem uhfTracialState_norm_le (n : ℕ) (A : UHFStage n) :
    ‖uhfTracialState n A‖ ≤ ‖A‖ := by
  unfold uhfTracialState
  rw [matrixTraceState_apply, norm_mul, norm_div, norm_one]
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hpow_norm : ‖(2 ^ n : ℂ)‖ = (2 : ℝ) ^ n := by
    have hc : ((2 ^ n : ℂ)) = ↑((2 : ℝ) ^ n) := by push_cast; rfl
    rw [hc, Complex.norm_real, Real.norm_of_nonneg hpow_pos.le]
  rw [hpow_norm]
  have htr_le : ‖Matrix.trace A‖ ≤ (2 : ℝ) ^ n * ‖A‖ := by
    calc
      ‖Matrix.trace A‖ = ‖∑ i : Fin (2 ^ n), A i i‖ := rfl
      _ ≤ ∑ i : Fin (2 ^ n), ‖A i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin (2 ^ n), ‖A‖ :=
          Finset.sum_le_sum fun i _ => uhfStage_entry_norm_le A i i
      _ = (2 : ℝ) ^ n * ‖A‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_cast
  calc
    1 / (2 : ℝ) ^ n * ‖Matrix.trace A‖
        ≤ 1 / (2 : ℝ) ^ n * ((2 : ℝ) ^ n * ‖A‖) :=
          mul_le_mul_of_nonneg_left htr_le (by positivity)
    _ = ‖A‖ := by field_simp [hpow_pos.ne']

private lemma uhfTracialState_eq_of_heq {m₁ m₂ : ℕ} {X : UHFStage m₁} {Y : UHFStage m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    uhfTracialState m₁ X = uhfTracialState m₂ Y := by
  subst h_dim
  cases eq_of_heq h_heq
  rfl

private lemma uhfColimitTrace_well_defined
    (u v : Σ n : ℕ, UHFStage n) (h : UHFRel u v) :
    uhfTracialState u.1 u.2 = uhfTracialState v.1 v.2 := by
  rcases h with ⟨k₁, k₂, hdim, heq⟩
  rw [← uhfTracialState_compat_iter k₁ u.2, ← uhfTracialState_compat_iter k₂ v.2]
  exact uhfTracialState_eq_of_heq hdim heq

/-- Canonical normalized tracial state lifted to the colimit algebra `UHFAlg`. -/
def uhfColimitTrace : UHFAlg → ℂ :=
  Quotient.lift (fun u => uhfTracialState u.1 u.2) uhfColimitTrace_well_defined

@[simp]
theorem uhfColimitTrace_toUHF (n : ℕ) (A : UHFStage n) :
    uhfColimitTrace (toUHF n A) = uhfTracialState n A :=
  rfl

theorem uhfColimitTrace_one : uhfColimitTrace (1 : UHFAlg) = 1 := by
  change uhfColimitTrace (toUHF 0 1) = 1
  rw [uhfColimitTrace_toUHF]
  exact uhfTracialState_one

theorem uhfColimitTrace_add (x y : UHFAlg) :
    uhfColimitTrace (x + y) = uhfColimitTrace x + uhfColimitTrace y := by
  rcases toUHF_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
  rw [add_toUHF, uhfColimitTrace_toUHF, uhfColimitTrace_toUHF, uhfColimitTrace_toUHF]
  unfold uhfTracialState
  rw [matrixTraceState_apply, matrixTraceState_apply, matrixTraceState_apply,
    Matrix.trace_add, mul_add]

theorem uhfColimitTrace_sub (x y : UHFAlg) :
    uhfColimitTrace (x - y) = uhfColimitTrace x - uhfColimitTrace y := by
  rcases toUHF_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
  have hsub : toUHF n X - toUHF n Y = toUHF n (X - Y) := by
    rw [sub_eq_add_neg, neg_toUHF, add_toUHF, ← sub_eq_add_neg]
  rw [hsub, uhfColimitTrace_toUHF, uhfColimitTrace_toUHF, uhfColimitTrace_toUHF]
  unfold uhfTracialState
  rw [matrixTraceState_apply, matrixTraceState_apply, matrixTraceState_apply,
    Matrix.trace_sub, mul_sub]

theorem uhfColimitTrace_mul_comm (x y : UHFAlg) :
    uhfColimitTrace (x * y) = uhfColimitTrace (y * x) := by
  rcases toUHF_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
  rw [mul_toUHF, mul_toUHF, uhfColimitTrace_toUHF, uhfColimitTrace_toUHF]
  exact uhfTracialState_mul_comm X Y

theorem uhfColimitTrace_star (x : UHFAlg) :
    star (uhfColimitTrace x) = uhfColimitTrace (star x) := by
  rcases exists_toUHF x with ⟨n, X, rfl⟩
  rw [star_toUHF, uhfColimitTrace_toUHF, uhfColimitTrace_toUHF]
  exact matrixTraceState_star n X

theorem uhfColimitTrace_nonneg (x : UHFAlg) :
    0 ≤ (uhfColimitTrace (star x * x)).re := by
  rcases exists_toUHF x with ⟨n, X, rfl⟩
  rw [star_toUHF, mul_toUHF, uhfColimitTrace_toUHF]
  exact uhfTracialState_nonneg X

theorem uhfColimitTrace_symmetric (x y : UHFAlg) :
    (uhfColimitTrace (star y * x)).re = (uhfColimitTrace (star x * y)).re := by
  rcases toUHF_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
  rw [star_toUHF, mul_toUHF, star_toUHF, mul_toUHF, uhfColimitTrace_toUHF, uhfColimitTrace_toUHF]
  exact uhfTracialState_symmetric X Y

theorem uhfColimitTrace_norm_le (x : UHFAlg) :
    ‖uhfColimitTrace x‖ ≤ ‖x‖ := by
  rcases exists_toUHF x with ⟨n, X, rfl⟩
  rw [uhfColimitTrace_toUHF, norm_toUHF_stage]
  exact uhfTracialState_norm_le n X

/-- Real part of the `(0, 0)` pure diagonal state on stage `1` (`M₂(ℂ)`). -/
def stageOneTopLeftRe (A : UHFStage 1) : ℝ := (A 0 0).re

/-- Real part of the normalized tracial state on stage `1` (`M₂(ℂ)`). -/
def stageOneTraceRe (A : UHFStage 1) : ℝ := (uhfTracialState 1 A).re

/-- Exact non-trivial Connes spectral distance on stage `1`:
`d_{diracGenerator}(e₀₀, ω₁) = 1 / 2`. -/
theorem stageOne_connesInfDistance_topLeft_trace :
    connesInfDistance (uhfDirac 0) stageOneTopLeftRe stageOneTraceRe = 1 / 2 := by
  have hupper : StateDistanceBound (uhfDirac 0) stageOneTopLeftRe stageOneTraceRe (1 / 2) := by
    refine ⟨fun A hA => ?_, by norm_num⟩
    have hdiff :
        stageOneTopLeftRe A - stageOneTraceRe A = (1 / 2 : ℝ) * ((A 0 0).re - (A 1 1).re) := by
      unfold stageOneTopLeftRe stageOneTraceRe uhfTracialState
      rw [matrixTraceState_apply]
      have htr : Matrix.trace A = A 0 0 + A 1 1 := by
        simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
      have hhalf : (1 / ((2 : ℂ) ^ 1)) = ↑(1 / 2 : ℝ) := by norm_num
      rw [htr, hhalf, Complex.re_ofReal_mul, Complex.add_re]
      ring
    have hcomm10 : (CuntzConnesSpectralDistance.commutator (uhfDirac 0) A) 1 0 = A 0 0 - A 1 1 := by
      unfold CuntzConnesSpectralDistance.commutator uhfDirac
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
      change (∑ j : Fin 2, diracGenerator 1 j * A j 0) -
        (∑ j : Fin 2, A 1 j * diracGenerator j 0) = A 0 0 - A 1 1
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      simp [diracGenerator]
    have hre_le : |(A 0 0).re - (A 1 1).re| ≤ 1 := by
      calc
        |(A 0 0).re - (A 1 1).re|
            = |(A 0 0 - A 1 1).re| := by rw [Complex.sub_re]
        _ ≤ ‖A 0 0 - A 1 1‖ := Complex.abs_re_le_norm _
        _ = ‖(CuntzConnesSpectralDistance.commutator (uhfDirac 0) A) 1 0‖ := by rw [hcomm10]
        _ ≤ ‖CuntzConnesSpectralDistance.commutator (uhfDirac 0) A‖ := uhfStage_entry_norm_le _ 1 0
        _ ≤ 1 := hA
    rw [hdiff, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    nlinarith
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ hd => hd.2⟩ hupper
  · apply le_csInf ⟨1 / 2, hupper⟩
    intro d hd
    have hp := hd.1 stageOneProj0 (uhfDirac_stageProj0_lipschitz 0)
    have hval : |stageOneTopLeftRe stageOneProj0 - stageOneTraceRe stageOneProj0| = 1 / 2 := by
      unfold stageOneTopLeftRe stageOneTraceRe uhfTracialState
      rw [matrixTraceState_apply]
      have htr : Matrix.trace stageOneProj0 = 1 := by
        simp [stageOneProj0, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
      have h00 : (stageOneProj0 0 0).re = 1 := by simp [stageOneProj0]
      rw [htr, mul_one, h00]
      have hhalf : ((1 / ((2 : ℂ) ^ 1))).re = 1 / 2 := by norm_num
      rw [hhalf]
      norm_num
    linarith

/-- Package the stage-`n` normalized trace as a `RealAlgebraicState` on `UHFStage n`. -/
def uhfStageRealState (n : ℕ) : RealAlgebraicState (UHFStage n) where
  toLinearMap := Complex.reCLM.toLinearMap.comp ((matrixTraceFunctional n).restrictScalars ℝ)
  normalized := by
    change (matrixTraceState n 1).re = 1
    rw [matrixTraceState_one]
    simp
  positive A := by
    change 0 ≤ (matrixTraceState n (star A * A)).re
    exact matrixTraceState_nonneg n A
  symmetric x y := by
    change (uhfTracialState n (star y * x)).re = (uhfTracialState n (star x * y)).re
    exact uhfTracialState_symmetric x y

/-- Faithfulness of the normalized trace on `UHFStage n`: `ωₙ(A* A).re = 0 ↔ A = 0`. -/
theorem uhfStageRealState_faithful (n : ℕ) (A : UHFStage n) :
    (uhfStageRealState n).eval (star A * A) = 0 ↔ A = 0 := by
  change (matrixTraceState n (star A * A)).re = 0 ↔ A = 0
  rw [matrixTraceState_apply]
  have hcast : (1 / (2 ^ n : ℂ)) = ↑(1 / (2 ^ n : ℝ)) := by push_cast; rfl
  rw [hcast, Complex.re_ofReal_mul]
  have hfactor : (0 : ℝ) < 1 / (2 ^ n : ℝ) := by positivity
  rw [mul_eq_zero, or_iff_right hfactor.ne']
  have htr : Matrix.trace (star A * A) =
      ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.star_apply, Complex.star_def]
  have h_elem (k i : Fin (2 ^ n)) :
      (starRingEnd ℂ (A k i) * A k i).re = Complex.normSq (A k i) := by
    rw [mul_comm, Complex.mul_conj]
    rfl
  have h_sum2 (i : Fin (2 ^ n)) :
      (∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i).re =
        ∑ k : Fin (2 ^ n), Complex.normSq (A k i) := by
    have h_map := map_sum Complex.reAddGroupHom
      (fun k => starRingEnd ℂ (A k i) * A k i) Finset.univ
    change Complex.reAddGroupHom (∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i) =
      ∑ k : Fin (2 ^ n), Complex.normSq (A k i)
    rw [h_map]
    congr 1; ext k
    exact h_elem k i
  have hre : (Matrix.trace (star A * A)).re =
      ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), Complex.normSq (A k i) := by
    rw [htr]
    have h_map := map_sum Complex.reAddGroupHom
      (fun i => ∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i) Finset.univ
    change Complex.reAddGroupHom (∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i) =
      ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), Complex.normSq (A k i)
    rw [h_map]
    congr 1; ext i
    exact h_sum2 i
  rw [hre, Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun k _ => Complex.normSq_nonneg (A k i))]
  constructor
  · intro h
    ext k i
    have hi := Finset.sum_eq_zero_iff_of_nonneg (fun l _ => Complex.normSq_nonneg (A l i))
      |>.mp (h i (Finset.mem_univ i)) k (Finset.mem_univ k)
    exact Complex.normSq_eq_zero.mp hi
  · intro h i _
    subst h
    simp

/-- Bridge to `GNSQuotientStrictPositivity`: the GNS quotient class of `A`
under `uhfStageRealState n` equals `0` iff `A = 0`. -/
theorem uhfStageRealState_gns_strict_positivity (n : ℕ) (A : UHFStage n) :
    Quotient.mk (uhfStageRealState n).gnsSetoid A =
      Quotient.mk (uhfStageRealState n).gnsSetoid 0 ↔ A = 0 := by
  rw [← gns_strict_positivity (uhfStageRealState n) A]
  exact uhfStageRealState_faithful n A

/-- Faithfulness of `uhfColimitTrace` on the directed colimit algebra `UHFAlg`. -/
theorem uhfColimitTrace_faithful (x : UHFAlg) :
    (uhfColimitTrace (star x * x)).re = 0 ↔ x = 0 := by
  rcases exists_toUHF x with ⟨n, A, rfl⟩
  rw [star_toUHF, mul_toUHF, uhfColimitTrace_toUHF]
  have h1 : (uhfTracialState n (star A * A)).re = 0 ↔ A = 0 := by
    simpa [uhfStageRealState, RealAlgebraicState.eval, uhfTracialState] using
      uhfStageRealState_faithful n A
  rw [h1]
  constructor
  · intro h
    rw [h, toUHF_zero]
  · intro h
    have h' : toUHF n A = toUHF n (0 : UHFStage n) := h.trans (toUHF_zero n).symm
    have hrel : UHFRel ⟨n, A⟩ ⟨n, (0 : UHFStage n)⟩ := Quotient.exact h'
    rcases hrel with ⟨k₁, k₂, hdim, heq⟩
    dsimp at hdim
    have hk : k₁ = k₂ := by omega
    subst hk
    have hstep : uhfStepIter k₁ A = uhfStepIter k₁ (0 : UHFStage n) := eq_of_heq heq
    rw [uhfStepIter_zero] at hstep
    have hnorm : ‖A‖ = 0 := by
      rw [← uhfStepIter_norm k₁ A, hstep, norm_zero]
    exact norm_eq_zero.mp hnorm

end InfoGeometry.Canonical.UHFDiracSpectralTripleColimit
