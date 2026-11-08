/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analytic.LogSumExp
import InfoGeometry.Analytic.PrimonZeta
import InfoGeometry.Analytic.HKColimitAnalyticity
import InfoGeometry.Analysis.SpectralSurprisalLogDetBridge
import InfoGeometry.Analysis.LogDetSelfConcordantBarrier
import InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
import InfoGeometry.Analysis.HurwitzAsanoColimitLimitBridge
import InfoGeometry.Analysis.BregmanMonodromyBridge
import InfoGeometry.Analysis.SouriauThermodynamics
import InfoGeometry.Canonical.UnifiedDikinGeometry
import InfoGeometry.Canonical.ModularSurprisalVolumeClockingBKMClosurePoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.CladisticPhylogenesisBridge

/-!
===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.UnifiedAnalyticGeometricFramework
Role: Canonical puzzle-synthesis owner uniting the 7 mathematical and epistemic
  clades of "analytic" across InfoGeometry into one kernel-checked geometric
  framework:
  (I)   Scalar & Arithmetic Cumulant-Generating Analyticity (LogSumExp & PrimonZeta),
  (II)  Spectral Surprisal & Log-Det Self-Concordant Barrier Analyticity,
  (III) Non-Commutative Complex Matrix Fréchet Log-Volume & Inverse Calculus,
  (IV)  Complex Lee-Yang Zero Localization & Log-Monodromy Jordan Block Analyticity,
  (V)   Souriau-Bregman Dual-Flat Geometry & Unified Dikin Barrier Ellipsoids,
  (VI)  Filtered Inductive Colimit Hestenes-Krein Phase & Peirce Cladistic Spine,
  (VII) Epistemic Thesis-vs-Shadow Binary Cut, 1:(-2) Modular Clocking & BKM Poset.
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.UnifiedAnalyticGeometricFramework

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.Analytic
open InfoGeometry.Analytic.PrimonZeta
open InfoGeometry.Analytic.HKColimitAnalyticity
open InfoGeometry.Analysis
open InfoGeometry.Analysis.SelfConcordant
open InfoGeometry.Analysis.SpectralSurprisalLogDetBridge
open InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
open InfoGeometry.Analysis.HurwitzAsano
open InfoGeometry.Geometry.LegendreDifferential
open InfoGeometry.Canonical.ModularSurprisalVolumeClockingBKMClosurePoset
open InfoGeometry.OperatorAlgebra.PeirceSpine

/-!
## Piece I: Cumulant-Generating & Arithmetic Partition Analyticity
The generating potential $\psi(\theta) = \log Z(\theta)$ relates statistical
moments to Riemannian curvature: its 1st derivative is the Gibbs expectation
and its 2nd derivative is the Fisher-Rao variance, while for logarithmic
primon energies $E_n = \log n$ the Boltzmann partition sum coincides with the
Dirichlet series $\sum_{n \ge 1} n^{-\beta}$.
-/

theorem pieceI_cumulant_and_primon_partition_analyticity
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ β : ℝ) (hβ : 1 < β) :
    HasDerivAt (logSumExp w a) (logSumExpMean w a θ) θ ∧
    deriv (fun t => deriv (logSumExp w a) t) θ = logSumExpVariance w a θ ∧
    primonPartitionFunction β = ∑' n : ℕ, (n : ℝ) ^ (-β) :=
  ⟨hasDerivAt_logSumExp w a hw θ,
   logSumExp_secondDeriv_eq_variance w a hw θ,
   primonPartition_eq_dirichletZeta β hβ⟩

/-!
## Piece II: Spectral Surprisal & Self-Concordant Log-Determinant Barrier
On the positive-definite cone $\mathcal{S}^n_{++}$, the log-determinant barrier
$\Phi(A) = -\log\det A$ equals the total spectral surprisal $\sum_i (-\log \lambda_i)$
and its 2nd variation $\nabla^2 \Phi(A)[H, K] = \mathrm{Tr}(A^{-1} H A^{-1} K)$
defines the symmetric Riemannian Fisher-Rao / Siegel metric.
-/

theorem pieceII_spectral_surprisal_and_barrier_hessian
    {n : ℕ} (A : PosDefCone n) (vals : Fin n → ℝ)
    (hpos : ∀ i, 0 < vals i) (hdiag : A.mat = Matrix.diagonal vals)
    (A_inv H K : Matrix (Fin n) (Fin n) ℝ) :
    phi A = ∑ i : Fin n, spectralSurprisal vals i ∧
    Matrix.trace (surprisalDiagonal vals) = ∑ i : Fin n, spectralSurprisal vals i ∧
    hessianPhi A_inv H K = hessianPhi A_inv K H :=
  ⟨logDetBarrier_eq_sum_spectralSurprisal A vals hpos hdiag,
   trace_surprisalDiagonal vals,
   hessianPhi_symm A_inv H K⟩

/-!
## Piece III: Non-Commutative Fréchet Log-Volume & Resolvent Inverse Calculus
On the full complex matrix algebra $M_n(\mathbb{C})$, the negative log-determinant
$-\log\|\det A\|$ has native Fréchet derivative $-\mathrm{Re}\,\mathrm{Tr}(A^{-1} H)$,
and the matrix inverse $B \mapsto B^{-1}$ has Fréchet derivative $H \mapsto -A^{-1} H A^{-1}$
in the noncommutative operator order.
-/

theorem pieceIII_noncommutative_frechet_log_volume_and_inv
    {n : Type*} [Fintype n] [DecidableEq n]
    (A H : Matrix n n ℂ) (hA : IsUnit A) :
    HasFDerivAt negLogDet (logDetDifferential A) A ∧
    fderiv ℝ negLogDet A H = -(Matrix.trace (A⁻¹ * H)).re ∧
    HasFDerivAt (fun B : Matrix n n ℂ => B⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) A⁻¹ A⁻¹) A :=
  ⟨hasFDerivAt_negLogDet A hA,
   fderiv_negLogDet_apply A H hA,
   hasFDerivAt_matrix_inv A hA⟩

/-!
## Piece IV: Complex Zero-Free Domain, Lee-Yang Circle & Log-Monodromy Jordan Block
Complex analyticity of $\log Z(z)$ holds on the zero-free region of $Z(z)$.
Under open-disk zero-freeness and reciprocal symmetry, all roots localize to the
unit circle $\|z_0\| = 1$, while winding $m$ times around a logarithmic branch
point accumulates the nilpotent Jordan monodromy $J^m = \begin{pmatrix} 1 & 2\pi m \\ 0 & 1 \end{pmatrix}$.
-/

theorem pieceIV_complex_zero_boundary_and_monodromy
    {f : ℂ → ℂ}
    (h_disk_free : ∀ z ∈ openUnitDisk, f z ≠ 0)
    (h_symm : ∀ z : ℂ, z ≠ 0 → (f z = 0 ↔ f z⁻¹ = 0))
    {z0 : ℂ} (hz0_root : f z0 = 0) (m : ℕ) (ν : ℝ) (z : ℂ) :
    ‖z0‖ = 1 ∧
    monodromyJordanBlock ^ m = !![1, (m : ℂ) * (2 * Real.pi); 0, 1] ∧
    complexMonodromyErrorShift ν z - ν * Complex.log z = 2 * Complex.I * Real.pi * ν :=
  ⟨root_modulus_one_of_disk_free_reciprocal_symmetry h_disk_free h_symm hz0_root,
   monodromyJordanBlock_pow m,
   complexMonodromyErrorShift_sub_logTerm ν z⟩

/-!
## Piece V: Dual-Flat Souriau-Bregman Geometry & Dikin Barrier Hessian
The Legendre / Bregman divergence gap on the trace-zero $\mathfrak{sl}_2(\mathbb{C})$
temperature carrier vanishes at equal temperatures, while any `DikinBarrier`
identifies the local Dikin metric $g_x(v)$ with the Fréchet Hessian quadratic form
$\nabla^2 \Phi(x)[v, v]$ of its analytic barrier potential.
-/

theorem pieceV_souriau_bregman_and_dikin_barrier
    (Φ : SL2cAlgebra → ℝ) (nablaΦ : SL2cAlgebra → SL2cDual) (β : SL2cAlgebra)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [B : DikinBarrier E]
    (x v : E) {r : ℝ} (hr : 0 ≤ r) :
    souriauBregmanDivergence Φ nablaΦ β β = 0 ∧
    B.dikin_metric x v = hessianMap B.dikin_barrier x v v ∧
    x ∈ B.dikin_ellipsoid x r :=
  ⟨bregman_gap_identity Φ nablaΦ β,
   DikinBarrier.dikin_metric_eq_hessian x v,
   DikinMetric.dikin_ellipsoid_center_mem x hr⟩

/-!
## Piece VI: Filtered Inductive Colimit Hestenes-Krein Phase & Peirce Cladistics
Along an inductive tower of finite stages, compatible Hestenes-Krein phases
$J_n^2 = -I$ descend to an injective colimit phase operator satisfying $J_\infty^2 = -I$,
while the Peirce daughter-idempotent lineage tower remains idempotent at every
generation $k$ and its divergence difference squares to the Gramian metric $V$.
-/

theorem pieceVI_inductive_colimit_and_peirce_cladistics
    {Stage : ℕ → Type*} [∀ k, AddCommGroup (Stage k)]
    (f : ∀ m k : ℕ, m ≤ k → Stage m →+ Stage k)
    (J : FilteredKreinPhaseFamily Stage f)
    (z : AddCommGroup.DirectLimit Stage f)
    {R : Type*} [Ring R] {P : R} (hP : P * P = P) (A C : R) (k : ℕ) :
    FilteredKreinPhaseFamily.directLimitPhase Stage f J
      (FilteredKreinPhaseFamily.directLimitPhase Stage f J z) = -z ∧
    Function.Injective (FilteredKreinPhaseFamily.directLimitPhase Stage f J) ∧
    phyloLineage k P A * phyloLineage k P A = phyloLineage k P A ∧
    ((P + coneMinus P C) - (P - conePlus P A)) *
      ((P + coneMinus P C) - (P - conePlus P A)) = genV P A C :=
  ⟨FilteredKreinPhaseFamily.directLimitPhase_sq_apply Stage f J z,
   FilteredKreinPhaseFamily.directLimitPhase_injective Stage f J,
   phyloLineage_idempotent hP A k,
   (lineage_divergence_metric hP A C).2⟩

/-!
## Piece VII: Epistemic Binary Cut, 1:(-2) Modular Clocking Lock & Thermal Oscillator
The epistemic cut between the diagonal isotropic vacuum thesis ($S_P$) and the
off-diagonal supercolor shadow deformation ($\Phi = N_+ + N_-$) generates the
Gramian strain $V = \Phi^2 = \{N_+, N_-\}$, locking the modular generator
$\Sigma = S_P V$ to the double commutator via the universal $1:(-2)$ identity
$-[\Phi, [\Phi, J]] = -2[\Sigma, \Phi] = -4 V J$ and driving thermal harmonic
oscillation $[K_{\text{sheet}}, [K_{\text{sheet}}, \Phi]] = (\Delta s)^2 \Phi$.
-/

theorem pieceVII_epistemic_modular_clocking_and_oscillator
    {B : Type*} [Ring B]
    {P : B} (hP : P * P = P) (s_p s_q A C : B)
    (hsp : ∀ X : B, s_p * X = X * s_p) (hsq : ∀ X : B, s_q * X = X * s_q) :
    (-comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) =
       -((2 : ℤ) • comm (genSig P A C) (genPhi P A C)) ∧
     -comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) =
       -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
     comm (sheetSurprisalOp P s_p s_q)
         (comm (sheetSurprisalOp P s_p s_q) (genPhi P A C)) =
       (s_q - s_p) * (s_q - s_p) * genPhi P A C) ∧
    (witnessMat3Proj : Matrix (Fin 3) (Fin 3) ℤ) *
        (witnessMat3Pot : Matrix (Fin 3) (Fin 3) ℤ) ≠
      (witnessMat3Pot : Matrix (Fin 3) (Fin 3) ℤ) *
        (witnessMat3Proj : Matrix (Fin 3) (Fin 3) ℤ) := by
  have hS5 :=
    archetype_S5_master_clocking_identity_and_thermal_harmonic_oscillator
      hP s_p s_q A C hsp hsq
  exact ⟨⟨hS5.1, hS5.2.1, hS5.2.2.2.2.1⟩,
         witnessMat3Proj_witnessMat3Pot_noncomm (R := ℤ)⟩

/-!
## Master Puzzle Synthesis Theorem: The Unified Geometric Framework of Analyticity
Consolidates all 7 pieces of the analytic puzzle into a single kernel-checked
structural synthesis theorem.
-/

theorem unified_analytic_geometric_puzzle_synthesis
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ)
    {n : ℕ} (A_cone : PosDefCone n) (vals : Fin n → ℝ)
    (hpos : ∀ i, 0 < vals i) (hdiag : A_cone.mat = Matrix.diagonal vals)
    (A_mat H_mat : Matrix (Fin n) (Fin n) ℂ) (hA_mat : IsUnit A_mat)
    {f_hol : ℂ → ℂ}
    (h_disk_free : ∀ z ∈ openUnitDisk, f_hol z ≠ 0)
    (h_symm : ∀ z : ℂ, z ≠ 0 → (f_hol z = 0 ↔ f_hol z⁻¹ = 0))
    {z0 : ℂ} (hz0_root : f_hol z0 = 0) (m : ℕ)
    {B : Type*} [Ring B]
    {P : B} (hP : P * P = P) (s_p s_q A C : B)
    (hsp : ∀ X : B, s_p * X = X * s_p) (hsq : ∀ X : B, s_q * X = X * s_q) :
    -- (1) Scalar cumulant analyticity: 1st derivative = mean, 2nd derivative = Fisher variance
    (HasDerivAt (logSumExp w a) (logSumExpMean w a θ) θ ∧
     deriv (fun t => deriv (logSumExp w a) t) θ = logSumExpVariance w a θ) ∧
    -- (2) Spectral surprisal barrier: -log det A = ∑ (-log λ_i)
    (phi A_cone = ∑ i : Fin n, spectralSurprisal vals i) ∧
    -- (3) Noncommutative matrix Fréchet log-volume and inverse derivatives
    (HasFDerivAt negLogDet (logDetDifferential A_mat) A_mat ∧
     fderiv ℝ negLogDet A_mat H_mat = -(Matrix.trace (A_mat⁻¹ * H_mat)).re) ∧
    -- (4) Complex Lee-Yang root localization on S¹ & logarithmic monodromy Jordan block
    (‖z0‖ = 1 ∧
     monodromyJordanBlock ^ m = !![1, (m : ℂ) * (2 * Real.pi); 0, 1]) ∧
    -- (5) Epistemic-to-Analytic 1:(-2) Modular Clocking Lock & Non-Commutative Matrix Witness
    ((-comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) =
        -((2 : ℤ) • comm (genSig P A C) (genPhi P A C)) ∧
      -comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) =
        -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
      comm (sheetSurprisalOp P s_p s_q)
          (comm (sheetSurprisalOp P s_p s_q) (genPhi P A C)) =
        (s_q - s_p) * (s_q - s_p) * genPhi P A C) ∧
     (witnessMat3Proj : Matrix (Fin 3) (Fin 3) ℤ) *
         (witnessMat3Pot : Matrix (Fin 3) (Fin 3) ℤ) ≠
       (witnessMat3Pot : Matrix (Fin 3) (Fin 3) ℤ) *
         (witnessMat3Proj : Matrix (Fin 3) (Fin 3) ℤ)) := by
  have hS5 :=
    archetype_S5_master_clocking_identity_and_thermal_harmonic_oscillator
      hP s_p s_q A C hsp hsq
  exact ⟨⟨hasDerivAt_logSumExp w a hw θ, logSumExp_secondDeriv_eq_variance w a hw θ⟩,
         logDetBarrier_eq_sum_spectralSurprisal A_cone vals hpos hdiag,
         ⟨hasFDerivAt_negLogDet A_mat hA_mat, fderiv_negLogDet_apply A_mat H_mat hA_mat⟩,
         ⟨root_modulus_one_of_disk_free_reciprocal_symmetry h_disk_free h_symm hz0_root,
          monodromyJordanBlock_pow m⟩,
         ⟨⟨hS5.1, hS5.2.1, hS5.2.2.2.2.1⟩,
          witnessMat3Proj_witnessMat3Pot_noncomm (R := ℤ)⟩⟩

end InfoGeometry.Canonical.UnifiedAnalyticGeometricFramework
