/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Conformal.MannheimWeylKazanasCosmology
import InfoGeometry.Conformal.MannheimOpenDebtConstructiveClosure
import InfoGeometry.Synthesis.MannheimTwistorBlochWavefrontEpistemicSynthesis
import InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
import InfoGeometry.Lie.DoubledMinkowskiGradedDifferentialBridge
import InfoGeometry.Lie.DoubledMinkowskiLatticeContinuumLimit
import InfoGeometry.Lie.DoubledMinkowskiManifoldYangMillsPDE

/-!
# Typed Bridge: Mannheim Conformal-Plus-Yang–Mills Unification to Doubled-Minkowski Suite

Constructs the typed Lean 4 bridge connecting Philip Mannheim's conformal-plus-Yang–Mills
local scale–phase unification (`ψ ↦ exp(β(x) + i α(x)) ψ`, `scaleGaugeMultiplier β α`,
`conformalRescale`, `spinorScale`, `vol4Scale`, `gramBlochState`) across all four layers
of the Doubled-Minkowski chiral Yang–Mills suite:

- **Layer 0 (`DoubledMinkowskiCircularChiralYangMillsBridge`)**:
  `mannheimChiralGaugeMat4`, `chiralKreinBilin`, `mannheim_witt_krein_conformal_scaling`,
  `mannheim_weyl_bloch_scale_gauge_invariance`, and
  `mannheim_chiral_phase_curvature_action_covariant`.
- **Layer 1 (`DoubledMinkowskiGradedDifferentialBridge`, R1)**:
  `mannheim_graded_even_compat_preserved` and `mannheim_even_oneForm_abelian_shift`
  (strictly scoped to `circularEvenOmega` / `MatrixIsHomogeneous 1`, keeping degree-mixed
  `circularGradedOmega` distinct).
- **Layer 2 (`DoubledMinkowskiLatticeContinuumLimit`, R2)**:
  `mannheimGaugeShiftMat4` and `mannheim_lattice_continuum_gauge_covariance` (`ContDiff ℝ 3`
  smoothness preservation, Schwarz second-derivative symmetry, `wilsonPlaquette` /
  `continuumCurvature` / `continuumPlaquetteAction` covariance, `Tendsto` continuum limits,
  and `circularColimit_continuum_transport`).
- **Layer 3 (`DoubledMinkowskiManifoldYangMillsPDE`, R3)**:
  `mannheimFiberScalar`, `mannheimGradOneForm`, `mannheim_fiberKreinPairing_scale_phase_law`,
  `mannheim_bundle_covariant_derivative_4d`, `mannheim_ymCurvature_and_pde_invariance`
  (`ContDiff ℝ 2`), and `mannheim_shifted_circularGaugeForm_and_waveForm_solutions`.
-/

noncomputable section

open scoped BigOperators _root_.Topology Matrix MatrixOrder ComplexOrder ComplexConjugate
open InfoGeometry.Conformal.MannheimWeylKazanasCosmology
open InfoGeometry.Conformal.MannheimOpenDebtConstructiveClosure
open InfoGeometry.Synthesis.MannheimTwistorBlochWavefrontEpistemicSynthesis
open InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
open InfoGeometry.Lie
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
  (wittNorm symmSection antiSection)
open InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge (pauliSolder2x2)
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
  (coordinateEquiv frame coordinateEquiv_apply_frame)
open InfoGeometry.Lie.SplitOctonionEllCrossChannel (uPlus uMinus)
open InfoGeometry.Canonical.RealDoubledChiralKreinFrame (frameBasis)
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
  (chiralKreinForm chiralKreinForm_to_doubled)
open InfoGeometry.OperatorAlgebra.PeirceSpine (genPhi genJ genV genSig evenGrade)
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge (peirceGradingDeriv)
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
  (matrixExteriorDerivative matrixTraceForm matrixTrace_one_form_square_eq_zero
   matrixTrace_connection_curvature_exact)
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge (curvatureFromConnection)
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge (covariantDerivative)
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
  (IsHomogeneousExteriorDegree MatrixIsHomogeneous homogeneous_one_iff_exists_generator)
open InfoGeometry.Modular.BlochBallUmegakiAndQuantumSpohn
  (quantumUmegakiGibbs coherenceRelEntropy blochZ)
open InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants (bregmanPhi meanSpin)
open InfoGeometry.MetaCompiler

namespace InfoGeometry.Synthesis.MannheimDoubledMinkowskiYangMillsBridge

/-! ## 0. Explicit Matrix Non-Commutativity Witnesses (T16) -/

/-- Explicit T16 non-commutativity witness in `Matrix (Fin 4) (Fin 4) ℂ`. -/
theorem mannheim_circularConnection_mat4C_noncomm_witness :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℂ, A * B ≠ B * A := by
  refine ⟨chiralProjMat4, circularConnectionMat4 (coordinateEquiv uPlus), ?_⟩
  intro h
  have h02 := congrFun (congrFun h 0) 2
  have hc : coordinateEquiv uPlus = Pi.single 0 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 0
  simp [chiralProjMat4, chiralProj4, chiralDiagBlock4, circularConnectionMat4,
    chiralOffBlock4, Matrix.mul_apply, Fin.sum_univ_four] at h02
  rw [hc] at h02
  simp [weylUpperMat, pauliSolder2x2,
    InfoGeometry.Quantum.PauliSoldering.solder,
    InfoGeometry.Quantum.PauliSoldering.σ0,
    InfoGeometry.Quantum.PauliSoldering.σ1,
    InfoGeometry.Quantum.PauliSoldering.σ2,
    InfoGeometry.Quantum.PauliSoldering.σ3] at h02

/-- Explicit T16 non-commutativity witness in `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem mannheim_weyl_mat2C_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨weylUpperMat (coordinateEquiv (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 0)),
    weylUpperMat (coordinateEquiv (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus 1)), ?_⟩
  exact weylUpperMat_rootPlus_comm.2

/-- Explicit T16 non-commutativity witness in
`Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ))`. -/
theorem mannheim_mat4_exterior_noncomm_witness :
    ∃ A B : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)), A * B ≠ B * A := by
  let P := chiralExteriorProj4 (Fin 4 → ℂ)
  let B := chiralOffBlock4 (1 : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ))) 1
  refine ⟨P, B, ?_⟩
  intro h
  have h02 := congrFun (congrFun h 0) 2
  simp [P, B, chiralExteriorProj4, chiralProj4, chiralDiagBlock4, chiralOffBlock4,
    Matrix.mul_apply, Fin.sum_univ_four] at h02

/-! ## 1. Layer 0: Circular Chiral Yang–Mills, Witt–Krein Scaling, & Bloch Invariance -/

/-- Combined $4 \times 4$ Mannheim conformal-plus-chiral-gauge matrix
`diag(exp(β + i α) I₂, exp(β - i α) I₂)` built from `scaleGaugeMultiplier`. -/
def mannheimChiralGaugeMat4 (β α : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  chiralDiagBlock4
    (scaleGaugeMultiplier β α • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (scaleGaugeMultiplier β (-α) • (1 : Matrix (Fin 2) (Fin 2) ℂ))

private lemma star_scaleGaugeMultiplier (β α : ℝ) :
    star (scaleGaugeMultiplier β α) = scaleGaugeMultiplier β (-α) := by
  dsimp [scaleGaugeMultiplier]
  change starRingEnd ℂ (Complex.exp ((β : ℂ) + (α : ℂ) * Complex.I)) =
    Complex.exp ((β : ℂ) + ((-α : ℝ) : ℂ) * Complex.I)
  rw [← Complex.exp_conj]
  simp [Complex.conj_ofReal, mul_neg]

private lemma scaleGaugeMultiplier_zero_neg_mul (α : ℝ) :
    scaleGaugeMultiplier 0 (-α) * scaleGaugeMultiplier 0 α = 1 := by
  simpa using scaleGaugeMultiplier_neg_mul_cancel 0 α

theorem mannheimChiralGaugeMat4_conjTranspose (β α : ℝ) :
    (mannheimChiralGaugeMat4 β α)ᴴ = mannheimChiralGaugeMat4 β (-α) := by
  rw [mannheimChiralGaugeMat4, chiralDiagBlock4_conjTranspose]
  simp [Matrix.conjTranspose_smul, star_scaleGaugeMultiplier, mannheimChiralGaugeMat4]

theorem mannheimChiralGaugeMat4_add (β₁ α₁ β₂ α₂ : ℝ) :
    mannheimChiralGaugeMat4 (β₁ + β₂) (α₁ + α₂) =
      mannheimChiralGaugeMat4 β₁ α₁ * mannheimChiralGaugeMat4 β₂ α₂ := by
  rw [mannheimChiralGaugeMat4, mannheimChiralGaugeMat4, mannheimChiralGaugeMat4,
    chiralDiagBlock4_mul]
  have h1 :
      scaleGaugeMultiplier (β₁ + β₂) (α₁ + α₂) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
        (scaleGaugeMultiplier β₁ α₁ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier β₂ α₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, scaleGaugeMultiplier_add]
  have h2 :
      scaleGaugeMultiplier (β₁ + β₂) (-(α₁ + α₂)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
        (scaleGaugeMultiplier β₁ (-α₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier β₂ (-α₂) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, ← scaleGaugeMultiplier_add,
      neg_add]
  rw [h1, h2]

theorem mannheimChiralGaugeMat4_zero :
    mannheimChiralGaugeMat4 0 0 = 1 := by
  rw [mannheimChiralGaugeMat4, neg_zero, scaleGaugeMultiplier_zero, one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]

theorem mannheimChiralGaugeMat4_neg_mul_cancel (β α : ℝ) :
    mannheimChiralGaugeMat4 (-β) (-α) * mannheimChiralGaugeMat4 β α = 1 := by
  rw [← mannheimChiralGaugeMat4_add, neg_add_cancel, neg_add_cancel, mannheimChiralGaugeMat4_zero]

theorem mannheimChiralGaugeMat4_mul_neg_cancel (β α : ℝ) :
    mannheimChiralGaugeMat4 β α * mannheimChiralGaugeMat4 (-β) (-α) = 1 := by
  rw [← mannheimChiralGaugeMat4_add, add_neg_cancel, add_neg_cancel, mannheimChiralGaugeMat4_zero]

theorem mannheimChiralGaugeMat4_conjTranspose_mul (β α : ℝ) :
    (mannheimChiralGaugeMat4 β α)ᴴ * mannheimChiralGaugeMat4 β α =
      (Real.exp (2 * β) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [mannheimChiralGaugeMat4_conjTranspose, ← mannheimChiralGaugeMat4_add, neg_add_cancel]
  have h2β : scaleGaugeMultiplier (β + β) 0 = (Real.exp (2 * β) : ℂ) := by
    dsimp [scaleGaugeMultiplier]
    rw [zero_mul, add_zero, ← two_mul, ← Complex.ofReal_exp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mannheimChiralGaugeMat4, chiralDiagBlock4, h2β]

theorem mannheimChiralGaugeMat4_unitary_of_beta_zero (α : ℝ) :
    (mannheimChiralGaugeMat4 0 α)ᴴ * mannheimChiralGaugeMat4 0 α = 1 ∧
    mannheimChiralGaugeMat4 0 α * (mannheimChiralGaugeMat4 0 α)ᴴ = 1 := by
  refine ⟨?_, ?_⟩
  · rw [mannheimChiralGaugeMat4_conjTranspose_mul, mul_zero, Real.exp_zero, Complex.ofReal_one,
      one_smul]
  · rw [mannheimChiralGaugeMat4_conjTranspose]
    simpa using mannheimChiralGaugeMat4_mul_neg_cancel 0 α

theorem mannheimChiralGaugeMat4_chiralProj_comm (β α : ℝ) :
    mannheimChiralGaugeMat4 β α * chiralProjMat4 =
      chiralProjMat4 * mannheimChiralGaugeMat4 β α := by
  change mannheimChiralGaugeMat4 β α * chiralDiagBlock4 1 0 =
    chiralDiagBlock4 1 0 * mannheimChiralGaugeMat4 β α
  rw [mannheimChiralGaugeMat4, chiralDiagBlock4_mul, chiralDiagBlock4_mul]
  simp

/-- Real bilinear form packaging `chiralKreinForm` on `KreinFrame4` for `conformalRescale`. -/
def chiralKreinBilin : LinearMap.BilinForm ℝ KreinFrame4 where
  toFun u :=
    { toFun := fun v => chiralKreinForm (E := FourSpace) u v
      map_add' := fun v w => by
        change inner ℝ (WithLp.fst u) (WithLp.snd v + WithLp.snd w) +
            inner ℝ (WithLp.snd u) (WithLp.fst v + WithLp.fst w) =
          (inner ℝ (WithLp.fst u) (WithLp.snd v) + inner ℝ (WithLp.snd u) (WithLp.fst v)) +
            (inner ℝ (WithLp.fst u) (WithLp.snd w) + inner ℝ (WithLp.snd u) (WithLp.fst w))
        rw [inner_add_right, inner_add_right]
        abel
      map_smul' := fun c v => by
        change inner ℝ (WithLp.fst u) (c • WithLp.snd v) +
            inner ℝ (WithLp.snd u) (c • WithLp.fst v) =
          c * (inner ℝ (WithLp.fst u) (WithLp.snd v) + inner ℝ (WithLp.snd u) (WithLp.fst v))
        rw [real_inner_smul_right, real_inner_smul_right, ← mul_add] }
  map_add' u₁ u₂ := by
    ext v
    change inner ℝ (WithLp.fst u₁ + WithLp.fst u₂) (WithLp.snd v) +
        inner ℝ (WithLp.snd u₁ + WithLp.snd u₂) (WithLp.fst v) =
      (inner ℝ (WithLp.fst u₁) (WithLp.snd v) + inner ℝ (WithLp.snd u₁) (WithLp.fst v)) +
        (inner ℝ (WithLp.fst u₂) (WithLp.snd v) + inner ℝ (WithLp.snd u₂) (WithLp.fst v))
    rw [inner_add_left, inner_add_left]
    abel
  map_smul' c u := by
    ext v
    change inner ℝ (c • WithLp.fst u) (WithLp.snd v) +
        inner ℝ (c • WithLp.snd u) (WithLp.fst v) =
      c * (inner ℝ (WithLp.fst u) (WithLp.snd v) + inner ℝ (WithLp.snd u) (WithLp.fst v))
    rw [real_inner_smul_left, real_inner_smul_left, ← mul_add]

private lemma smul_symm_add_antiSection (r t x1 x2 x3 tau y1 y2 y3 : ℝ) :
    r • (symmSection t x1 x2 x3 + antiSection tau y1 y2 y3) =
      symmSection (r * t) (r * x1) (r * x2) (r * x3) +
        antiSection (r * tau) (r * y1) (r * y2) (r * y3) := by
  ext i
  fin_cases i <;> simp [symmSection, antiSection] <;> ring

private lemma wittNorm_smul (r : ℝ) (x : Coordinate) :
    wittNorm (r • x) = r ^ 2 * wittNorm x := by
  simp only [wittNorm, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Layer 0 (Witt–Krein Conformal Scaling & Pauli Soldering Bridge)**:
Scaling a circular split-octonion coordinate `x` by `r = ‖scaleGaugeMultiplier β α‖ = exp β`
transports linearly to `KreinFrame4`, rescales `wittNorm` and `chiralKreinForm` by `exp (2 β)`,
matches `conformalRescale β chiralKreinBilin`, preserves the null cone `wittNorm x = 0`,
rescales the double-Minkowski Pauli soldering determinant difference by `exp (2 β)`, and
preserves all three $d = 4$ conformal invariance weights (`vol4Scale`, `spinorScale`,
`invTetradScale`, `confScalarScale`). -/
theorem mannheim_witt_krein_conformal_scaling
    (β α : ℝ) (x : Coordinate) (t x1 x2 x3 tau y1 y2 y3 : ℝ) :
    let r : ℝ := ‖scaleGaugeMultiplier β α‖
    let v : Coordinate := symmSection t x1 x2 x3 + antiSection tau y1 y2 y3
    r = Real.exp β ∧
    circularCoordToKreinFrame (r • x) = r • circularCoordToKreinFrame x ∧
    wittNorm (r • x) = Real.exp (2 * β) * wittNorm x ∧
    chiralKreinForm (E := FourSpace)
        (circularCoordToKreinFrame (r • x)) (circularCoordToKreinFrame (r • x)) =
      conformalRescale β chiralKreinBilin
        (circularCoordToKreinFrame x) (circularCoordToKreinFrame x) ∧
    (conformalRescale β chiralKreinBilin
        (circularCoordToKreinFrame x) (circularCoordToKreinFrame x) = 0 ↔
      wittNorm x = 0) ∧
    ((pauliSolder2x2 (r * t) (r * x1) (r * x2) (r * x3)).det -
      (pauliSolder2x2 (r * tau) (r * y1) (r * y2) (r * y3)).det =
        (Real.exp (2 * β) : ℂ) *
          ((pauliSolder2x2 t x1 x2 x3).det - (pauliSolder2x2 tau y1 y2 y3).det) ∧
     (1 / 2 : ℝ) * chiralKreinForm (E := FourSpace)
         (circularCoordToKreinFrame (r • v)) (circularCoordToKreinFrame (r • v)) =
       Real.exp (2 * β) * ((t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2)) -
         (tau ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)))) ∧
    (vol4Scale β * spinorScale β * invTetradScale β * spinorScale β = 1 ∧
     vol4Scale β * confScalarScale β * (spinorScale β) ^ 2 = 1 ∧
     vol4Scale β * (confScalarScale β) ^ 4 = 1) := by
  intro r v
  have hr : r = Real.exp β := norm_scaleGaugeMultiplier β α
  have hexp2 : r ^ 2 = Real.exp (2 * β) := by
    rw [hr, sq, ← Real.exp_add, ← two_mul]
  have hlin : circularCoordToKreinFrame (r • x) = r • circularCoordToKreinFrame x :=
    circularCoordToKreinFrame.map_smul r x
  have hwitt : wittNorm (r • x) = Real.exp (2 * β) * wittNorm x := by
    rw [wittNorm_smul, hexp2]
  have hkrein :
      chiralKreinForm (E := FourSpace)
          (circularCoordToKreinFrame (r • x)) (circularCoordToKreinFrame (r • x)) =
        conformalRescale β chiralKreinBilin
          (circularCoordToKreinFrame x) (circularCoordToKreinFrame x) := by
    rw [chiralKreinForm_diag_eq_two_wittNorm, hwitt]
    dsimp [conformalRescale, chiralKreinBilin]
    rw [chiralKreinForm_diag_eq_two_wittNorm]
    dsimp [wittNorm]
    ring
  have hnull :
      conformalRescale β chiralKreinBilin
          (circularCoordToKreinFrame x) (circularCoordToKreinFrame x) = 0 ↔
        wittNorm x = 0 := by
    rw [conformalRescale_null_cone_iff]
    change chiralKreinForm (E := FourSpace)
        (circularCoordToKreinFrame x) (circularCoordToKreinFrame x) = 0 ↔ wittNorm x = 0
    rw [chiralKreinForm_diag_eq_two_wittNorm]
    simp
  have hpauli :
      (pauliSolder2x2 (r * t) (r * x1) (r * x2) (r * x3)).det -
        (pauliSolder2x2 (r * tau) (r * y1) (r * y2) (r * y3)).det =
          (Real.exp (2 * β) : ℂ) *
            ((pauliSolder2x2 t x1 x2 x3).det - (pauliSolder2x2 tau y1 y2 y3).det) ∧
      (1 / 2 : ℝ) * chiralKreinForm (E := FourSpace)
          (circularCoordToKreinFrame (r • v)) (circularCoordToKreinFrame (r • v)) =
        Real.exp (2 * β) * ((t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2)) -
          (tau ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2))) := by
    have hBridge0 := doubledMinkowski_krein_pauli_soldering_bridge t x1 x2 x3 tau y1 y2 y3
    have hBridgeR :=
      doubledMinkowski_krein_pauli_soldering_bridge
        (r * t) (r * x1) (r * x2) (r * x3) (r * tau) (r * y1) (r * y2) (r * y3)
    dsimp only at hBridge0 hBridgeR
    rw [← smul_symm_add_antiSection] at hBridgeR
    have hv_krein :
        (1 / 2 : ℝ) * chiralKreinForm (E := FourSpace)
            (circularCoordToKreinFrame (r • v)) (circularCoordToKreinFrame (r • v)) =
          Real.exp (2 * β) *
            ((1 / 2 : ℝ) * chiralKreinForm (E := FourSpace)
              (circularCoordToKreinFrame v) (circularCoordToKreinFrame v)) := by
      rw [chiralKreinForm_diag_eq_two_wittNorm, chiralKreinForm_diag_eq_two_wittNorm,
        wittNorm_smul, hexp2]
      ring
    have hK_real :
        (1 / 2 : ℝ) * chiralKreinForm (E := FourSpace)
            (circularCoordToKreinFrame (r • v)) (circularCoordToKreinFrame (r • v)) =
          Real.exp (2 * β) * ((t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2)) -
            (tau ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2))) := by
      rw [hv_krein, hBridge0.1]
    refine ⟨?_, hK_real⟩
    rw [hBridgeR.2, hBridge0.2, hv_krein]
    push_cast
    rfl
  have hweights := dirac_yukawa_quartic_conformal_invariant_vs_mass_breaking β
  exact ⟨hr, hlin, hwitt, hkrein, hnull, hpauli, ⟨hweights.1, hweights.2.1, hweights.2.2.1⟩⟩

/-- **Layer 0 (Weyl–Bloch Scale–Gauge Invariance & Umegaki Pythagoras)**:
Left-multiplying `circularConnectionMat4 x` by `mannheimChiralGaugeMat4 β α` scales the
upper Weyl sheet by `exp(β + i α)` and the lower Weyl sheet by `exp(β - i α)`, leaving
both `gramBlochState` density matrices, strict positivity, and the quantum Umegaki–Bregman
Pythagorean identity completely invariant. -/
theorem mannheim_weyl_bloch_scale_gauge_invariance
    (β α : ℝ) (x : Coordinate) (θ : ℝ) :
    let U_g : Matrix (Fin 2) (Fin 2) ℂ := scaleGaugeMultiplier β α • weylUpperMat x
    let L_g : Matrix (Fin 2) (Fin 2) ℂ := scaleGaugeMultiplier β (-α) • weylLowerMat x
    mannheimChiralGaugeMat4 β α * circularConnectionMat4 x = chiralOffBlock4 U_g L_g ∧
    gramBlochState U_g = gramBlochState (weylUpperMat x) ∧
    gramBlochState L_g = gramBlochState (weylLowerMat x) ∧
    (Matrix.det (weylUpperMat x) ≠ 0 →
      IsStrictlyPositive (gramBlochState U_g) ∧
      0 ≤ quantumUmegakiGibbs (gramBlochState U_g) θ ∧
      quantumUmegakiGibbs (gramBlochState U_g) θ =
        coherenceRelEntropy (gramBlochState U_g) +
          bregmanPhi (blochZ (gramBlochState U_g)) (meanSpin θ)) ∧
    (Matrix.det (weylLowerMat x) ≠ 0 →
      IsStrictlyPositive (gramBlochState L_g) ∧
      0 ≤ quantumUmegakiGibbs (gramBlochState L_g) θ ∧
      quantumUmegakiGibbs (gramBlochState L_g) θ =
        coherenceRelEntropy (gramBlochState L_g) +
          bregmanPhi (blochZ (gramBlochState L_g)) (meanSpin θ)) := by
  intro U_g L_g
  have hMul :
      mannheimChiralGaugeMat4 β α * circularConnectionMat4 x = chiralOffBlock4 U_g L_g := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mannheimChiralGaugeMat4, chiralDiagBlock4, circularConnectionMat4, chiralOffBlock4,
        U_g, L_g, Matrix.mul_apply, Fin.sum_univ_four]
  have hGram := gramBlochState_determinant_and_unconditional_umegaki
  have hU : gramBlochState U_g = gramBlochState (weylUpperMat x) :=
    hGram.2.2.1 β α (weylUpperMat x)
  have hL : gramBlochState L_g = gramBlochState (weylLowerMat x) :=
    hGram.2.2.1 β (-α) (weylLowerMat x)
  refine ⟨hMul, hU, hL, ?_, ?_⟩
  · intro hdet
    rw [hU]
    have hg := hGram.2.2.2 (weylUpperMat x) θ hdet
    exact ⟨hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2⟩
  · intro hdet
    rw [hL]
    have hg := hGram.2.2.2 (weylLowerMat x) θ hdet
    exact ⟨hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2⟩

private lemma weylUpperMat_smul (c : ℝ) (x : Coordinate) :
    weylUpperMat (c • x) = (c : ℂ) • weylUpperMat x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylUpperMat, pauliSolder2x2,
      InfoGeometry.Quantum.PauliSoldering.solder,
      InfoGeometry.Quantum.PauliSoldering.σ0,
      InfoGeometry.Quantum.PauliSoldering.σ1,
      InfoGeometry.Quantum.PauliSoldering.σ2,
      InfoGeometry.Quantum.PauliSoldering.σ3] <;>
    ring

private lemma weylLowerMat_smul (c : ℝ) (x : Coordinate) :
    weylLowerMat (c • x) = (c : ℂ) • weylLowerMat x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylLowerMat, pauliSolder2x2,
      InfoGeometry.Quantum.PauliSoldering.solder,
      InfoGeometry.Quantum.PauliSoldering.σ0,
      InfoGeometry.Quantum.PauliSoldering.σ1,
      InfoGeometry.Quantum.PauliSoldering.σ2,
      InfoGeometry.Quantum.PauliSoldering.σ3] <;>
    ring

private lemma chiralOffBlock4_smul {R : Type*} [CommRing R] (s : R)
    (u l : Matrix (Fin 2) (Fin 2) R) :
    chiralOffBlock4 (s • u) (s • l) = s • chiralOffBlock4 u l := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralOffBlock4]

private lemma circularConnectionMat4_smul (c : ℝ) (x : Coordinate) :
    circularConnectionMat4 (c • x) = (c : ℂ) • circularConnectionMat4 x := by
  rw [circularConnectionMat4, weylUpperMat_smul, weylLowerMat_smul, chiralOffBlock4_smul]
  rfl

private lemma chiralDiagBlock4_mul_chiralOffBlock4 {R : Type*} [Ring R]
    (d₁ d₂ u l : Matrix (Fin 2) (Fin 2) R) :
    chiralDiagBlock4 d₁ d₂ * chiralOffBlock4 u l = chiralOffBlock4 (d₁ * u) (d₂ * l) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralDiagBlock4, chiralOffBlock4, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

private lemma chiralOffBlock4_mul_chiralDiagBlock4 {R : Type*} [Ring R]
    (u l d₁ d₂ : Matrix (Fin 2) (Fin 2) R) :
    chiralOffBlock4 u l * chiralDiagBlock4 d₁ d₂ = chiralOffBlock4 (u * d₂) (l * d₁) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralDiagBlock4, chiralOffBlock4, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

/-- **Layer 0 (Chiral Phase Curvature, Vorticity Action Gap, & Inductive Star-Colimit Transport)**:
Under conformal coordinate scaling `x_sc = exp β • x` and unitary chiral phase conjugation
`Uα = mannheimChiralGaugeMat4 0 α`, the gauged connection `A_g = Uα A_sc Uαᴴ` yields
covariant curvature `F_g = exp(2 β) • F(x)`, `vol4Scale β`-weighted Hilbert–Schmidt action and
vorticity gap (exactly compensated by `vol4Scale (-β)`), and full `InductiveStarColimitCone`
transport of `opElectron`, `opQuadraticCoupling`, `cone.compat`, and `opSpinDipole`. -/
theorem mannheim_chiral_phase_curvature_action_covariant
    (β α : ℝ) (x : Coordinate)
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (k : ℕ)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom (Matrix (Fin 4) (Fin 4) ℂ) (A_tower k)) :
    let Uα : Matrix (Fin 4) (Fin 4) ℂ := mannheimChiralGaugeMat4 0 α
    let x_sc : Coordinate := Real.exp β • x
    let A_sc : Matrix (Fin 4) (Fin 4) ℂ := circularConnectionMat4 x_sc
    let A_g : Matrix (Fin 4) (Fin 4) ℂ := Uα * A_sc * Uαᴴ
    let F_g : Matrix (Fin 4) (Fin 4) ℂ := A_g * A_g
    let ψ : Matrix (Fin 4) (Fin 4) ℂ →+* B_inf := (cone.toColimit k).toRingHom.comp ι.toRingHom
    (Uαᴴ * Uα = 1 ∧ Uα * Uαᴴ = 1) ∧
    A_sc = (Real.exp β : ℂ) • circularConnectionMat4 x ∧
    F_g = circularCurvatureMat4 x_sc ∧
    F_g = (Real.exp (2 * β) : ℂ) • circularCurvatureMat4 x ∧
    (F_gᴴ * F_g).trace =
      (vol4Scale β : ℂ) * ((circularCurvatureMat4 x)ᴴ * circularCurvatureMat4 x).trace ∧
    (F_g * F_g).trace =
      (vol4Scale β : ℂ) * (circularCurvatureMat4 x * circularCurvatureMat4 x).trace ∧
    ((F_gᴴ * F_g).trace - (F_g * F_g).trace =
      ((8 * vol4Scale β * normSq3 (chiralVorticityVec x) : ℝ) : ℂ) ∧
     (vol4Scale (-β) : ℂ) * ((F_gᴴ * F_g).trace - (F_g * F_g).trace) =
      ((8 * normSq3 (chiralVorticityVec x) : ℝ) : ℂ)) ∧
    (CanonicalTwoSheetedInductiveColimit.opElectron (ψ chiralProjMat4) (ψ A_g) (ψ A_g) = ψ A_g ∧
     CanonicalTwoSheetedInductiveColimit.opQuadraticCoupling (ψ chiralProjMat4) (ψ A_g) (ψ A_g) =
       ψ F_g ∧
     (cone.toColimit (k + 1)).toRingHom ((cone.stepHom k).toRingHom (ι.toRingHom F_g)) = ψ F_g ∧
     CanonicalTwoSheetedInductiveColimit.opSpinDipole (ψ chiralProjMat4) (ψ A_g) (ψ A_g) =
       CanonicalTwoSheetedInductiveColimit.opBitGrading (ψ chiralProjMat4) * ψ F_g) := by
  intro Uα x_sc A_sc A_g F_g ψ
  have hUnit := mannheimChiralGaugeMat4_unitary_of_beta_zero α
  have hAsc : A_sc = (Real.exp β : ℂ) • circularConnectionMat4 x :=
    circularConnectionMat4_smul (Real.exp β) x
  have hUα_conj : Uαᴴ = mannheimChiralGaugeMat4 0 (-α) :=
    mannheimChiralGaugeMat4_conjTranspose 0 α
  have hFg_sc : F_g = circularCurvatureMat4 x_sc := by
    have hAA : F_g = Uα * circularCurvatureMat4 x_sc * Uαᴴ := by
      calc
        F_g = (Uα * A_sc * Uαᴴ) * (Uα * A_sc * Uαᴴ) := rfl
        _ = Uα * A_sc * (Uαᴴ * Uα) * A_sc * Uαᴴ := by simp only [Matrix.mul_assoc]
        _ = Uα * A_sc * A_sc * Uαᴴ := by rw [hUnit.1, Matrix.mul_one]
        _ = Uα * (A_sc * A_sc) * Uαᴴ := by simp only [Matrix.mul_assoc]
        _ = Uα * circularCurvatureMat4 x_sc * Uαᴴ := rfl
    rw [hAA, circularCurvatureMat4_eq_diagBlocks, hUα_conj]
    dsimp only [Uα]
    rw [mannheimChiralGaugeMat4, mannheimChiralGaugeMat4, chiralDiagBlock4_mul, chiralDiagBlock4_mul]
    have ha1 : scaleGaugeMultiplier 0 α * scaleGaugeMultiplier 0 (-α) = 1 := by
      rw [mul_comm]; exact scaleGaugeMultiplier_zero_neg_mul α
    have ha2 : scaleGaugeMultiplier 0 (-α) * scaleGaugeMultiplier 0 α = 1 :=
      scaleGaugeMultiplier_zero_neg_mul α
    have hB1 :
        (scaleGaugeMultiplier 0 α • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (weylUpperMat x_sc * weylLowerMat x_sc) *
          (scaleGaugeMultiplier 0 (-α) • 1) =
          weylUpperMat x_sc * weylLowerMat x_sc := by
      rw [Matrix.smul_mul, one_mul, Matrix.mul_smul, mul_one, smul_smul, mul_comm, ha1, one_smul]
    have hB2 :
        (scaleGaugeMultiplier 0 (-α) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (weylLowerMat x_sc * weylUpperMat x_sc) *
          (scaleGaugeMultiplier 0 (- -α) • 1) =
          weylLowerMat x_sc * weylUpperMat x_sc := by
      rw [neg_neg, Matrix.smul_mul, one_mul, Matrix.mul_smul, mul_one, smul_smul, mul_comm, ha2,
        one_smul]
    rw [hB1, hB2]
  have hexp2C : ((Real.exp β : ℂ) * (Real.exp β : ℂ)) = (Real.exp (2 * β) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, ← two_mul]
  have hFg_scale : F_g = (Real.exp (2 * β) : ℂ) • circularCurvatureMat4 x := by
    rw [hFg_sc]
    dsimp only [circularCurvatureMat4]
    rw [← show A_sc = circularConnectionMat4 x_sc from rfl, hAsc, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hexp2C]
  have hvolC : ((Real.exp (2 * β) : ℂ) * (Real.exp (2 * β) : ℂ)) = (vol4Scale β : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have h4 : 2 * β + 2 * β = 4 * β := by ring
    rw [h4]
    rfl
  have hHS :
      (F_gᴴ * F_g).trace =
        (vol4Scale β : ℂ) * ((circularCurvatureMat4 x)ᴴ * circularCurvatureMat4 x).trace := by
    rw [hFg_scale, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.trace_smul, Complex.star_def, Complex.conj_ofReal, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hvolC]
  have hSq :
      (F_g * F_g).trace =
        (vol4Scale β : ℂ) * (circularCurvatureMat4 x * circularCurvatureMat4 x).trace := by
    rw [hFg_scale, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul, ← mul_assoc, hvolC]
  have hGap :
      (F_gᴴ * F_g).trace - (F_g * F_g).trace =
        ((8 * vol4Scale β * normSq3 (chiralVorticityVec x) : ℝ) : ℂ) := by
    rw [hHS, hSq, ← mul_sub, circularCurvatureMat4_vorticity_action_gap x]
    push_cast
    rw [mul_left_comm (vol4Scale β : ℂ) (8 : ℂ), mul_assoc]
  have hGapComp :
      (vol4Scale (-β) : ℂ) * ((F_gᴴ * F_g).trace - (F_g * F_g).trace) =
        ((8 * normSq3 (chiralVorticityVec x) : ℝ) : ℂ) := by
    rw [hGap]
    have hScale : vol4Scale (-β) * vol4Scale β = 1 := by
      dsimp [vol4Scale]
      rw [← Real.exp_add]
      have hz : 4 * -β + 4 * β = 0 := by rw [mul_neg, neg_add_cancel]
      rw [hz, Real.exp_zero]
    push_cast
    calc
      (vol4Scale (-β) : ℂ) * (8 * (vol4Scale β : ℂ) * (normSq3 (chiralVorticityVec x) : ℂ)) =
          8 * ((vol4Scale (-β) * vol4Scale β : ℝ) : ℂ) * (normSq3 (chiralVorticityVec x) : ℂ) := by
        push_cast
        rw [← mul_assoc (vol4Scale (-β) : ℂ), mul_left_comm (vol4Scale (-β) : ℂ) (8 : ℂ)]
      _ = 8 * (1 : ℂ) * (normSq3 (chiralVorticityVec x) : ℂ) := by rw [hScale]; norm_num
      _ = 8 * (normSq3 (chiralVorticityVec x) : ℂ) := by rw [mul_one]
  have hAg_block :
      A_g = chiralOffBlock4
        (scaleGaugeMultiplier 0 (2 * α) • weylUpperMat x_sc)
        (scaleGaugeMultiplier 0 (-2 * α) • weylLowerMat x_sc) := by
    have h2a : scaleGaugeMultiplier 0 α * scaleGaugeMultiplier 0 α =
        scaleGaugeMultiplier 0 (2 * α) := by
      rw [← scaleGaugeMultiplier_add, add_zero, ← two_mul]
    have hn2a : scaleGaugeMultiplier 0 (-α) * scaleGaugeMultiplier 0 (-α) =
        scaleGaugeMultiplier 0 (-2 * α) := by
      rw [← scaleGaugeMultiplier_add, add_zero]
      have hneg : -α + -α = -2 * α := by ring
      rw [hneg]
    dsimp only [A_g, Uα, A_sc]
    rw [hUα_conj, mannheimChiralGaugeMat4, mannheimChiralGaugeMat4, circularConnectionMat4,
      chiralDiagBlock4_mul_chiralOffBlock4, chiralOffBlock4_mul_chiralDiagBlock4]
    have hU :
        (scaleGaugeMultiplier 0 α • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * weylUpperMat x_sc *
          (scaleGaugeMultiplier 0 (- -α) • 1) =
          scaleGaugeMultiplier 0 (2 * α) • weylUpperMat x_sc := by
      rw [neg_neg, Matrix.smul_mul, one_mul, Matrix.mul_smul, mul_one, smul_smul, h2a]
    have hL :
        (scaleGaugeMultiplier 0 (-α) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * weylLowerMat x_sc *
          (scaleGaugeMultiplier 0 (-α) • 1) =
          scaleGaugeMultiplier 0 (-2 * α) • weylLowerMat x_sc := by
      rw [Matrix.smul_mul, one_mul, Matrix.mul_smul, mul_one, smul_smul, hn2a]
    rw [hU, hL]
  have hStar : ∀ M : Matrix (Fin 4) (Fin 4) ℂ, ψ (star M) = star (ψ M) := by
    intro M
    change (cone.toColimit k).toRingHom (ι.toRingHom (star M)) =
      star ((cone.toColimit k).toRingHom (ι.toRingHom M))
    rw [ι.map_star', (cone.toColimit k).map_star']
  have hPψ : ψ chiralProjMat4 * ψ chiralProjMat4 = ψ chiralProjMat4 := by
    rw [← map_mul, chiralProjMat4_idempotent]
  have hOp := CanonicalTwoSheetedInductiveColimit.starRingHom_intertwines_two_sheeted_operators
    ψ hStar chiralProjMat4 A_g A_g
  have hPhiAg : genPhi chiralProjMat4 A_g A_g = A_g := by
    rw [hAg_block]
    exact genPhi_chiralOffBlock4 _ _
  have hGenVAg : genV chiralProjMat4 A_g A_g = F_g := by
    rw [hAg_block]
    change genV (chiralProj4 ℂ) _ _ = _
    rw [genV, InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm,
      InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.conePlus_chiralOffBlock4,
      InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge.coneMinus_chiralOffBlock4,
      chiralOffBlock4_mul, chiralOffBlock4_mul]
    have hFg_diag :
        F_g = chiralDiagBlock4
          ((scaleGaugeMultiplier 0 (2 * α) • weylUpperMat x_sc) *
            (scaleGaugeMultiplier 0 (-2 * α) • weylLowerMat x_sc))
          ((scaleGaugeMultiplier 0 (-2 * α) • weylLowerMat x_sc) *
            (scaleGaugeMultiplier 0 (2 * α) • weylUpperMat x_sc)) := by
      change A_g * A_g = _
      rw [hAg_block, chiralOffBlock4_mul]
    rw [hFg_diag]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]
  have hElec :
      CanonicalTwoSheetedInductiveColimit.opElectron (ψ chiralProjMat4) (ψ A_g) (ψ A_g) = ψ A_g := by
    rw [← hOp.2.2.2.1]
    dsimp [CanonicalTwoSheetedInductiveColimit.opElectron]
    rw [hPhiAg]
  have hQuad :
      CanonicalTwoSheetedInductiveColimit.opQuadraticCoupling (ψ chiralProjMat4) (ψ A_g) (ψ A_g) =
        ψ F_g := by
    rw [← hOp.2.2.2.2.2.1]
    dsimp [CanonicalTwoSheetedInductiveColimit.opQuadraticCoupling]
    rw [hGenVAg]
  have hCocycle :
      (cone.toColimit (k + 1)).toRingHom ((cone.stepHom k).toRingHom (ι.toRingHom F_g)) = ψ F_g :=
    cone.compat k (ι.toRingHom F_g)
  have hSpin :
      CanonicalTwoSheetedInductiveColimit.opSpinDipole (ψ chiralProjMat4) (ψ A_g) (ψ A_g) =
        CanonicalTwoSheetedInductiveColimit.opBitGrading (ψ chiralProjMat4) * ψ F_g := by
    rw [← hQuad]
    dsimp [CanonicalTwoSheetedInductiveColimit.opSpinDipole,
      CanonicalTwoSheetedInductiveColimit.opBitGrading,
      CanonicalTwoSheetedInductiveColimit.opQuadraticCoupling]
    peirce_nf hPψ
  exact ⟨hUnit, hAsc, hFg_sc, hFg_scale, hHS, hSq, ⟨hGap, hGapComp⟩,
    ⟨hElec, hQuad, hCocycle, hSpin⟩⟩

/-! ## 2. Layer 1: Graded Differential Bridge (`DoubledMinkowskiGradedDifferentialBridge`) -/

private lemma matrix_map_alg4_mul_entry
    (U : Matrix (Fin 4) (Fin 4) ℂ)
    (M : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    (i j : Fin 4) :
    ((U.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))) * M) i j =
      ∑ k : Fin 4, U i k • M k j := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Algebra.smul_def]

private lemma matrix_mul_map_alg4_entry
    (M : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    (V : Matrix (Fin 4) (Fin 4) ℂ)
    (i j : Fin 4) :
    (M * (V.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))))) i j =
      ∑ k : Fin 4, V k j • M i k := by
  simp only [Matrix.mul_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Algebra.commutes, Algebra.smul_def]

private lemma matrixExteriorDerivative_conj_map
    (d : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    (U V : Matrix (Fin 4) (Fin 4) ℂ)
    (M : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ))) :
    matrixExteriorDerivative d
        ((U.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))) * M *
          (V.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))))) =
      (U.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))) *
        matrixExteriorDerivative d M *
        (V.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))) := by
  have hLeft : ∀ N : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)),
      matrixExteriorDerivative d
          ((U.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))) * N) =
        (U.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))) *
          matrixExteriorDerivative d N := by
    intro N
    ext i j
    simp only [matrixExteriorDerivative, Matrix.of_apply, matrix_map_alg4_mul_entry,
      map_sum, map_smul]
  have hRight : ∀ N : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)),
      matrixExteriorDerivative d
          (N * (V.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))))) =
        matrixExteriorDerivative d N *
          (V.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))) := by
    intro N
    ext i j
    simp only [matrixExteriorDerivative, Matrix.of_apply, matrix_mul_map_alg4_entry,
      map_sum, map_smul]
  rw [hRight, hLeft]

private lemma peirceGradingDeriv_conj_comm
    {B : Type*} [Ring B] {P U Uinv M : B}
    (hUP : U * P = P * U) (hUinvP : Uinv * P = P * Uinv) :
    peirceGradingDeriv P (U * M * Uinv) = U * peirceGradingDeriv P M * Uinv := by
  simp only [peirceGradingDeriv, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  calc
    P * (U * M * Uinv) - (U * M * Uinv) * P
      = (P * U) * M * Uinv - U * M * (Uinv * P) := by simp only [mul_assoc]
    _ = (U * P) * M * Uinv - U * M * (P * Uinv) := by rw [← hUP, hUinvP]
    _ = U * (P * M - M * P) * Uinv := by noncomm_ring

private lemma matrixIsHomogeneous_one_conj_map
    (U V : Matrix (Fin 4) (Fin 4) ℂ)
    {M : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ))}
    (hM : MatrixIsHomogeneous 1 M) :
    MatrixIsHomogeneous 1
      ((U.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))) * M *
        (V.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))))) := by
  have hLeft : ∀ N : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)),
      MatrixIsHomogeneous 1 N →
      MatrixIsHomogeneous 1 ((U.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))) * N) := by
    intro N hN i j
    rw [matrix_map_alg4_mul_entry]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ (U i k) (hN k j)
  have hRight : ∀ N : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)),
      MatrixIsHomogeneous 1 N →
      MatrixIsHomogeneous 1 (N * (V.map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))))) := by
    intro N hN i j
    rw [matrix_mul_map_alg4_entry]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ (V k j) (hN i k)
  exact hRight _ (hLeft _ hM)

/-- **Layer 1 (Graded & Even Derivation Compatibility Preservation under Chiral Gauge Action)**:
Independent chiral Weyl scale–phase transformations `(β₁, α₁)` on the upper sheet and
`(β₂, α₂)` on the lower sheet lift to invertible matrices `U, Uinv` over
`ExteriorAlgebra ℂ (Fin 4 → ℂ)` commuting with `chiralExteriorProj4`, preserving:
1. `circularGradedDiff` strong derivative eigencondition, curvature decomposition `F = J + V`, and
   `evenGrade P F = V` on `circularGradedOmega x`;
2. `MatrixIsHomogeneous 1`, `circularEvenDiff` strong derivative eigencondition, and covariant vanishing
   `covariantDerivative A_ev' circularEvenDiff (genV P A_ev' A_ev') = 0` on
   `circularEvenOmega x`. -/
theorem mannheim_graded_even_compat_preserved
    (β₁ α₁ β₂ α₂ : ℝ) (x : Coordinate) :
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let U : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
      (chiralDiagBlock4
        (scaleGaugeMultiplier β₁ α₁ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (scaleGaugeMultiplier β₂ α₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ))).map
        (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    let Uinv : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
      (chiralDiagBlock4
        (scaleGaugeMultiplier (-β₁) (-α₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (scaleGaugeMultiplier (-β₂) (-α₂) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).map
        (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    let A_gr := circularGaugeConnection4 (circularGradedOmega x)
    let A_gr' := U * A_gr * Uinv
    let A_ev := circularGaugeConnection4 (circularEvenOmega x)
    let A_ev' := U * A_ev * Uinv
    U * Uinv = 1 ∧
    Uinv * U = 1 ∧
    U * P = P * U ∧
    matrixExteriorDerivative circularGradedDiff A_gr' = peirceGradingDeriv P A_gr' ∧
    curvatureFromConnection circularGradedDiff A_gr' =
      U * curvatureFromConnection circularGradedDiff A_gr * Uinv ∧
    curvatureFromConnection circularGradedDiff A_gr' = genJ P A_gr' A_gr' + genV P A_gr' A_gr' ∧
    evenGrade P (curvatureFromConnection circularGradedDiff A_gr') = genV P A_gr' A_gr' ∧
    MatrixIsHomogeneous 1 A_ev' ∧
    matrixExteriorDerivative circularEvenDiff A_ev' = peirceGradingDeriv P A_ev' ∧
    covariantDerivative A_ev' circularEvenDiff (genV P A_ev' A_ev') = 0 := by
  intro P U Uinv A_gr A_gr' A_ev A_ev'
  let U₀ : Matrix (Fin 4) (Fin 4) ℂ :=
    chiralDiagBlock4
      (scaleGaugeMultiplier β₁ α₁ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (scaleGaugeMultiplier β₂ α₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
  let Uinv₀ : Matrix (Fin 4) (Fin 4) ℂ :=
    chiralDiagBlock4
      (scaleGaugeMultiplier (-β₁) (-α₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (scaleGaugeMultiplier (-β₂) (-α₂) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
  let alg := algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))
  have hU₀_mul : U₀ * Uinv₀ = 1 := by
    rw [show U₀ * Uinv₀ = chiralDiagBlock4
        ((scaleGaugeMultiplier β₁ α₁ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier (-β₁) (-α₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ)))
        ((scaleGaugeMultiplier β₂ α₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier (-β₂) (-α₂) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) from
      chiralDiagBlock4_mul _ _ _ _]
    have h1 :
        (scaleGaugeMultiplier β₁ α₁ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier (-β₁) (-α₁) • 1) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, mul_comm,
        scaleGaugeMultiplier_neg_mul_cancel, one_smul]
    have h2 :
        (scaleGaugeMultiplier β₂ α₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier (-β₂) (-α₂) • 1) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, mul_comm,
        scaleGaugeMultiplier_neg_mul_cancel, one_smul]
    rw [h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]
  have hUinv₀_mul : Uinv₀ * U₀ = 1 := by
    rw [show Uinv₀ * U₀ = chiralDiagBlock4
        ((scaleGaugeMultiplier (-β₁) (-α₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier β₁ α₁ • (1 : Matrix (Fin 2) (Fin 2) ℂ)))
        ((scaleGaugeMultiplier (-β₂) (-α₂) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier β₂ α₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ))) from
      chiralDiagBlock4_mul _ _ _ _]
    have h1 :
        (scaleGaugeMultiplier (-β₁) (-α₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier β₁ α₁ • 1) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
        scaleGaugeMultiplier_neg_mul_cancel, one_smul]
    have h2 :
        (scaleGaugeMultiplier (-β₂) (-α₂) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier β₂ α₂ • 1) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
        scaleGaugeMultiplier_neg_mul_cancel, one_smul]
    rw [h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]
  have hUUinv : U * Uinv = 1 := by
    change U₀.map alg * Uinv₀.map alg = 1
    rw [← Matrix.map_mul, hU₀_mul, Matrix.map_one alg alg.map_zero alg.map_one]
  have hUinvU : Uinv * U = 1 := by
    change Uinv₀.map alg * U₀.map alg = 1
    rw [← Matrix.map_mul, hUinv₀_mul, Matrix.map_one alg alg.map_zero alg.map_one]
  have hP_map : P = (chiralProj4 ℂ).map alg := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, chiralExteriorProj4, chiralProj4, chiralDiagBlock4]
  have hU₀P : U₀ * chiralProj4 ℂ = chiralProj4 ℂ * U₀ := by
    change chiralDiagBlock4 _ _ * chiralDiagBlock4 1 0 = chiralDiagBlock4 1 0 * chiralDiagBlock4 _ _
    rw [chiralDiagBlock4_mul, chiralDiagBlock4_mul]
    simp
  have hUinv₀P : Uinv₀ * chiralProj4 ℂ = chiralProj4 ℂ * Uinv₀ := by
    change chiralDiagBlock4 _ _ * chiralDiagBlock4 1 0 = chiralDiagBlock4 1 0 * chiralDiagBlock4 _ _
    rw [chiralDiagBlock4_mul, chiralDiagBlock4_mul]
    simp
  have hUP : U * P = P * U := by
    rw [hP_map]
    change U₀.map alg * (chiralProj4 ℂ).map alg = (chiralProj4 ℂ).map alg * U₀.map alg
    rw [← Matrix.map_mul, ← Matrix.map_mul, hU₀P]
  have hUinvP : Uinv * P = P * Uinv := by
    rw [hP_map]
    change Uinv₀.map alg * (chiralProj4 ℂ).map alg = (chiralProj4 ℂ).map alg * Uinv₀.map alg
    rw [← Matrix.map_mul, ← Matrix.map_mul, hUinv₀P]
  have hCompatGr :
      matrixExteriorDerivative circularGradedDiff A_gr' = peirceGradingDeriv P A_gr' := by
    change matrixExteriorDerivative circularGradedDiff (U₀.map alg * A_gr * Uinv₀.map alg) =
      peirceGradingDeriv P (U * A_gr * Uinv)
    rw [matrixExteriorDerivative_conj_map, peirceGradingDeriv_conj_comm hUP hUinvP,
      circularGradedDiff_eigencondition x]
  have hCurvGr :
      curvatureFromConnection circularGradedDiff A_gr' =
        U * curvatureFromConnection circularGradedDiff A_gr * Uinv := by
    dsimp only [curvatureFromConnection, A_gr']
    have hD : matrixExteriorDerivative circularGradedDiff (U * A_gr * Uinv) =
        U * matrixExteriorDerivative circularGradedDiff A_gr * Uinv :=
      matrixExteriorDerivative_conj_map circularGradedDiff U₀ Uinv₀ A_gr
    have hSq : (U * A_gr * Uinv) * (U * A_gr * Uinv) = U * (A_gr * A_gr) * Uinv := by
      calc
        (U * A_gr * Uinv) * (U * A_gr * Uinv)
          = U * A_gr * (Uinv * U) * A_gr * Uinv := by simp only [mul_assoc]
        _ = U * A_gr * A_gr * Uinv := by rw [hUinvU, Matrix.mul_one]
        _ = U * (A_gr * A_gr) * Uinv := by simp only [mul_assoc]
    rw [hD, hSq, Matrix.mul_add, Matrix.add_mul]
  have hGenJ : genJ P A_gr' A_gr' = U * genJ P A_gr A_gr * Uinv := by
    simp only [genJ, InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus, A_gr']
    have h1mU : (1 - P) * U = U * (1 - P) := by
      calc
        (1 - P) * U = U - P * U := by rw [sub_mul, one_mul]
        _ = U - U * P := by rw [hUP]
        _ = U * (1 - P) := by rw [mul_sub, mul_one]
    have h1mUinv : (1 - P) * Uinv = Uinv * (1 - P) := by
      calc
        (1 - P) * Uinv = Uinv - P * Uinv := by rw [sub_mul, one_mul]
        _ = Uinv - Uinv * P := by rw [hUinvP]
        _ = Uinv * (1 - P) := by rw [mul_sub, mul_one]
    calc
      P * (U * A_gr * Uinv) * (1 - P) - (1 - P) * (U * A_gr * Uinv) * P
        = (P * U) * A_gr * (Uinv * (1 - P)) - ((1 - P) * U) * A_gr * (Uinv * P) := by
          simp only [mul_assoc]
      _ = (U * P) * A_gr * ((1 - P) * Uinv) - (U * (1 - P)) * A_gr * (P * Uinv) := by
          rw [hUP, h1mUinv, h1mU, hUinvP]
      _ = U * (P * A_gr * (1 - P) - (1 - P) * A_gr * P) * Uinv := by noncomm_ring
  have hGenV : ∀ M : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)),
      genV P (U * M * Uinv) (U * M * Uinv) = U * genV P M M * Uinv := by
    intro M
    have h1mU : (1 - P) * U = U * (1 - P) := by
      calc
        (1 - P) * U = U - P * U := by rw [sub_mul, one_mul]
        _ = U - U * P := by rw [hUP]
        _ = U * (1 - P) := by rw [mul_sub, mul_one]
    have h1mUinv : (1 - P) * Uinv = Uinv * (1 - P) := by
      calc
        (1 - P) * Uinv = Uinv - P * Uinv := by rw [sub_mul, one_mul]
        _ = Uinv - Uinv * P := by rw [hUinvP]
        _ = Uinv * (1 - P) := by rw [mul_sub, mul_one]
    have hcp :
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P (U * M * Uinv) =
          U * InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P M * Uinv := by
      simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus]
      calc
        P * (U * M * Uinv) * (1 - P) = (P * U) * M * (Uinv * (1 - P)) := by
          simp only [mul_assoc]
        _ = (U * P) * M * ((1 - P) * Uinv) := by rw [hUP, h1mUinv]
        _ = U * (P * M * (1 - P)) * Uinv := by simp only [mul_assoc]
    have hcm :
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P (U * M * Uinv) =
          U * InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P M * Uinv := by
      simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus]
      calc
        (1 - P) * (U * M * Uinv) * P = ((1 - P) * U) * M * (Uinv * P) := by
          simp only [mul_assoc]
        _ = (U * (1 - P)) * M * (P * Uinv) := by rw [h1mU, hUinvP]
        _ = U * ((1 - P) * M * P) * Uinv := by simp only [mul_assoc]
    simp only [genV, InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm, hcp, hcm]
    calc
      (U * InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P M * Uinv) *
          (U * InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P M * Uinv) +
        (U * InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P M * Uinv) *
          (U * InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P M * Uinv)
        = U * InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P M * (Uinv * U) *
            InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P M * Uinv +
          U * InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P M * (Uinv * U) *
            InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P M * Uinv := by
          simp only [mul_assoc]
      _ = U * (InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P M *
            InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P M +
          InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P M *
            InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P M) * Uinv := by
          rw [hUinvU]
          noncomm_ring
  have hEven : ∀ M : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)),
      evenGrade P (U * M * Uinv) = U * evenGrade P M * Uinv := by
    intro M
    have h1mU : (1 - P) * U = U * (1 - P) := by
      calc
        (1 - P) * U = U - P * U := by rw [sub_mul, one_mul]
        _ = U - U * P := by rw [hUP]
        _ = U * (1 - P) := by rw [mul_sub, mul_one]
    have h1mUinv : (1 - P) * Uinv = Uinv * (1 - P) := by
      calc
        (1 - P) * Uinv = Uinv - P * Uinv := by rw [sub_mul, one_mul]
        _ = Uinv - Uinv * P := by rw [hUinvP]
        _ = Uinv * (1 - P) := by rw [mul_sub, mul_one]
    simp only [evenGrade]
    calc
      P * (U * M * Uinv) * P + (1 - P) * (U * M * Uinv) * (1 - P)
        = (P * U) * M * (Uinv * P) + ((1 - P) * U) * M * (Uinv * (1 - P)) := by
          simp only [mul_assoc]
      _ = (U * P) * M * (P * Uinv) + (U * (1 - P)) * M * ((1 - P) * Uinv) := by
          rw [hUP, hUinvP, h1mU, h1mUinv]
      _ = U * (P * M * P + (1 - P) * M * (1 - P)) * Uinv := by noncomm_ring
  have hBridgeGr := circularGradedDiff_yang_mills_bridge x
  have hCurvEqGr :
      curvatureFromConnection circularGradedDiff A_gr' = genJ P A_gr' A_gr' + genV P A_gr' A_gr' := by
    rw [hCurvGr, hBridgeGr.2.2.1, hGenJ, hGenV A_gr, Matrix.mul_add, Matrix.add_mul]
  have hEvenEqGr :
      evenGrade P (curvatureFromConnection circularGradedDiff A_gr') = genV P A_gr' A_gr' := by
    rw [hCurvGr, hEven, hBridgeGr.2.2.2.1, hGenV A_gr]
  have hHomEv : MatrixIsHomogeneous 1 A_ev' :=
    matrixIsHomogeneous_one_conj_map U₀ Uinv₀ (circularEvenOmega_homogeneous x)
  have hCompatEv :
      matrixExteriorDerivative circularEvenDiff A_ev' = peirceGradingDeriv P A_ev' := by
    change matrixExteriorDerivative circularEvenDiff (U₀.map alg * A_ev * Uinv₀.map alg) =
      peirceGradingDeriv P (U * A_ev * Uinv)
    rw [matrixExteriorDerivative_conj_map, peirceGradingDeriv_conj_comm hUP hUinvP,
      circularEvenDiff_eigencondition x]
  have hCovEv : covariantDerivative A_ev' circularEvenDiff (genV P A_ev' A_ev') = 0 := by
    dsimp only [covariantDerivative,
      InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge.matrixCommutator]
    rw [hGenV A_ev]
    change matrixExteriorDerivative circularEvenDiff (U₀.map alg * genV P A_ev A_ev * Uinv₀.map alg) +
      (A_ev' * (U * genV P A_ev A_ev * Uinv) - (U * genV P A_ev A_ev * Uinv) * A_ev') = 0
    rw [matrixExteriorDerivative_conj_map]
    have hCommConj :
        A_ev' * (U * genV P A_ev A_ev * Uinv) - (U * genV P A_ev A_ev * Uinv) * A_ev' =
          U * (A_ev * genV P A_ev A_ev - genV P A_ev A_ev * A_ev) * Uinv := by
      dsimp only [A_ev']
      calc
        (U * A_ev * Uinv) * (U * genV P A_ev A_ev * Uinv) -
            (U * genV P A_ev A_ev * Uinv) * (U * A_ev * Uinv)
          = U * A_ev * (Uinv * U) * genV P A_ev A_ev * Uinv -
              U * genV P A_ev A_ev * (Uinv * U) * A_ev * Uinv := by
            simp only [mul_assoc]
        _ = U * (A_ev * genV P A_ev A_ev - genV P A_ev A_ev * A_ev) * Uinv := by
          rw [hUinvU]
          noncomm_ring
    rw [hCommConj]
    have hZero :
        U * matrixExteriorDerivative circularEvenDiff (genV P A_ev A_ev) * Uinv +
          U * (A_ev * genV P A_ev A_ev - genV P A_ev A_ev * A_ev) * Uinv =
          U * covariantDerivative A_ev circularEvenDiff (genV P A_ev A_ev) * Uinv := by
      dsimp only [covariantDerivative,
        InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge.matrixCommutator]
      noncomm_ring
    rw [hZero, circularEvenDiff_covariant_vanishing x, Matrix.mul_zero, Matrix.zero_mul]
  exact ⟨hUUinv, hUinvU, hUP, hCompatGr, hCurvGr, hCurvEqGr, hEvenEqGr, hHomEv, hCompatEv, hCovEv⟩

/-- General abelian 1-form shift invariance for `A * A` on any `MatrixIsHomogeneous 1` matrix
(holds strictly in degree 1 by anticommutativity `ι u * ι v + ι v * ι u = 0`). -/
theorem oneForm_abelian_shift_sq_invariant
    {n : ℕ} (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    (hA : MatrixIsHomogeneous 1 A)
    (η : ExteriorAlgebra ℂ (Fin 4 → ℂ))
    (hη : IsHomogeneousExteriorDegree 1 η) :
    let S : Matrix (Fin n) (Fin n) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
      Matrix.diagonal (fun _ => η)
    MatrixIsHomogeneous 1 (A + S) ∧
    (A + S) * (A + S) = A * A := by
  intro S
  have hS : MatrixIsHomogeneous 1 S := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simpa [S] using hη
    · simp only [S, Matrix.diagonal_apply_ne _ hij]
      exact Submodule.zero_mem _
  have hAS_hom : MatrixIsHomogeneous 1 (A + S) := fun i j => Submodule.add_mem _ (hA i j) (hS i j)
  rcases (homogeneous_one_iff_exists_generator η).mp hη with ⟨v, hv⟩
  have hSS : S * S = 0 := by
    dsimp only [S]
    rw [Matrix.diagonal_mul_diagonal]
    have hSq0 : η * η = 0 := by
      rw [← hv]
      exact ExteriorAlgebra.ι_sq_zero v
    simp [hSq0]
  have hAnticomm : A * S + S * A = 0 := by
    ext i j
    rcases (homogeneous_one_iff_exists_generator (A i j)).mp (hA i j) with ⟨u, hu⟩
    simp only [S, Matrix.add_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Matrix.zero_apply]
    rw [← hu, ← hv]
    exact ExteriorAlgebra.ι_add_mul_swap u v
  have hSq : (A + S) * (A + S) = A * A := by
    calc
      (A + S) * (A + S) = A * A + (A * S + S * A) + S * S := by noncomm_ring
      _ = A * A := by rw [hAnticomm, hSS, add_zero, add_zero]
  exact ⟨hAS_hom, hSq⟩

/-- **Layer 1 (Abelian 1-Form Shift Strictly Scoped to `circularEvenOmega` / `MatrixIsHomogeneous 1`)**:
Shifting the homogeneous 1-form connection `A = circularGaugeConnection4 (circularEvenOmega x)`
by a diagonal abelian 1-form `S = diag(η, η, η, η)` preserves `MatrixIsHomogeneous 1`, leaves
`A * A` and `matrixTraceForm (A * A) = 0` invariant, commutes with `chiralExteriorProj4`, and
shifts `curvatureFromConnection d` by `matrixExteriorDerivative d S` (with `matrixTraceForm`
exact `d (matrixTraceForm S)` and full curvature invariance when `d η = 0`). -/
theorem mannheim_even_oneForm_abelian_shift
    (d : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    (x : Coordinate) (η : ExteriorAlgebra ℂ (Fin 4 → ℂ))
    (hη : IsHomogeneousExteriorDegree 1 η) :
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let A := circularGaugeConnection4 (circularEvenOmega x)
    let S : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
      Matrix.diagonal (fun _ => η)
    MatrixIsHomogeneous 1 (A + S) ∧
    (A + S) * (A + S) = A * A ∧
    matrixTraceForm ((A + S) * (A + S)) = 0 ∧
    peirceGradingDeriv P (A + S) = peirceGradingDeriv P A ∧
    curvatureFromConnection d (A + S) =
      curvatureFromConnection d A + matrixExteriorDerivative d S ∧
    matrixTraceForm (curvatureFromConnection d (A + S)) = d (matrixTraceForm S) ∧
    (d η = 0 →
      matrixExteriorDerivative d (A + S) = matrixExteriorDerivative d A ∧
      curvatureFromConnection d (A + S) = curvatureFromConnection d A) := by
  intro P A S
  have hShift := oneForm_abelian_shift_sq_invariant A (circularEvenOmega_homogeneous x) η hη
  have hHom : MatrixIsHomogeneous 1 (A + S) := hShift.1
  have hSq : (A + S) * (A + S) = A * A := hShift.2
  have hTrSq : matrixTraceForm ((A + S) * (A + S)) = 0 :=
    matrixTrace_one_form_square_eq_zero (A + S) hHom
  have hPS : P * S = S * P := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, S, chiralExteriorProj4, chiralProj4, chiralDiagBlock4]
  have hPeirce : peirceGradingDeriv P (A + S) = peirceGradingDeriv P A := by
    simp only [peirceGradingDeriv, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    calc
      P * (A + S) - (A + S) * P = (P * A - A * P) + (P * S - S * P) := by noncomm_ring
      _ = P * A - A * P := by rw [hPS, sub_self, add_zero]
  have hDerivAdd :
      matrixExteriorDerivative d (A + S) =
        matrixExteriorDerivative d A + matrixExteriorDerivative d S := by
    ext i j
    simp [matrixExteriorDerivative, map_add]
  have hCurvAdd :
      curvatureFromConnection d (A + S) =
        curvatureFromConnection d A + matrixExteriorDerivative d S := by
    dsimp only [curvatureFromConnection]
    rw [hDerivAdd, hSq]
    abel
  have hTrA : matrixTraceForm A = 0 := by
    simp [matrixTraceForm, A, circularGaugeConnection4, chiralOffBlock4, Fin.sum_univ_four]
  have hTrCurv :
      matrixTraceForm (curvatureFromConnection d (A + S)) = d (matrixTraceForm S) := by
    dsimp only [curvatureFromConnection]
    rw [matrixTrace_connection_curvature_exact d (A + S) hHom, LinearMap.map_add, hTrA, zero_add]
  refine ⟨hHom, hSq, hTrSq, hPeirce, hCurvAdd, hTrCurv, ?_⟩
  intro hdη
  have hdS : matrixExteriorDerivative d S = 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [matrixExteriorDerivative, S, hdη]
    · simp [matrixExteriorDerivative, S, hij]
  refine ⟨?_, ?_⟩
  · rw [hDerivAdd, hdS, add_zero]
  · rw [hCurvAdd, hdS, add_zero]

/-! ## 3. Layer 2: Lattice–Continuum Limit (`DoubledMinkowskiLatticeContinuumLimit`) -/

section Layer2LatticeContinuum

open scoped Matrix.Norms.Operator

/-- Abelian Weyl-plus-phase logarithmic 1-form shift
`(∂_μ β(y) + i ∂_μ α(y)) • I₄` induced by `ψ(y) ↦ exp(β(y) + i α(y)) ψ(y)`. -/
def mannheimGaugeShiftMat4
    (β α : FourSpace → ℝ) (y : FourSpace) (μ : Fin 4) : Mat4C :=
  (((fderiv ℝ β y (frameBasis μ) : ℝ) : ℂ) +
    Complex.I * ((fderiv ℝ α y (frameBasis μ) : ℝ) : ℂ)) • (1 : Mat4C)

theorem mannheimGaugeShiftMat4_contDiff
    {β α : FourSpace → ℝ} (hβ : ContDiff ℝ 3 β) (hα : ContDiff ℝ 3 α) :
    ContDiff ℝ 2 (mannheimGaugeShiftMat4 β α) := by
  have hβ' : ContDiff ℝ 2 (fderiv ℝ β) := hβ.fderiv_right (by norm_num)
  have hα' : ContDiff ℝ 2 (fderiv ℝ α) := hα.fderiv_right (by norm_num)
  refine contDiff_pi.mpr fun μ => ?_
  have hβμ : ContDiff ℝ 2 (fun z => fderiv ℝ β z (frameBasis μ)) :=
    hβ'.clm_apply contDiff_const
  have hαμ : ContDiff ℝ 2 (fun z => fderiv ℝ α z (frameBasis μ)) :=
    hα'.clm_apply contDiff_const
  have hβC : ContDiff ℝ 2 (fun z => ((fderiv ℝ β z (frameBasis μ) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hβμ
  have hαC : ContDiff ℝ 2 (fun z => Complex.I * ((fderiv ℝ α z (frameBasis μ) : ℝ) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hαμ)
  exact (hβC.add hαC).smul_const (1 : Mat4C)

private lemma fderiv_apply_frameBasis_symm
    {β : FourSpace → ℝ} (hβ : ContDiff ℝ 2 β) (y : FourSpace) (μ ν : Fin 4) :
    fderiv ℝ (fun z => fderiv ℝ β z (frameBasis ν)) y (frameBasis μ) =
      fderiv ℝ (fun z => fderiv ℝ β z (frameBasis μ)) y (frameBasis ν) := by
  have hDiff : DifferentiableAt ℝ (fderiv ℝ β) y :=
    ((hβ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  have hSwap : ∀ (u v : FourSpace),
      fderiv ℝ (fun z => fderiv ℝ β z v) y u = fderiv ℝ (fderiv ℝ β) y u v := by
    intro u v
    rw [fderiv_clm_apply hDiff (differentiableAt_const v), fderiv_const_apply]
    simp [ContinuousLinearMap.comp_zero]
  rw [hSwap (frameBasis μ) (frameBasis ν), hSwap (frameBasis ν) (frameBasis μ)]
  exact (hβ.contDiffAt.isSymmSndFDerivAt (by simp)).eq (frameBasis μ) (frameBasis ν)

private def chiralConjCLM (U Uinv : Mat4C) : Mat4C →L[ℝ] Mat4C :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => U * M * Uinv
      map_add' := fun M₁ M₂ => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c M => by
        change U * (c • M) * Uinv = c • (U * M * Uinv)
        rw [Matrix.mul_smul, Matrix.smul_mul] }

private lemma fderiv_chiralConjCLM_comp (U Uinv : Mat4C) {g : FourSpace → Mat4C}
    {y : FourSpace} (hg : DifferentiableAt ℝ g y) (v : FourSpace) :
    fderiv ℝ (fun z => U * g z * Uinv) y v = U * fderiv ℝ g y v * Uinv := by
  have hComp :
      fderiv ℝ (fun z => (chiralConjCLM U Uinv) (g z)) y =
        (chiralConjCLM U Uinv).comp (fderiv ℝ g y) :=
    ((chiralConjCLM U Uinv).hasFDerivAt.comp y hg.hasFDerivAt).fderiv
  change (fderiv ℝ (fun z => (chiralConjCLM U Uinv) (g z)) y) v =
    (chiralConjCLM U Uinv) ((fderiv ℝ g y) v)
  rw [hComp]
  rfl

private lemma fderiv_mannheimGaugeShiftMat4_apply
    {β α : FourSpace → ℝ} (hβ : ContDiff ℝ 3 β) (hα : ContDiff ℝ 3 α)
    (y : FourSpace) (ρ σ : Fin 4) :
    fderiv ℝ (fun z => mannheimGaugeShiftMat4 β α z ρ) y (frameBasis σ) =
      (((fderiv ℝ (fun z => fderiv ℝ β z (frameBasis ρ)) y (frameBasis σ) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ (fun z => fderiv ℝ α z (frameBasis ρ)) y (frameBasis σ) : ℝ) : ℂ)) •
        (1 : Mat4C) := by
  have hβ2 : ContDiff ℝ 2 β := hβ.of_le (by norm_num)
  have hα2 : ContDiff ℝ 2 α := hα.of_le (by norm_num)
  have hDβ : DifferentiableAt ℝ (fun z => fderiv ℝ β z (frameBasis ρ)) y :=
    (((hβ2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)) y
  have hDα : DifferentiableAt ℝ (fun z => fderiv ℝ α z (frameBasis ρ)) y :=
    (((hα2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)) y
  have h1 : HasFDerivAt (fun z => ((fderiv ℝ β z (frameBasis ρ) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun z => fderiv ℝ β z (frameBasis ρ)) y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hDβ.hasFDerivAt
  have h2 : HasFDerivAt (fun z => Complex.I * ((fderiv ℝ α z (frameBasis ρ) : ℝ) : ℂ))
      ((ContinuousLinearMap.mul ℝ ℂ Complex.I).comp
        (Complex.ofRealCLM.comp (fderiv ℝ (fun z => fderiv ℝ α z (frameBasis ρ)) y))) y :=
    (ContinuousLinearMap.mul ℝ ℂ Complex.I).hasFDerivAt.comp y
      (Complex.ofRealCLM.hasFDerivAt.comp y hDα.hasFDerivAt)
  have h3 : HasFDerivAt (fun z => mannheimGaugeShiftMat4 β α z ρ)
      (((Complex.ofRealCLM.comp (fderiv ℝ (fun z => fderiv ℝ β z (frameBasis ρ)) y) +
        (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp
          (Complex.ofRealCLM.comp (fderiv ℝ (fun z => fderiv ℝ α z (frameBasis ρ)) y)))).smulRight
        (1 : Mat4C)) y :=
    (h1.add h2).smul_const (1 : Mat4C)
  rw [h3.fderiv]
  simp

private lemma mannheimGaugeShiftMat4_comm (β α : FourSpace → ℝ)
    (y : FourSpace) (μ : Fin 4) (M : Mat4C) :
    mannheimGaugeShiftMat4 β α y μ * M = M * mannheimGaugeShiftMat4 β α y μ := by
  dsimp only [mannheimGaugeShiftMat4]
  rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

private lemma mannheimGaugeShiftMat4_conj (U Uinv : Mat4C)
    (hUUinv : U * Uinv = 1) (β α : FourSpace → ℝ) (y : FourSpace) (μ : Fin 4) :
    U * mannheimGaugeShiftMat4 β α y μ * Uinv = mannheimGaugeShiftMat4 β α y μ := by
  dsimp only [mannheimGaugeShiftMat4]
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, hUUinv]

set_option backward.isDefEq.respectTransparency false in
private lemma exp_scalar_one_mul_conj (c : ℂ) (M : Mat4C) :
    NormedSpace.exp (c • (1 : Mat4C)) * M * (NormedSpace.exp (c • (1 : Mat4C)))⁻¹ = M := by
  have hDiag : c • (1 : Mat4C) = Matrix.diagonal (fun _ : Fin 4 => c) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hExp : NormedSpace.exp (Matrix.diagonal (fun _ : Fin 4 => c)) =
      (NormedSpace.exp c : ℂ) • (1 : Mat4C) := by
    rw [Matrix.exp_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hNeg : ((NormedSpace.exp c : ℂ) • (1 : Mat4C))⁻¹ =
      ((NormedSpace.exp (-c) : ℂ)) • (1 : Mat4C) := by
    rw [← hExp, ← Matrix.exp_neg]
    have hNegD : -(Matrix.diagonal (fun _ : Fin 4 => c)) =
        Matrix.diagonal (fun _ : Fin 4 => -c) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hNegD, Matrix.exp_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hExpCancel : (NormedSpace.exp c : ℂ) * NormedSpace.exp (-c) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.all c (-c)), add_neg_cancel, NormedSpace.exp_zero]
  rw [hDiag, hExp, hNeg, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul, mul_comm,
    hExpCancel, one_smul]

set_option backward.isDefEq.respectTransparency false in
private lemma unitary_conj_hs_trace (U : Mat4C)
    (hUH : Uᴴ * U = 1) (hUinv : U⁻¹ = Uᴴ) (M : Mat4C) :
    ((U * M * U⁻¹)ᴴ * (U * M * U⁻¹)).trace = (Mᴴ * M).trace := by
  rw [hUinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hInner : U * Mᴴ * Uᴴ * (U * M * Uᴴ) = U * (Mᴴ * M) * Uᴴ := by
    calc
      U * Mᴴ * Uᴴ * (U * M * Uᴴ) = U * Mᴴ * (Uᴴ * U) * M * Uᴴ := by
        simp only [Matrix.mul_assoc]
      _ = U * Mᴴ * M * Uᴴ := by rw [hUH, Matrix.mul_one]
      _ = U * (Mᴴ * M) * Uᴴ := by simp only [Matrix.mul_assoc]
  rw [show U * (Mᴴ * Uᴴ) * (U * M * Uᴴ) = U * Mᴴ * Uᴴ * (U * M * Uᴴ) by simp only [Matrix.mul_assoc],
    hInner, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUH, Matrix.one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- **Layer 2 (Lattice–Continuum Gauge Covariance & `ContDiff ℝ 3` Continuum Limits)**:
Under local smooth Mannheim scale–phase fields `β, α : FourSpace → ℝ` (`ContDiff ℝ 3`) and
global chiral unitary conjugation `U = chiralDiagBlock4 (exp(i α₁) I₂) (exp(i α₂) I₂)`,
the gauged connection `A_full z ρ = U * A z ρ * U⁻¹ + mannheimGaugeShiftMat4 β α z ρ` and
matter field `Φ_conj z = U * Φ z * U⁻¹` preserve `ContDiff ℝ 2` and `DifferentiableAt`, factor
`circularLinkTransport`, render `latticeCovariantDiff`, `continuumCovariantDeriv`,
`wilsonPlaquette`, `continuumCurvature`, `wilsonPlaquetteAction`, and `continuumPlaquetteAction`
exact-covariant/invariant (via Schwarz second-derivative symmetry), preserve both `a → 0`
Wilson-plaquette continuum `Tendsto` limits, and transport along `circularColimit_continuum_transport`. -/
theorem mannheim_lattice_continuum_gauge_covariance
    (α₁ α₂ : ℝ) (β α : FourSpace → ℝ)
    (hβ : ContDiff ℝ 3 β) (hα : ContDiff ℝ 3 α)
    (x : FourSpace → Fin 4 → Coordinate)
    (A : FourSpace → Fin 4 → Mat4C) (hA : ContDiff ℝ 2 A)
    (Φ : FourSpace → Mat4C) (y : FourSpace) (hΦ : DifferentiableAt ℝ Φ y)
    (μ ν : Fin 4) :
    let U : Mat4C := chiralDiagBlock4
      (scaleGaugeMultiplier 0 α₁ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (scaleGaugeMultiplier 0 α₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    let S := mannheimGaugeShiftMat4 β α
    let A_shift : FourSpace → Fin 4 → Mat4C := fun z ρ => A z ρ + S z ρ
    let A_conj : FourSpace → Fin 4 → Mat4C := fun z ρ => U * A z ρ * U⁻¹
    let A_full : FourSpace → Fin 4 → Mat4C := fun z ρ => U * A z ρ * U⁻¹ + S z ρ
    let Φ_conj : FourSpace → Mat4C := fun z => U * Φ z * U⁻¹
    ContDiff ℝ 2 A_shift ∧
    ContDiff ℝ 2 A_conj ∧
    ContDiff ℝ 2 A_full ∧
    DifferentiableAt ℝ Φ_conj y ∧
    (∀ a : ℝ,
      NormedSpace.exp (a • (circularConnectionMat4 (x y μ) + S y μ)) =
        circularLinkTransport x y μ a * NormedSpace.exp (a • S y μ) ∧
      NormedSpace.exp (a • (U * circularConnectionMat4 (x y μ) * U⁻¹)) =
        U * circularLinkTransport x y μ a * U⁻¹) ∧
    (∀ a : ℝ, latticeCovariantDiff A_shift Φ y μ a = latticeCovariantDiff A Φ y μ a) ∧
    (∀ a : ℝ, latticeCovariantDiff A_full Φ_conj y μ a =
      U * latticeCovariantDiff A Φ y μ a * U⁻¹) ∧
    continuumCovariantDeriv A_full Φ_conj y μ = U * continuumCovariantDeriv A Φ y μ * U⁻¹ ∧
    (∀ a : ℝ, wilsonPlaquette A_conj y μ ν a = U * wilsonPlaquette A y μ ν a * U⁻¹) ∧
    (∀ a : ℝ, wilsonPlaquetteAction A_conj y μ ν a = wilsonPlaquetteAction A y μ ν a) ∧
    continuumCurvature A_shift y μ ν = continuumCurvature A y μ ν ∧
    continuumCurvature A_full y μ ν = U * continuumCurvature A y μ ν * U⁻¹ ∧
    continuumPlaquetteAction A_shift y μ ν = continuumPlaquetteAction A y μ ν ∧
    continuumPlaquetteAction A_full y μ ν = continuumPlaquetteAction A y μ ν ∧
    Filter.Tendsto (fun a : ℝ => (a ^ 2)⁻¹ • (wilsonPlaquette A_full y μ ν a - 1))
      (𝓝[≠] 0) (𝓝 (U * continuumCurvature A y μ ν * U⁻¹)) ∧
    Filter.Tendsto (fun a : ℝ => wilsonPlaquetteAction A_full y μ ν a)
      (𝓝[≠] 0) (𝓝 (continuumPlaquetteAction A y μ ν)) ∧
    (∀ {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
       {B_inf : Type*} [Ring B_inf] [StarRing B_inf] [TopologicalSpace B_inf]
       (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
       (k : ℕ)
       (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C (A_tower k)),
       Continuous ((cone.toColimit k).toRingHom.comp ι.toRingHom) →
       let ψ : Mat4C →+* B_inf := (cone.toColimit k).toRingHom.comp ι.toRingHom
       Filter.Tendsto (fun a : ℝ => ψ (latticeCovariantDiff A_full Φ_conj y μ a))
         (𝓝[≠] 0) (𝓝 (ψ U * ψ (continuumCovariantDeriv A Φ y μ) * ψ U⁻¹)) ∧
       Filter.Tendsto (fun a : ℝ => ψ ((a ^ 2)⁻¹ • (wilsonPlaquette A_full y μ ν a - 1)))
         (𝓝[≠] 0) (𝓝 (ψ U * ψ (continuumCurvature A y μ ν) * ψ U⁻¹)) ∧
       Filter.Tendsto (fun a : ℝ => ψ (U * circularLinkTransport x y μ a * U⁻¹))
         (𝓝 0) (𝓝 (1 : B_inf)) ∧
       Filter.Tendsto (fun a : ℝ => ψ (a⁻¹ • (U * circularLinkTransport x y μ a * U⁻¹ - 1)))
         (𝓝[≠] 0) (𝓝 (ψ U * ψ (circularConnectionMat4 (x y μ)) * ψ U⁻¹))) := by
  intro U S A_shift A_conj A_full Φ_conj
  let U_inv : Mat4C := chiralDiagBlock4
    (scaleGaugeMultiplier 0 (-α₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (scaleGaugeMultiplier 0 (-α₂) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
  have hUH_eq : Uᴴ = U_inv := by
    rw [chiralDiagBlock4_conjTranspose]
    simp [Matrix.conjTranspose_smul, star_scaleGaugeMultiplier, U_inv]
  have hU_mul_inv : U * U_inv = 1 := by
    dsimp only [U, U_inv]
    rw [chiralDiagBlock4_mul]
    have h1 :
        (scaleGaugeMultiplier 0 α₁ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier 0 (-α₁) • 1) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, mul_comm,
        scaleGaugeMultiplier_zero_neg_mul, one_smul]
    have h2 :
        (scaleGaugeMultiplier 0 α₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier 0 (-α₂) • 1) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, mul_comm,
        scaleGaugeMultiplier_zero_neg_mul, one_smul]
    rw [h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]
  have hU_inv_mul : U_inv * U = 1 := by
    dsimp only [U, U_inv]
    rw [chiralDiagBlock4_mul]
    have h1 :
        (scaleGaugeMultiplier 0 (-α₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier 0 α₁ • 1) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
        scaleGaugeMultiplier_zero_neg_mul, one_smul]
    have h2 :
        (scaleGaugeMultiplier 0 (-α₂) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scaleGaugeMultiplier 0 α₂ • 1) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
        scaleGaugeMultiplier_zero_neg_mul, one_smul]
    rw [h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]
  have hU_inv_eq : U⁻¹ = U_inv := Matrix.inv_eq_right_inv hU_mul_inv
  have hUUinv : U * U⁻¹ = 1 := by rw [hU_inv_eq, hU_mul_inv]
  have hUinvU : U⁻¹ * U = 1 := by rw [hU_inv_eq, hU_inv_mul]
  have hU_unit : IsUnit U := ⟨⟨U, U⁻¹, hUUinv, hUinvU⟩, rfl⟩
  have hUH : Uᴴ * U = 1 := by rw [hUH_eq, hU_inv_mul]
  have hUinv_H : U⁻¹ = Uᴴ := by rw [hU_inv_eq, hUH_eq]
  have hS_cd : ContDiff ℝ 2 S := mannheimGaugeShiftMat4_contDiff hβ hα
  have hA_shift_cd : ContDiff ℝ 2 A_shift := hA.add hS_cd
  have hA_conj_cd : ContDiff ℝ 2 A_conj := by
    refine contDiff_pi.mpr fun ρ => ?_
    exact (chiralConjCLM U U⁻¹).contDiff.comp (contDiff_pi.mp hA ρ)
  have hA_full_cd : ContDiff ℝ 2 A_full := hA_conj_cd.add hS_cd
  have hΦ_conj_diff : DifferentiableAt ℝ Φ_conj y :=
    (chiralConjCLM U U⁻¹).differentiableAt.comp y hΦ
  have hLink : ∀ a : ℝ,
      NormedSpace.exp (a • (circularConnectionMat4 (x y μ) + S y μ)) =
        circularLinkTransport x y μ a * NormedSpace.exp (a • S y μ) ∧
      NormedSpace.exp (a • (U * circularConnectionMat4 (x y μ) * U⁻¹)) =
        U * circularLinkTransport x y μ a * U⁻¹ := by
    intro a
    refine ⟨?_, ?_⟩
    · rw [smul_add]
      refine Matrix.exp_add_of_commute _ _ ?_
      change (a • circularConnectionMat4 (x y μ)) * (a • S y μ) =
        (a • S y μ) * (a • circularConnectionMat4 (x y μ))
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
        mannheimGaugeShiftMat4_comm]
    · have hConj : a • (U * circularConnectionMat4 (x y μ) * U⁻¹) =
          U * (a • circularConnectionMat4 (x y μ)) * U⁻¹ := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [hConj, Matrix.exp_conj _ _ hU_unit]
      rfl
  have hLatShift :
      ∀ a : ℝ, latticeCovariantDiff A_shift Φ y μ a = latticeCovariantDiff A Φ y μ a := by
    intro a
    dsimp only [latticeCovariantDiff, A_shift]
    have hComm : Commute (a • A y μ) (a • S y μ) := by
      change (a • A y μ) * (a • S y μ) = (a • S y μ) * (a • A y μ)
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
        mannheimGaugeShiftMat4_comm]
    have hExp : NormedSpace.exp (a • (A y μ + S y μ)) =
        NormedSpace.exp (a • A y μ) * NormedSpace.exp (a • S y μ) := by
      rw [smul_add]
      exact Matrix.exp_add_of_commute _ _ hComm
    have hExpInv :
        (NormedSpace.exp (a • A y μ) * NormedSpace.exp (a • S y μ))⁻¹ =
          (NormedSpace.exp (a • S y μ))⁻¹ * (NormedSpace.exp (a • A y μ))⁻¹ := by
      rw [← hExp, ← Matrix.exp_neg, ← Matrix.exp_neg, ← Matrix.exp_neg, smul_add, neg_add,
        add_comm (-(a • A y μ)) (-(a • S y μ))]
      exact Matrix.exp_add_of_commute _ _ hComm.symm.neg_left.neg_right
    rw [hExp, hExpInv]
    let φ : ℂ := ((a : ℝ) : ℂ) * (((fderiv ℝ β y (frameBasis μ) : ℝ) : ℂ) +
      Complex.I * ((fderiv ℝ α y (frameBasis μ) : ℝ) : ℂ))
    have haS : a • S y μ = φ • (1 : Mat4C) := by
      dsimp only [S, mannheimGaugeShiftMat4, φ]
      rw [← Complex.real_smul, smul_assoc]
    rw [haS]
    have hCancel :
        NormedSpace.exp (a • A y μ) * NormedSpace.exp (φ • (1 : Mat4C)) *
          Φ (y + a • frameBasis μ) *
          ((NormedSpace.exp (φ • (1 : Mat4C)))⁻¹ * (NormedSpace.exp (a • A y μ))⁻¹) =
          NormedSpace.exp (a • A y μ) * Φ (y + a • frameBasis μ) *
            (NormedSpace.exp (a • A y μ))⁻¹ := by
      calc
        NormedSpace.exp (a • A y μ) * NormedSpace.exp (φ • (1 : Mat4C)) *
            Φ (y + a • frameBasis μ) *
            ((NormedSpace.exp (φ • (1 : Mat4C)))⁻¹ * (NormedSpace.exp (a • A y μ))⁻¹)
          = NormedSpace.exp (a • A y μ) *
              (NormedSpace.exp (φ • (1 : Mat4C)) * Φ (y + a • frameBasis μ) *
                (NormedSpace.exp (φ • (1 : Mat4C)))⁻¹) *
              (NormedSpace.exp (a • A y μ))⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = NormedSpace.exp (a • A y μ) * Φ (y + a • frameBasis μ) *
              (NormedSpace.exp (a • A y μ))⁻¹ := by
            rw [exp_scalar_one_mul_conj φ (Φ (y + a • frameBasis μ))]
    rw [hCancel]
  have hA_full_eq : ∀ z ρ, A_full z ρ = U * A_shift z ρ * U⁻¹ := by
    intro z ρ
    dsimp only [A_full, A_shift]
    rw [Matrix.mul_add, Matrix.add_mul, mannheimGaugeShiftMat4_conj U U⁻¹ hUUinv]
  have hLatFull : ∀ a : ℝ,
      latticeCovariantDiff A_full Φ_conj y μ a = U * latticeCovariantDiff A Φ y μ a * U⁻¹ := by
    intro a
    rw [← hLatShift a]
    dsimp only [latticeCovariantDiff, Φ_conj]
    rw [hA_full_eq y μ]
    have hExp : NormedSpace.exp (a • (U * A_shift y μ * U⁻¹)) =
        U * NormedSpace.exp (a • A_shift y μ) * U⁻¹ := by
      rw [show a • (U * A_shift y μ * U⁻¹) = U * (a • A_shift y μ) * U⁻¹ by
        rw [Matrix.mul_smul, Matrix.smul_mul]]
      exact Matrix.exp_conj _ _ hU_unit
    have hExpInv : (U * NormedSpace.exp (a • A_shift y μ) * U⁻¹)⁻¹ =
        U * (NormedSpace.exp (a • A_shift y μ))⁻¹ * U⁻¹ := by
      have hNegConj : -(a • (U * A_shift y μ * U⁻¹)) = U * (-(a • A_shift y μ)) * U⁻¹ := by
        rw [Matrix.mul_neg, Matrix.neg_mul]
        congr 1
        rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [← hExp, ← Matrix.exp_neg, ← Matrix.exp_neg, hNegConj]
      exact Matrix.exp_conj _ _ hU_unit
    rw [hExp, hExpInv]
    have hConjDiff :
        (U * NormedSpace.exp (a • A_shift y μ) * U⁻¹) *
            (U * Φ (y + a • frameBasis μ) * U⁻¹) *
            (U * (NormedSpace.exp (a • A_shift y μ))⁻¹ * U⁻¹) -
          U * Φ y * U⁻¹ =
        U * (NormedSpace.exp (a • A_shift y μ) * Φ (y + a • frameBasis μ) *
            (NormedSpace.exp (a • A_shift y μ))⁻¹ - Φ y) * U⁻¹ := by
      calc
        (U * NormedSpace.exp (a • A_shift y μ) * U⁻¹) *
            (U * Φ (y + a • frameBasis μ) * U⁻¹) *
            (U * (NormedSpace.exp (a • A_shift y μ))⁻¹ * U⁻¹) -
          U * Φ y * U⁻¹
          = U * NormedSpace.exp (a • A_shift y μ) * (U⁻¹ * U) *
              Φ (y + a • frameBasis μ) * (U⁻¹ * U) *
              (NormedSpace.exp (a • A_shift y μ))⁻¹ * U⁻¹ -
            U * Φ y * U⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = U * (NormedSpace.exp (a • A_shift y μ) * Φ (y + a • frameBasis μ) *
              (NormedSpace.exp (a • A_shift y μ))⁻¹) * U⁻¹ -
            U * Φ y * U⁻¹ := by
            rw [hUinvU, Matrix.mul_one, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
        _ = U * (NormedSpace.exp (a • A_shift y μ) * Φ (y + a • frameBasis μ) *
              (NormedSpace.exp (a • A_shift y μ))⁻¹ - Φ y) * U⁻¹ := by
            rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    rw [hConjDiff, Matrix.mul_smul, Matrix.smul_mul]
  have hContCov :
      continuumCovariantDeriv A_full Φ_conj y μ = U * continuumCovariantDeriv A Φ y μ * U⁻¹ := by
    dsimp only [continuumCovariantDeriv]
    have hfderiv : fderiv ℝ Φ_conj y (frameBasis μ) =
        U * fderiv ℝ Φ y (frameBasis μ) * U⁻¹ :=
      fderiv_chiralConjCLM_comp U U⁻¹ hΦ (frameBasis μ)
    rw [hfderiv]
    dsimp only [A_full, Φ_conj]
    have hComm1 : (U * A y μ * U⁻¹ + S y μ) * (U * Φ y * U⁻¹) =
        U * (A y μ * Φ y) * U⁻¹ + S y μ * (U * Φ y * U⁻¹) := by
      rw [Matrix.add_mul]
      have h1 : (U * A y μ * U⁻¹) * (U * Φ y * U⁻¹) = U * (A y μ * Φ y) * U⁻¹ := by
        calc
          (U * A y μ * U⁻¹) * (U * Φ y * U⁻¹) = U * A y μ * (U⁻¹ * U) * Φ y * U⁻¹ := by
            simp only [Matrix.mul_assoc]
          _ = U * (A y μ * Φ y) * U⁻¹ := by rw [hUinvU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      rw [h1]
    have hComm2 : (U * Φ y * U⁻¹) * (U * A y μ * U⁻¹ + S y μ) =
        U * (Φ y * A y μ) * U⁻¹ + (U * Φ y * U⁻¹) * S y μ := by
      rw [Matrix.mul_add]
      have h1 : (U * Φ y * U⁻¹) * (U * A y μ * U⁻¹) = U * (Φ y * A y μ) * U⁻¹ := by
        calc
          (U * Φ y * U⁻¹) * (U * A y μ * U⁻¹) = U * Φ y * (U⁻¹ * U) * A y μ * U⁻¹ := by
            simp only [Matrix.mul_assoc]
          _ = U * (Φ y * A y μ) * U⁻¹ := by rw [hUinvU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      rw [h1]
    rw [hComm1, hComm2, mannheimGaugeShiftMat4_comm β α y μ (U * Φ y * U⁻¹)]
    rw [add_sub_add_right_eq_sub, ← Matrix.sub_mul, ← Matrix.mul_sub,
      ← Matrix.add_mul, ← Matrix.mul_add]
  have hWilConj :
      ∀ a : ℝ, wilsonPlaquette A_conj y μ ν a = U * wilsonPlaquette A y μ ν a * U⁻¹ := by
    intro a
    dsimp only [wilsonPlaquette, A_conj]
    have hF1 : NormedSpace.exp (a • (U * A y μ * U⁻¹)) = U * NormedSpace.exp (a • A y μ) * U⁻¹ := by
      rw [show a • (U * A y μ * U⁻¹) = U * (a • A y μ) * U⁻¹ by
        rw [Matrix.mul_smul, Matrix.smul_mul]]
      exact Matrix.exp_conj _ _ hU_unit
    have hF2 : NormedSpace.exp (a • (U * A (y + a • frameBasis μ) ν * U⁻¹)) =
        U * NormedSpace.exp (a • A (y + a • frameBasis μ) ν) * U⁻¹ := by
      rw [show a • (U * A (y + a • frameBasis μ) ν * U⁻¹) =
          U * (a • A (y + a • frameBasis μ) ν) * U⁻¹ by
        rw [Matrix.mul_smul, Matrix.smul_mul]]
      exact Matrix.exp_conj _ _ hU_unit
    have hI1 : (NormedSpace.exp (a • (U * A (y + a • frameBasis ν) μ * U⁻¹)))⁻¹ =
        U * (NormedSpace.exp (a • A (y + a • frameBasis ν) μ))⁻¹ * U⁻¹ := by
      rw [← Matrix.exp_neg, ← Matrix.exp_neg,
        show -(a • (U * A (y + a • frameBasis ν) μ * U⁻¹)) =
            U * (-(a • A (y + a • frameBasis ν) μ)) * U⁻¹ by
          rw [show a • (U * A (y + a • frameBasis ν) μ * U⁻¹) =
              U * (a • A (y + a • frameBasis ν) μ) * U⁻¹ by
            rw [Matrix.mul_smul, Matrix.smul_mul], Matrix.mul_neg, Matrix.neg_mul]]
      exact Matrix.exp_conj _ _ hU_unit
    have hI2 : (NormedSpace.exp (a • (U * A y ν * U⁻¹)))⁻¹ =
        U * (NormedSpace.exp (a • A y ν))⁻¹ * U⁻¹ := by
      rw [← Matrix.exp_neg, ← Matrix.exp_neg,
        show -(a • (U * A y ν * U⁻¹)) = U * (-(a • A y ν)) * U⁻¹ by
          rw [show a • (U * A y ν * U⁻¹) = U * (a • A y ν) * U⁻¹ by
            rw [Matrix.mul_smul, Matrix.smul_mul], Matrix.mul_neg, Matrix.neg_mul]]
      exact Matrix.exp_conj _ _ hU_unit
    rw [hF1, hF2, hI1, hI2]
    calc
      U * NormedSpace.exp (a • A y μ) * U⁻¹ *
          (U * NormedSpace.exp (a • A (y + a • frameBasis μ) ν) * U⁻¹) *
          (U * (NormedSpace.exp (a • A (y + a • frameBasis ν) μ))⁻¹ * U⁻¹) *
          (U * (NormedSpace.exp (a • A y ν))⁻¹ * U⁻¹)
        = U * NormedSpace.exp (a • A y μ) * (U⁻¹ * U) *
            NormedSpace.exp (a • A (y + a • frameBasis μ) ν) * (U⁻¹ * U) *
            (NormedSpace.exp (a • A (y + a • frameBasis ν) μ))⁻¹ * (U⁻¹ * U) *
            (NormedSpace.exp (a • A y ν))⁻¹ * U⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = U * (NormedSpace.exp (a • A y μ) *
            NormedSpace.exp (a • A (y + a • frameBasis μ) ν) *
            (NormedSpace.exp (a • A (y + a • frameBasis ν) μ))⁻¹ *
            (NormedSpace.exp (a • A y ν))⁻¹) * U⁻¹ := by
          rw [hUinvU, Matrix.mul_one, Matrix.mul_one, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have hWilAct :
      ∀ a : ℝ, wilsonPlaquetteAction A_conj y μ ν a = wilsonPlaquetteAction A y μ ν a := by
    intro a
    dsimp only [wilsonPlaquetteAction]
    rw [hWilConj a]
    have hSub : U * wilsonPlaquette A y μ ν a * U⁻¹ - 1 =
        U * (wilsonPlaquette A y μ ν a - 1) * U⁻¹ := by
      calc
        U * wilsonPlaquette A y μ ν a * U⁻¹ - 1
          = U * wilsonPlaquette A y μ ν a * U⁻¹ - U * 1 * U⁻¹ := by rw [Matrix.mul_one, hUUinv]
        _ = U * (wilsonPlaquette A y μ ν a - 1) * U⁻¹ := by
          rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    rw [hSub, unitary_conj_hs_trace U hUH hUinv_H]
  have hCurvShift : continuumCurvature A_shift y μ ν = continuumCurvature A y μ ν := by
    dsimp only [continuumCurvature, A_shift]
    have hDiffAν : DifferentiableAt ℝ (fun z => A z ν) y :=
      ((contDiff_pi.mp hA ν).differentiable (by norm_num)) y
    have hDiffAμ : DifferentiableAt ℝ (fun z => A z μ) y :=
      ((contDiff_pi.mp hA μ).differentiable (by norm_num)) y
    have hDiffSν : DifferentiableAt ℝ (fun z => S z ν) y :=
      ((contDiff_pi.mp hS_cd ν).differentiable (by norm_num)) y
    have hDiffSμ : DifferentiableAt ℝ (fun z => S z μ) y :=
      ((contDiff_pi.mp hS_cd μ).differentiable (by norm_num)) y
    have hD1 : fderiv ℝ (fun z => A z ν + S z ν) y =
        fderiv ℝ (fun z => A z ν) y + fderiv ℝ (fun z => S z ν) y :=
      fderiv_add hDiffAν hDiffSν
    have hD2 : fderiv ℝ (fun z => A z μ + S z μ) y =
        fderiv ℝ (fun z => A z μ) y + fderiv ℝ (fun z => S z μ) y :=
      fderiv_add hDiffAμ hDiffSμ
    have hSymmS :
        fderiv ℝ (fun z => S z ν) y (frameBasis μ) -
          fderiv ℝ (fun z => S z μ) y (frameBasis ν) = 0 := by
      rw [fderiv_mannheimGaugeShiftMat4_apply hβ hα y ν μ,
        fderiv_mannheimGaugeShiftMat4_apply hβ hα y μ ν]
      rw [fderiv_apply_frameBasis_symm (hβ.of_le (by norm_num)) y μ ν,
        fderiv_apply_frameBasis_symm (hα.of_le (by norm_num)) y μ ν, sub_self]
    have hCommS :
        (A y μ + S y μ) * (A y ν + S y ν) - (A y ν + S y ν) * (A y μ + S y μ) =
          A y μ * A y ν - A y ν * A y μ := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_add, mannheimGaugeShiftMat4_comm β α y μ (A y ν),
        mannheimGaugeShiftMat4_comm β α y ν (A y μ),
        mannheimGaugeShiftMat4_comm β α y μ (S y ν)]
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply]
      ring
    rw [hD1, hD2, add_apply, add_apply, hCommS]
    calc
      (fderiv ℝ (fun z => A z ν) y (frameBasis μ) + fderiv ℝ (fun z => S z ν) y (frameBasis μ)) -
          (fderiv ℝ (fun z => A z μ) y (frameBasis ν) + fderiv ℝ (fun z => S z μ) y (frameBasis ν)) +
          (A y μ * A y ν - A y ν * A y μ)
        = (fderiv ℝ (fun z => A z ν) y (frameBasis μ) -
            fderiv ℝ (fun z => A z μ) y (frameBasis ν)) +
          (fderiv ℝ (fun z => S z ν) y (frameBasis μ) -
            fderiv ℝ (fun z => S z μ) y (frameBasis ν)) +
          (A y μ * A y ν - A y ν * A y μ) := by
          ext i j; simp; ring
      _ = (fderiv ℝ (fun z => A z ν) y (frameBasis μ) -
            fderiv ℝ (fun z => A z μ) y (frameBasis ν)) +
          (A y μ * A y ν - A y ν * A y μ) := by rw [hSymmS, add_zero]
  have hCurvFull : continuumCurvature A_full y μ ν = U * continuumCurvature A y μ ν * U⁻¹ := by
    rw [← hCurvShift]
    dsimp only [continuumCurvature]
    have hDiffShiftν : DifferentiableAt ℝ (fun z => A_shift z ν) y :=
      ((contDiff_pi.mp hA_shift_cd ν).differentiable (by norm_num)) y
    have hDiffShiftμ : DifferentiableAt ℝ (fun z => A_shift z μ) y :=
      ((contDiff_pi.mp hA_shift_cd μ).differentiable (by norm_num)) y
    have hDν : fderiv ℝ (fun z => A_full z ν) y (frameBasis μ) =
        U * fderiv ℝ (fun z => A_shift z ν) y (frameBasis μ) * U⁻¹ := by
      have hFun : (fun z => A_full z ν) = fun z => U * A_shift z ν * U⁻¹ := by
        funext z; exact hA_full_eq z ν
      rw [hFun]
      exact fderiv_chiralConjCLM_comp U U⁻¹ hDiffShiftν (frameBasis μ)
    have hDμ : fderiv ℝ (fun z => A_full z μ) y (frameBasis ν) =
        U * fderiv ℝ (fun z => A_shift z μ) y (frameBasis ν) * U⁻¹ := by
      have hFun : (fun z => A_full z μ) = fun z => U * A_shift z μ * U⁻¹ := by
        funext z; exact hA_full_eq z μ
      rw [hFun]
      exact fderiv_chiralConjCLM_comp U U⁻¹ hDiffShiftμ (frameBasis ν)
    rw [hDν, hDμ, hA_full_eq y μ, hA_full_eq y ν]
    have hComm1 : (U * A_shift y μ * U⁻¹) * (U * A_shift y ν * U⁻¹) =
        U * (A_shift y μ * A_shift y ν) * U⁻¹ := by
      calc
        (U * A_shift y μ * U⁻¹) * (U * A_shift y ν * U⁻¹)
          = U * A_shift y μ * (U⁻¹ * U) * A_shift y ν * U⁻¹ := by simp only [Matrix.mul_assoc]
        _ = U * (A_shift y μ * A_shift y ν) * U⁻¹ := by
          rw [hUinvU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have hComm2 : (U * A_shift y ν * U⁻¹) * (U * A_shift y μ * U⁻¹) =
        U * (A_shift y ν * A_shift y μ) * U⁻¹ := by
      calc
        (U * A_shift y ν * U⁻¹) * (U * A_shift y μ * U⁻¹)
          = U * A_shift y ν * (U⁻¹ * U) * A_shift y μ * U⁻¹ := by simp only [Matrix.mul_assoc]
        _ = U * (A_shift y ν * A_shift y μ) * U⁻¹ := by
          rw [hUinvU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [hComm1, hComm2, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.sub_mul, ← Matrix.mul_sub,
      ← Matrix.add_mul, ← Matrix.mul_add]
  have hActShift : continuumPlaquetteAction A_shift y μ ν = continuumPlaquetteAction A y μ ν := by
    dsimp only [continuumPlaquetteAction]
    rw [hCurvShift]
  have hActFull : continuumPlaquetteAction A_full y μ ν = continuumPlaquetteAction A y μ ν := by
    dsimp only [continuumPlaquetteAction]
    rw [hCurvFull, unitary_conj_hs_trace U hUH hUinv_H]
  have hTendCurv :
      Filter.Tendsto (fun a : ℝ => (a ^ 2)⁻¹ • (wilsonPlaquette A_full y μ ν a - 1))
        (𝓝[≠] 0) (𝓝 (U * continuumCurvature A y μ ν * U⁻¹)) := by
    rw [← hCurvFull]
    exact tendsto_wilsonPlaquette_curvature A_full y μ ν hA_full_cd
  have hTendAct :
      Filter.Tendsto (fun a : ℝ => wilsonPlaquetteAction A_full y μ ν a)
        (𝓝[≠] 0) (𝓝 (continuumPlaquetteAction A y μ ν)) := by
    rw [← hActFull]
    exact tendsto_wilsonPlaquetteAction A_full y μ ν hA_full_cd
  refine ⟨hA_shift_cd, hA_conj_cd, hA_full_cd, hΦ_conj_diff, hLink, hLatShift, hLatFull,
    hContCov, hWilConj, hWilAct, hCurvShift, hCurvFull, hActShift, hActFull,
    hTendCurv, hTendAct, ?_⟩
  intro A_tower _ _ B_inf _ _ _ cone k ι hCont ψ
  have hCol := circularColimit_continuum_transport cone k ι hCont x A_full Φ_conj y μ ν
    hA_full_cd hΦ_conj_diff
  have hCovLim :
      Filter.Tendsto (fun a : ℝ => ψ (latticeCovariantDiff A_full Φ_conj y μ a))
        (𝓝[≠] 0) (𝓝 (ψ U * ψ (continuumCovariantDeriv A Φ y μ) * ψ U⁻¹)) := by
    have h1 := hCol.1
    rw [hContCov, map_mul, map_mul] at h1
    exact h1
  have hCurvLim :
      Filter.Tendsto (fun a : ℝ => ψ ((a ^ 2)⁻¹ • (wilsonPlaquette A_full y μ ν a - 1)))
        (𝓝[≠] 0) (𝓝 (ψ U * ψ (continuumCurvature A y μ ν) * ψ U⁻¹)) := by
    have h2 := hCol.2.1
    rw [hCurvFull, map_mul, map_mul] at h2
    exact h2
  have hLinkConj :
      Filter.Tendsto (fun a : ℝ => U * circularLinkTransport x y μ a * U⁻¹)
        (𝓝 0) (𝓝 (1 : Mat4C)) := by
    have hLim : Filter.Tendsto (fun a : ℝ => (chiralConjCLM U U⁻¹) (circularLinkTransport x y μ a))
        (𝓝 0) (𝓝 ((chiralConjCLM U U⁻¹) 1)) := by
      have h0' : circularLinkTransport x y μ 0 = 1 := by simp [circularLinkTransport]
      have hContLink : Filter.Tendsto (fun a : ℝ => circularLinkTransport x y μ a) (𝓝 0) (𝓝 1) := by
        rw [← h0']
        exact (circularLinkTransport_continuous x y μ).continuousAt.tendsto
      exact (chiralConjCLM U U⁻¹).continuous.continuousAt.tendsto.comp hContLink
    have hOne : (chiralConjCLM U U⁻¹) 1 = 1 := by
      dsimp [chiralConjCLM]
      rw [Matrix.mul_one, hUUinv]
    simpa [chiralConjCLM, hOne, hUUinv] using hLim
  have hLinkLim :
      Filter.Tendsto (fun a : ℝ => ψ (U * circularLinkTransport x y μ a * U⁻¹))
        (𝓝 0) (𝓝 (1 : B_inf)) := by
    simpa only [Function.comp_def, map_one] using (hCont.continuousAt (x := 1)).tendsto.comp hLinkConj
  have hLinkSlope :
      Filter.Tendsto (fun a : ℝ => ψ (a⁻¹ • (U * circularLinkTransport x y μ a * U⁻¹ - 1)))
        (𝓝[≠] 0) (𝓝 (ψ U * ψ (circularConnectionMat4 (x y μ)) * ψ U⁻¹)) := by
    have hDeriv : HasDerivAt (fun a : ℝ => NormedSpace.exp (a • circularConnectionMat4 (x y μ)))
        (circularConnectionMat4 (x y μ)) 0 := by
      simpa [zero_smul, NormedSpace.exp_zero, one_mul] using
        hasDerivAt_exp_smul_const (circularConnectionMat4 (x y μ)) (0 : ℝ)
    have hSlope0 :
        Filter.Tendsto (fun a : ℝ => a⁻¹ • (circularLinkTransport x y μ a - 1))
          (𝓝[≠] 0) (𝓝 (circularConnectionMat4 (x y μ))) := by
      simpa [circularLinkTransport, zero_smul, NormedSpace.exp_zero] using hDeriv.tendsto_slope_zero
    have hSlopeConj :
        Filter.Tendsto
          (fun a : ℝ => a⁻¹ • (U * circularLinkTransport x y μ a * U⁻¹ - 1))
          (𝓝[≠] 0) (𝓝 (U * circularConnectionMat4 (x y μ) * U⁻¹)) := by
      have hEq :
          (fun a : ℝ => a⁻¹ • (U * circularLinkTransport x y μ a * U⁻¹ - 1)) =
            fun a : ℝ => (chiralConjCLM U U⁻¹) (a⁻¹ • (circularLinkTransport x y μ a - 1)) := by
        funext a
        dsimp [chiralConjCLM]
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
          hUUinv]
      rw [hEq]
      exact ((chiralConjCLM U U⁻¹).continuous.continuousAt (x := circularConnectionMat4 (x y μ))).tendsto.comp
        hSlope0
    simpa only [Function.comp_def, map_mul] using
      (hCont.continuousAt (x := U * circularConnectionMat4 (x y μ) * U⁻¹)).tendsto.comp hSlopeConj
  exact ⟨hCovLim, hCurvLim, hLinkLim, hLinkSlope⟩

end Layer2LatticeContinuum

/-! ## 4. Layer 3: Manifold Yang–Mills PDE (`DoubledMinkowskiManifoldYangMillsPDE`) -/

section Layer3ManifoldPDE

open scoped Matrix.Norms.Elementwise

/-- Conformal-plus-phase fiber multiplier `exp(w * β(x) + i * α(x))` on `ChiralFiber`. -/
def mannheimFiberScalar (w : ℝ) (β α : FourSpace → ℝ) (x : FourSpace) : ℂ :=
  scaleGaugeMultiplier (w * β x) (α x)

/-- Abelian Weyl-plus-phase logarithmic 1-form `(w dβ + i dα) • I₄` valued in `Mat4C`. -/
def mannheimGradOneForm (w : ℝ) (β α : FourSpace → ℝ) : Mat4CForm 1 :=
  fun x =>
    ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace)
      (F := Mat4C) (0 : Fin 1)
      ((w • fderiv ℝ β x).smulRight (1 : Mat4C) +
        (fderiv ℝ α x).smulRight (Complex.I • (1 : Mat4C)))

private lemma complex_re_im_normSq_mul (c z w : ℂ) :
    (c * z).re * (c * w).re + (c * z).im * (c * w).im =
      Complex.normSq c * (z.re * w.re + z.im * w.im) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

private lemma chiralFiberToKreinFrame_fst (u : ChiralFiber) :
    (chiralFiberToKreinFrame u).1.1 =
      WithLp.toLp (2 : ENNReal) ![(u 0).re, (u 0).im, (u 1).re, (u 1).im] :=
  rfl

private lemma chiralFiberToKreinFrame_snd (u : ChiralFiber) :
    (chiralFiberToKreinFrame u).1.2 =
      WithLp.toLp (2 : ENNReal) ![(u 2).re, (u 2).im, (u 3).re, (u 3).im] :=
  rfl

/-- **Layer 3 (Fiber Krein Pairing Scale–Phase Law)**:
Under `u ↦ mannheimFiberScalar w β α x • u`, the phase `α(x)` cancels identically in
`fiberKreinPairing`, leaving only the conformal weight factor `exp (2 * w * β x)` (pure
isometry at `β x = 0`, metric factor `exp (2 * β x)` at `w = 1`, and exact `d = 4`
Dirac-spinor compensation `vol4Scale * invTetradScale * fiberKreinPairing = fiberKreinPairing`
at `w = -3/2`). -/
theorem mannheim_fiberKreinPairing_scale_phase_law
    (w : ℝ) (β α : FourSpace → ℝ) (x : FourSpace) (u v : ChiralFiber) :
    fiberKreinPairing
        (mannheimFiberScalar w β α x • u)
        (mannheimFiberScalar w β α x • v) =
      Real.exp (2 * w * β x) * fiberKreinPairing u v ∧
    (β x = 0 →
      fiberKreinPairing
          (mannheimFiberScalar w β α x • u)
          (mannheimFiberScalar w β α x • v) =
        fiberKreinPairing u v) ∧
    (w = 1 →
      fiberKreinPairing
          (mannheimFiberScalar 1 β α x • u)
          (mannheimFiberScalar 1 β α x • v) =
        Real.exp (2 * β x) * fiberKreinPairing u v) ∧
    (w = -(3 / 2 : ℝ) →
      ‖mannheimFiberScalar (-(3 / 2 : ℝ)) β α x‖ = spinorScale (β x) ∧
      vol4Scale (β x) * invTetradScale (β x) *
        fiberKreinPairing
          (mannheimFiberScalar (-(3 / 2 : ℝ)) β α x • u)
          (mannheimFiberScalar (-(3 / 2 : ℝ)) β α x • v) =
        fiberKreinPairing u v) := by
  let c : ℂ := mannheimFiberScalar w β α x
  have hMain : fiberKreinPairing (c • u) (c • v) = Real.exp (2 * w * β x) * fiberKreinPairing u v := by
    have hNormSq : Complex.normSq c = Real.exp (2 * w * β x) := by
      dsimp only [c, mannheimFiberScalar]
      rw [Complex.normSq_eq_norm_sq, norm_scaleGaugeMultiplier, sq, ← Real.exp_add]
      have h2 : w * β x + w * β x = 2 * w * β x := by ring
      rw [h2]
    have hExpand :
        fiberKreinPairing (c • u) (c • v) =
          Complex.normSq c * fiberKreinPairing u v := by
      dsimp only [fiberKreinPairing]
      rw [chiralKreinForm_to_doubled, chiralKreinForm_to_doubled]
      simp_rw [chiralFiberToKreinFrame_fst, chiralFiberToKreinFrame_snd]
      rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
        EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial, dotProduct, Fin.sum_univ_four,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.smul_apply, smul_eq_mul]
      have h02 := complex_re_im_normSq_mul c (u 0) (v 2)
      have h13 := complex_re_im_normSq_mul c (u 1) (v 3)
      have h20 := complex_re_im_normSq_mul c (u 2) (v 0)
      have h31 := complex_re_im_normSq_mul c (u 3) (v 1)
      linarith
    rw [hExpand, hNormSq]
  refine ⟨hMain, ?_, ?_, ?_⟩
  · intro hβ0
    rw [hMain, hβ0, mul_zero, Real.exp_zero, one_mul]
  · intro hw
    subst hw
    simpa [one_mul] using hMain
  · intro hw
    subst hw
    have hNorm : ‖mannheimFiberScalar (-(3 / 2 : ℝ)) β α x‖ = spinorScale (β x) := by
      dsimp only [mannheimFiberScalar, spinorScale]
      rw [norm_scaleGaugeMultiplier]
    refine ⟨hNorm, ?_⟩
    rw [hMain]
    dsimp [vol4Scale, invTetradScale]
    rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    have hexp0 : 4 * β x + -β x + 2 * -(3 / 2 : ℝ) * β x = 0 := by ring
    rw [hexp0, Real.exp_zero, one_mul]

private lemma mannheimGradOneForm_apply (w : ℝ) (β α : FourSpace → ℝ)
    (x v : FourSpace) :
    mannheimGradOneForm w β α x (fun _ => v) =
      (((w * fderiv ℝ β x v : ℝ) : ℂ) +
        ((fderiv ℝ α x v : ℝ) : ℂ) * Complex.I) • (1 : Mat4C) := by
  have h0 : mannheimGradOneForm w β α x (fun _ => v) =
      ((w • fderiv ℝ β x).smulRight (1 : Mat4C) +
        (fderiv ℝ α x).smulRight (Complex.I • (1 : Mat4C))) v := rfl
  rw [h0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Complex.real_smul, mul_comm Complex.I]

/-- **Layer 3 (4D Bundle Covariant Derivative Equivariance)**:
`circularBundleConnection (A - mannheimGradOneForm w β α)` is strictly equivariant under
`σ ↦ mannheimFiberScalar w β α • σ` at every `x, v : FourSpace`. -/
theorem mannheim_bundle_covariant_derivative_4d
    (w : ℝ) (β α : FourSpace → ℝ) (A : Mat4CForm 1) (σ : FourSpace → ChiralFiber)
    (x v : FourSpace)
    (hβ : DifferentiableAt ℝ β x) (hα : DifferentiableAt ℝ α x)
    (hσ : DifferentiableAt ℝ σ x) :
    circularBundleConnection (A - mannheimGradOneForm w β α)
        (fun y => mannheimFiberScalar w β α y • σ y) x v =
      mannheimFiberScalar w β α x • circularBundleConnection A σ x v := by
  rw [circularBundleConnection_apply, circularBundleConnection_apply]
  have hExpAt :
      HasFDerivAt (mannheimFiberScalar w β α)
        (mannheimFiberScalar w β α x •
          (w • Complex.ofRealCLM.comp (fderiv ℝ β x) +
            ((ContinuousLinearMap.mul ℝ ℂ).flip Complex.I).comp
              (Complex.ofRealCLM.comp (fderiv ℝ α x)))) x := by
    have hArg :
        HasFDerivAt (fun y => ((w * β y : ℝ) : ℂ) + ((α y : ℝ) : ℂ) * Complex.I)
          (w • Complex.ofRealCLM.comp (fderiv ℝ β x) +
            ((ContinuousLinearMap.mul ℝ ℂ).flip Complex.I).comp
              (Complex.ofRealCLM.comp (fderiv ℝ α x))) x := by
      have h1 : HasFDerivAt (fun y => ((w * β y : ℝ) : ℂ))
          (w • Complex.ofRealCLM.comp (fderiv ℝ β x)) x := by
        simpa [Function.comp_def, smul_eq_mul] using
          (Complex.ofRealCLM.hasFDerivAt.comp x (hβ.hasFDerivAt.const_smul w))
      have h2 : HasFDerivAt (fun y => ((α y : ℝ) : ℂ) * Complex.I)
          (((ContinuousLinearMap.mul ℝ ℂ).flip Complex.I).comp
            (Complex.ofRealCLM.comp (fderiv ℝ α x))) x := by
        have hmul : HasFDerivAt (fun z : ℂ => z * Complex.I)
            ((ContinuousLinearMap.mul ℝ ℂ).flip Complex.I) ((α x : ℝ) : ℂ) :=
          ((ContinuousLinearMap.mul ℝ ℂ).flip Complex.I).hasFDerivAt
        exact hmul.comp x (Complex.ofRealCLM.hasFDerivAt.comp x hα.hasFDerivAt)
      exact h1.add h2
    change HasFDerivAt (fun y => Complex.exp (((w * β y : ℝ) : ℂ) + ((α y : ℝ) : ℂ) * Complex.I)) _ x
    exact hArg.cexp
  have hProd := hExpAt.smul hσ.hasFDerivAt
  have hDeriv :
      fderiv ℝ (fun y => mannheimFiberScalar w β α y • σ y) x v =
        mannheimFiberScalar w β α x • fderiv ℝ σ x v +
          (mannheimFiberScalar w β α x *
            (((w * fderiv ℝ β x v : ℝ) : ℂ) +
              ((fderiv ℝ α x v : ℝ) : ℂ) * Complex.I)) • σ x := by
    change fderiv ℝ (mannheimFiberScalar w β α • σ) x v = _
    rw [hProd.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply,
      Complex.real_smul, Complex.ofReal_mul]
    ext i
    simp
  have hGrad :
      (mannheimGradOneForm w β α x (fun _ => v)).mulVec (mannheimFiberScalar w β α x • σ x) =
        (mannheimFiberScalar w β α x *
          (((w * fderiv ℝ β x v : ℝ) : ℂ) +
            ((fderiv ℝ α x v : ℝ) : ℂ) * Complex.I)) • σ x := by
    rw [mannheimGradOneForm_apply, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, mul_comm]
  have hA_mul :
      ((A - mannheimGradOneForm w β α) x (fun _ => v)).mulVec (mannheimFiberScalar w β α x • σ x) =
        mannheimFiberScalar w β α x • (A x (fun _ => v)).mulVec (σ x) -
          (mannheimGradOneForm w β α x (fun _ => v)).mulVec (mannheimFiberScalar w β α x • σ x) := by
    change (A x (fun _ => v) - mannheimGradOneForm w β α x (fun _ => v)).mulVec
        (mannheimFiberScalar w β α x • σ x) = _
    rw [Matrix.sub_mulVec, Matrix.mulVec_smul]
  rw [hDeriv, hA_mul, hGrad, smul_add]
  ext i
  simp

private lemma mannheimGradOneForm_comm_zero (w : ℝ) (β α : FourSpace → ℝ)
    (x v : FourSpace) (M : Mat4C) :
    mat4CCommCLM (mannheimGradOneForm w β α x (fun _ => v)) M = 0 := by
  rw [mannheimGradOneForm_apply, mat4CCommCLM_apply]
  rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, sub_self]

private lemma mannheimGradOneForm_comm_zero_right (w : ℝ) (β α : FourSpace → ℝ)
    (x v : FourSpace) (M : Mat4C) :
    mat4CCommCLM M (mannheimGradOneForm w β α x (fun _ => v)) = 0 := by
  rw [mannheimGradOneForm_apply, mat4CCommCLM_apply]
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul, sub_self]

private lemma mannheimGradOneForm_differentiable
    (w : ℝ) {β α : FourSpace → ℝ} (hβ : ContDiff ℝ 2 β) (hα : ContDiff ℝ 2 α) :
    Differentiable ℝ (mannheimGradOneForm w β α) := by
  have hβ' : ContDiff ℝ 1 (fderiv ℝ β) := hβ.fderiv_right (by norm_num)
  have hα' : ContDiff ℝ 1 (fderiv ℝ α) := hα.fderiv_right (by norm_num)
  let smulOneCLM : (FourSpace →L[ℝ] ℝ) →L[ℝ] (FourSpace [⋀^Fin 1]→L[ℝ] Mat4C) :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace)
      (F := Mat4C) (0 : Fin 1)).toContinuousLinearMap.comp
      ((ContinuousLinearMap.smulRightL ℝ FourSpace Mat4C).flip (1 : Mat4C))
  let smulICLM : (FourSpace →L[ℝ] ℝ) →L[ℝ] (FourSpace [⋀^Fin 1]→L[ℝ] Mat4C) :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace)
      (F := Mat4C) (0 : Fin 1)).toContinuousLinearMap.comp
      ((ContinuousLinearMap.smulRightL ℝ FourSpace Mat4C).flip (Complex.I • (1 : Mat4C)))
  have h1 : ContDiff ℝ 1 (fun x => smulOneCLM (w • fderiv ℝ β x)) :=
    smulOneCLM.contDiff.comp (hβ'.const_smul w)
  have h2 : ContDiff ℝ 1 (fun x => smulICLM (fderiv ℝ α x)) :=
    smulICLM.contDiff.comp hα'
  have hEq : mannheimGradOneForm w β α =
      fun x => smulOneCLM (w • fderiv ℝ β x) + smulICLM (fderiv ℝ α x) := by
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    change ((w • fderiv ℝ β x).smulRight (1 : Mat4C) +
        (fderiv ℝ α x).smulRight (Complex.I • (1 : Mat4C))) (v 0) =
      ((w • fderiv ℝ β x).smulRight (1 : Mat4C)) (v 0) +
        ((fderiv ℝ α x).smulRight (Complex.I • (1 : Mat4C))) (v 0)
    rfl
  rw [hEq]
  exact (h1.add h2).differentiable (by norm_num)

private noncomputable def extD3 {k : ℕ} (η : Mat4CForm k) : Mat4CForm (k + 1) :=
  extDeriv η

private lemma extD3_add {k : ℕ} {η₁ η₂ : Mat4CForm k} {x : FourSpace}
    (h₁ : DifferentiableAt ℝ η₁ x) (h₂ : DifferentiableAt ℝ η₂ x) :
    extD3 (η₁ + η₂) x = extD3 η₁ x + extD3 η₂ x :=
  extDeriv_add h₁ h₂

private lemma extD3_smul {k : ℕ} (c : ℝ) (η : Mat4CForm k) (x : FourSpace) :
    extD3 (c • η) x = c • extD3 η x :=
  extDeriv_smul c η

private lemma extD3_extD3 {k : ℕ} {η : Mat4CForm k} (h : ContDiff ℝ 2 η) :
    extD3 (extD3 η) = 0 :=
  extDeriv_extDeriv h (by simp)

private lemma mannheimGradOneForm_exact_and_closed
    (w : ℝ) {β α : FourSpace → ℝ} (hβ : ContDiff ℝ 2 β) (hα : ContDiff ℝ 2 α) :
    extD3 (mannheimGradOneForm w β α) = 0 := by
  let logScalar : FourSpace → Mat4C := fun y =>
    (((w * β y : ℝ) : ℂ) + ((α y : ℝ) : ℂ) * Complex.I) • (1 : Mat4C)
  have hLogCD : ContDiff ℝ 2 logScalar := by
    have h1 : ContDiff ℝ 2 (fun y => ((w * β y : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hβ.const_smul w)
    have h2 : ContDiff ℝ 2 (fun y => ((α y : ℝ) : ℂ) * Complex.I) :=
      (Complex.ofRealCLM.contDiff.comp hα).mul contDiff_const
    exact (h1.add h2).smul_const (1 : Mat4C)
  let zeroForm : Mat4CForm 0 := fun y =>
    ContinuousAlternatingMap.constOfIsEmpty ℝ FourSpace (Fin 0) (logScalar y)
  have hZeroCD : ContDiff ℝ 2 zeroForm := by
    let constLM : Mat4C →ₗ[ℝ] (FourSpace [⋀^Fin 0]→L[ℝ] Mat4C) :=
      { toFun := ContinuousAlternatingMap.constOfIsEmpty ℝ FourSpace (Fin 0)
        map_add' := fun a b => by ext v; simp
        map_smul' := fun c a => by ext v; simp }
    let constCLM : Mat4C →L[ℝ] (FourSpace [⋀^Fin 0]→L[ℝ] Mat4C) :=
      LinearMap.mkContinuous constLM 1 fun a => by
        rw [one_mul]
        exact (ContinuousAlternatingMap.opNorm_le_iff (norm_nonneg a)).mpr fun v => by
          rw [Fintype.prod_empty, mul_one]
          change ‖(ContinuousAlternatingMap.constOfIsEmpty ℝ FourSpace (Fin 0) a) v‖ ≤ ‖a‖
          rw [ContinuousAlternatingMap.constOfIsEmpty_apply]
    exact constCLM.contDiff.comp hLogCD
  have hZeroDiff : Differentiable ℝ zeroForm := hZeroCD.differentiable (by norm_num)
  have hGradEq : mannheimGradOneForm w β α = extD3 zeroForm := by
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    have hDlog :
        fderiv ℝ logScalar x (v 0) =
          (((w * fderiv ℝ β x (v 0) : ℝ) : ℂ) +
            ((fderiv ℝ α x (v 0) : ℝ) : ℂ) * Complex.I) • (1 : Mat4C) := by
      have h1 : HasFDerivAt (fun y => ((w * β y : ℝ) : ℂ))
          (w • Complex.ofRealCLM.comp (fderiv ℝ β x)) x := by
        simpa [Function.comp_def, smul_eq_mul] using
          (Complex.ofRealCLM.hasFDerivAt.comp x
            ((hβ.differentiable (by norm_num) x).hasFDerivAt.const_smul w))
      have h2 : HasFDerivAt (fun y => ((α y : ℝ) : ℂ) * Complex.I)
          (((ContinuousLinearMap.mul ℝ ℂ).flip Complex.I).comp
            (Complex.ofRealCLM.comp (fderiv ℝ α x))) x := by
        have hmul : HasFDerivAt (fun z : ℂ => z * Complex.I)
            ((ContinuousLinearMap.mul ℝ ℂ).flip Complex.I) ((α x : ℝ) : ℂ) :=
          ((ContinuousLinearMap.mul ℝ ℂ).flip Complex.I).hasFDerivAt
        exact hmul.comp x
          (Complex.ofRealCLM.hasFDerivAt.comp x (hα.differentiable (by norm_num) x).hasFDerivAt)
      have h12 :
          HasFDerivAt (fun y => ((w * β y : ℝ) : ℂ) + ((α y : ℝ) : ℂ) * Complex.I)
            (w • Complex.ofRealCLM.comp (fderiv ℝ β x) +
              ((ContinuousLinearMap.mul ℝ ℂ).flip Complex.I).comp
                (Complex.ofRealCLM.comp (fderiv ℝ α x))) x := h1.add h2
      have hSmul :
          HasFDerivAt logScalar
            ((w • Complex.ofRealCLM.comp (fderiv ℝ β x) +
              ((ContinuousLinearMap.mul ℝ ℂ).flip Complex.I).comp
                (Complex.ofRealCLM.comp (fderiv ℝ α x))).smulRight (1 : Mat4C)) x :=
        h12.smul_const (1 : Mat4C)
      rw [hSmul.fderiv]
      simp [Complex.real_smul, Complex.ofReal_mul, mul_comm Complex.I]
    have hExt0 : extD3 zeroForm x v = fderiv ℝ logScalar x (v 0) := by
      change extDeriv zeroForm x v = fderiv ℝ logScalar x (v 0)
      rw [extDeriv_apply (hZeroDiff x) v, Fin.sum_univ_one]
      have hEval : (fun y => zeroForm y ((0 : Fin 1).removeNth v)) = logScalar := rfl
      simp only [Fin.val_zero, pow_zero, one_smul]
      change fderiv ℝ (fun y => zeroForm y ((0 : Fin 1).removeNth v)) x (v 0) =
        fderiv ℝ logScalar x (v 0)
      rw [hEval]
    have hv0 : v = fun _ => v 0 := by
      funext i
      fin_cases i
      rfl
    rw [hExt0, hDlog]
    conv_lhs => rw [hv0]
    exact mannheimGradOneForm_apply w β α x (v 0)
  rw [hGradEq]
  exact extD3_extD3 hZeroCD

/-- **Layer 3 (4D Curvature, Covariant Exterior Derivative, Self-Duality & Yang–Mills PDE Invariance)**:
Assuming only `ContDiff ℝ 2 β` and `ContDiff ℝ 2 α` (since `ymCurvature` and `covExtDeriv`
close directly under `extDeriv (mannheimGradOneForm w β α) = 0`), shifting `A` by
`mannheimGradOneForm w β α` leaves `ymCurvature`, `covExtDeriv`, `IsSelfDualForm4`,
`YangMillsPDE`, and `YangMillsPDEMinkowski` strictly invariant. -/
theorem mannheim_ymCurvature_and_pde_invariance
    (w : ℝ) (β α : FourSpace → ℝ)
    (hβ : ContDiff ℝ 2 β) (hα : ContDiff ℝ 2 α)
    (A : Mat4CForm 1) (hA : Differentiable ℝ A) :
    ymCurvature (A - mannheimGradOneForm w β α) = ymCurvature A ∧
    (∀ {k : ℕ} (η : Mat4CForm k),
      covExtDeriv (A - mannheimGradOneForm w β α) η = covExtDeriv A η) ∧
    (IsSelfDualForm4 (A - mannheimGradOneForm w β α) ↔ IsSelfDualForm4 A) ∧
    (YangMillsPDE (A - mannheimGradOneForm w β α) ↔ YangMillsPDE A) ∧
    (YangMillsPDEMinkowski (A - mannheimGradOneForm w β α) ↔ YangMillsPDEMinkowski A) := by
  have hDiffG : Differentiable ℝ (mannheimGradOneForm w β α) :=
    mannheimGradOneForm_differentiable w hβ hα
  have hClosedG : extD3 (mannheimGradOneForm w β α) = 0 :=
    mannheimGradOneForm_exact_and_closed w hβ hα
  have hWedge : ∀ {k : ℕ} (η : Mat4CForm k),
      wedgeComm (A - mannheimGradOneForm w β α) η = wedgeComm A η := by
    intro k η
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    change wedgeCommAt k ((A - mannheimGradOneForm w β α) x) (η x) v =
      wedgeCommAt k (A x) (η x) v
    rw [wedgeCommAt_apply, wedgeCommAt_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    change mat4CCommCLM (A x (fun _ => v i) - mannheimGradOneForm w β α x (fun _ => v i))
        (η x (i.removeNth v)) =
      mat4CCommCLM (A x (fun _ => v i)) (η x (i.removeNth v))
    rw [map_sub, sub_apply, mannheimGradOneForm_comm_zero, sub_zero]
  have hCov : ∀ {k : ℕ} (η : Mat4CForm k),
      covExtDeriv (A - mannheimGradOneForm w β α) η = covExtDeriv A η := by
    intro k η
    funext x
    change extD3 η x + wedgeComm (A - mannheimGradOneForm w β α) η x =
      extD3 η x + wedgeComm A η x
    rw [hWedge]
  have hHalf : halfWedgeSelf (A - mannheimGradOneForm w β α) = halfWedgeSelf A := by
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    rw [halfWedgeSelf_apply, halfWedgeSelf_apply]
    change mat4CCommCLM (A x (fun _ => v 0) - mannheimGradOneForm w β α x (fun _ => v 0))
        (A x (fun _ => v 1) - mannheimGradOneForm w β α x (fun _ => v 1)) =
      mat4CCommCLM (A x (fun _ => v 0)) (A x (fun _ => v 1))
    rw [map_sub, mannheimGradOneForm_comm_zero_right, sub_zero, map_sub, sub_apply,
      mannheimGradOneForm_comm_zero, sub_zero]
  have hExtD : extD3 (A - mannheimGradOneForm w β α) = extD3 A := by
    funext x
    have hsub : A - mannheimGradOneForm w β α = A + (-1 : ℝ) • mannheimGradOneForm w β α := by
      ext y v i j; simp [sub_eq_add_neg]
    rw [hsub, extD3_add (hA x) ((hDiffG x).const_smul (-1 : ℝ)), extD3_smul]
    have hGx : extD3 (mannheimGradOneForm w β α) x = 0 := congrFun hClosedG x
    rw [hGx, smul_zero, add_zero]
  have hCurv : ymCurvature (A - mannheimGradOneForm w β α) = ymCurvature A := by
    funext x
    change extD3 (A - mannheimGradOneForm w β α) x +
        halfWedgeSelf (A - mannheimGradOneForm w β α) x =
      extD3 A x + halfWedgeSelf A x
    rw [hExtD, hHalf]
  refine ⟨hCurv, hCov, ?_, ?_, ?_⟩
  · simp only [IsSelfDualForm4, hCurv]
  · simp only [YangMillsPDE, hCurv, hCov]
  · simp only [YangMillsPDEMinkowski, hCurv, hCov]

/-- **Layer 3 (Shifted Non-Abelian `circularGaugeForm` & `circularMinkowskiWaveForm` Solutions)**:
Shifting the self-dual Euclidean instanton `circularGaugeForm` or the Lorentzian plane-wave
solution `circularMinkowskiWaveForm f` by `mannheimGradOneForm w β α` (`ContDiff ℝ 2`) yields
non-vanishing curvature solving `IsSelfDualForm4`, `YangMillsPDE`, and `YangMillsPDEMinkowski`. -/
theorem mannheim_shifted_circularGaugeForm_and_waveForm_solutions
    (w : ℝ) (β α : FourSpace → ℝ)
    (hβ : ContDiff ℝ 2 β) (hα : ContDiff ℝ 2 α)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hf0 : f 0 ≠ 0) :
    (ymCurvature (circularGaugeForm - mannheimGradOneForm w β α) ≠ 0 ∧
     IsSelfDualForm4 (circularGaugeForm - mannheimGradOneForm w β α) ∧
     YangMillsPDE (circularGaugeForm - mannheimGradOneForm w β α)) ∧
    (ymCurvature (circularMinkowskiWaveForm f - mannheimGradOneForm w β α) ≠ 0 ∧
     YangMillsPDEMinkowski (circularMinkowskiWaveForm f - mannheimGradOneForm w β α)) := by
  have hG_diff : Differentiable ℝ circularGaugeForm :=
    circularGaugeForm_contDiff.differentiable (by norm_num)
  have hInvG := mannheim_ymCurvature_and_pde_invariance w β α hβ hα circularGaugeForm hG_diff
  have hWave_diff : Differentiable ℝ (circularMinkowskiWaveForm f) := by
    let lc : FourSpace →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap
        { toFun := fun x => x 0 - x 1
          map_add' := fun x y => by simp; ring
          map_smul' := fun c x => by simp; ring }
    have hlc : ContDiff ℝ 2 (fun x : FourSpace => f (lc x)) := hf.comp lc.contDiff
    have hcd : ContDiff ℝ 2 (circularMinkowskiWaveForm f) :=
      (hlc.smul contDiff_const).add contDiff_const
    exact hcd.differentiable (by norm_num)
  have hInvW :=
    mannheim_ymCurvature_and_pde_invariance w β α hβ hα (circularMinkowskiWaveForm f) hWave_diff
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [hInvG.1]
      exact circularGaugeForm_ymCurvature_ne_zero
    · exact hInvG.2.2.1.mpr circularGaugeForm_isSelfDual
    · exact hInvG.2.2.2.1.mpr circularGaugeForm_solves_yangMillsPDE
  · refine ⟨?_, ?_⟩
    · rw [hInvW.1]
      exact circularMinkowskiWaveForm_ymCurvature_ne_zero hf hf0
    · exact hInvW.2.2.2.2.mpr (circularMinkowskiWaveForm_solves_yangMillsPDEMinkowski hf)

end Layer3ManifoldPDE

/-! ## 5. Certified `TypedArchetype` Registration -/

section ArchetypeRegistrations

open scoped Matrix.Norms.Operator

/-- Proved `TypedArchetype` certifying the typed unification bridge from Mannheim's
conformal-plus-Yang–Mills scale–phase law (`ψ ↦ exp(β + i α) ψ`) across Layers 0–3 of
the Doubled-Minkowski chiral Yang–Mills suite. -/
def archMannheimDoubledMinkowskiYangMillsBridge : TypedArchetype Unit .proved where
  name := `archMannheimDoubledMinkowskiYangMillsBridge
  phase := 14
  claim := fun _ =>
    (∀ (β α : ℝ) (x : Coordinate),
      ‖scaleGaugeMultiplier β α‖ = Real.exp β ∧
      wittNorm (‖scaleGaugeMultiplier β α‖ • x) = Real.exp (2 * β) * wittNorm x ∧
      chiralKreinForm (E := FourSpace)
          (circularCoordToKreinFrame (‖scaleGaugeMultiplier β α‖ • x))
          (circularCoordToKreinFrame (‖scaleGaugeMultiplier β α‖ • x)) =
        conformalRescale β chiralKreinBilin
          (circularCoordToKreinFrame x) (circularCoordToKreinFrame x)) ∧
    (∀ (β α : ℝ) (x : Coordinate),
      gramBlochState (scaleGaugeMultiplier β α • weylUpperMat x) =
        gramBlochState (weylUpperMat x) ∧
      gramBlochState (scaleGaugeMultiplier β (-α) • weylLowerMat x) =
        gramBlochState (weylLowerMat x)) ∧
    (∀ (β₁ α₁ β₂ α₂ : ℝ) (x : Coordinate),
      let P := chiralExteriorProj4 (Fin 4 → ℂ)
      let U := (chiralDiagBlock4
        (scaleGaugeMultiplier β₁ α₁ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (scaleGaugeMultiplier β₂ α₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ))).map
        (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
      let Uinv := (chiralDiagBlock4
        (scaleGaugeMultiplier (-β₁) (-α₁) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (scaleGaugeMultiplier (-β₂) (-α₂) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).map
        (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
      let A_ev' := U * circularGaugeConnection4 (circularEvenOmega x) * Uinv
      MatrixIsHomogeneous 1 A_ev' ∧
      matrixExteriorDerivative circularEvenDiff A_ev' = peirceGradingDeriv P A_ev' ∧
      covariantDerivative A_ev' circularEvenDiff (genV P A_ev' A_ev') = 0) ∧
    (∀ (x : Coordinate) (η : ExteriorAlgebra ℂ (Fin 4 → ℂ)),
       IsHomogeneousExteriorDegree 1 η →
       (circularGaugeConnection4 (circularEvenOmega x) + Matrix.diagonal (fun _ => η)) *
         (circularGaugeConnection4 (circularEvenOmega x) + Matrix.diagonal (fun _ => η)) =
         circularGaugeConnection4 (circularEvenOmega x) *
           circularGaugeConnection4 (circularEvenOmega x)) ∧
    (∀ (α₁ α₂ : ℝ) (β α : FourSpace → ℝ),
      ContDiff ℝ 3 β → ContDiff ℝ 3 α →
      ∀ (A : FourSpace → Fin 4 → Mat4C), ContDiff ℝ 2 A →
      ∀ (y : FourSpace) (μ ν : Fin 4),
        let U := chiralDiagBlock4
          (scaleGaugeMultiplier 0 α₁ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
          (scaleGaugeMultiplier 0 α₂ • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        continuumCurvature (fun z ρ => U * A z ρ * U⁻¹ + mannheimGaugeShiftMat4 β α z ρ) y μ ν =
          U * continuumCurvature A y μ ν * U⁻¹ ∧
        continuumPlaquetteAction
            (fun z ρ => U * A z ρ * U⁻¹ + mannheimGaugeShiftMat4 β α z ρ) y μ ν =
          continuumPlaquetteAction A y μ ν) ∧
    (∀ (w : ℝ) (β α : FourSpace → ℝ),
      ContDiff ℝ 2 β → ContDiff ℝ 2 α →
      ∀ (A : Mat4CForm 1), Differentiable ℝ A →
        ymCurvature (A - mannheimGradOneForm w β α) = ymCurvature A ∧
        (YangMillsPDE (A - mannheimGradOneForm w β α) ↔ YangMillsPDE A) ∧
        (YangMillsPDEMinkowski (A - mannheimGradOneForm w β α) ↔ YangMillsPDEMinkowski A))
  evidence := fun _ =>
    ⟨fun β α x =>
      let h := mannheim_witt_krein_conformal_scaling β α x 0 0 0 0 0 0 0 0
      ⟨h.1, h.2.2.1, h.2.2.2.1⟩,
     fun β α x =>
      let h := mannheim_weyl_bloch_scale_gauge_invariance β α x 0
      ⟨h.2.1, h.2.2.1⟩,
     fun β₁ α₁ β₂ α₂ x =>
      let h := mannheim_graded_even_compat_preserved β₁ α₁ β₂ α₂ x
      ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩,
     fun x η hη => (mannheim_even_oneForm_abelian_shift circularEvenDiff x η hη).2.1,
     fun α₁ α₂ β α hβ hα A hA y μ ν =>
      let h := mannheim_lattice_continuum_gauge_covariance.{0, 0}
        α₁ α₂ β α hβ hα (fun _ _ => 0) A hA (fun _ => 0) y (differentiableAt_const (0 : Mat4C)) μ ν
      ⟨h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩,
     fun w β α hβ hα A hA =>
      let h := mannheim_ymCurvature_and_pde_invariance w β α hβ hα A hA
      ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩⟩

#register_archetype archMannheimDoubledMinkowskiYangMillsBridge
#audit_archetype archMannheimDoubledMinkowskiYangMillsBridge

end ArchetypeRegistrations

end InfoGeometry.Synthesis.MannheimDoubledMinkowskiYangMillsBridge
