/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Analytic Continuum Limit (`a → 0`) for Doubled-Minkowski Lattice Chiral Yang–Mills

This module formalizes the analytic lattice-to-continuum limit (`a → 0` along `𝓝[≠] 0`)
for the doubled-Minkowski circular split-octonion chiral Yang–Mills gauge theory on
`Mat4C := Matrix (Fin 4) (Fin 4) ℂ`, bridging `DoubledMinkowskiCircularChiralYangMillsBridge`
to normed matrix exponentials, covariant finite differences, Wilson plaquette curvature and
Hilbert–Schmidt action, and continuous inductive star-ring colimit transport:

1. **Normed Carrier & Link Transporters**: Uses `Matrix.Norms.Operator` on `Mat4C` and defines
   `circularLinkTransport` via `NormedSpace.exp (a • circularConnectionMat4 (x y μ))`.
2. **Covariant Finite Difference Limit**: Proves `tendsto_latticeCovariantDiff`, showing
   `a⁻¹ • (U_μ(y, a) Φ(y + a e_μ) U_μ(y, a)⁻¹ - Φ(y))` converges to
   `∂_μ Φ(y) + [A_μ(y), Φ(y)]` as `a → 0` (`𝓝[≠] 0`).
3. **Wilson Plaquette Curvature & Action Limits**: Proves `tendsto_wilsonPlaquette_curvature`
   and `tendsto_wilsonPlaquetteAction` (`C²` connection `A`), recovering the non-Abelian
   curvature `∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν]` and Hilbert–Schmidt action `Re Tr(Fᴴ F)`.
4. **Non-Abelian Witness & Star-Colimit Transport**: Exhibits an explicit `circularConnectionMat4`
   field with `continuumCurvature ≠ 0` and `continuumPlaquetteAction = 4 > 0` linked to
   `circularCurvatureMat4_hilbertSchmidt_action` and `circularCurvatureMat4_vorticity_action_gap`,
   and proves `circularColimit_continuum_transport` plus a concrete `tailTowerCone Mat4C`
   instantiation `circularColimit_continuum_transport_tailTower`.
-/

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Operator Topology

namespace InfoGeometry.Lie

open InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
open InfoGeometry.Canonical.RealDoubledChiralKreinFrame (frameBasis)
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
  (coordinateEquiv frame coordinateEquiv_apply_frame)
open InfoGeometry.Lie.SplitOctonionEllCrossChannel (uPlus uMinus)
open InfoGeometry.Lie.SplitOctonionEllPolarization (rootPlus rootMinus)
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge (wittNorm)
open InfoGeometry.Quantum.PauliSoldering (solder σ0 σ1 σ2 σ3)
open InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge (pauliSolder2x2)

/-! ## 1. Normed Two-Sheet Matrix Carrier & Link Transporters -/

/-- Complex $4 \times 4$ two-sheeted matrix carrier equipped with `Matrix.Norms.Operator`. -/
abbrev Mat4C := Matrix (Fin 4) (Fin 4) ℂ

/-- Lattice gauge link transporter `U_μ(y, a) = exp(a A_μ(x y μ))` driven by
`circularConnectionMat4`. -/
noncomputable def circularLinkTransport
    (x : FourSpace → Fin 4 → Coordinate) (y : FourSpace) (μ : Fin 4) (a : ℝ) : Mat4C :=
  NormedSpace.exp (a • circularConnectionMat4 (x y μ))

set_option backward.isDefEq.respectTransparency false in
theorem circularLinkTransport_continuous
    (x : FourSpace → Fin 4 → Coordinate) (y : FourSpace) (μ : Fin 4) :
    Continuous (fun a : ℝ => circularLinkTransport x y μ a) := by
  have hDiff : Differentiable ℝ (fun a : ℝ => circularLinkTransport x y μ a) := fun t =>
    (hasDerivAt_exp_smul_const (circularConnectionMat4 (x y μ)) t).differentiableAt
  exact hDiff.continuous

/-! ## 2. Lattice Covariant Difference & `a → 0` Convergence -/

/-- Lattice covariant finite difference along direction `frameBasis μ` with lattice spacing `a`. -/
noncomputable def latticeCovariantDiff
    (A : FourSpace → Fin 4 → Mat4C) (Φ : FourSpace → Mat4C)
    (y : FourSpace) (μ : Fin 4) (a : ℝ) : Mat4C :=
  a⁻¹ • (NormedSpace.exp (a • A y μ) * Φ (y + a • frameBasis μ) *
    (NormedSpace.exp (a • A y μ))⁻¹ - Φ y)

/-- Continuum covariant derivative `∂_μ Φ(y) + [A_μ(y), Φ(y)]` in direction `frameBasis μ`. -/
noncomputable def continuumCovariantDeriv
    (A : FourSpace → Fin 4 → Mat4C) (Φ : FourSpace → Mat4C)
    (y : FourSpace) (μ : Fin 4) : Mat4C :=
  fderiv ℝ Φ y (frameBasis μ) + (A y μ * Φ y - Φ y * A y μ)

theorem latticeCovariantDiff_at_zero
    (A : FourSpace → Fin 4 → Mat4C) (Φ : FourSpace → Mat4C)
    (y : FourSpace) (μ : Fin 4) :
    latticeCovariantDiff A Φ y μ 0 = 0 := by
  dsimp only [latticeCovariantDiff]
  rw [inv_zero, zero_smul]

theorem continuumCovariantDeriv_zero_const
    (M0 : Mat4C) (y : FourSpace) (μ : Fin 4) :
    continuumCovariantDeriv 0 (fun _ => M0) y μ = 0 := by
  dsimp only [continuumCovariantDeriv]
  simp

theorem continuumCovariantDeriv_abelian_const
    (c d : ℂ) (y : FourSpace) (μ : Fin 4) :
    continuumCovariantDeriv (fun _ _ => c • (1 : Mat4C)) (fun _ => d • (1 : Mat4C)) y μ = 0 := by
  simp [continuumCovariantDeriv]
  rw [smul_comm, sub_self]

theorem continuumCovariantDeriv_nonabelian_const_nonzero (y : FourSpace) :
    let A : FourSpace → Fin 4 → Mat4C := fun _ _ =>
      circularConnectionMat4 (coordinateEquiv uPlus)
    let Φ : FourSpace → Mat4C := fun _ => chiralProjMat4
    continuumCovariantDeriv A Φ y 0 ≠ 0 := by
  intro A Φ hZero
  dsimp only [A, Φ, continuumCovariantDeriv] at hZero
  rw [fderiv_const_apply, zero_apply, zero_add] at hZero
  have hComm :
      circularConnectionMat4 (coordinateEquiv uPlus) * chiralProjMat4 =
        chiralProjMat4 * circularConnectionMat4 (coordinateEquiv uPlus) :=
    sub_eq_zero.mp hZero
  have h02 := congrFun (congrFun hComm 0) 2
  have hc : coordinateEquiv uPlus = Pi.single 0 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 0
  simp [chiralProjMat4, chiralProj4, chiralDiagBlock4, circularConnectionMat4,
    chiralOffBlock4, Matrix.mul_apply, Fin.sum_univ_four, hc,
    weylUpperMat, pauliSolder2x2, solder, σ0, σ1, σ2, σ3] at h02

theorem continuumCovariantDeriv_connection_sq_zero
    (x : Coordinate) (y : FourSpace) (μ : Fin 4) :
    continuumCovariantDeriv (fun _ _ => circularConnectionMat4 x)
      (fun _ => circularCurvatureMat4 x) y μ = 0 := by
  dsimp only [continuumCovariantDeriv, circularCurvatureMat4]
  simp [mul_assoc]

private lemma hasDerivAt_line_zero (y : FourSpace) (μ : Fin 4) :
    HasDerivAt (fun a : ℝ => y + a • frameBasis μ) (frameBasis μ) 0 := by
  have hId : HasDerivAt (fun a : ℝ => a) (1 : ℝ) 0 := hasDerivAt_id 0
  have hSmul : HasDerivAt (fun a : ℝ => a • frameBasis μ) ((1 : ℝ) • frameBasis μ) 0 :=
    hId.smul_const (frameBasis μ)
  simpa using hSmul.const_add y

set_option backward.isDefEq.respectTransparency false in
private lemma hasDerivAt_exp_smul_zero (M : Mat4C) :
    HasDerivAt (fun a : ℝ => NormedSpace.exp (a • M)) M 0 := by
  simpa [zero_smul, NormedSpace.exp_zero, one_mul] using hasDerivAt_exp_smul_const M (0 : ℝ)

set_option backward.isDefEq.respectTransparency false in
private lemma hasDerivAt_exp_neg_smul_zero (M : Mat4C) :
    HasDerivAt (fun a : ℝ => (NormedSpace.exp (a • M))⁻¹) (-M) 0 := by
  have hFun : (fun a : ℝ => (NormedSpace.exp (a • M))⁻¹) =
      fun a : ℝ => NormedSpace.exp (a • (-M)) := by
    funext a
    rw [← Matrix.exp_neg, ← smul_neg]
  rw [hFun]
  exact hasDerivAt_exp_smul_zero (-M)

set_option backward.isDefEq.respectTransparency false in
theorem tendsto_latticeCovariantDiff
    (A : FourSpace → Fin 4 → Mat4C) (Φ : FourSpace → Mat4C)
    (y : FourSpace) (μ : Fin 4) (hΦ : DifferentiableAt ℝ Φ y) :
    Filter.Tendsto (fun a : ℝ => latticeCovariantDiff A Φ y μ a)
      (𝓝[≠] 0) (𝓝 (continuumCovariantDeriv A Φ y μ)) := by
  let U : ℝ → Mat4C := fun a => NormedSpace.exp (a • A y μ)
  let Uinv : ℝ → Mat4C := fun a => (NormedSpace.exp (a • A y μ))⁻¹
  let Φline : ℝ → Mat4C := fun a => Φ (y + a • frameBasis μ)
  have hU : HasDerivAt U (A y μ) 0 := hasDerivAt_exp_smul_zero (A y μ)
  have hUinv : HasDerivAt Uinv (-(A y μ)) 0 := hasDerivAt_exp_neg_smul_zero (A y μ)
  have hΦline : HasDerivAt Φline (fderiv ℝ Φ y (frameBasis μ)) 0 :=
    hΦ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line_zero y μ) (by simp)
  have hLeft := hU.mul hΦline
  simp only [U, Φline, zero_smul, NormedSpace.exp_zero, one_mul, add_zero] at hLeft
  have hFull := hLeft.mul hUinv
  simp only [Uinv, Pi.mul_apply, zero_smul, NormedSpace.exp_zero, inv_one, mul_one,
    one_mul, add_zero] at hFull
  have hDerivEq :
      (A y μ * Φ y + fderiv ℝ Φ y (frameBasis μ) + Φ y * -(A y μ)) =
        continuumCovariantDeriv A Φ y μ := by
    simp only [continuumCovariantDeriv, mul_neg]
    abel
  rw [hDerivEq] at hFull
  have hSlope := hFull.tendsto_slope_zero
  simpa [latticeCovariantDiff, U, Uinv, Φline, zero_smul, NormedSpace.exp_zero,
    inv_one, one_mul, mul_one] using hSlope

/-! ## 3. Wilson Plaquette Curvature & `a → 0` Convergence -/

private lemma real_mul_sq (a : ℝ) : a * a ^ 2 = a ^ 3 := by ring
private lemma real_sq_mul (a : ℝ) : a ^ 2 * a = a ^ 3 := by ring
private lemma real_sq_sq (a : ℝ) : a ^ 2 * a ^ 2 = a ^ 4 := by ring
private lemma real_inv_sq_sq (a : ℝ) : (a ^ 2)⁻¹ * (a ^ 2)⁻¹ = (a ^ 4)⁻¹ := by ring

set_option backward.isDefEq.respectTransparency false in
private lemma exp_taylor2_isBigO :
    (fun X : Mat4C => NormedSpace.exp X - (1 + X + (2 : ℝ)⁻¹ • (X * X))) =O[𝓝 0]
      fun X => ‖X‖ ^ 3 := by
  have hPS : HasFPowerSeriesAt (NormedSpace.exp : Mat4C → Mat4C)
      (NormedSpace.expSeries ℝ Mat4C) 0 :=
    NormedSpace.exp_hasFPowerSeriesAt_zero
  have hBigO := hPS.isBigO_sub_partialSum_pow 3
  refine hBigO.congr' (Filter.Eventually.of_forall fun X => ?_)
    (Filter.Eventually.of_forall fun _ => rfl)
  simp only [zero_add, FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    Finset.range_zero, Finset.sum_empty, zero_add]
  rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq,
    NormedSpace.expSeries_apply_eq]
  simp [Nat.factorial, pow_zero, pow_one, sq]

set_option backward.isDefEq.respectTransparency false in
private lemma exp_smul_taylor2 (B : ℝ → Mat4C) (B₁ : Mat4C) (hB : HasDerivAt B B₁ 0) :
    (fun a : ℝ => NormedSpace.exp (a • B a) -
      (1 + a • B 0 + (a ^ 2) • (B₁ + (2 : ℝ)⁻¹ • (B 0 * B 0)))) =o[𝓝 0]
      fun a => a ^ 2 := by
  have hB0 : Filter.Tendsto B (𝓝 0) (𝓝 (B 0)) := hB.continuousAt.tendsto
  have hB_diff0 : Filter.Tendsto (fun a => B a - B 0) (𝓝 0) (𝓝 0) := by
    rw [← sub_self (B 0)]
    exact hB0.sub tendsto_const_nhds
  have hS_tendsto : Filter.Tendsto (fun a : ℝ => a • B a) (𝓝 0) (𝓝 0) := by
    simpa [zero_smul] using Filter.Tendsto.smul Filter.tendsto_id hB0
  have hB_bigO : B =O[𝓝 0] (1 : ℝ → ℝ) := hB.continuousAt.isBigO
  have hS_bigO : (fun a : ℝ => a • B a) =O[𝓝 0] (fun a : ℝ => a) := by
    simpa using (Asymptotics.isBigO_refl (fun a : ℝ => a) (𝓝 0)).smul hB_bigO
  have hExp_bigO :
      (fun a : ℝ => NormedSpace.exp (a • B a) -
        (1 + a • B a + (2 : ℝ)⁻¹ • ((a • B a) * (a • B a)))) =O[𝓝 0]
        fun a : ℝ => ‖a • B a‖ ^ 3 :=
    exp_taylor2_isBigO.comp_tendsto hS_tendsto
  have hCube_bigO : (fun a : ℝ => ‖a • B a‖ ^ 3) =O[𝓝 0] fun a : ℝ => a ^ 3 := by
    have hNorm : (fun a : ℝ => ‖a • B a‖) =O[𝓝 0] fun a : ℝ => a := hS_bigO.norm_left
    have hPow := hNorm.pow 3
    simpa [Real.norm_eq_abs, abs_pow, norm_pow] using hPow
  have hCube_littleO : (fun a : ℝ => a ^ 3) =o[𝓝 0] fun a : ℝ => a ^ 2 :=
    Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 3)
  have hTail :
      (fun a : ℝ => NormedSpace.exp (a • B a) -
        (1 + a • B a + (2 : ℝ)⁻¹ • ((a • B a) * (a • B a)))) =o[𝓝 0]
        fun a : ℝ => a ^ 2 :=
    (hExp_bigO.trans hCube_bigO).trans_isLittleO hCube_littleO
  have hLin_B : (fun a : ℝ => B a - B 0 - a • B₁) =o[𝓝 0] fun a : ℝ => a := by
    simpa using hB.isLittleO
  have hLin :
      (fun a : ℝ => a • B a - (a • B 0 + (a ^ 2) • B₁)) =o[𝓝 0] fun a : ℝ => a ^ 2 := by
    have hSmul := (Asymptotics.isBigO_refl (fun a : ℝ => a) (𝓝 0)).smul_isLittleO hLin_B
    refine hSmul.congr' (Filter.Eventually.of_forall fun a => ?_)
      (Filter.Eventually.of_forall fun a => ?_)
    · simp only [smul_sub, smul_add, smul_smul, sq, sub_sub]
    · simp [sq]
  have hQuad_inner :
      (fun a : ℝ => B a * B a - B 0 * B 0) =o[𝓝 0] (1 : ℝ → ℝ) := by
    have hDiff_littleO : (fun a : ℝ => B a - B 0) =o[𝓝 0] (1 : ℝ → ℝ) :=
      (Asymptotics.isLittleO_one_iff ℝ).2 hB_diff0
    have hProd1 := hB_bigO.mul_isLittleO hDiff_littleO
    have hConst : (fun _ : ℝ => B 0) =O[𝓝 0] (1 : ℝ → ℝ) :=
      Asymptotics.isBigO_const_of_tendsto (tendsto_const_nhds (x := B 0)) one_ne_zero
    have hProd2 := hDiff_littleO.mul_isBigO hConst
    have hSum := hProd1.add hProd2
    refine hSum.congr' (Filter.Eventually.of_forall fun a => ?_)
      (Filter.Eventually.of_forall fun _ => by simp)
    noncomm_ring
  have hQuad :
      (fun a : ℝ => (2 : ℝ)⁻¹ • ((a • B a) * (a • B a)) -
        (a ^ 2) • ((2 : ℝ)⁻¹ • (B 0 * B 0))) =o[𝓝 0]
        fun a : ℝ => a ^ 2 := by
    have hSq : (fun a : ℝ => a ^ 2) =O[𝓝 0] fun a : ℝ => a ^ 2 :=
      Asymptotics.isBigO_refl _ _
    have hSmul := (hSq.smul_isLittleO hQuad_inner).const_smul_left (2 : ℝ)⁻¹
    refine hSmul.congr' (Filter.Eventually.of_forall fun a => ?_)
      (Filter.Eventually.of_forall fun a => ?_)
    · simp only [Pi.smul_apply, smul_sub, smul_smul, smul_mul_assoc,
        mul_smul_comm, sq]
      rw [mul_comm (2 : ℝ)⁻¹ (a * a)]
    · simp
  have hComb := (hTail.add hLin).add hQuad
  refine hComb.congr' (Filter.Eventually.of_forall fun a => ?_)
    (Filter.Eventually.of_forall fun _ => rfl)
  simp only [smul_add]
  abel

set_option backward.isDefEq.respectTransparency false in
private lemma mul_taylor2
    (F₁ F₂ : ℝ → Mat4C) (X₁ X₂ Y₁ Y₂ : Mat4C)
    (h₁ : (fun a : ℝ => F₁ a - (1 + a • X₁ + (a ^ 2) • Y₁)) =o[𝓝 0] fun a => a ^ 2)
    (h₂ : (fun a : ℝ => F₂ a - (1 + a • X₂ + (a ^ 2) • Y₂)) =o[𝓝 0] fun a => a ^ 2) :
    (fun a : ℝ => F₁ a * F₂ a -
      (1 + a • (X₁ + X₂) + (a ^ 2) • (Y₁ + Y₂ + X₁ * X₂))) =o[𝓝 0]
      fun a => a ^ 2 := by
  let P₁ : ℝ → Mat4C := fun a => 1 + a • X₁ + (a ^ 2) • Y₁
  let P₂ : ℝ → Mat4C := fun a => 1 + a • X₂ + (a ^ 2) • Y₂
  have hId0 : Filter.Tendsto (fun a : ℝ => a) (𝓝 0) (𝓝 0) := Filter.tendsto_id
  have hPow0 : Filter.Tendsto (fun a : ℝ => a ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using hId0.pow 2
  have hP₁_tendsto : Filter.Tendsto P₁ (𝓝 0) (𝓝 1) := by
    have h1 : Filter.Tendsto (fun a : ℝ => a • X₁) (𝓝 0) (𝓝 0) := by
      simpa using hId0.smul (tendsto_const_nhds (x := X₁))
    have h2 : Filter.Tendsto (fun a : ℝ => (a ^ 2) • Y₁) (𝓝 0) (𝓝 0) := by
      simpa using hPow0.smul (tendsto_const_nhds (x := Y₁))
    simpa [P₁] using ((tendsto_const_nhds (x := (1 : Mat4C))).add h1).add h2
  have hP₂_tendsto : Filter.Tendsto P₂ (𝓝 0) (𝓝 1) := by
    have h1 : Filter.Tendsto (fun a : ℝ => a • X₂) (𝓝 0) (𝓝 0) := by
      simpa using hId0.smul (tendsto_const_nhds (x := X₂))
    have h2 : Filter.Tendsto (fun a : ℝ => (a ^ 2) • Y₂) (𝓝 0) (𝓝 0) := by
      simpa using hPow0.smul (tendsto_const_nhds (x := Y₂))
    simpa [P₂] using ((tendsto_const_nhds (x := (1 : Mat4C))).add h1).add h2
  have hP₁_bigO : P₁ =O[𝓝 0] (1 : ℝ → ℝ) :=
    Asymptotics.isBigO_const_of_tendsto hP₁_tendsto one_ne_zero
  have hP₂_bigO : P₂ =O[𝓝 0] (1 : ℝ → ℝ) :=
    Asymptotics.isBigO_const_of_tendsto hP₂_tendsto one_ne_zero
  have hF₁_bigO : F₁ =O[𝓝 0] (1 : ℝ → ℝ) := by
    have hPow_bigO : (fun a : ℝ => a ^ 2) =O[𝓝 0] (1 : ℝ → ℝ) :=
      Asymptotics.isBigO_const_of_tendsto hPow0 one_ne_zero
    have hSub : (fun a : ℝ => F₁ a - P₁ a) =O[𝓝 0] (1 : ℝ → ℝ) :=
      h₁.isBigO.trans hPow_bigO
    simpa [sub_add_cancel] using hSub.add hP₁_bigO
  have hCube : (fun a : ℝ => a ^ 3) =o[𝓝 0] fun a : ℝ => a ^ 2 :=
    Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 3)
  have hQuart : (fun a : ℝ => a ^ 4) =o[𝓝 0] fun a : ℝ => a ^ 2 :=
    Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 4)
  have hPoly_rem :
      (fun a : ℝ => P₁ a * P₂ a -
        (1 + a • (X₁ + X₂) + (a ^ 2) • (Y₁ + Y₂ + X₁ * X₂))) =o[𝓝 0]
        fun a => a ^ 2 := by
    have hC1 : (fun _ : ℝ => X₁ * Y₂) =O[𝓝 0] (1 : ℝ → ℝ) :=
      Asymptotics.isBigO_const_of_tendsto (tendsto_const_nhds (x := X₁ * Y₂)) one_ne_zero
    have hC2 : (fun _ : ℝ => Y₁ * X₂) =O[𝓝 0] (1 : ℝ → ℝ) :=
      Asymptotics.isBigO_const_of_tendsto (tendsto_const_nhds (x := Y₁ * X₂)) one_ne_zero
    have hC3 : (fun _ : ℝ => Y₁ * Y₂) =O[𝓝 0] (1 : ℝ → ℝ) :=
      Asymptotics.isBigO_const_of_tendsto (tendsto_const_nhds (x := Y₁ * Y₂)) one_ne_zero
    have h3a : (fun a : ℝ => (a ^ 3) • (X₁ * Y₂)) =o[𝓝 0] fun a => a ^ 2 :=
      (hCube.smul_isBigO hC1).congr_right fun _ => by simp
    have h3b : (fun a : ℝ => (a ^ 3) • (Y₁ * X₂)) =o[𝓝 0] fun a => a ^ 2 :=
      (hCube.smul_isBigO hC2).congr_right fun _ => by simp
    have h4 : (fun a : ℝ => (a ^ 4) • (Y₁ * Y₂)) =o[𝓝 0] fun a => a ^ 2 :=
      (hQuart.smul_isBigO hC3).congr_right fun _ => by simp
    have hSum := (h3a.add h3b).add h4
    refine hSum.congr' (Filter.Eventually.of_forall fun a => ?_)
      (Filter.Eventually.of_forall fun _ => rfl)
    simp only [P₁, P₂, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      smul_smul, smul_add]
    rw [← sq a, real_mul_sq, real_sq_mul, real_sq_sq]
    abel
  have hTerm1 : (fun a : ℝ => F₁ a * (F₂ a - P₂ a)) =o[𝓝 0] fun a => a ^ 2 :=
    (hF₁_bigO.mul_isLittleO h₂).congr_right fun _ => by simp
  have hTerm2 : (fun a : ℝ => (F₁ a - P₁ a) * P₂ a) =o[𝓝 0] fun a => a ^ 2 :=
    (h₁.mul_isBigO hP₂_bigO).congr_right fun _ => by simp
  have hComb := (hTerm1.add hTerm2).add hPoly_rem
  refine hComb.congr' (Filter.Eventually.of_forall fun a => ?_)
    (Filter.Eventually.of_forall fun _ => rfl)
  noncomm_ring

/-- Wilson plaquette `U_μ(y, a) U_ν(y + a e_μ, a) U_μ(y + a e_ν, a)⁻¹ U_ν(y, a)⁻¹`
for a `Mat4C`-valued gauge potential `A`. -/
noncomputable def wilsonPlaquette
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4) (a : ℝ) : Mat4C :=
  NormedSpace.exp (a • A y μ) *
    NormedSpace.exp (a • A (y + a • frameBasis μ) ν) *
    (NormedSpace.exp (a • A (y + a • frameBasis ν) μ))⁻¹ *
    (NormedSpace.exp (a • A y ν))⁻¹

/-- Continuum Yang–Mills curvature `∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν]` on `FourSpace`. -/
noncomputable def continuumCurvature
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4) : Mat4C :=
  fderiv ℝ (fun z => A z ν) y (frameBasis μ) -
    fderiv ℝ (fun z => A z μ) y (frameBasis ν) +
    (A y μ * A y ν - A y ν * A y μ)

theorem wilsonPlaquette_diag_trivial
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ : Fin 4) (a : ℝ) :
    wilsonPlaquette A y μ μ a = 1 ∧ continuumCurvature A y μ μ = 0 := by
  refine ⟨?_, ?_⟩
  · simp only [wilsonPlaquette]
    have hInv : ∀ X : Mat4C, NormedSpace.exp X * (NormedSpace.exp X)⁻¹ = 1 := fun X =>
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp X))
    rw [mul_assoc (NormedSpace.exp (a • A y μ)), hInv, mul_one, hInv]
  · simp [continuumCurvature]

/-- Continuum curvature vanishes identically for `A = 0`. -/
theorem continuumCurvature_zero (y : FourSpace) (μ ν : Fin 4) :
    continuumCurvature 0 y μ ν = 0 := by
  dsimp only [continuumCurvature]
  simp

theorem continuumCurvature_abelian_const_zero
    (c : Fin 4 → ℂ) (y : FourSpace) (μ ν : Fin 4) :
    let A : FourSpace → Fin 4 → Mat4C := fun _ ρ => c ρ • (1 : Mat4C)
    continuumCurvature A y μ ν = 0 := by
  simp [continuumCurvature]
  rw [smul_comm, sub_self]

theorem continuumCurvature_antisymm
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4) :
    continuumCurvature A y ν μ = -continuumCurvature A y μ ν := by
  simp only [continuumCurvature]
  abel

set_option backward.isDefEq.respectTransparency false in
theorem tendsto_wilsonPlaquette_curvature
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4)
    (hA : ContDiff ℝ 2 A) :
    Filter.Tendsto
      (fun a : ℝ => (a ^ 2)⁻¹ • (wilsonPlaquette A y μ ν a - 1))
      (𝓝[≠] 0) (𝓝 (continuumCurvature A y μ ν)) := by
  have hDiff : ∀ ρ : Fin 4, DifferentiableAt ℝ (fun z => A z ρ) y := fun ρ =>
    (contDiff_pi.mp hA ρ).differentiable (by norm_num) y
  let F₁ : ℝ → Mat4C := fun a => NormedSpace.exp (a • A y μ)
  let F₂ : ℝ → Mat4C := fun a => NormedSpace.exp (a • A (y + a • frameBasis μ) ν)
  let F₃ : ℝ → Mat4C := fun a => NormedSpace.exp (a • (-(A (y + a • frameBasis ν) μ)))
  let F₄ : ℝ → Mat4C := fun a => NormedSpace.exp (a • (-(A y ν)))
  have hW_eq : ∀ a : ℝ, wilsonPlaquette A y μ ν a = F₁ a * F₂ a * F₃ a * F₄ a := by
    intro a
    simp only [wilsonPlaquette, F₁, F₂, F₃, F₄]
    rw [← Matrix.exp_neg (a • A (y + a • frameBasis ν) μ),
      ← Matrix.exp_neg (a • A y ν), ← smul_neg, ← smul_neg]
  have hB₁ : HasDerivAt (fun _ : ℝ => A y μ) 0 0 := hasDerivAt_const 0 (A y μ)
  have hB₂ : HasDerivAt (fun a : ℝ => A (y + a • frameBasis μ) ν)
      (fderiv ℝ (fun z => A z ν) y (frameBasis μ)) 0 :=
    (hDiff ν).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line_zero y μ) (by simp)
  have hB₃ : HasDerivAt (fun a : ℝ => -(A (y + a • frameBasis ν) μ))
      (-(fderiv ℝ (fun z => A z μ) y (frameBasis ν))) 0 :=
    ((hDiff μ).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line_zero y ν) (by simp)).neg
  have hB₄ : HasDerivAt (fun _ : ℝ => -(A y ν)) 0 0 := hasDerivAt_const 0 (-(A y ν))
  have hT₁ := exp_smul_taylor2 _ _ hB₁
  have hT₂ := exp_smul_taylor2 _ _ hB₂
  have hT₃ := exp_smul_taylor2 _ _ hB₃
  have hT₄ := exp_smul_taylor2 _ _ hB₄
  simp only [zero_add, zero_smul, add_zero] at hT₁ hT₂ hT₃ hT₄
  have hT₁₂ := mul_taylor2 F₁ F₂ _ _ _ _ hT₁ hT₂
  have hT₁₂₃ := mul_taylor2 (fun a => F₁ a * F₂ a) F₃ _ _ _ _ hT₁₂ hT₃
  have hT₁₂₃₄ := mul_taylor2 (fun a => F₁ a * F₂ a * F₃ a) F₄ _ _ _ _ hT₁₂₃ hT₄
  have hLin0 : A y μ + A y ν + -(A y μ) + -(A y ν) = 0 := by abel
  have hHalf : ∀ M : Mat4C, (2 : ℝ)⁻¹ • M + (2 : ℝ)⁻¹ • M = M := fun M => by
    rw [← add_smul]
    norm_num
  have hQuadEq :
      ((2 : ℝ)⁻¹ • (A y μ * A y μ) +
        (fderiv ℝ (fun z => A z ν) y (frameBasis μ) + (2 : ℝ)⁻¹ • (A y ν * A y ν)) +
        A y μ * A y ν +
        (-(fderiv ℝ (fun z => A z μ) y (frameBasis ν)) +
          (2 : ℝ)⁻¹ • (-(A y μ) * -(A y μ))) +
        (A y μ + A y ν) * -(A y μ) +
        (2 : ℝ)⁻¹ • (-(A y ν) * -(A y ν)) +
        (A y μ + A y ν + -(A y μ)) * -(A y ν)) =
        continuumCurvature A y μ ν := by
    have hμν : A y μ + A y ν + -(A y μ) = A y ν := by abel
    rw [hμν]
    simp only [continuumCurvature, neg_mul, mul_neg, neg_neg, add_mul]
    have h1 : ∀ P Q R S T U : Mat4C,
        (2 : ℝ)⁻¹ • P + (R + (2 : ℝ)⁻¹ • Q) + S + (-T + (2 : ℝ)⁻¹ • P) + -(P + U) +
          (2 : ℝ)⁻¹ • Q + -Q =
        ((2 : ℝ)⁻¹ • P + (2 : ℝ)⁻¹ • P) + -P + ((2 : ℝ)⁻¹ • Q + (2 : ℝ)⁻¹ • Q) + -Q +
          (R - T + (S - U)) := fun _ _ _ _ _ _ => by abel
    rw [h1, hHalf, hHalf, add_neg_cancel, zero_add, add_neg_cancel, zero_add]
  have hMain_littleO :
      (fun a : ℝ => wilsonPlaquette A y μ ν a - 1 - (a ^ 2) • continuumCurvature A y μ ν) =o[𝓝 0]
        fun a => a ^ 2 := by
    refine hT₁₂₃₄.congr_left fun a => ?_
    rw [hW_eq a, hLin0, smul_zero, add_zero, hQuadEq, sub_sub]
  have hWithin :
      (fun a : ℝ => wilsonPlaquette A y μ ν a - 1 - (a ^ 2) • continuumCurvature A y μ ν) =o[𝓝[≠] 0]
        fun a => a ^ 2 :=
    hMain_littleO.mono nhdsWithin_le_nhds
  have hQuot_zero :
      Filter.Tendsto
        (fun a : ℝ => (a ^ 2)⁻¹ • (wilsonPlaquette A y μ ν a - 1) - continuumCurvature A y μ ν)
        (𝓝[≠] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hNorm := hWithin.norm_norm.tendsto_div_nhds_zero
    refine hNorm.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a (ha : a ≠ 0)
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    rw [div_eq_inv_mul, ← norm_inv, ← norm_smul, smul_sub, inv_smul_smul₀ ha2]
  exact tendsto_sub_nhds_zero_iff.mp hQuot_zero

/-! ## 4. Hilbert–Schmidt Wilson Plaquette Action & Convergence -/

private noncomputable def hilbertSchmidtAction4 (M : Mat4C) : ℝ :=
  ((Mᴴ * M).trace).re

private lemma hilbertSchmidtAction4_nonneg (M : Mat4C) : 0 ≤ hilbertSchmidtAction4 M := by
  simp only [hilbertSchmidtAction4, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

private lemma hilbertSchmidtAction4_smul (r : ℝ) (M : Mat4C) :
    hilbertSchmidtAction4 (r • M) = r ^ 2 * hilbertSchmidtAction4 M := by
  have hConj : (r • M)ᴴ = r • Mᴴ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hMul : (r • M)ᴴ * (r • M) = (r * r) • (Mᴴ * M) := by
    rw [hConj, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [hilbertSchmidtAction4, hMul, Matrix.trace_smul, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, sq]

set_option backward.isDefEq.respectTransparency false in
private lemma continuous_hilbertSchmidtAction4 : Continuous hilbertSchmidtAction4 := by
  have hEntry : ∀ i j : Fin 4, Continuous (fun M : Mat4C => M i j) := by
    intro i j
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun M N => ?_).continuous
    have hDist : dist (M i j) (N i j) ≤ dist M N := by
      rw [dist_eq_norm, dist_eq_norm, ← Matrix.sub_apply]
      have h1 : ‖(M - N) i j‖₊ ≤ ∑ k : Fin 4, ‖(M - N) i k‖₊ :=
        Finset.single_le_sum (f := fun k : Fin 4 => ‖(M - N) i k‖₊)
          (fun _ _ => zero_le) (Finset.mem_univ j)
      have h2 : (∑ k : Fin 4, ‖(M - N) i k‖₊) ≤ ‖M - N‖₊ := by
        rw [Matrix.linfty_opNNNorm_def]
        exact Finset.le_sup (f := fun r : Fin 4 => ∑ k : Fin 4, ‖(M - N) r k‖₊)
          (Finset.mem_univ i)
      exact_mod_cast h1.trans h2
    simpa using hDist
  have hEq : hilbertSchmidtAction4 = fun M : Mat4C =>
      ∑ i : Fin 4, ∑ j : Fin 4, (star (M j i) * M j i).re := by
    funext M
    simp [hilbertSchmidtAction4, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.re_sum]
  rw [hEq]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact Complex.continuous_re.comp ((continuous_star.comp (hEntry j i)).mul (hEntry j i))

/-- Hilbert–Schmidt Wilson plaquette action `(a ^ 4)⁻¹ * Re Tr((W - 1)ᴴ (W - 1))`. -/
noncomputable def wilsonPlaquetteAction
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4) (a : ℝ) : ℝ :=
  (a ^ 4)⁻¹ * (((wilsonPlaquette A y μ ν a - 1)ᴴ * (wilsonPlaquette A y μ ν a - 1)).trace).re

/-- Continuum Hilbert–Schmidt Yang–Mills plaquette action `Re Tr(Fᴴ F)`. -/
noncomputable def continuumPlaquetteAction
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4) : ℝ :=
  (((continuumCurvature A y μ ν)ᴴ * continuumCurvature A y μ ν).trace).re

theorem continuumPlaquetteAction_nonneg
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4) :
    0 ≤ continuumPlaquetteAction A y μ ν :=
  hilbertSchmidtAction4_nonneg (continuumCurvature A y μ ν)

theorem wilsonPlaquette_at_zero
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4) :
    wilsonPlaquette A y μ ν 0 = 1 ∧ wilsonPlaquetteAction A y μ ν 0 = 0 := by
  simp [wilsonPlaquette, wilsonPlaquetteAction]

set_option backward.isDefEq.respectTransparency false in
theorem tendsto_wilsonPlaquetteAction
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4)
    (hA : ContDiff ℝ 2 A) :
    Filter.Tendsto (fun a : ℝ => wilsonPlaquetteAction A y μ ν a)
      (𝓝[≠] 0) (𝓝 (continuumPlaquetteAction A y μ ν)) := by
  have hCurv := tendsto_wilsonPlaquette_curvature A y μ ν hA
  have hComp :
      Filter.Tendsto
        (fun a : ℝ => hilbertSchmidtAction4 ((a ^ 2)⁻¹ • (wilsonPlaquette A y μ ν a - 1)))
        (𝓝[≠] 0) (𝓝 (continuumPlaquetteAction A y μ ν)) :=
    (continuous_hilbertSchmidtAction4.tendsto _).comp hCurv
  refine hComp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a _
  rw [hilbertSchmidtAction4_smul, sq, real_inv_sq_sq]
  rfl

/-! ## 5. Non-Abelian Circular Lattice Continuum Witness -/

/-- Explicit circular coordinate carrying nonzero cross-sheet vorticity `![0, 0, 1]`. -/
def witnessCoord : Coordinate :=
  coordinateEquiv (rootPlus 0 + rootMinus 1)

/-- Constant circular coordinate gauge field pairing `rootPlus 0` along direction `0`
and `rootMinus 1` along direction `1`. -/
def witnessCircularField : FourSpace → Fin 4 → Coordinate :=
  fun _ μ => match μ with
    | 0 => coordinateEquiv (rootPlus 0)
    | 1 => coordinateEquiv (rootMinus 1)
    | _ => 0

private lemma witnessCoord_eq : witnessCoord = Pi.single 1 1 + Pi.single 6 1 := by
  have hc1 : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 1
  have hc6 : coordinateEquiv (rootMinus 1) = Pi.single 6 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 6
  change coordinateEquiv (rootPlus 0 + rootMinus 1) = Pi.single 1 1 + Pi.single 6 1
  rw [LinearEquiv.map_add, hc1, hc6]

private lemma witnessCoord_vorticity :
    chiralVorticityVec witnessCoord = ![0, 0, 1] := by
  ext i
  rw [witnessCoord_eq]
  fin_cases i <;> simp [chiralVorticityVec]

private lemma witnessCoord_wittNorm : wittNorm witnessCoord = 0 := by
  rw [witnessCoord_eq]
  simp [wittNorm]

private lemma witnessCoord_boost : chiralBoostVec witnessCoord = 0 := by
  ext i
  rw [witnessCoord_eq]
  fin_cases i <;> simp [chiralBoostVec]

private lemma witnessCircularField_curv (y : FourSpace) :
    let A : FourSpace → Fin 4 → Mat4C :=
      fun z μ => circularConnectionMat4 (witnessCircularField z μ)
    continuumCurvature A y 0 1 =
      chiralDiagBlock4 (weylUpperMat witnessCoord * weylLowerMat witnessCoord)
        (-(weylLowerMat witnessCoord * weylUpperMat witnessCoord)) := by
  intro A
  have hc1 : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 1
  have hc6 : coordinateEquiv (rootMinus 1) = Pi.single 6 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 6
  have hU_eq : weylUpperMat (coordinateEquiv (rootPlus 0)) = weylUpperMat witnessCoord := by
    rw [witnessCoord_eq, hc1]
    ext i j
    simp [weylUpperMat]
  have hL_eq : weylLowerMat (coordinateEquiv (rootMinus 1)) = weylLowerMat witnessCoord := by
    rw [witnessCoord_eq, hc6]
    ext i j
    simp [weylLowerMat]
  have hL0 : weylLowerMat (coordinateEquiv (rootPlus 0)) = 0 := by
    rw [hc1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylLowerMat, pauliSolder2x2, solder]
  have hU1 : weylUpperMat (coordinateEquiv (rootMinus 1)) = 0 := by
    rw [hc6]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylUpperMat, pauliSolder2x2, solder]
  have hA0 : A y 0 = chiralOffBlock4 (weylUpperMat witnessCoord) 0 := by
    simp only [A, witnessCircularField, circularConnectionMat4, hU_eq, hL0]
  have hA1 : A y 1 = chiralOffBlock4 0 (weylLowerMat witnessCoord) := by
    simp only [A, witnessCircularField, circularConnectionMat4, hU1, hL_eq]
  have hDeriv0 : fderiv ℝ (fun z => A z 1) y = 0 := fderiv_const_apply (A y 1)
  have hDeriv1 : fderiv ℝ (fun z => A z 0) y = 0 := fderiv_const_apply (A y 0)
  simp only [continuumCurvature, hDeriv0, hDeriv1, zero_apply, sub_zero,
    zero_add, hA0, hA1, chiralOffBlock4_mul, mul_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]

theorem circularLattice_nonabelian_continuum_witness (y : FourSpace) :
    let A : FourSpace → Fin 4 → Mat4C :=
      fun z μ => circularConnectionMat4 (witnessCircularField z μ)
    let F_cont := continuumCurvature A y 0 1
    let F_alg := circularCurvatureMat4 witnessCoord
    weylUpperMat witnessCoord * weylLowerMat witnessCoord ≠
      weylLowerMat witnessCoord * weylUpperMat witnessCoord ∧
    chiralVorticityVec witnessCoord ≠ 0 ∧
    F_cont ≠ 0 ∧
    continuumPlaquetteAction A y 0 1 = 4 ∧
    0 < continuumPlaquetteAction A y 0 1 ∧
    (F_algᴴ * F_alg).trace =
      ((4 * (wittNorm witnessCoord ^ 2 + normSq3 (chiralBoostVec witnessCoord) +
        normSq3 (chiralVorticityVec witnessCoord)) : ℝ) : ℂ) ∧
    (F_algᴴ * F_alg).trace - (F_alg * F_alg).trace =
      ((8 * normSq3 (chiralVorticityVec witnessCoord) : ℝ) : ℂ) ∧
    Filter.Tendsto (fun a : ℝ => (a ^ 2)⁻¹ • (wilsonPlaquette A y 0 1 a - 1))
      (𝓝[≠] 0) (𝓝 F_cont) ∧
    Filter.Tendsto (fun a : ℝ => wilsonPlaquetteAction A y 0 1 a)
      (𝓝[≠] 0) (𝓝 (continuumPlaquetteAction A y 0 1)) := by
  intro A F_cont F_alg
  have hNoncomm :
      weylUpperMat witnessCoord * weylLowerMat witnessCoord ≠
        weylLowerMat witnessCoord * weylUpperMat witnessCoord :=
    weylChannel_noncomm_sheet_blocks_witness
  have hVortNe : chiralVorticityVec witnessCoord ≠ 0 := by
    intro h
    have h2 := congrFun h 2
    rw [witnessCoord_vorticity] at h2
    simp at h2
  have hNormSq : normSq3 (chiralVorticityVec witnessCoord) = 1 := by
    rw [witnessCoord_vorticity]
    norm_num [normSq3]
  have hHS_alg := circularCurvatureMat4_hilbertSchmidt_action witnessCoord
  have hGap_alg := circularCurvatureMat4_vorticity_action_gap witnessCoord
  have hHS_eq : (F_contᴴ * F_cont).trace = (F_algᴴ * F_alg).trace := by
    have hFc : F_cont =
        chiralDiagBlock4 (weylUpperMat witnessCoord * weylLowerMat witnessCoord)
          (-(weylLowerMat witnessCoord * weylUpperMat witnessCoord)) :=
      witnessCircularField_curv y
    have hFa : F_alg =
        chiralDiagBlock4 (weylUpperMat witnessCoord * weylLowerMat witnessCoord)
          (weylLowerMat witnessCoord * weylUpperMat witnessCoord) :=
      circularCurvatureMat4_eq_diagBlocks witnessCoord
    rw [hFc, hFa, chiralDiagBlock4_conjTranspose, chiralDiagBlock4_conjTranspose,
      chiralDiagBlock4_mul, chiralDiagBlock4_mul, chiralDiagBlock4_trace,
      chiralDiagBlock4_trace]
    simp only [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_neg]
  have hTrace4 : (F_algᴴ * F_alg).trace = (4 : ℂ) := by
    rw [hHS_alg, witnessCoord_wittNorm, witnessCoord_boost, hNormSq]
    simp [normSq3]
  have hAct4 : continuumPlaquetteAction A y 0 1 = 4 := by
    change ((F_contᴴ * F_cont).trace).re = 4
    rw [hHS_eq, hTrace4]
    norm_num
  have hFne : F_cont ≠ 0 := by
    intro hZero
    have h0 : continuumPlaquetteAction A y 0 1 = 0 := by
      simp [continuumPlaquetteAction, F_cont] at hZero ⊢
      rw [hZero]
      simp
    rw [hAct4] at h0
    norm_num at h0
  have hActPos : 0 < continuumPlaquetteAction A y 0 1 := by
    rw [hAct4]
    norm_num
  have hA_cd : ContDiff ℝ 2 A := by
    have hA_eq : A = fun _ μ => circularConnectionMat4 (witnessCircularField 0 μ) := rfl
    rw [hA_eq]
    exact contDiff_const
  exact ⟨hNoncomm, hVortNe, hFne, hAct4, hActPos, hHS_alg, hGap_alg,
    tendsto_wilsonPlaquette_curvature A y 0 1 hA_cd,
    tendsto_wilsonPlaquetteAction A y 0 1 hA_cd⟩

theorem circularLattice_nonabelian_continuum_smooth_witness :
    ∃ (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4),
      ContDiff ℝ 2 A ∧
      continuumCurvature A y μ ν ≠ 0 ∧
      0 < continuumPlaquetteAction A y μ ν := by
  have hW := circularLattice_nonabelian_continuum_witness (0 : FourSpace)
  let A₀ : FourSpace → Fin 4 → Mat4C :=
    fun _ μ => circularConnectionMat4 (witnessCircularField 0 μ)
  have hCd : ContDiff ℝ 2 A₀ := contDiff_const
  exact ⟨fun z μ => circularConnectionMat4 (witnessCircularField z μ),
    0, 0, 1, hCd, hW.2.2.1, hW.2.2.2.2.1⟩

/-! ## 6. Continuous Star-Ring Inductive Colimit Transport -/

set_option backward.isDefEq.respectTransparency false in
theorem circularColimit_continuum_transport
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf] [TopologicalSpace B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (k : ℕ)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C (A_tower k))
    (hCont : Continuous ((cone.toColimit k).toRingHom.comp ι.toRingHom))
    (x : FourSpace → Fin 4 → Coordinate)
    (A : FourSpace → Fin 4 → Mat4C)
    (Φ : FourSpace → Mat4C)
    (y : FourSpace) (μ ν : Fin 4)
    (hA : ContDiff ℝ 2 A)
    (hΦ : DifferentiableAt ℝ Φ y) :
    let ψ : Mat4C →+* B_inf := (cone.toColimit k).toRingHom.comp ι.toRingHom
    let P_inf := ψ chiralProjMat4
    let A_xy := ψ (circularConnectionMat4 (x y μ))
    let F_xy := ψ (circularCurvatureMat4 (x y μ))
    Filter.Tendsto (fun a : ℝ => ψ (latticeCovariantDiff A Φ y μ a))
      (𝓝[≠] 0) (𝓝 (ψ (continuumCovariantDeriv A Φ y μ))) ∧
    Filter.Tendsto (fun a : ℝ => ψ ((a ^ 2)⁻¹ • (wilsonPlaquette A y μ ν a - 1)))
      (𝓝[≠] 0) (𝓝 (ψ (continuumCurvature A y μ ν))) ∧
    Filter.Tendsto (fun a : ℝ => ψ (circularLinkTransport x y μ a))
      (𝓝 0) (𝓝 (1 : B_inf)) ∧
    Filter.Tendsto (fun a : ℝ => ψ (a⁻¹ • (circularLinkTransport x y μ a - 1)))
      (𝓝[≠] 0) (𝓝 A_xy) ∧
    (∀ a : ℝ, (cone.toColimit (k + 1)).toRingHom
        ((cone.stepHom k).toRingHom (ι.toRingHom (wilsonPlaquette A y μ ν a))) =
      ψ (wilsonPlaquette A y μ ν a)) ∧
    P_inf * P_inf = P_inf ∧
    star P_inf = P_inf ∧
    CanonicalTwoSheetedInductiveColimit.opElectron P_inf A_xy A_xy = A_xy ∧
    CanonicalTwoSheetedInductiveColimit.opQuadraticCoupling P_inf A_xy A_xy = F_xy ∧
    (cone.toColimit (k + 1)).toRingHom
        ((cone.stepHom k).toRingHom (ι.toRingHom (circularCurvatureMat4 (x y μ)))) =
      F_xy ∧
    CanonicalTwoSheetedInductiveColimit.opSpinDipole P_inf A_xy A_xy =
      CanonicalTwoSheetedInductiveColimit.opBitGrading P_inf * F_xy := by
  intro ψ P_inf A_xy F_xy
  have hContAt : ∀ M : Mat4C, ContinuousAt ψ M := fun _ => hCont.continuousAt
  have hCovLim : Filter.Tendsto (fun a : ℝ => ψ (latticeCovariantDiff A Φ y μ a))
      (𝓝[≠] 0) (𝓝 (ψ (continuumCovariantDeriv A Φ y μ))) :=
    (hContAt _).tendsto.comp (tendsto_latticeCovariantDiff A Φ y μ hΦ)
  have hCurvLim :
      Filter.Tendsto (fun a : ℝ => ψ ((a ^ 2)⁻¹ • (wilsonPlaquette A y μ ν a - 1)))
        (𝓝[≠] 0) (𝓝 (ψ (continuumCurvature A y μ ν))) :=
    (hContAt _).tendsto.comp (tendsto_wilsonPlaquette_curvature A y μ ν hA)
  have hLinkCont : Filter.Tendsto (fun a : ℝ => circularLinkTransport x y μ a) (𝓝 0) (𝓝 1) := by
    have h0 : circularLinkTransport x y μ 0 = 1 := by simp [circularLinkTransport]
    rw [← h0]
    exact (circularLinkTransport_continuous x y μ).continuousAt.tendsto
  have hLinkLim : Filter.Tendsto (fun a : ℝ => ψ (circularLinkTransport x y μ a))
      (𝓝 0) (𝓝 (1 : B_inf)) := by
    simpa only [Function.comp_def, map_one] using (hContAt 1).tendsto.comp hLinkCont
  have hLinkSlope : Filter.Tendsto (fun a : ℝ => ψ (a⁻¹ • (circularLinkTransport x y μ a - 1)))
      (𝓝[≠] 0) (𝓝 A_xy) := by
    have hDeriv := (hasDerivAt_exp_smul_zero (circularConnectionMat4 (x y μ))).tendsto_slope_zero
    have hSlope : Filter.Tendsto (fun a : ℝ => a⁻¹ • (circularLinkTransport x y μ a - 1))
        (𝓝[≠] 0) (𝓝 (circularConnectionMat4 (x y μ))) := by
      simpa [circularLinkTransport, zero_smul, NormedSpace.exp_zero] using hDeriv
    exact (hContAt _).tendsto.comp hSlope
  have hPlaCompat : ∀ a : ℝ, (cone.toColimit (k + 1)).toRingHom
      ((cone.stepHom k).toRingHom (ι.toRingHom (wilsonPlaquette A y μ ν a))) =
      ψ (wilsonPlaquette A y μ ν a) :=
    fun a => cone.compat k (ι.toRingHom (wilsonPlaquette A y μ ν a))
  have hAlg := circularConnection_starColimit_transport cone k ι (x y μ)
  exact ⟨hCovLim, hCurvLim, hLinkLim, hLinkSlope, hPlaCompat,
    hAlg.1, hAlg.2.1, hAlg.2.2.1, hAlg.2.2.2.1, hAlg.2.2.2.2.1, hAlg.2.2.2.2.2⟩

/-- Diagonal unital star-ring embedding of `Mat4C` into `TowerLevel Mat4C k`. -/
def diagTowerStarHom (k : ℕ) :
    CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C
      (CanonicalTwoSheetedInductiveColimit.TowerLevel Mat4C k) where
  toFun M := (fun _ => M, M)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem circularColimit_continuum_transport_tailTower (k : ℕ) (y : FourSpace) :
    let cone := CanonicalTwoSheetedInductiveColimit.tailTowerCone Mat4C
    let ι := diagTowerStarHom k
    let ψ : Mat4C →+* CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C :=
      (cone.toColimit k).toRingHom.comp ι.toRingHom
    let A : FourSpace → Fin 4 → Mat4C :=
      fun z μ => circularConnectionMat4 (witnessCircularField z μ)
    ψ (continuumCurvature A y 0 1) ≠ 0 ∧
    Filter.Tendsto (fun a : ℝ => ψ ((a ^ 2)⁻¹ • (wilsonPlaquette A y 0 1 a - 1)))
      (𝓝[≠] 0) (𝓝 (ψ (continuumCurvature A y 0 1))) ∧
    Filter.Tendsto (fun a : ℝ => ψ (latticeCovariantDiff A (fun _ => 1) y 0 a))
      (𝓝[≠] 0) (𝓝 (ψ (continuumCovariantDeriv A (fun _ => 1) y 0))) := by
  intro cone ι ψ A
  have hψ_eq : (ψ : Mat4C → CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C) =
      fun M _ => M := by
    funext M n
    change CanonicalTwoSheetedInductiveColimit.towerColimitFn k (fun _ => M, M) n = M
    by_cases hn : n < k <;> simp [CanonicalTwoSheetedInductiveColimit.towerColimitFn, hn]
  have hCont : Continuous (cone.toColimit k |>.toRingHom.comp ι.toRingHom) := by
    change Continuous (ψ : Mat4C → CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C)
    rw [hψ_eq]
    exact continuous_pi fun _ => continuous_id
  have hA_cd : ContDiff ℝ 2 A := by
    have hA_eq : A = fun _ μ => circularConnectionMat4 (witnessCircularField 0 μ) := rfl
    rw [hA_eq]
    exact contDiff_const
  have hTrans := circularColimit_continuum_transport cone k ι hCont witnessCircularField A
    (fun _ => 1) y 0 1 hA_cd (differentiableAt_const 1)
  have hW := circularLattice_nonabelian_continuum_witness y
  have hNe : ψ (continuumCurvature A y 0 1) ≠ 0 := by
    intro h0
    have h0' : continuumCurvature A y 0 1 = 0 := by
      have hEval := congrFun h0 0
      change (ψ : Mat4C → CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C)
        (continuumCurvature A y 0 1) 0 = 0 at hEval
      rw [hψ_eq] at hEval
      exact hEval
    exact hW.2.2.1 h0'
  exact ⟨hNe, hTrans.2.1, hTrans.1⟩

end InfoGeometry.Lie
