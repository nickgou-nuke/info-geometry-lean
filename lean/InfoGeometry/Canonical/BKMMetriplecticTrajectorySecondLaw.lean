/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.GenericMetriplecticFlow
import InfoGeometry.Canonical.BKMOnsagerMobilityBridge
import InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
import InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge
import InfoGeometry.Canonical.SouriauOnsagerBKMSelfAdjoint
import InfoGeometry.Canonical.SouriauOnsagerBKMStrictPositivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Trajectory-level Fréchet chain-rule metriplectic Second Law

This module upgrades the pointwise/algebraic metriplectic rate bounds of
`GenericMetriplecticFlow`, `SouriauOnsagerBKM`, and `BKMOnsagerMobilityBridge`
to genuine trajectory-level analytical Second Laws (`HasDerivAt`, `deriv ≤ 0`,
strict `< 0` off equilibrium, and `AntitoneOn` over convex intervals):

1. **Layer 1 (Banach-space chain rule & `GenericMetriplecticFlow.System`):**
   Over any real normed space `E`, composing `HasFDerivAt Φ (dΦ (x t)) (x t)`
   with `HasDerivAt x (v_rev t + v_diss t) t` where the reversible vector field
   lies in `ker (dΦ (x t))` and the dissipative term satisfies
   `dΦ (x t) (v_diss t) ≤ 0` yields `deriv (Φ ∘ x) t ≤ 0` and `AntitoneOn`.
2. **Layer 2 (Finite noncommutative Gibbs–BKM trajectory):**
   On `FiniteOperatorAlgebra n` (`[Nonempty (Fin n)]`), we prove `HasFDerivAt`
   for `gibbsRelativePotential σ H`, construct the self-adjointness-preserving
   state-dependent `gibbsMetriplecticFlow`, prove **unconditional** vanishing of
   the unitary commutator trace without `[H_eq, H] = 0`, derive exact BKM
   entropy-production rate `-D_t.bkmRealBilinForm ... ≤ 0` (strictly `< 0` when
   `ρ_t ≠ σ`), prove `kuboMoriTransform_commutator_eq_commutator_rho`, and
   differentiate `normalizedExponential` to map `H(t)` trajectories to `ρ(t)`
   metriplectic trajectories.
3. **Layer 3 (Primal matrix trajectory upgrade):**
   We construct continuous `ℝ`-linear equivalences `matrixOfOpCLMℝ` /
   `matrixOpCLMℝ` for arbitrary `[NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ)]`
   `[NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ)]`, lift all three variants of
   `BKMOnsagerMobilityBridge` / `MetriplecticDissipation` to `HasDerivAt` and
   `AntitoneOn`, and instantiate them on `rho t := matrixOfOp (normalizedExponential (H t))`
   with evolving density `D t := faithfulGibbsDensity (H t) ...` and the
   concrete `traceNormalizedSquarePotential`.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw

open MeasureTheory
open scoped Interval

/-! ## Layer 1: General Banach-Space Fréchet Chain-Rule Metriplectic Second Law -/

section Layer1BanachMetriplectic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact Fréchet chain-rule rate along a metriplectic splitting
`v_rev t + v_diss t` when the reversible component annihilates `dΦ (x t)`. -/
theorem banach_metriplectic_hasDerivAt_eq
    {Φ : E → ℝ} {dΦ : E → (E →L[ℝ] ℝ)} {x v_rev v_diss : ℝ → E} {t : ℝ}
    (hΦ : HasFDerivAt Φ (dΦ (x t)) (x t))
    (hx : HasDerivAt x (v_rev t + v_diss t) t)
    (hrev : dΦ (x t) (v_rev t) = 0) :
    HasDerivAt (fun s => Φ (x s)) (dΦ (x t) (v_diss t)) t := by
  have hcomp :
      HasDerivAt (fun s => Φ (x s)) (dΦ (x t) (v_rev t + v_diss t)) t :=
    hΦ.comp_hasDerivAt t hx
  rw [map_add, hrev, zero_add] at hcomp
  exact hcomp

/-- Combined `HasDerivAt` and nonpositivity statement for a Banach-space
metriplectic trajectory. -/
theorem banach_metriplectic_hasDerivAt_nonpos
    {Φ : E → ℝ} {dΦ : E → (E →L[ℝ] ℝ)} {x v_rev v_diss : ℝ → E} {t : ℝ}
    (hΦ : HasFDerivAt Φ (dΦ (x t)) (x t))
    (hx : HasDerivAt x (v_rev t + v_diss t) t)
    (hrev : dΦ (x t) (v_rev t) = 0)
    (hdiss : dΦ (x t) (v_diss t) ≤ 0) :
    HasDerivAt (fun s => Φ (x s)) (dΦ (x t) (v_diss t)) t ∧
      dΦ (x t) (v_diss t) ≤ 0 :=
  ⟨banach_metriplectic_hasDerivAt_eq hΦ hx hrev, hdiss⟩

/-- Nonpositive `deriv` along a Banach-space metriplectic trajectory. -/
theorem banach_metriplectic_deriv_nonpos
    {Φ : E → ℝ} {dΦ : E → (E →L[ℝ] ℝ)} {x v_rev v_diss : ℝ → E} {t : ℝ}
    (hΦ : HasFDerivAt Φ (dΦ (x t)) (x t))
    (hx : HasDerivAt x (v_rev t + v_diss t) t)
    (hrev : dΦ (x t) (v_rev t) = 0)
    (hdiss : dΦ (x t) (v_diss t) ≤ 0) :
    deriv (fun s => Φ (x s)) t ≤ 0 := by
  rw [(banach_metriplectic_hasDerivAt_eq hΦ hx hrev).deriv]
  exact hdiss

/-- Convex-interval trajectory monotonicity (`AntitoneOn`) for a Banach-space
metriplectic flow via `antitoneOn_of_deriv_nonpos`. -/
theorem banach_metriplectic_antitoneOn
    {Φ : E → ℝ} {dΦ : E → (E →L[ℝ] ℝ)} {x v_rev v_diss : ℝ → E}
    {I : Set ℝ} (hI : Convex ℝ I)
    (hcont : ContinuousOn (fun t => Φ (x t)) I)
    (hΦ : ∀ t ∈ interior I, HasFDerivAt Φ (dΦ (x t)) (x t))
    (hx : ∀ t ∈ interior I, HasDerivAt x (v_rev t + v_diss t) t)
    (hrev : ∀ t ∈ interior I, dΦ (x t) (v_rev t) = 0)
    (hdiss : ∀ t ∈ interior I, dΦ (x t) (v_diss t) ≤ 0) :
    AntitoneOn (fun t => Φ (x t)) I := by
  apply antitoneOn_of_deriv_nonpos hI hcont
  · intro t ht
    exact (banach_metriplectic_hasDerivAt_eq (hΦ t ht) (hx t ht)
      (hrev t ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact banach_metriplectic_deriv_nonpos (hΦ t ht) (hx t ht)
      (hrev t ht) (hdiss t ht)

/-- Global `Antitone` Banach-space metriplectic trajectory Second Law. -/
theorem banach_metriplectic_antitone
    {Φ : E → ℝ} {dΦ : E → (E →L[ℝ] ℝ)} {x v_rev v_diss : ℝ → E}
    (hΦ : ∀ t, HasFDerivAt Φ (dΦ (x t)) (x t))
    (hx : ∀ t, HasDerivAt x (v_rev t + v_diss t) t)
    (hrev : ∀ t, dΦ (x t) (v_rev t) = 0)
    (hdiss : ∀ t, dΦ (x t) (v_diss t) ≤ 0) :
    Antitone (fun t => Φ (x t)) := by
  apply antitone_of_hasDerivAt_nonpos
    (f' := fun t => dΦ (x t) (v_diss t))
  · intro t
    exact banach_metriplectic_hasDerivAt_eq (hΦ t) (hx t) (hrev t)
  · intro t
    exact hdiss t

section GenericMetriplecticNormed

open InfoGeometry.Thermo.GenericMetriplecticFlow

/-- Pointwise `HasDerivAt` and nonpositive free-energy rate along a trajectory
of a normed `GenericMetriplecticFlow.System E` (`Φ = H_fn - T * S_fn`, `0 ≤ T`). -/
theorem genericMetriplectic_freeEnergy_hasDerivAt_nonpos
    {sys : ℝ → System E} {H_fn S_fn : E → ℝ} {T : ℝ} (hT : 0 ≤ T)
    {dH_clm dS_clm : ℝ → (E →L[ℝ] ℝ)} {x : ℝ → E} {t : ℝ}
    (hdH : ∀ v, dH_clm t v = (sys t).dH v)
    (hdS : ∀ v, dS_clm t v = (sys t).dS v)
    (hH : HasFDerivAt H_fn (dH_clm t) (x t))
    (hS : HasFDerivAt S_fn (dS_clm t) (x t))
    (hx : HasDerivAt x (sys t).flow t) :
    HasDerivAt (fun s => H_fn (x s) - T * S_fn (x s))
        (-(T * (sys t).dS ((sys t).M (sys t).dS))) t ∧
      -(T * (sys t).dS ((sys t).M (sys t).dS)) ≤ 0 := by
  have hF :
      HasFDerivAt (fun y => H_fn y - T * S_fn y) (dH_clm t - T • dS_clm t) (x t) :=
    hH.sub (hS.const_smul T)
  have hx' :
      HasDerivAt x
        ((sys t).L (sys t).dH + (sys t).M (sys t).dS) t := by
    simpa [System.flow] using hx
  have hrev :
      (dH_clm t - T • dS_clm t) ((sys t).L (sys t).dH) = 0 := by
    simp only [sub_apply, smul_apply,
      smul_eq_mul, hdH, hdS,
      (sys t).reversible_hamiltonian_rate, (sys t).reversible_entropy_rate,
      mul_zero, sub_self]
  have hdiss_eq :
      (dH_clm t - T • dS_clm t) ((sys t).M (sys t).dS) =
        -(T * (sys t).dS ((sys t).M (sys t).dS)) := by
    simp only [sub_apply, smul_apply,
      smul_eq_mul, hdH, hdS, (sys t).dissipative_hamiltonian_rate, zero_sub]
  have hdiss_nonpos :
      (dH_clm t - T • dS_clm t) ((sys t).M (sys t).dS) ≤ 0 := by
    rw [hdiss_eq]
    exact neg_nonpos.mpr (mul_nonneg hT ((sys t).M_nonneg (sys t).dS))
  have hmain :=
    banach_metriplectic_hasDerivAt_nonpos
      (dΦ := fun _ => dH_clm t - T • dS_clm t)
      (v_rev := fun _ => (sys t).L (sys t).dH)
      (v_diss := fun _ => (sys t).M (sys t).dS)
      hF hx' hrev hdiss_nonpos
  rw [hdiss_eq] at hmain
  exact hmain

/-- Convex-interval free-energy monotonicity along a normed
`GenericMetriplecticFlow.System E` trajectory. -/
theorem genericMetriplectic_freeEnergy_antitoneOn
    {sys : ℝ → System E} {H_fn S_fn : E → ℝ} {T : ℝ} (hT : 0 ≤ T)
    {dH_clm dS_clm : ℝ → (E →L[ℝ] ℝ)} {x : ℝ → E}
    {I : Set ℝ} (hI : Convex ℝ I)
    (hcont : ContinuousOn (fun t => H_fn (x t) - T * S_fn (x t)) I)
    (hdH : ∀ t ∈ interior I, ∀ v, dH_clm t v = (sys t).dH v)
    (hdS : ∀ t ∈ interior I, ∀ v, dS_clm t v = (sys t).dS v)
    (hH : ∀ t ∈ interior I, HasFDerivAt H_fn (dH_clm t) (x t))
    (hS : ∀ t ∈ interior I, HasFDerivAt S_fn (dS_clm t) (x t))
    (hx : ∀ t ∈ interior I, HasDerivAt x (sys t).flow t) :
    AntitoneOn (fun t => H_fn (x t) - T * S_fn (x t)) I := by
  apply antitoneOn_of_deriv_nonpos hI hcont
  · intro t ht
    exact (genericMetriplectic_freeEnergy_hasDerivAt_nonpos hT
      (hdH t ht) (hdS t ht) (hH t ht) (hS t ht) (hx t ht)).1.differentiableAt.differentiableWithinAt
  · intro t ht
    have hpt := genericMetriplectic_freeEnergy_hasDerivAt_nonpos hT
      (hdH t ht) (hdS t ht) (hH t ht) (hS t ht) (hx t ht)
    rw [hpt.1.deriv]
    exact hpt.2

/-- Convex-interval entropy monotonicity (`MonotoneOn`) along a normed
`GenericMetriplecticFlow.System E` trajectory. -/
theorem genericMetriplectic_entropy_monotoneOn
    {sys : ℝ → System E} {S_fn : E → ℝ}
    {dS_clm : ℝ → (E →L[ℝ] ℝ)} {x : ℝ → E}
    {I : Set ℝ} (hI : Convex ℝ I)
    (hcont : ContinuousOn (fun t => S_fn (x t)) I)
    (hdS : ∀ t ∈ interior I, ∀ v, dS_clm t v = (sys t).dS v)
    (hS : ∀ t ∈ interior I, HasFDerivAt S_fn (dS_clm t) (x t))
    (hx : ∀ t ∈ interior I, HasDerivAt x (sys t).flow t) :
    MonotoneOn (fun t => S_fn (x t)) I := by
  apply monotoneOn_of_deriv_nonneg hI hcont
  · intro t ht
    have hcomp : HasDerivAt (fun s => S_fn (x s)) (dS_clm t (sys t).flow) t :=
      (hS t ht).comp_hasDerivAt t (hx t ht)
    exact hcomp.differentiableAt.differentiableWithinAt
  · intro t ht
    have hcomp : HasDerivAt (fun s => S_fn (x s)) (dS_clm t (sys t).flow) t :=
      (hS t ht).comp_hasDerivAt t (hx t ht)
    rw [hcomp.deriv, hdS t ht]
    exact (sys t).entropy_rate_nonneg

/-- Finite-dimensional specialization of `genericMetriplectic_freeEnergy_antitoneOn`,
automatically upgrading algebraic covectors `(sys t).dH`, `(sys t).dS` via
`LinearMap.toContinuousLinearMap`. -/
theorem genericMetriplectic_freeEnergy_antitoneOn_finiteDim
    [FiniteDimensional ℝ E]
    {sys : ℝ → System E} {H_fn S_fn : E → ℝ} {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → E} {I : Set ℝ} (hI : Convex ℝ I)
    (hcont : ContinuousOn (fun t => H_fn (x t) - T * S_fn (x t)) I)
    (hH : ∀ t ∈ interior I,
      HasFDerivAt H_fn ((sys t).dH.toContinuousLinearMap) (x t))
    (hS : ∀ t ∈ interior I,
      HasFDerivAt S_fn ((sys t).dS.toContinuousLinearMap) (x t))
    (hx : ∀ t ∈ interior I, HasDerivAt x (sys t).flow t) :
    AntitoneOn (fun t => H_fn (x t) - T * S_fn (x t)) I :=
  genericMetriplectic_freeEnergy_antitoneOn hT hI hcont
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) hH hS hx

end GenericMetriplecticNormed

end Layer1BanachMetriplectic

/-! ## Layer 2: Noncommutative Finite Gibbs–BKM Trajectory Second Law -/

section Layer2GibbsBKMTrajectory

open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsSecondDerivativeCenteredBridge
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge

/-- Gibbs relative potential (dual Helmholtz / Massieu–Planck potential relative
to a target density `σ`): `Φ_σ(H) = Re log Tr(exp H) - Re Tr(σ * H)`. -/
noncomputable def gibbsRelativePotential {n : ℕ} (σ H : FiniteOperatorAlgebra n) : ℝ :=
  (logTracedExponential H).re - (finiteOperatorTrace (σ * H)).re

/-- Fréchet differential of `gibbsRelativePotential σ` at `H` over `ℝ`. -/
noncomputable def gibbsRelativePotentialFDeriv
    {n : ℕ} (σ H : FiniteOperatorAlgebra n) : FiniteOperatorAlgebra n →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((logTracedExponentialDerivative H) -
      (finiteOperatorTraceCLM n).comp
        (ContinuousLinearMap.mul ℂ (FiniteOperatorAlgebra n) σ)).restrictScalars ℝ)

@[simp] theorem gibbsRelativePotentialFDeriv_apply
    {n : ℕ} (σ H V : FiniteOperatorAlgebra n) :
    gibbsRelativePotentialFDeriv σ H V =
      (finiteOperatorTrace ((normalizedExponential H - σ) * V)).re := by
  dsimp [gibbsRelativePotentialFDeriv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.mul_apply',
    finiteOperatorTraceCLM_apply,
    logTracedExponentialDerivative_apply_eq_expectation]
  change (operatorExpectation H V - finiteOperatorTrace (σ * V)).re = _
  unfold operatorExpectation
  change (finiteOperatorTrace (normalizedExponential H * V) -
      finiteOperatorTrace (σ * V)).re = _
  congr 1
  change (finiteOperatorTraceLinear n) (normalizedExponential H * V) -
      (finiteOperatorTraceLinear n) (σ * V) =
    (finiteOperatorTraceLinear n) ((normalizedExponential H - σ) * V)
  rw [← map_sub, sub_mul]

theorem gibbsRelativePotentialFDeriv_apply_of_isSelfAdjoint
    {n : ℕ} (σ H V : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) :
    gibbsRelativePotentialFDeriv σ H V =
      (finiteOperatorTrace
        (((faithfulGibbsDensity H hH hZ).rho - σ) * V)).re := by
  rw [gibbsRelativePotentialFDeriv_apply,
    faithfulGibbsDensity_rho_eq_normalizedExponential H hH hZ]

/-- Genuine Fréchet differentiability of `gibbsRelativePotential σ` on the
principal slit-plane locus. -/
theorem hasFDerivAt_gibbsRelativePotential
    {n : ℕ} (σ H : FiniteOperatorAlgebra n)
    (hSlit : tracedExponential H ∈ Complex.slitPlane) :
    HasFDerivAt (gibbsRelativePotential σ)
      (gibbsRelativePotentialFDeriv σ H) H := by
  have h1 :
      HasFDerivAt (fun X => (logTracedExponential X).re)
        (Complex.reCLM.comp ((logTracedExponentialDerivative H).restrictScalars ℝ)) H :=
    Complex.reCLM.hasFDerivAt.comp H
      ((hasFDerivAt_logTracedExponential H hSlit).restrictScalars ℝ)
  let Lσ : FiniteOperatorAlgebra n →L[ℝ] ℝ :=
    Complex.reCLM.comp
      (((finiteOperatorTraceCLM n).comp
        (ContinuousLinearMap.mul ℂ (FiniteOperatorAlgebra n) σ)).restrictScalars ℝ)
  have h2 : HasFDerivAt (fun X => (finiteOperatorTrace (σ * X)).re) Lσ H :=
    Lσ.hasFDerivAt
  have hsub :
      HasFDerivAt (gibbsRelativePotential σ)
        (Complex.reCLM.comp ((logTracedExponentialDerivative H).restrictScalars ℝ) - Lσ) H :=
    h1.fun_sub h2
  refine hsub.congr_fderiv ?_
  ext V
  simp [gibbsRelativePotentialFDeriv, Lσ]

/-- Self-adjoint specialization of `hasFDerivAt_gibbsRelativePotential` with the
slit-plane hypothesis discharged internally. -/
theorem hasFDerivAt_gibbsRelativePotential_of_isSelfAdjoint
    {n : ℕ} [Nonempty (Fin n)] (σ H : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) :
    HasFDerivAt (gibbsRelativePotential σ)
      (gibbsRelativePotentialFDeriv σ H) H :=
  hasFDerivAt_gibbsRelativePotential σ H
    (tracedExponential_mem_slitPlane_of_isSelfAdjoint H hH)

/-- Reversible Heisenberg/unitary generator drift `-i [H_eq, H]` on `FiniteOperatorAlgebra n`. -/
noncomputable def gibbsUnitaryVectorField
    {n : ℕ} (H_eq H : FiniteOperatorAlgebra n) : FiniteOperatorAlgebra n :=
  -Complex.I • (H_eq * H - H * H_eq)

/-- State-dependent BKM gradient-descent dissipative vector field
`-K_{D_H}(ρ_H - σ)`. -/
noncomputable def gibbsBKMDissipativeField
    {n : ℕ} [Nonempty (Fin n)] (σ H : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) :
    FiniteOperatorAlgebra n :=
  let hZ : 0 < gibbsPartitionReal H :=
    (tracedExponential_re_pos_of_isSelfAdjoint H hH : 0 < gibbsPartitionReal H);
  let D := faithfulGibbsDensity H hH hZ;
  -(D.kuboMoriTransform (D.rho - σ))

/-- Full state-dependent Gibbs–BKM metriplectic vector field
`-i [H_eq, H] - K_{D_H}(ρ_H - σ)`. -/
noncomputable def gibbsMetriplecticFlow
    {n : ℕ} [Nonempty (Fin n)] (H_eq σ H : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) :
    FiniteOperatorAlgebra n :=
  gibbsUnitaryVectorField H_eq H + gibbsBKMDissipativeField σ H hH

/-- `gibbsUnitaryVectorField` preserves self-adjointness. -/
theorem isSelfAdjoint_gibbsUnitaryVectorField
    {n : ℕ} {H_eq H : FiniteOperatorAlgebra n}
    (hH_eq : IsSelfAdjoint H_eq) (hH : IsSelfAdjoint H) :
    IsSelfAdjoint (gibbsUnitaryVectorField H_eq H) := by
  rw [isSelfAdjoint_iff, gibbsUnitaryVectorField, star_smul]
  have hcomm_star :
      star (H_eq * H - H * H_eq) = H * H_eq - H_eq * H := by
    change ContinuousLinearMap.adjoint (H_eq * H - H * H_eq) = H * H_eq - H_eq * H
    rw [map_sub]
    change star (H_eq * H) - star (H * H_eq) = H * H_eq - H_eq * H
    rw [star_mul, star_mul, hH.star_eq, hH_eq.star_eq]
  have hI : star (-Complex.I) = Complex.I := by simp
  rw [hcomm_star, hI, smul_sub, smul_sub]
  rw [neg_smul, neg_smul]
  abel

/-- `gibbsBKMDissipativeField` preserves self-adjointness whenever `σ` is
self-adjoint. -/
theorem isSelfAdjoint_gibbsBKMDissipativeField
    {n : ℕ} [Nonempty (Fin n)] {σ H : FiniteOperatorAlgebra n}
    (hσ : IsSelfAdjoint σ) (hH : IsSelfAdjoint H) :
    IsSelfAdjoint (gibbsBKMDissipativeField σ H hH) := by
  dsimp [gibbsBKMDissipativeField]
  have hZ : 0 < gibbsPartitionReal H :=
    tracedExponential_re_pos_of_isSelfAdjoint H hH
  let D := faithfulGibbsDensity H hH hZ
  have hdiff : star (D.rho - σ) = D.rho - σ :=
    (D.strictlyPositive.isSelfAdjoint.sub hσ).star_eq
  have hkmt :
      star (D.kuboMoriTransform (D.rho - σ)) =
        D.kuboMoriTransform (D.rho - σ) :=
    D.kuboMoriTransform_preserves_selfAdjoint
      (continuous_faithfulGibbsDensity_rpow H hH hZ) (D.rho - σ) hdiff
  change ContinuousLinearMap.adjoint (-D.kuboMoriTransform (D.rho - σ)) =
    -D.kuboMoriTransform (D.rho - σ)
  rw [map_neg]
  change -(star (D.kuboMoriTransform (D.rho - σ))) = -D.kuboMoriTransform (D.rho - σ)
  rw [hkmt]

/-- `gibbsMetriplecticFlow` preserves the self-adjoint subspace. -/
theorem isSelfAdjoint_gibbsMetriplecticFlow
    {n : ℕ} [Nonempty (Fin n)] {H_eq σ H : FiniteOperatorAlgebra n}
    (hH_eq : IsSelfAdjoint H_eq) (hσ : IsSelfAdjoint σ) (hH : IsSelfAdjoint H) :
    IsSelfAdjoint (gibbsMetriplecticFlow H_eq σ H hH) := by
  change ContinuousLinearMap.adjoint (gibbsUnitaryVectorField H_eq H + gibbsBKMDissipativeField σ H hH) =
    gibbsUnitaryVectorField H_eq H + gibbsBKMDissipativeField σ H hH
  rw [map_add]
  change star (gibbsUnitaryVectorField H_eq H) + star (gibbsBKMDissipativeField σ H hH) =
    gibbsUnitaryVectorField H_eq H + gibbsBKMDissipativeField σ H hH
  rw [(isSelfAdjoint_gibbsUnitaryVectorField hH_eq hH).star_eq,
    (isSelfAdjoint_gibbsBKMDissipativeField hσ hH).star_eq]

/-- Cyclic-trace helper: if `A` commutes with `B`, then `Tr(A * [C, B]) = 0`
without assuming `[C, B] = 0` or `[A, C] = 0`. -/
theorem finiteOperatorTrace_mul_commutator_eq_zero_of_commute
    {n : ℕ} (A B C : FiniteOperatorAlgebra n) (hAB : Commute A B) :
    finiteOperatorTrace (A * (C * B - B * C)) = 0 := by
  change (finiteOperatorTraceLinear n) (A * (C * B - B * C)) = 0
  rw [mul_sub, map_sub]
  have hcyc :
      (finiteOperatorTraceLinear n) (A * (C * B)) =
        (finiteOperatorTraceLinear n) (A * (B * C)) := by
    calc
      finiteOperatorTrace (A * (C * B))
          = finiteOperatorTrace ((A * C) * B) := by rw [mul_assoc]
      _ = finiteOperatorTrace (B * (A * C)) := finiteOperatorTrace_mul_comm _ _
      _ = finiteOperatorTrace ((B * A) * C) := by rw [mul_assoc]
      _ = finiteOperatorTrace ((A * B) * C) := by rw [hAB.symm.eq]
      _ = finiteOperatorTrace (A * (B * C)) := by rw [mul_assoc]
  rw [hcyc, sub_self]

/-- Every Gibbs state `normalizedExponential H` commutes with its generator `H`. -/
theorem commute_normalizedExponential_self
    {n : ℕ} (H : FiniteOperatorAlgebra n) :
    Commute (normalizedExponential H) H := by
  letI : NormedAlgebra ℚ (FiniteOperatorAlgebra n) :=
    NormedAlgebra.restrictScalars ℚ ℂ (FiniteOperatorAlgebra n)
  exact ((Commute.refl H).exp_left).smul_left (tracedExponential H)⁻¹

/-- Unconditional complex trace vanishing of `(ρ_H - σ) * (-i [H_eq, H])`
whenever `Commute σ H_eq` (without assuming `[H_eq, H] = 0`). -/
theorem finiteOperatorTrace_sub_mul_gibbsUnitaryVectorField_eq_zero
    {n : ℕ} [Nonempty (Fin n)] (H_eq σ H : FiniteOperatorAlgebra n)
    (hH : IsSelfAdjoint H) (hcomm_σ : Commute σ H_eq) :
    finiteOperatorTrace
        (((faithfulGibbsDensity H hH
            (tracedExponential_re_pos_of_isSelfAdjoint H hH)).rho - σ) *
          gibbsUnitaryVectorField H_eq H) = 0 := by
  have hZ : 0 < gibbsPartitionReal H :=
    tracedExponential_re_pos_of_isSelfAdjoint H hH
  let D := faithfulGibbsDensity H hH hZ
  have hρ_eq : D.rho = normalizedExponential H :=
    faithfulGibbsDensity_rho_eq_normalizedExponential H hH hZ
  have hcomm_ρ : Commute D.rho H := by
    rw [hρ_eq]
    exact commute_normalizedExponential_self H
  have h1 : finiteOperatorTrace (D.rho * (H_eq * H - H * H_eq)) = 0 :=
    finiteOperatorTrace_mul_commutator_eq_zero_of_commute D.rho H H_eq hcomm_ρ
  have h2_aux : finiteOperatorTrace (σ * (H * H_eq - H_eq * H)) = 0 :=
    finiteOperatorTrace_mul_commutator_eq_zero_of_commute σ H_eq H hcomm_σ
  have h2 : finiteOperatorTrace (σ * (H_eq * H - H * H_eq)) = 0 := by
    have hneg : σ * (H_eq * H - H * H_eq) = -(σ * (H * H_eq - H_eq * H)) := by
      rw [mul_sub, mul_sub, neg_sub]
    change (finiteOperatorTraceLinear n) (σ * (H_eq * H - H * H_eq)) = 0
    rw [hneg, map_neg]
    change -(finiteOperatorTrace (σ * (H * H_eq - H_eq * H))) = 0
    rw [h2_aux, neg_zero]
  unfold gibbsUnitaryVectorField
  rw [mul_smul_comm, finiteOperatorTrace_complex_smul]
  change -Complex.I * (finiteOperatorTraceLinear n) ((D.rho - σ) * (H_eq * H - H * H_eq)) = 0
  rw [sub_mul, map_sub]
  change -Complex.I *
      (finiteOperatorTrace (D.rho * (H_eq * H - H * H_eq)) -
        finiteOperatorTrace (σ * (H_eq * H - H * H_eq))) = 0
  rw [h1, h2, sub_zero, mul_zero]

/-- Unconditional real-part trace vanishing of `(ρ_H - σ) * (-i [H_eq, H])`
without assuming `[H_eq, H] = 0`. -/
theorem finiteOperatorTrace_gibbsUnitaryVectorField_re_eq_zero
    {n : ℕ} [Nonempty (Fin n)] (H_eq σ H : FiniteOperatorAlgebra n)
    (hH : IsSelfAdjoint H) (hcomm_σ : Commute σ H_eq) :
    (finiteOperatorTrace
        (((faithfulGibbsDensity H hH
            (tracedExponential_re_pos_of_isSelfAdjoint H hH)).rho - σ) *
          gibbsUnitaryVectorField H_eq H)).re = 0 := by
  rw [finiteOperatorTrace_sub_mul_gibbsUnitaryVectorField_eq_zero H_eq σ H hH hcomm_σ]
  simp

/-- Pointwise Fréchet chain-rule Second Law for `gibbsRelativePotential σ`
along a trajectory `H : ℝ → FiniteOperatorAlgebra n` following `gibbsMetriplecticFlow`.
Does NOT assume `[H_eq, H t] = 0`. -/
theorem hasDerivAt_gibbsRelativePotential_metriplectic
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n) (hσ : IsSelfAdjoint σ) (hcomm_σ : Commute σ H_eq)
    (H : ℝ → FiniteOperatorAlgebra n) {t : ℝ} (hH : IsSelfAdjoint (H t))
    (hderiv : HasDerivAt H (gibbsMetriplecticFlow H_eq σ (H t) hH) t) :
    HasDerivAt (fun s => gibbsRelativePotential σ (H s))
      (-(faithfulGibbsDensity (H t) hH
          (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).bkmRealBilinForm
        (continuous_faithfulGibbsDensity_rpow (H t) hH
          (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH))
        ((faithfulGibbsDensity (H t) hH
          (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).rho - σ)
        ((faithfulGibbsDensity (H t) hH
          (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).rho - σ)) t := by
  have hZ : 0 < gibbsPartitionReal (H t) :=
    tracedExponential_re_pos_of_isSelfAdjoint (H t) hH
  let D := faithfulGibbsDensity (H t) hH hZ
  let hpow := continuous_faithfulGibbsDensity_rpow (H t) hH hZ
  have hΦ :
      HasFDerivAt (gibbsRelativePotential σ)
        (gibbsRelativePotentialFDeriv σ (H t)) (H t) :=
    hasFDerivAt_gibbsRelativePotential_of_isSelfAdjoint σ (H t) hH
  have hrev :
      gibbsRelativePotentialFDeriv σ (H t) (gibbsUnitaryVectorField H_eq (H t)) = 0 := by
    rw [gibbsRelativePotentialFDeriv_apply_of_isSelfAdjoint σ (H t) _ hH hZ]
    exact finiteOperatorTrace_gibbsUnitaryVectorField_re_eq_zero H_eq σ (H t) hH hcomm_σ
  have hdiss_eq :
      gibbsRelativePotentialFDeriv σ (H t) (gibbsBKMDissipativeField σ (H t) hH) =
        -D.bkmRealBilinForm hpow (D.rho - σ) (D.rho - σ) := by
    rw [gibbsRelativePotentialFDeriv_apply_of_isSelfAdjoint σ (H t) _ hH hZ]
    have hfield :
        gibbsBKMDissipativeField σ (H t) hH = -D.kuboMoriTransform (D.rho - σ) := rfl
    rw [hfield]
    have hmul_neg :
        (D.rho - σ) * (-D.kuboMoriTransform (D.rho - σ)) =
          -((D.rho - σ) * D.kuboMoriTransform (D.rho - σ)) :=
      mul_neg (D.rho - σ) (D.kuboMoriTransform (D.rho - σ))
    rw [hmul_neg]
    change ((finiteOperatorTraceLinear n)
        (-((D.rho - σ) * D.kuboMoriTransform (D.rho - σ)))).re = _
    rw [map_neg, Complex.neg_re]
    have hsa : star (D.rho - σ) = D.rho - σ :=
      (D.strictlyPositive.isSelfAdjoint.sub hσ).star_eq
    have htr :
        finiteOperatorTrace ((D.rho - σ) * D.kuboMoriTransform (D.rho - σ)) =
          D.kuboMoriPairing (D.rho - σ) (D.rho - σ) := by
      rw [finiteOperatorTrace_mul_comm]
      calc
        finiteOperatorTrace (D.kuboMoriTransform (D.rho - σ) * (D.rho - σ))
            = finiteOperatorTrace
                (D.kuboMoriTransform (star (D.rho - σ)) * (D.rho - σ)) := by
                  rw [hsa]
        _ = D.kuboMoriPairing (D.rho - σ) (D.rho - σ) :=
              (D.kuboMoriPairing_eq_trace_kuboMoriTransform
                (D.rho - σ) (D.rho - σ) hpow).symm
    change -(finiteOperatorTrace ((D.rho - σ) * D.kuboMoriTransform (D.rho - σ))).re = _
    rw [htr, D.bkmRealBilinForm_apply]
  have hflow_split :
      HasDerivAt H
        (gibbsUnitaryVectorField H_eq (H t) + gibbsBKMDissipativeField σ (H t) hH) t :=
    hderiv
  have hmain :=
    banach_metriplectic_hasDerivAt_eq
      (dΦ := fun _ => gibbsRelativePotentialFDeriv σ (H t))
      (v_rev := fun _ => gibbsUnitaryVectorField H_eq (H t))
      (v_diss := fun _ => gibbsBKMDissipativeField σ (H t) hH)
      hΦ hflow_split hrev
  rw [hdiss_eq] at hmain
  exact hmain

/-- Nonpositive derivative of `gibbsRelativePotential σ` along a metriplectic
Gibbs trajectory (without assuming `[H_eq, H t] = 0`). -/
theorem deriv_gibbsRelativePotential_metriplectic_nonpos
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n) (hσ : IsSelfAdjoint σ) (hcomm_σ : Commute σ H_eq)
    (H : ℝ → FiniteOperatorAlgebra n) {t : ℝ} (hH : IsSelfAdjoint (H t))
    (hderiv : HasDerivAt H (gibbsMetriplecticFlow H_eq σ (H t) hH) t) :
    deriv (fun s => gibbsRelativePotential σ (H s)) t ≤ 0 := by
  let hZ := tracedExponential_re_pos_of_isSelfAdjoint (H t) hH
  let D := faithfulGibbsDensity (H t) hH hZ
  let hpow := continuous_faithfulGibbsDensity_rpow (H t) hH hZ
  rw [(hasDerivAt_gibbsRelativePotential_metriplectic
    H_eq σ hσ hcomm_σ H hH hderiv).deriv]
  exact neg_nonpos.mpr (D.kuboMoriPairing_self_re_nonneg (D.rho - σ) hpow)

/-- Strict negativity (`d/dt Φ < 0`) whenever the current Gibbs state `ρ_t` is
not equal to the target state `σ`. -/
theorem deriv_gibbsRelativePotential_metriplectic_neg_of_ne
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n) (hσ : IsSelfAdjoint σ) (hcomm_σ : Commute σ H_eq)
    (H : ℝ → FiniteOperatorAlgebra n) {t : ℝ} (hH : IsSelfAdjoint (H t))
    (hderiv : HasDerivAt H (gibbsMetriplecticFlow H_eq σ (H t) hH) t)
    (hne :
      (faithfulGibbsDensity (H t) hH
        (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).rho ≠ σ) :
    deriv (fun s => gibbsRelativePotential σ (H s)) t < 0 := by
  let hZ := tracedExponential_re_pos_of_isSelfAdjoint (H t) hH
  let D := faithfulGibbsDensity (H t) hH hZ
  let hpow := continuous_faithfulGibbsDensity_rpow (H t) hH hZ
  rw [(hasDerivAt_gibbsRelativePotential_metriplectic
    H_eq σ hσ hcomm_σ H hH hderiv).deriv]
  exact neg_neg_of_pos
    (D.kuboMoriPairing_self_re_pos (D.rho - σ) hpow (sub_ne_zero.mpr hne))

/-- Trajectory-level `AntitoneOn` monotonicity of `gibbsRelativePotential σ`
on any convex interval `I` along a `gibbsMetriplecticFlow` solution (without
assuming `[H_eq, H t] = 0`). -/
theorem antitoneOn_gibbsRelativePotential_metriplectic
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n) (hσ : IsSelfAdjoint σ) (hcomm_σ : Commute σ H_eq)
    (H : ℝ → FiniteOperatorAlgebra n) {I : Set ℝ} (hI : Convex ℝ I)
    (hH : ∀ t ∈ I, IsSelfAdjoint (H t))
    (hflow : ∀ t (ht : t ∈ I), HasDerivAt H (gibbsMetriplecticFlow H_eq σ (H t) (hH t ht)) t) :
    AntitoneOn (fun s => gibbsRelativePotential σ (H s)) I := by
  have hcont : ContinuousOn (fun s => gibbsRelativePotential σ (H s)) I := by
    intro t ht
    exact (hasDerivAt_gibbsRelativePotential_metriplectic H_eq σ hσ hcomm_σ
      H (hH t ht) (hflow t ht)).continuousAt.continuousWithinAt
  apply antitoneOn_of_deriv_nonpos hI hcont
  · intro t ht
    exact (hasDerivAt_gibbsRelativePotential_metriplectic H_eq σ hσ hcomm_σ
      H (hH t (interior_subset ht)) (hflow t (interior_subset ht))).differentiableAt.differentiableWithinAt
  · intro t ht
    exact deriv_gibbsRelativePotential_metriplectic_nonpos H_eq σ hσ hcomm_σ
      H (hH t (interior_subset ht)) (hflow t (interior_subset ht))

/-- Fundamental Theorem of Calculus identity in any real Banach algebra:
`∫₀¹ exp(s H) [H, A] exp((1 - s) H) ds = [exp H, A]`. -/
theorem integral_exp_smul_commutator_eq
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (H X : A) :
    (∫ s in (0 : ℝ)..1,
      NormedSpace.exp (s • H) * (H * X - X * H) * NormedSpace.exp ((1 - s) • H)) =
      NormedSpace.exp H * X - X * NormedSpace.exp H := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let F : ℝ → A := fun s =>
    NormedSpace.exp (s • H) * X * NormedSpace.exp ((1 - s) • H)
  have hderiv :
      ∀ s ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt F
          (NormedSpace.exp (s • H) * (H * X - X * H) *
            NormedSpace.exp ((1 - s) • H)) s := by
    intro s _
    have h1 :
        HasDerivAt (fun u : ℝ => NormedSpace.exp (u • H))
          (NormedSpace.exp (s • H) * H) s :=
      (hasStrictDerivAt_exp_smul_const H s).hasDerivAt
    have h2_0 :
        HasDerivAt (fun u : ℝ => NormedSpace.exp (u • H))
          (H * NormedSpace.exp ((1 - s) • H)) (1 - s) :=
      (hasStrictDerivAt_exp_smul_const' H (1 - s)).hasDerivAt
    have hu : HasDerivAt (fun u : ℝ => 1 - u) (-1) s := by
      have hsub := (hasDerivAt_const s (1 : ℝ)).fun_sub (hasDerivAt_id s)
      rw [zero_sub] at hsub
      exact hsub
    have h2 :
        HasDerivAt (fun u : ℝ => NormedSpace.exp ((1 - u) • H))
          (-(H * NormedSpace.exp ((1 - s) • H))) s := by
      simpa [Function.comp_def] using h2_0.scomp s hu
    have hprod := (h1.mul_const X).mul h2
    have heq :
        ((NormedSpace.exp (s • H) * H * X) * NormedSpace.exp ((1 - s) • H) +
          (NormedSpace.exp (s • H) * X) * (-(H * NormedSpace.exp ((1 - s) • H)))) =
          NormedSpace.exp (s • H) * (H * X - X * H) *
            NormedSpace.exp ((1 - s) • H) := by
      noncomm_ring
    rw [heq] at hprod
    exact hprod
  have hint :
      IntervalIntegrable
        (fun s : ℝ =>
          NormedSpace.exp (s • H) * (H * X - X * H) *
            NormedSpace.exp ((1 - s) • H)) volume 0 1 := by
    have hcont :
        Continuous (fun s : ℝ =>
          NormedSpace.exp (s • H) * (H * X - X * H) *
            NormedSpace.exp ((1 - s) • H)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa [F] using hftc

/-- Exact Kubo–Mori commutator intertwining identity:
`D_H.kuboMoriTransform (H * A - A * H) = D_H.rho * A - A * D_H.rho`. -/
theorem kuboMoriTransform_commutator_eq_commutator_rho
    {n : ℕ} (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) :
    (faithfulGibbsDensity H hH hZ).kuboMoriTransform (H * A - A * H) =
      (faithfulGibbsDensity H hH hZ).rho * A -
        A * (faithfulGibbsDensity H hH hZ).rho := by
  let D := faithfulGibbsDensity H hH hZ
  let Z : ℝ := gibbsPartitionReal H
  have hZ_ne : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have h_integrand :
      ∀ s : ℝ,
        D.modularInterpolation s (H * A - A * H) =
          (Z⁻¹ : ℂ) •
            (NormedSpace.exp (s • H) * (H * A - A * H) *
              NormedSpace.exp ((1 - s) • H)) := by
    intro s
    unfold FaithfulDensityOperator.modularInterpolation
    dsimp [D]
    rw [faithfulGibbsDensity_rpow H hH hZ s,
      faithfulGibbsDensity_rpow H hH hZ (1 - s)]
    simp only [real_smul_eq_complex_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    rw [← Complex.ofReal_mul, ← Real.rpow_add hZ]
    have hsum : -(1 - s) + -s = (-1 : ℝ) := by ring
    rw [hsum, Real.rpow_neg_one, Complex.ofReal_inv]
  calc
    D.kuboMoriTransform (H * A - A * H)
        = ∫ s in (0 : ℝ)..1, D.modularInterpolation s (H * A - A * H) := rfl
    _ = ∫ s in (0 : ℝ)..1,
          (Z⁻¹ : ℂ) •
            (NormedSpace.exp (s • H) * (H * A - A * H) *
              NormedSpace.exp ((1 - s) • H)) := by
          apply intervalIntegral.integral_congr
          intro s _
          exact h_integrand s
    _ = (Z⁻¹ : ℂ) •
          ∫ s in (0 : ℝ)..1,
            NormedSpace.exp (s • H) * (H * A - A * H) *
              NormedSpace.exp ((1 - s) • H) := by
          rw [intervalIntegral.integral_smul]
    _ = (Z⁻¹ : ℂ) • (NormedSpace.exp H * A - A * NormedSpace.exp H) := by
          rw [integral_exp_smul_commutator_eq H A]
    _ = D.rho * A - A * D.rho := by
          have hρ : D.rho = (Z⁻¹ : ℂ) • NormedSpace.exp H := by
            rw [faithfulGibbsDensity_rho_eq_normalizedExponential H hH hZ]
            unfold normalizedExponential
            rw [tracedExponential_eq_gibbsPartitionReal H hH]
          rw [hρ, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- Corollary of `kuboMoriTransform_commutator_eq_commutator_rho` stated in
terms of `normalizedExponential H`. -/
theorem kuboMoriTransform_commutator_eq_commutator_normalizedExponential
    {n : ℕ} (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) :
    (faithfulGibbsDensity H hH hZ).kuboMoriTransform (H * A - A * H) =
      normalizedExponential H * A - A * normalizedExponential H := by
  rw [kuboMoriTransform_commutator_eq_commutator_rho H A hH hZ,
    faithfulGibbsDensity_rho_eq_normalizedExponential H hH hZ]

/-- Fréchet differential of `normalizedExponential` over `ℂ` at `H`. -/
noncomputable def normalizedExponentialFDeriv
    {n : ℕ} (H : FiniteOperatorAlgebra n) : FiniteOperatorAlgebra n →L[ℂ] FiniteOperatorAlgebra n :=
  (-(tracedExponential H ^ 2)⁻¹ • tracedExponentialDerivative H).smulRight
      (NormedSpace.exp H) +
    (tracedExponential H)⁻¹ • exponentialDerivative (𝕜 := ℂ) H

/-- Genuine Fréchet differentiability of `normalizedExponential` over `ℂ` on
the nonvanishing trace locus. -/
theorem hasFDerivAt_normalizedExponential
    {n : ℕ} (H : FiniteOperatorAlgebra n) (hZ_ne : tracedExponential H ≠ 0) :
    HasFDerivAt (normalizedExponential (n := n))
      (normalizedExponentialFDeriv H) H := by
  have hf1 :
      HasFDerivAt (fun X : FiniteOperatorAlgebra n => (tracedExponential X)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℂ
            (-(tracedExponential H ^ 2)⁻¹)).comp
          (tracedExponentialDerivative H)) H :=
    (hasFDerivAt_inv hZ_ne).comp H (hasFDerivAt_tracedExponential H)
  have hf2 :
      HasFDerivAt (NormedSpace.exp : FiniteOperatorAlgebra n → FiniteOperatorAlgebra n)
        (exponentialDerivative (𝕜 := ℂ) H) H :=
    hasFDerivAt_exp_noncommutative (𝕜 := ℂ) H
  have hsmul := hf1.fun_smul hf2
  have hEq :
      (fun X : FiniteOperatorAlgebra n => (tracedExponential X)⁻¹ • NormedSpace.exp X) =
        normalizedExponential := rfl
  rw [hEq] at hsmul
  refine hsmul.congr_fderiv ?_
  ext V
  simp only [normalizedExponentialFDeriv, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, add_comm, mul_comm]

/-- On self-adjoint `H`, `(tracedExponential H)⁻¹ • duhamelDerivative H V`
equals `D_H.kuboMoriTransform V`. -/
theorem inv_tracedExponential_smul_duhamelDerivative_eq_kuboMoriTransform
    {n : ℕ} (H V : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) :
    (tracedExponential H)⁻¹ • duhamelDerivative H V =
      (faithfulGibbsDensity H hH hZ).kuboMoriTransform V := by
  let D := faithfulGibbsDensity H hH hZ
  let Z : ℝ := gibbsPartitionReal H
  rw [duhamelDerivative_apply_integral, tracedExponential_eq_gibbsPartitionReal H hH,
    ← intervalIntegral.integral_smul]
  have h1 :
      (∫ s in (0 : ℝ)..1,
        (Z : ℂ)⁻¹ •
          (NormedSpace.exp ((1 - s) • H) * V * NormedSpace.exp (s • H))) =
        ∫ s in (0 : ℝ)..1,
          (Z : ℂ)⁻¹ •
            (NormedSpace.exp (s • H) * V * NormedSpace.exp ((1 - s) • H)) := by
    simpa only [sub_sub_cancel] using
      intervalIntegral_one_sub_eq
        (fun s : ℝ =>
          (Z : ℂ)⁻¹ •
            (NormedSpace.exp (s • H) * V * NormedSpace.exp ((1 - s) • H)))
  rw [h1]
  unfold FaithfulDensityOperator.kuboMoriTransform
  apply intervalIntegral.integral_congr
  intro s _
  unfold FaithfulDensityOperator.modularInterpolation
  dsimp [D]
  rw [faithfulGibbsDensity_rpow H hH hZ s,
    faithfulGibbsDensity_rpow H hH hZ (1 - s)]
  simp only [real_smul_eq_complex_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.rpow_add hZ]
  have hsum : -(1 - s) + -s = (-1 : ℝ) := by ring
  rw [hsum, Real.rpow_neg_one, Complex.ofReal_inv]

/-- `D.kuboMoriTransform 1 = D.rho`. -/
theorem kuboMoriTransform_one
    {n : ℕ} (D : FaithfulDensityOperator n) :
    D.kuboMoriTransform (1 : FiniteOperatorAlgebra n) = D.rho := by
  unfold FaithfulDensityOperator.kuboMoriTransform
    FaithfulDensityOperator.modularInterpolation
  have hpt : ∀ s : ℝ, D.rpow s * (1 : FiniteOperatorAlgebra n) * D.rpow (1 - s) = D.rho := by
    intro s
    rw [mul_one, ← D.rpow_add]
    have hs : s + (1 - s) = 1 := by ring
    rw [hs, D.rpow_one]
  simp_rw [hpt]
  simp

/-- Exact evaluation of `normalizedExponentialFDeriv H V` as the centered
Kubo–Mori transform `D_H.kuboMoriTransform (V - Tr(ρ_H V) • 1)`. -/
theorem normalizedExponentialFDeriv_apply_eq_kuboMoriTransform
    {n : ℕ} (H V : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) :
    normalizedExponentialFDeriv H V =
      (faithfulGibbsDensity H hH hZ).kuboMoriTransform
        (V - finiteOperatorTrace ((faithfulGibbsDensity H hH hZ).rho * V) • (1 : FiniteOperatorAlgebra n)) := by
  let D := faithfulGibbsDensity H hH hZ
  let hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
  have hρ : D.rho = (tracedExponential H)⁻¹ • NormedSpace.exp H :=
    faithfulGibbsDensity_rho_eq_normalizedExponential H hH hZ
  have hlin :
      D.kuboMoriTransform
          (V - finiteOperatorTrace (D.rho * V) • (1 : FiniteOperatorAlgebra n)) =
        D.kuboMoriTransform V -
          finiteOperatorTrace (D.rho * V) • D.kuboMoriTransform (1 : FiniteOperatorAlgebra n) := by
    change D.kuboMoriTransformLinear hpow
        (V - finiteOperatorTrace (D.rho * V) • (1 : FiniteOperatorAlgebra n)) =
      D.kuboMoriTransformLinear hpow V -
        finiteOperatorTrace (D.rho * V) • D.kuboMoriTransformLinear hpow (1 : FiniteOperatorAlgebra n)
    rw [map_sub, map_smul]
  rw [hlin, kuboMoriTransform_one D]
  unfold normalizedExponentialFDeriv
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, tracedExponentialDerivative_apply]
  rw [exponentialDerivative_complex_apply_eq_real H V,
    gibbs_exponentialDerivative_eq_duhamelDerivative H,
    inv_tracedExponential_smul_duhamelDerivative_eq_kuboMoriTransform H V hH hZ]
  have hterm1 :
      (-(tracedExponential H ^ 2)⁻¹ • finiteOperatorTrace (NormedSpace.exp H * V)) •
          NormedSpace.exp H =
        -(finiteOperatorTrace (D.rho * V) • D.rho) := by
    rw [hρ, smul_mul_assoc, finiteOperatorTrace_complex_smul]
    apply ContinuousLinearMap.ext
    intro x
    ext i
    simp
    ring
  rw [hterm1, sub_eq_add_neg, add_comm]

/-- Self-adjoint observable specialization of `normalizedExponentialFDeriv`:
`normalizedExponentialFDeriv H V = D_H.kuboMoriTransform (centeredStatistic D_H V)`. -/
theorem normalizedExponentialFDeriv_apply_eq_kuboMoriTransform_centered
    {n : ℕ} [Nonempty (Fin n)] (H V : FiniteOperatorAlgebra n)
    (hH : IsSelfAdjoint H) (hV : IsSelfAdjoint V)
    (hZ : 0 < gibbsPartitionReal H) :
    normalizedExponentialFDeriv H V =
      (faithfulGibbsDensity H hH hZ).kuboMoriTransform
        (centeredStatistic (faithfulGibbsDensity H hH hZ) V) := by
  rw [normalizedExponentialFDeriv_apply_eq_kuboMoriTransform H V hH hZ]
  have htr :
      finiteOperatorTrace ((faithfulGibbsDensity H hH hZ).rho * V) =
        (expectationReal (faithfulGibbsDensity H hH hZ) V : ℂ) := by
    rw [← operatorExpectation_eq_faithfulGibbsDensity_expectation H hH hZ V]
    have him := operatorExpectation_im_eq_zero_of_isSelfAdjoint H hH hZ V hV
    apply Complex.ext
    · simp [expectationReal, operatorExpectation_eq_faithfulGibbsDensity_expectation H hH hZ V]
    · simp [him]
  rw [htr, ← real_smul_eq_complex_smul]
  rfl

/-- Trajectory derivative of `s ↦ normalizedExponential (H s)` along any
differentiable self-adjoint curve `H` with `HasDerivAt H V t`. -/
theorem hasDerivAt_normalizedExponential
    {n : ℕ} [Nonempty (Fin n)] (H : ℝ → FiniteOperatorAlgebra n) {V : FiniteOperatorAlgebra n} {t : ℝ}
    (hH : IsSelfAdjoint (H t)) (hderiv : HasDerivAt H V t) :
    HasDerivAt (fun s => normalizedExponential (H s))
      ((faithfulGibbsDensity (H t) hH
          (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).kuboMoriTransform
        (V -
          finiteOperatorTrace
              ((faithfulGibbsDensity (H t) hH
                  (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).rho * V) •
            (1 : FiniteOperatorAlgebra n))) t := by
  let hZ := tracedExponential_re_pos_of_isSelfAdjoint (H t) hH
  have hZ_ne : tracedExponential (H t) ≠ 0 :=
    Complex.slitPlane_ne_zero (tracedExponential_mem_slitPlane_of_isSelfAdjoint (H t) hH)
  have hf :=
    ((hasFDerivAt_normalizedExponential (H t) hZ_ne).restrictScalars ℝ).comp_hasDerivAt
      t hderiv
  change HasDerivAt (fun s => normalizedExponential (H s))
      (normalizedExponentialFDeriv (H t) V) t at hf
  rw [normalizedExponentialFDeriv_apply_eq_kuboMoriTransform (H t) V hH hZ] at hf
  exact hf

/-- Self-adjoint tangent specialization of `hasDerivAt_normalizedExponential`
using `centeredStatistic`. -/
theorem hasDerivAt_normalizedExponential_centered
    {n : ℕ} [Nonempty (Fin n)] (H : ℝ → FiniteOperatorAlgebra n) {V : FiniteOperatorAlgebra n} {t : ℝ}
    (hH : IsSelfAdjoint (H t)) (hV : IsSelfAdjoint V) (hderiv : HasDerivAt H V t) :
    HasDerivAt (fun s => normalizedExponential (H s))
      ((faithfulGibbsDensity (H t) hH
          (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).kuboMoriTransform
        (centeredStatistic
          (faithfulGibbsDensity (H t) hH
            (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)) V)) t := by
  let hZ := tracedExponential_re_pos_of_isSelfAdjoint (H t) hH
  have hZ_ne : tracedExponential (H t) ≠ 0 :=
    Complex.slitPlane_ne_zero (tracedExponential_mem_slitPlane_of_isSelfAdjoint (H t) hH)
  have hf :=
    ((hasFDerivAt_normalizedExponential (H t) hZ_ne).restrictScalars ℝ).comp_hasDerivAt
      t hderiv
  change HasDerivAt (fun s => normalizedExponential (H s))
      (normalizedExponentialFDeriv (H t) V) t at hf
  rw [normalizedExponentialFDeriv_apply_eq_kuboMoriTransform_centered (H t) V hH hV hZ] at hf
  exact hf

/-- Mapping an `H(t)` trajectory driven by `gibbsMetriplecticFlow` to the
induced `ρ(t) = normalizedExponential (H t)` metriplectic trajectory. -/
theorem hasDerivAt_normalizedExponential_gibbsMetriplecticFlow
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n) (hH_eq : IsSelfAdjoint H_eq) (hσ : IsSelfAdjoint σ)
    (H : ℝ → FiniteOperatorAlgebra n) {t : ℝ} (hH : IsSelfAdjoint (H t))
    (hderiv : HasDerivAt H (gibbsMetriplecticFlow H_eq σ (H t) hH) t) :
    HasDerivAt (fun s => normalizedExponential (H s))
      (gibbsUnitaryVectorField H_eq
          (faithfulGibbsDensity (H t) hH
            (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).rho -
        (faithfulGibbsDensity (H t) hH
            (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).kuboMoriTransform
          (centeredStatistic
            (faithfulGibbsDensity (H t) hH
              (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH))
            ((faithfulGibbsDensity (H t) hH
                (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).kuboMoriTransform
              ((faithfulGibbsDensity (H t) hH
                  (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).rho - σ)))) t := by
  let hZ := tracedExponential_re_pos_of_isSelfAdjoint (H t) hH
  let D := faithfulGibbsDensity (H t) hH hZ
  let hpow := continuous_faithfulGibbsDensity_rpow (H t) hH hZ
  have hflow_sa : IsSelfAdjoint (gibbsMetriplecticFlow H_eq σ (H t) hH) :=
    isSelfAdjoint_gibbsMetriplecticFlow hH_eq hσ hH
  have hρ_deriv :=
    hasDerivAt_normalizedExponential_centered H hH hflow_sa hderiv
  have hcomm_ρH : Commute D.rho (H t) := by
    rw [faithfulGibbsDensity_rho_eq_normalizedExponential (H t) hH hZ]
    exact commute_normalizedExponential_self (H t)
  have htr_unitary :
      finiteOperatorTrace (D.rho * gibbsUnitaryVectorField H_eq (H t)) = 0 := by
    unfold gibbsUnitaryVectorField
    rw [mul_smul_comm, finiteOperatorTrace_complex_smul,
      finiteOperatorTrace_mul_commutator_eq_zero_of_commute D.rho (H t) H_eq hcomm_ρH,
      mul_zero]
  have hexp_unitary : expectationReal D (gibbsUnitaryVectorField H_eq (H t)) = 0 := by
    simp [expectationReal, htr_unitary]
  have hcent_unitary :
      centeredStatistic D (gibbsUnitaryVectorField H_eq (H t)) =
        gibbsUnitaryVectorField H_eq (H t) := by
    unfold centeredStatistic
    have hzero : (0 : ℂ) • (1 : FiniteOperatorAlgebra n) = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      ext i
      simp
    rw [hexp_unitary, real_smul_eq_complex_smul, Complex.ofReal_zero, hzero, sub_zero]
  have hkmt_unitary :
      D.kuboMoriTransform (gibbsUnitaryVectorField H_eq (H t)) =
        gibbsUnitaryVectorField H_eq D.rho := by
    unfold gibbsUnitaryVectorField
    change D.kuboMoriTransformCLM hpow (-Complex.I • (H_eq * H t - H t * H_eq)) =
      -Complex.I • (H_eq * D.rho - D.rho * H_eq)
    rw [(D.kuboMoriTransformCLM hpow).map_smul,
      D.kuboMoriTransformCLM_apply]
    have hneg_comm : H_eq * H t - H t * H_eq = -(H t * H_eq - H_eq * H t) := by abel
    have hkmt_neg :
        D.kuboMoriTransform (-(H t * H_eq - H_eq * H t)) =
          -D.kuboMoriTransform (H t * H_eq - H_eq * H t) := by
      change D.kuboMoriTransformCLM hpow (-(H t * H_eq - H_eq * H t)) =
        -D.kuboMoriTransformCLM hpow (H t * H_eq - H_eq * H t)
      exact map_neg (D.kuboMoriTransformCLM hpow) _
    rw [hneg_comm, hkmt_neg,
      kuboMoriTransform_commutator_eq_commutator_rho (H t) H_eq hH hZ]
    congr 1
    abel
  have hsplit_cent :
      centeredStatistic D (gibbsMetriplecticFlow H_eq σ (H t) hH) =
        gibbsUnitaryVectorField H_eq (H t) -
          centeredStatistic D (D.kuboMoriTransform (D.rho - σ)) := by
    have hflow_eq :
        gibbsMetriplecticFlow H_eq σ (H t) hH =
          gibbsUnitaryVectorField H_eq (H t) + -(D.kuboMoriTransform (D.rho - σ)) := rfl
    rw [hflow_eq]
    have htr_add :
        finiteOperatorTrace
            (D.rho * (gibbsUnitaryVectorField H_eq (H t) + -(D.kuboMoriTransform (D.rho - σ)))) =
          finiteOperatorTrace (D.rho * gibbsUnitaryVectorField H_eq (H t)) -
            finiteOperatorTrace (D.rho * D.kuboMoriTransform (D.rho - σ)) := by
      rw [mul_add]
      have hm : D.rho.comp (-(D.kuboMoriTransform (D.rho - σ))) =
          -(D.rho.comp (D.kuboMoriTransform (D.rho - σ))) :=
        ContinuousLinearMap.comp_neg _ _
      change finiteOperatorTrace
          (D.rho * gibbsUnitaryVectorField H_eq (H t) +
            D.rho.comp (-(D.kuboMoriTransform (D.rho - σ)))) = _
      rw [hm]
      change (finiteOperatorTraceLinear n)
          (D.rho * gibbsUnitaryVectorField H_eq (H t) +
            -(D.rho * D.kuboMoriTransform (D.rho - σ))) =
        (finiteOperatorTraceLinear n) (D.rho * gibbsUnitaryVectorField H_eq (H t)) -
          (finiteOperatorTraceLinear n) (D.rho * D.kuboMoriTransform (D.rho - σ))
      rw [map_add, map_neg]
      rfl
    unfold centeredStatistic expectationReal
    rw [htr_add, htr_unitary, zero_sub, Complex.neg_re]
    apply ContinuousLinearMap.ext
    intro x
    ext i
    simp [real_smul_eq_complex_smul]
    ring
  have hfinal_eq :
      D.kuboMoriTransform (centeredStatistic D (gibbsMetriplecticFlow H_eq σ (H t) hH)) =
        gibbsUnitaryVectorField H_eq D.rho -
          D.kuboMoriTransform (centeredStatistic D (D.kuboMoriTransform (D.rho - σ))) := by
    rw [hsplit_cent]
    change D.kuboMoriTransformCLM hpow
        (gibbsUnitaryVectorField H_eq (H t) -
          centeredStatistic D (D.kuboMoriTransform (D.rho - σ))) = _
    rw [map_sub, D.kuboMoriTransformCLM_apply, D.kuboMoriTransformCLM_apply,
      hkmt_unitary]
  rw [hfinal_eq] at hρ_deriv
  exact hρ_deriv

/-- Mapping a natural-gradient `H(t)` trajectory (`H'(t) = -i [H_eq, H(t)] - (H(t) - H_eq)`)
to the exact primal metriplectic `ρ(t)` trajectory
`ρ'(t) = -i [H_eq, ρ(t)] - K_{D_t}(centeredStatistic D_t (H(t) - H_eq))`. -/
theorem hasDerivAt_normalizedExponential_naturalGradientMetriplectic
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq : FiniteOperatorAlgebra n) (hH_eq : IsSelfAdjoint H_eq)
    (H : ℝ → FiniteOperatorAlgebra n) {t : ℝ} (hH : IsSelfAdjoint (H t))
    (hderiv :
      HasDerivAt H (gibbsUnitaryVectorField H_eq (H t) - (H t - H_eq)) t) :
    HasDerivAt (fun s => normalizedExponential (H s))
      (gibbsUnitaryVectorField H_eq
          (faithfulGibbsDensity (H t) hH
            (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).rho -
        (faithfulGibbsDensity (H t) hH
            (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).kuboMoriTransform
          (centeredStatistic
            (faithfulGibbsDensity (H t) hH
              (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH))
            (H t - H_eq))) t := by
  let hZ := tracedExponential_re_pos_of_isSelfAdjoint (H t) hH
  let D := faithfulGibbsDensity (H t) hH hZ
  let hpow := continuous_faithfulGibbsDensity_rpow (H t) hH hZ
  have hflow_sa :
      IsSelfAdjoint (gibbsUnitaryVectorField H_eq (H t) - (H t - H_eq)) := by
    change ContinuousLinearMap.adjoint (gibbsUnitaryVectorField H_eq (H t) - (H t - H_eq)) =
      gibbsUnitaryVectorField H_eq (H t) - (H t - H_eq)
    rw [map_sub, map_sub]
    change star (gibbsUnitaryVectorField H_eq (H t)) - (star (H t) - star H_eq) =
      gibbsUnitaryVectorField H_eq (H t) - (H t - H_eq)
    rw [(isSelfAdjoint_gibbsUnitaryVectorField hH_eq hH).star_eq,
      hH.star_eq, hH_eq.star_eq]
  have hρ_deriv :=
    hasDerivAt_normalizedExponential_centered H hH hflow_sa hderiv
  have hcomm_ρH : Commute D.rho (H t) := by
    rw [faithfulGibbsDensity_rho_eq_normalizedExponential (H t) hH hZ]
    exact commute_normalizedExponential_self (H t)
  have htr_unitary :
      finiteOperatorTrace (D.rho * gibbsUnitaryVectorField H_eq (H t)) = 0 := by
    unfold gibbsUnitaryVectorField
    rw [mul_smul_comm, finiteOperatorTrace_complex_smul,
      finiteOperatorTrace_mul_commutator_eq_zero_of_commute D.rho (H t) H_eq hcomm_ρH,
      mul_zero]
  have hexp_unitary : expectationReal D (gibbsUnitaryVectorField H_eq (H t)) = 0 := by
    simp [expectationReal, htr_unitary]
  have hcent_unitary :
      centeredStatistic D (gibbsUnitaryVectorField H_eq (H t)) =
        gibbsUnitaryVectorField H_eq (H t) := by
    unfold centeredStatistic
    have hzero : (0 : ℂ) • (1 : FiniteOperatorAlgebra n) = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      ext i
      simp
    rw [hexp_unitary, real_smul_eq_complex_smul, Complex.ofReal_zero, hzero, sub_zero]
  have hkmt_unitary :
      D.kuboMoriTransform (gibbsUnitaryVectorField H_eq (H t)) =
        gibbsUnitaryVectorField H_eq D.rho := by
    unfold gibbsUnitaryVectorField
    change D.kuboMoriTransformCLM hpow (-Complex.I • (H_eq * H t - H t * H_eq)) =
      -Complex.I • (H_eq * D.rho - D.rho * H_eq)
    rw [(D.kuboMoriTransformCLM hpow).map_smul,
      D.kuboMoriTransformCLM_apply]
    have hneg_comm : H_eq * H t - H t * H_eq = -(H t * H_eq - H_eq * H t) := by abel
    have hkmt_neg :
        D.kuboMoriTransform (-(H t * H_eq - H_eq * H t)) =
          -D.kuboMoriTransform (H t * H_eq - H_eq * H t) := by
      change D.kuboMoriTransformCLM hpow (-(H t * H_eq - H_eq * H t)) =
        -D.kuboMoriTransformCLM hpow (H t * H_eq - H_eq * H t)
      exact map_neg (D.kuboMoriTransformCLM hpow) _
    rw [hneg_comm, hkmt_neg,
      kuboMoriTransform_commutator_eq_commutator_rho (H t) H_eq hH hZ]
    congr 1
    abel
  have hsplit_cent :
      centeredStatistic D (gibbsUnitaryVectorField H_eq (H t) - (H t - H_eq)) =
        gibbsUnitaryVectorField H_eq (H t) - centeredStatistic D (H t - H_eq) := by
    have htr_sub :
        finiteOperatorTrace
            (D.rho * (gibbsUnitaryVectorField H_eq (H t) - (H t - H_eq))) =
          finiteOperatorTrace (D.rho * gibbsUnitaryVectorField H_eq (H t)) -
            finiteOperatorTrace (D.rho * (H t - H_eq)) := by
      rw [mul_sub]
      exact (finiteOperatorTraceLinear n).map_sub _ _
    unfold centeredStatistic expectationReal
    rw [htr_sub, htr_unitary, zero_sub, Complex.neg_re]
    apply ContinuousLinearMap.ext
    intro x
    ext i
    simp [real_smul_eq_complex_smul]
    ring
  have hfinal_eq :
      D.kuboMoriTransform
          (centeredStatistic D (gibbsUnitaryVectorField H_eq (H t) - (H t - H_eq))) =
        gibbsUnitaryVectorField H_eq D.rho -
          D.kuboMoriTransform (centeredStatistic D (H t - H_eq)) := by
    rw [hsplit_cent]
    change D.kuboMoriTransformCLM hpow
        (gibbsUnitaryVectorField H_eq (H t) - centeredStatistic D (H t - H_eq)) = _
    rw [map_sub, D.kuboMoriTransformCLM_apply, D.kuboMoriTransformCLM_apply,
      hkmt_unitary]
  rw [hfinal_eq] at hρ_deriv
  exact hρ_deriv

end Layer2GibbsBKMTrajectory

/-! ## Layer 3: Primal Matrix Trajectory Upgrade (`BKMOnsagerMobilityBridge`) -/

section Layer3MatrixEquivAndGeneral

open Matrix
open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.BKMOnsagerMobilityBridge

private theorem matrixOp_add_local {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    CblinfunMatrix.matrixOp (A + B) =
      CblinfunMatrix.matrixOp A + CblinfunMatrix.matrixOp B := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp [CblinfunMatrix.matrixOp]

private theorem matrixOp_complex_smul_local {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    CblinfunMatrix.matrixOp (c • A) = c • CblinfunMatrix.matrixOp A := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp [CblinfunMatrix.matrixOp]

/-- `ℝ`-linear map `matrixOfOp : FiniteOperatorAlgebra n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ`. -/
noncomputable def matrixOfOpLinearℝ (n : ℕ) :
    FiniteOperatorAlgebra n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := CblinfunMatrix.matrixOfOp
  map_add' := CblinfunMatrix.matrixOfOp_add
  map_smul' r A := by
    simpa [RingHom.id_apply] using matrixOfOp_real_smul r A

@[simp] theorem matrixOfOpLinearℝ_apply {n : ℕ} (A : FiniteOperatorAlgebra n) :
    matrixOfOpLinearℝ n A = CblinfunMatrix.matrixOfOp A := rfl

/-- `ℝ`-linear map `matrixOp : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] FiniteOperatorAlgebra n`. -/
noncomputable def matrixOpLinearℝ (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] FiniteOperatorAlgebra n where
  toFun := CblinfunMatrix.matrixOp
  map_add' := matrixOp_add_local
  map_smul' r A := by
    have h1 : (r : ℝ) • A = (r : ℂ) • A := by
      ext i j
      simp [Complex.real_smul]
    rw [h1, matrixOp_complex_smul_local, ← real_smul_eq_complex_smul]
    rfl

@[simp] theorem matrixOpLinearℝ_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    matrixOpLinearℝ n M = CblinfunMatrix.matrixOp M := rfl

/-- `ℝ`-linear equivalence between `FiniteOperatorAlgebra n` and `Matrix (Fin n) (Fin n) ℂ`. -/
noncomputable def matrixOfOpEquivℝ (n : ℕ) :
    FiniteOperatorAlgebra n ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toLinearMap := matrixOfOpLinearℝ n
  invFun := CblinfunMatrix.matrixOp
  left_inv := CblinfunMatrix.matrixOp_matrixOfOp
  right_inv := CblinfunMatrix.matrixOfOp_matrixOp

theorem finiteDimensional_real_finiteOperatorAlgebra (n : ℕ) :
    FiniteDimensional ℝ (FiniteOperatorAlgebra n) :=
  Module.Finite.equiv (matrixOfOpEquivℝ n).symm

section ArbitraryMatrixNorm

variable {n : ℕ}
variable [NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ)]
variable [NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ)]

/-- Continuous `ℝ`-linear map `matrixOfOp` for an arbitrary real normed
structure on `Matrix (Fin n) (Fin n) ℂ`. -/
noncomputable def matrixOfOpCLMℝ (n : ℕ)
    [NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ)]
    [NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ)] :
    FiniteOperatorAlgebra n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  letI : FiniteDimensional ℝ (FiniteOperatorAlgebra n) :=
    finiteDimensional_real_finiteOperatorAlgebra n
  (matrixOfOpLinearℝ n).toContinuousLinearMap

@[simp] theorem matrixOfOpCLMℝ_apply (A : FiniteOperatorAlgebra n) :
    matrixOfOpCLMℝ n A = CblinfunMatrix.matrixOfOp A := rfl

/-- Continuous `ℝ`-linear map `matrixOp` for an arbitrary real normed
structure on `Matrix (Fin n) (Fin n) ℂ`. -/
noncomputable def matrixOpCLMℝ (n : ℕ)
    [NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ)]
    [NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ)] :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] FiniteOperatorAlgebra n :=
  (matrixOpLinearℝ n).toContinuousLinearMap

@[simp] theorem matrixOpCLMℝ_apply (M : Matrix (Fin n) (Fin n) ℂ) :
    matrixOpCLMℝ n M = CblinfunMatrix.matrixOp M := rfl

end ArbitraryMatrixNorm

section Layer3MatrixFreeEnergy

open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

/-- Trajectory Fréchet chain-rule rate for any `MetriplecticDissipativeSystem`
with `matrixKuboMoriMobility`: `HasDerivAt (Φ ∘ rho) (freeEnergyRate (sys t)) t`. -/
theorem hasDerivAt_freeEnergy_of_matrixKuboMoriMobility
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (dΦ : ℝ → (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ))
    (rho : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (sys : ℝ → MetriplecticDissipation.MetriplecticDissipativeSystem (Fin n))
    {t : ℝ}
    (hrho : HasDerivAt rho (MetriplecticDissipation.stateEvolution (sys t)) t)
    (hΦ : HasFDerivAt Φ (dΦ t) (rho t))
    (hdΦ : ∀ V, dΦ t V = (Matrix.trace (star (sys t).grad_F * V)).re) :
    HasDerivAt (fun s => Φ (rho s)) (MetriplecticDissipation.freeEnergyRate (sys t)) t := by
  have hcomp := hΦ.comp_hasDerivAt t hrho
  rw [hdΦ] at hcomp
  exact hcomp

/-- Nonpositive `deriv` along a matrix BKM metriplectic trajectory when
`grad_F = A` is self-adjoint and commutes with `sys.H`. -/
theorem deriv_freeEnergy_nonpos_of_matrixKuboMoriMobility
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (dΦ : ℝ → (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ))
    (rho : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (sys : ℝ → MetriplecticDissipation.MetriplecticDissipativeSystem (Fin n))
    (D : ℝ → FaithfulDensityOperator n)
    (hD : ∀ t, Continuous (D t).rpow)
    {t : ℝ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : star A = A)
    (hgrad : (sys t).grad_F = A)
    (hmob : ∀ X, (sys t).Onsager X = matrixKuboMoriMobility (D t) (hD t) X)
    (hcomm : A * (sys t).H = (sys t).H * A)
    (hrho : HasDerivAt rho (MetriplecticDissipation.stateEvolution (sys t)) t)
    (hΦ : HasFDerivAt Φ (dΦ t) (rho t))
    (hdΦ : ∀ V, dΦ t V = (Matrix.trace (star (sys t).grad_F * V)).re) :
    deriv (fun s => Φ (rho s)) t ≤ 0 := by
  rw [(hasDerivAt_freeEnergy_of_matrixKuboMoriMobility Φ dΦ rho sys hrho hΦ hdΦ).deriv]
  exact freeEnergy_rate_nonpos_of_matrixKuboMoriMobility
    (D t) (hD t) (sys t) A hA hgrad hmob hcomm

/-- Convex-interval `AntitoneOn` monotonicity for a matrix BKM metriplectic
trajectory when `grad_F` is self-adjoint and commutes with `(sys t).H`. -/
theorem antitoneOn_freeEnergy_of_matrixKuboMoriMobility
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (dΦ : ℝ → (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ))
    (rho : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (sys : ℝ → MetriplecticDissipation.MetriplecticDissipativeSystem (Fin n))
    (D : ℝ → FaithfulDensityOperator n)
    (hD : ∀ t, Continuous (D t).rpow)
    {I : Set ℝ} (hI : Convex ℝ I)
    (hcont : ContinuousOn (fun t => Φ (rho t)) I)
    (hA : ∀ t ∈ interior I, star (sys t).grad_F = (sys t).grad_F)
    (hmob : ∀ t ∈ interior I, ∀ X,
      (sys t).Onsager X = matrixKuboMoriMobility (D t) (hD t) X)
    (hcomm : ∀ t ∈ interior I, (sys t).grad_F * (sys t).H = (sys t).H * (sys t).grad_F)
    (hrho : ∀ t ∈ interior I,
      HasDerivAt rho (MetriplecticDissipation.stateEvolution (sys t)) t)
    (hΦ : ∀ t ∈ interior I, HasFDerivAt Φ (dΦ t) (rho t))
    (hdΦ : ∀ t ∈ interior I, ∀ V, dΦ t V = (Matrix.trace (star (sys t).grad_F * V)).re) :
    AntitoneOn (fun t => Φ (rho t)) I := by
  apply antitoneOn_of_deriv_nonpos hI hcont
  · intro t ht
    exact (hasDerivAt_freeEnergy_of_matrixKuboMoriMobility Φ dΦ rho sys
      (hrho t ht) (hΦ t ht) (hdΦ t ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact deriv_freeEnergy_nonpos_of_matrixKuboMoriMobility Φ dΦ rho sys D hD
      (sys t).grad_F (hA t ht) rfl (hmob t ht) (hcomm t ht)
      (hrho t ht) (hΦ t ht) (hdΦ t ht)

/-- Nonpositive `deriv` along a matrix BKM metriplectic trajectory when
`(sys t).H` commutes with `(sys t).rho`. -/
theorem deriv_freeEnergy_nonpos_of_matrixKuboMoriMobility_of_commuting_state
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (dΦ : ℝ → (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ))
    (rho : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (sys : ℝ → MetriplecticDissipation.MetriplecticDissipativeSystem (Fin n))
    (D : ℝ → FaithfulDensityOperator n)
    (hD : ∀ t, Continuous (D t).rpow)
    {t : ℝ}
    (hmob : ∀ X, (sys t).Onsager X = matrixKuboMoriMobility (D t) (hD t) X)
    (hHrho : (sys t).H * (sys t).rho = (sys t).rho * (sys t).H)
    (hrho : HasDerivAt rho (MetriplecticDissipation.stateEvolution (sys t)) t)
    (hΦ : HasFDerivAt Φ (dΦ t) (rho t))
    (hdΦ : ∀ V, dΦ t V = (Matrix.trace (star (sys t).grad_F * V)).re) :
    deriv (fun s => Φ (rho s)) t ≤ 0 := by
  rw [(hasDerivAt_freeEnergy_of_matrixKuboMoriMobility Φ dΦ rho sys hrho hΦ hdΦ).deriv]
  exact freeEnergy_rate_nonpos_of_matrixKuboMoriMobility_of_commuting_state
    (D t) (hD t) (sys t) hmob hHrho

/-- Convex-interval `AntitoneOn` monotonicity for a matrix BKM metriplectic
trajectory when `(sys t).H` commutes with `(sys t).rho`. -/
theorem antitoneOn_freeEnergy_of_matrixKuboMoriMobility_of_commuting_state
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (dΦ : ℝ → (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ))
    (rho : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (sys : ℝ → MetriplecticDissipation.MetriplecticDissipativeSystem (Fin n))
    (D : ℝ → FaithfulDensityOperator n)
    (hD : ∀ t, Continuous (D t).rpow)
    {I : Set ℝ} (hI : Convex ℝ I)
    (hcont : ContinuousOn (fun t => Φ (rho t)) I)
    (hmob : ∀ t ∈ interior I, ∀ X,
      (sys t).Onsager X = matrixKuboMoriMobility (D t) (hD t) X)
    (hHrho : ∀ t ∈ interior I, (sys t).H * (sys t).rho = (sys t).rho * (sys t).H)
    (hrho : ∀ t ∈ interior I,
      HasDerivAt rho (MetriplecticDissipation.stateEvolution (sys t)) t)
    (hΦ : ∀ t ∈ interior I, HasFDerivAt Φ (dΦ t) (rho t))
    (hdΦ : ∀ t ∈ interior I, ∀ V, dΦ t V = (Matrix.trace (star (sys t).grad_F * V)).re) :
    AntitoneOn (fun t => Φ (rho t)) I := by
  apply antitoneOn_of_deriv_nonpos hI hcont
  · intro t ht
    exact (hasDerivAt_freeEnergy_of_matrixKuboMoriMobility Φ dΦ rho sys
      (hrho t ht) (hΦ t ht) (hdΦ t ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact deriv_freeEnergy_nonpos_of_matrixKuboMoriMobility_of_commuting_state
      Φ dΦ rho sys D hD (hmob t ht) (hHrho t ht)
      (hrho t ht) (hΦ t ht) (hdΦ t ht)

/-- Nonpositive `deriv` along a matrix BKM metriplectic trajectory under direct
reversible orthogonality `(Tr(grad_F* (-i[H, ρ]))).re = 0` (covering genuinely
noncommuting `[H, ρ] ≠ 0` and `[grad_F, H] ≠ 0` trajectories). -/
theorem deriv_freeEnergy_nonpos_of_matrixKuboMoriMobility_of_reversible_orthogonal
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (dΦ : ℝ → (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ))
    (rho : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (sys : ℝ → MetriplecticDissipation.MetriplecticDissipativeSystem (Fin n))
    (D : ℝ → FaithfulDensityOperator n)
    (hD : ∀ t, Continuous (D t).rpow)
    {t : ℝ}
    (hmob : ∀ X, (sys t).Onsager X = matrixKuboMoriMobility (D t) (hD t) X)
    (hrev :
      (Matrix.trace (star (sys t).grad_F *
        (-Complex.I • ((sys t).H * (sys t).rho - (sys t).rho * (sys t).H)))).re = 0)
    (hrho : HasDerivAt rho (MetriplecticDissipation.stateEvolution (sys t)) t)
    (hΦ : HasFDerivAt Φ (dΦ t) (rho t))
    (hdΦ : ∀ V, dΦ t V = (Matrix.trace (star (sys t).grad_F * V)).re) :
    deriv (fun s => Φ (rho s)) t ≤ 0 := by
  rw [(hasDerivAt_freeEnergy_of_matrixKuboMoriMobility Φ dΦ rho sys hrho hΦ hdΦ).deriv]
  have h_diss : ∀ B : Matrix (Fin n) (Fin n) ℂ,
      0 ≤ (Matrix.trace (star B * (sys t).Onsager B)).re := by
    intro B
    rw [hmob B]
    exact matrixKuboMoriMobility_trace_nonneg (D t) (hD t) B
  exact MetriplecticDissipation.freeEnergy_rate_nonpos (sys t) h_diss hrev

/-- Convex-interval `AntitoneOn` monotonicity under direct reversible
orthogonality `(Tr(grad_F* (-i[H, ρ]))).re = 0`. -/
theorem antitoneOn_freeEnergy_of_matrixKuboMoriMobility_of_reversible_orthogonal
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (dΦ : ℝ → (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ))
    (rho : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (sys : ℝ → MetriplecticDissipation.MetriplecticDissipativeSystem (Fin n))
    (D : ℝ → FaithfulDensityOperator n)
    (hD : ∀ t, Continuous (D t).rpow)
    {I : Set ℝ} (hI : Convex ℝ I)
    (hcont : ContinuousOn (fun t => Φ (rho t)) I)
    (hmob : ∀ t ∈ interior I, ∀ X,
      (sys t).Onsager X = matrixKuboMoriMobility (D t) (hD t) X)
    (hrev : ∀ t ∈ interior I,
      (Matrix.trace (star (sys t).grad_F *
        (-Complex.I • ((sys t).H * (sys t).rho - (sys t).rho * (sys t).H)))).re = 0)
    (hrho : ∀ t ∈ interior I,
      HasDerivAt rho (MetriplecticDissipation.stateEvolution (sys t)) t)
    (hΦ : ∀ t ∈ interior I, HasFDerivAt Φ (dΦ t) (rho t))
    (hdΦ : ∀ t ∈ interior I, ∀ V, dΦ t V = (Matrix.trace (star (sys t).grad_F * V)).re) :
    AntitoneOn (fun t => Φ (rho t)) I := by
  apply antitoneOn_of_deriv_nonpos hI hcont
  · intro t ht
    exact (hasDerivAt_freeEnergy_of_matrixKuboMoriMobility Φ dΦ rho sys
      (hrho t ht) (hΦ t ht) (hdΦ t ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact deriv_freeEnergy_nonpos_of_matrixKuboMoriMobility_of_reversible_orthogonal
      Φ dΦ rho sys D hD (hmob t ht) (hrev t ht)
      (hrho t ht) (hΦ t ht) (hdΦ t ht)

end Layer3MatrixFreeEnergy

end Layer3MatrixEquivAndGeneral

/-! ## Concrete Layer 3 Instantiation: Evolving `rho t = matrixOfOp (normalizedExponential (H t))` -/

section Layer3ConcreteGibbsInstantiation

open Matrix
open scoped Matrix.Norms.L2Operator
open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.BKMOnsagerMobilityBridge

private theorem matrixOfOp_sub_local {n : ℕ} (A B : FiniteOperatorAlgebra n) :
    CblinfunMatrix.matrixOfOp (A - B) =
      CblinfunMatrix.matrixOfOp A - CblinfunMatrix.matrixOfOp B :=
  (LinearMap.toMatrix (CblinfunMatrix.ketBasis (Fin n))
    (CblinfunMatrix.ketBasis (Fin n))).map_sub A.toLinearMap B.toLinearMap

private theorem matrixOfOp_mul_local {n : ℕ} (A B : FiniteOperatorAlgebra n) :
    CblinfunMatrix.matrixOfOp (A * B) =
      CblinfunMatrix.matrixOfOp A * CblinfunMatrix.matrixOfOp B :=
  CblinfunMatrix.matrixOfOp_comp A B

/-- State-dependent matrix `MetriplecticDissipativeSystem` with evolving
density `rho t = matrixOfOp D_t.rho` identical to the mobility density `D_t`
and `D_t`-centered gradient `grad_F = matrixOfOp (centeredStatistic D_t (D_t.rho - σ))`. -/
noncomputable def evolvingGibbsMetriplecticSystem
    {n : ℕ} [Nonempty (Fin n)] (H_eq σ H_t : FiniteOperatorAlgebra n) (hH_t : IsSelfAdjoint H_t) :
    MetriplecticDissipation.MetriplecticDissipativeSystem (Fin n) :=
  let hZ : 0 < gibbsPartitionReal H_t :=
    (tracedExponential_re_pos_of_isSelfAdjoint H_t hH_t : 0 < gibbsPartitionReal H_t);
  let D := faithfulGibbsDensity H_t hH_t hZ;
  let hD := continuous_faithfulGibbsDensity_rpow H_t hH_t hZ;
  { rho := CblinfunMatrix.matrixOfOp D.rho
    H := CblinfunMatrix.matrixOfOp H_eq
    grad_F := CblinfunMatrix.matrixOfOp (centeredStatistic D (D.rho - σ))
    Onsager := matrixKuboMoriMobility D hD }

/-- Transporting a natural-gradient `H(t)` trajectory
`H'(t) = -i [H_eq, H(t)] - (D_t.rho - σ)` (or `gibbsUnitaryVectorField H_eq (H t) - (D_t.rho - σ)`)
to `rho t := matrixOfOp (normalizedExponential (H t))` yields
`HasDerivAt rho (stateEvolution (evolvingGibbsMetriplecticSystem H_eq σ (H t) hH)) t`
with the mobility density `D_t` equal to the evolving state `rho t`! -/
theorem hasDerivAt_matrixNormalizedExponential_metriplectic
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n) (hH_eq : IsSelfAdjoint H_eq) (hσ : IsSelfAdjoint σ)
    (H : ℝ → FiniteOperatorAlgebra n) {t : ℝ} (hH : IsSelfAdjoint (H t))
    (hderiv :
      HasDerivAt H
        (gibbsUnitaryVectorField H_eq (H t) -
          ((faithfulGibbsDensity (H t) hH
              (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).rho - σ)) t) :
    HasDerivAt (fun s => CblinfunMatrix.matrixOfOp (normalizedExponential (H s)))
      (MetriplecticDissipation.stateEvolution
        (evolvingGibbsMetriplecticSystem H_eq σ (H t) hH)) t := by
  let hZ := tracedExponential_re_pos_of_isSelfAdjoint (H t) hH
  let D := faithfulGibbsDensity (H t) hH hZ
  let hD := continuous_faithfulGibbsDensity_rpow (H t) hH hZ
  have hflow_sa :
      IsSelfAdjoint (gibbsUnitaryVectorField H_eq (H t) - (D.rho - σ)) := by
    change ContinuousLinearMap.adjoint (gibbsUnitaryVectorField H_eq (H t) - (D.rho - σ)) =
      gibbsUnitaryVectorField H_eq (H t) - (D.rho - σ)
    rw [map_sub]
    change star (gibbsUnitaryVectorField H_eq (H t)) - star (D.rho - σ) =
      gibbsUnitaryVectorField H_eq (H t) - (D.rho - σ)
    rw [(isSelfAdjoint_gibbsUnitaryVectorField hH_eq hH).star_eq,
      (D.strictlyPositive.isSelfAdjoint.sub hσ).star_eq]
  have hρ_deriv := hasDerivAt_normalizedExponential_centered H hH hflow_sa hderiv
  have hcomm_ρH : Commute D.rho (H t) := by
    rw [faithfulGibbsDensity_rho_eq_normalizedExponential (H t) hH hZ]
    exact commute_normalizedExponential_self (H t)
  have htr_unitary :
      finiteOperatorTrace (D.rho * gibbsUnitaryVectorField H_eq (H t)) = 0 := by
    unfold gibbsUnitaryVectorField
    rw [mul_smul_comm, finiteOperatorTrace_complex_smul,
      finiteOperatorTrace_mul_commutator_eq_zero_of_commute D.rho (H t) H_eq hcomm_ρH,
      mul_zero]
  have hexp_unitary : expectationReal D (gibbsUnitaryVectorField H_eq (H t)) = 0 := by
    simp [expectationReal, htr_unitary]
  have hcent_unitary :
      centeredStatistic D (gibbsUnitaryVectorField H_eq (H t)) =
        gibbsUnitaryVectorField H_eq (H t) := by
    unfold centeredStatistic
    have hzero : (0 : ℂ) • (1 : FiniteOperatorAlgebra n) = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      ext i
      simp
    rw [hexp_unitary, real_smul_eq_complex_smul, Complex.ofReal_zero, hzero, sub_zero]
  have hkmt_unitary :
      D.kuboMoriTransform (gibbsUnitaryVectorField H_eq (H t)) =
        gibbsUnitaryVectorField H_eq D.rho := by
    let hpow := hD
    unfold gibbsUnitaryVectorField
    change D.kuboMoriTransformCLM hpow (-Complex.I • (H_eq * H t - H t * H_eq)) =
      -Complex.I • (H_eq * D.rho - D.rho * H_eq)
    rw [(D.kuboMoriTransformCLM hpow).map_smul,
      D.kuboMoriTransformCLM_apply]
    have hneg_comm : H_eq * H t - H t * H_eq = -(H t * H_eq - H_eq * H t) := by abel
    have hkmt_neg :
        D.kuboMoriTransform (-(H t * H_eq - H_eq * H t)) =
          -D.kuboMoriTransform (H t * H_eq - H_eq * H t) := by
      change D.kuboMoriTransformCLM hpow (-(H t * H_eq - H_eq * H t)) =
        -D.kuboMoriTransformCLM hpow (H t * H_eq - H_eq * H t)
      exact map_neg (D.kuboMoriTransformCLM hpow) _
    rw [hneg_comm, hkmt_neg,
      kuboMoriTransform_commutator_eq_commutator_rho (H t) H_eq hH hZ]
    congr 1
    abel
  have hsplit_cent :
      centeredStatistic D (gibbsUnitaryVectorField H_eq (H t) - (D.rho - σ)) =
        gibbsUnitaryVectorField H_eq (H t) - centeredStatistic D (D.rho - σ) := by
    have htr_sub :
        finiteOperatorTrace
            (D.rho * (gibbsUnitaryVectorField H_eq (H t) - (D.rho - σ))) =
          finiteOperatorTrace (D.rho * gibbsUnitaryVectorField H_eq (H t)) -
            finiteOperatorTrace (D.rho * (D.rho - σ)) := by
      rw [mul_sub]
      exact (finiteOperatorTraceLinear n).map_sub _ _
    unfold centeredStatistic expectationReal
    rw [htr_sub, htr_unitary, zero_sub, Complex.neg_re]
    apply ContinuousLinearMap.ext
    intro x
    ext i
    simp [real_smul_eq_complex_smul]
    ring
  have hcomp := (matrixOfOpCLMℝ n).hasFDerivAt.comp_hasDerivAt t hρ_deriv
  have hev_eq :
      (matrixOfOpCLMℝ n)
          (D.kuboMoriTransform
            (centeredStatistic D (gibbsUnitaryVectorField H_eq (H t) - (D.rho - σ)))) =
        MetriplecticDissipation.stateEvolution
          (evolvingGibbsMetriplecticSystem H_eq σ (H t) hH) := by
    rw [matrixOfOpCLMℝ_apply]
    dsimp [MetriplecticDissipation.stateEvolution,
      MetriplecticDissipation.unitaryFlow, MetriplecticDissipation.commutator,
      evolvingGibbsMetriplecticSystem, matrixKuboMoriMobility]
    rw [hsplit_cent]
    have hkmt_sub :
        D.kuboMoriTransform
            (gibbsUnitaryVectorField H_eq (H t) - centeredStatistic D (D.rho - σ)) =
          D.kuboMoriTransform (gibbsUnitaryVectorField H_eq (H t)) -
            D.kuboMoriTransform (centeredStatistic D (D.rho - σ)) := by
      change D.kuboMoriTransformCLM hD
          (gibbsUnitaryVectorField H_eq (H t) - centeredStatistic D (D.rho - σ)) =
        D.kuboMoriTransformCLM hD (gibbsUnitaryVectorField H_eq (H t)) -
          D.kuboMoriTransformCLM hD (centeredStatistic D (D.rho - σ))
      exact map_sub (D.kuboMoriTransformCLM hD) _ _
    rw [hkmt_sub, hkmt_unitary, matrixOfOp_sub_local,
      CblinfunMatrix.matrixOp_matrixOfOp]
    congr 1
    unfold gibbsUnitaryVectorField
    rw [matrixOfOp_complex_smul, matrixOfOp_sub_local,
      matrixOfOp_mul_local, matrixOfOp_mul_local]
  rw [hev_eq] at hcomp
  exact hcomp

/-- Trace-normalized Hilbert–Schmidt potential on `Matrix (Fin n) (Fin n) ℂ`:
`Φ_proj(M) = (1 / 2) Re Tr((N(M) - σ_M)* (N(M) - σ_M))` where `N(M) = (Tr M)⁻¹ • M`.
On the trace-1 self-adjoint Gibbs manifold `M = rho t`, its Fréchet gradient is
the exact `D_t`-centered operator `grad_F = matrixOfOp (centeredStatistic D_t (D_t.rho - σ))`. -/
noncomputable def traceNormalizedSquarePotential
    {n : ℕ} (σ_M M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  let N := (Matrix.trace M)⁻¹ • M
  (1 / 2 : ℝ) * (Matrix.trace (star (N - σ_M) * (N - σ_M))).re

private noncomputable def matrixHilbertSchmidtRealBilin {n : ℕ} :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ]
      (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ) where
  toFun X :=
    ({ toFun := fun Y => (Matrix.trace (star X * Y)).re
       map_add' := fun Y₁ Y₂ => by
         rw [mul_add, Matrix.trace_add, Complex.add_re]
       map_smul' := fun r Y => by
         change (Matrix.trace (star X * ((r : ℂ) • Y))).re =
           r * (Matrix.trace (star X * Y)).re
         rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul] } :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ).toContinuousLinearMap
  map_add' X₁ X₂ := by
    ext Y
    simp only [_root_.add_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
      AddHom.coe_mk, star_add, add_mul, Matrix.trace_add, Complex.add_re]
  map_smul' r X := by
    ext Y
    change (Matrix.trace (star ((r : ℂ) • X) * Y)).re =
      r * (Matrix.trace (star X * Y)).re
    rw [star_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

private noncomputable def matrixHilbertSchmidtRealCLM (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ]
      (Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ) :=
  matrixHilbertSchmidtRealBilin.toContinuousLinearMap

private theorem matrixHilbertSchmidtRealCLM_apply
    {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    matrixHilbertSchmidtRealCLM n X Y = (Matrix.trace (star X * Y)).re := rfl

private theorem matrixHilbertSchmidtRealCLM_symm
    {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    matrixHilbertSchmidtRealCLM n X Y = matrixHilbertSchmidtRealCLM n Y X := by
  simp only [matrixHilbertSchmidtRealCLM_apply]
  have hstar :
      star (Matrix.trace (star X * Y)) = Matrix.trace (star Y * X) := by
    calc
      star (Matrix.trace (star X * Y))
          = Matrix.trace (star X * Y)ᴴ := by
              rw [Matrix.trace_conjTranspose]
      _ = Matrix.trace (star (star X * Y)) := rfl
      _ = Matrix.trace (star Y * X) := by rw [star_mul, star_star]
  have hre := congrArg Complex.re hstar
  simpa [Complex.star_def] using hre

/-- Fréchet gradient covector for `traceNormalizedSquarePotential σ_M` at
a trace-1 Hermitian matrix `M` (`grad_M = (M - σ_M) - Re Tr(M * (M - σ_M)) • 1`). -/
noncomputable def traceNormalizedSquarePotentialFDeriv
    {n : ℕ} (σ_M M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
  matrixHilbertSchmidtRealCLM n
    ((M - σ_M) - (Matrix.trace (M * (M - σ_M))).re • (1 : Matrix (Fin n) (Fin n) ℂ))

/-- Exact Fréchet differentiability of `traceNormalizedSquarePotential σ_M` at
any trace-1 Hermitian matrix `M` (when `σ_M` is also Hermitian). -/
theorem hasFDerivAt_traceNormalizedSquarePotential
    {n : ℕ} (σ_M M : Matrix (Fin n) (Fin n) ℂ)
    (hσ : star σ_M = σ_M) (hM : star M = M) (htrM : Matrix.trace M = 1) :
    HasFDerivAt (traceNormalizedSquarePotential σ_M)
      (traceNormalizedSquarePotentialFDeriv σ_M M) M := by
  let trCLM : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap (Fin n) ℂ ℂ).toContinuousLinearMap
  have htr_ne : trCLM M ≠ 0 := by
    change Matrix.trace M ≠ 0
    rw [htrM]
    exact one_ne_zero
  have hinv :
      HasFDerivAt (fun X : Matrix (Fin n) (Fin n) ℂ => (Matrix.trace X)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℂ (-(trCLM M ^ 2)⁻¹)).comp trCLM) M :=
    (hasFDerivAt_inv htr_ne).comp M trCLM.hasFDerivAt
  have hid :
      HasFDerivAt (id : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
        (ContinuousLinearMap.id ℂ _) M :=
    hasFDerivAt_id M
  have hN_ℂ := hinv.fun_smul hid
  let dN_ℂ : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (trCLM M)⁻¹ • ContinuousLinearMap.id ℂ _ +
      ((ContinuousLinearMap.toSpanSingleton ℂ (-(trCLM M ^ 2)⁻¹)).comp trCLM).smulRight M
  have hu :
      HasFDerivAt (fun X => (Matrix.trace X)⁻¹ • X - σ_M)
        (dN_ℂ.restrictScalars ℝ) M :=
    (hN_ℂ.sub_const σ_M).restrictScalars ℝ
  have hB :
      HasFDerivAt
        (fun X =>
          matrixHilbertSchmidtRealCLM n
            ((Matrix.trace X)⁻¹ • X - σ_M)
            ((Matrix.trace X)⁻¹ • X - σ_M))
        (((matrixHilbertSchmidtRealCLM n ((Matrix.trace M)⁻¹ • M - σ_M)).comp
            (dN_ℂ.restrictScalars ℝ)) +
          ((matrixHilbertSchmidtRealCLM n).comp
            (dN_ℂ.restrictScalars ℝ)).flip ((Matrix.trace M)⁻¹ • M - σ_M)) M :=
    ((matrixHilbertSchmidtRealCLM n).hasFDerivAt.comp M hu).clm_apply hu
  have hΦ := hB.const_mul (1 / 2 : ℝ)
  have heq :
      (fun X => (1 / 2 : ℝ) *
        matrixHilbertSchmidtRealCLM n
          ((Matrix.trace X)⁻¹ • X - σ_M)
          ((Matrix.trace X)⁻¹ • X - σ_M)) =
      traceNormalizedSquarePotential σ_M := by
    funext X
    rfl
  rw [heq] at hΦ
  refine hΦ.congr_fderiv ?_
  ext V
  have hdN_apply : dN_ℂ V = V - Matrix.trace V • M := by
    simp [dN_ℂ, trCLM, htrM]
    rw [← sub_eq_add_neg]
  have hM_sub_star : star (M - σ_M) = M - σ_M := by
    rw [star_sub, hM, hσ]
  have htr_real :
      (Matrix.trace (M * (M - σ_M))).im = 0 := by
    have hstar :
        star (Matrix.trace (M * (M - σ_M))) = Matrix.trace (M * (M - σ_M)) := by
      calc
        star (Matrix.trace (M * (M - σ_M)))
            = Matrix.trace (M * (M - σ_M))ᴴ := by
                rw [Matrix.trace_conjTranspose]
        _ = Matrix.trace (star (M * (M - σ_M))) := rfl
        _ = Matrix.trace (star (M - σ_M) * star M) := by rw [star_mul]
        _ = Matrix.trace ((M - σ_M) * M) := by rw [hM_sub_star, hM]
        _ = Matrix.trace (M * (M - σ_M)) := Matrix.trace_mul_comm _ _
    have him := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at him
    linarith
  have htr_eq_re :
      Matrix.trace (M * (M - σ_M)) = ((Matrix.trace (M * (M - σ_M))).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using htr_real
  have hpair_eq :
      matrixHilbertSchmidtRealCLM n (M - σ_M) (V - Matrix.trace V • M) =
        traceNormalizedSquarePotentialFDeriv σ_M M V := by
    simp only [traceNormalizedSquarePotentialFDeriv, matrixHilbertSchmidtRealCLM_apply]
    have hgrad_star :
        star ((M - σ_M) - (Matrix.trace (M * (M - σ_M))).re • (1 : Matrix (Fin n) (Fin n) ℂ)) =
          (M - σ_M) - (Matrix.trace (M * (M - σ_M))).re • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [star_sub, hM_sub_star, star_smul, star_one, star_trivial]
    rw [hgrad_star, hM_sub_star, mul_sub, Matrix.trace_sub, Complex.sub_re]
    symm
    rw [sub_mul, sub_mul, Matrix.trace_sub, Matrix.trace_sub,
      Complex.sub_re, Complex.sub_re,
      Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    congr 1
    rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
    calc
      (Matrix.trace (M * (M - σ_M))).re * (Matrix.trace V).re
          = (((Matrix.trace (M * (M - σ_M))).re : ℂ) * Matrix.trace V).re := by
              rw [Complex.re_ofReal_mul]
      _ = (Matrix.trace (M * (M - σ_M)) * Matrix.trace V).re := by
              rw [← htr_eq_re]
      _ = (Matrix.trace V * Matrix.trace ((M - σ_M) * M)).re := by
              rw [Matrix.trace_mul_comm (M - σ_M) M, mul_comm]
  symm
  simp only [_root_.smul_apply, _root_.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_restrictScalars', smul_eq_mul,
    htrM, inv_one, one_smul, hdN_apply]
  rw [matrixHilbertSchmidtRealCLM_symm (M - σ_M) (V - Matrix.trace V • M),
    ← two_mul, ← mul_assoc, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul,
    matrixHilbertSchmidtRealCLM_symm (V - Matrix.trace V • M) (M - σ_M)]
  exact hpair_eq.symm

/-- Concrete trajectory-level Second Law on `rho t := matrixOfOp (normalizedExponential (H t))`
with evolving state-dependent mobility `D t := faithfulGibbsDensity (H t) ...` and
potential `traceNormalizedSquarePotential (matrixOfOp σ)`:
proves exact `HasDerivAt` equal to `freeEnergyRate (evolvingGibbsMetriplecticSystem ...)`
and `deriv ≤ 0`, WITHOUT assuming `[H_eq, H t] = 0`. -/
theorem hasDerivAt_traceNormalizedSquarePotential_gibbsTrajectory
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n) (hH_eq : IsSelfAdjoint H_eq)
    (hσ : IsSelfAdjoint σ) (hcomm_σ : Commute σ H_eq)
    (H : ℝ → FiniteOperatorAlgebra n) {t : ℝ} (hH : IsSelfAdjoint (H t))
    (hderiv :
      HasDerivAt H
        (gibbsUnitaryVectorField H_eq (H t) -
          ((faithfulGibbsDensity (H t) hH
              (tracedExponential_re_pos_of_isSelfAdjoint (H t) hH)).rho - σ)) t) :
    HasDerivAt
        (fun s =>
          traceNormalizedSquarePotential (CblinfunMatrix.matrixOfOp σ)
            (CblinfunMatrix.matrixOfOp (normalizedExponential (H s))))
        (MetriplecticDissipation.freeEnergyRate
          (evolvingGibbsMetriplecticSystem H_eq σ (H t) hH)) t ∧
      deriv
        (fun s =>
          traceNormalizedSquarePotential (CblinfunMatrix.matrixOfOp σ)
            (CblinfunMatrix.matrixOfOp (normalizedExponential (H s)))) t ≤ 0 := by
  have hZ : 0 < gibbsPartitionReal (H t) :=
    tracedExponential_re_pos_of_isSelfAdjoint (H t) hH
  let D := faithfulGibbsDensity (H t) hH hZ
  let hD := continuous_faithfulGibbsDensity_rpow (H t) hH hZ
  let rho : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun s => CblinfunMatrix.matrixOfOp (normalizedExponential (H s))
  let sys : ℝ → MetriplecticDissipation.MetriplecticDissipativeSystem (Fin n) := by
    classical
    exact fun s =>
      if hs : IsSelfAdjoint (H s) then
        evolvingGibbsMetriplecticSystem H_eq σ (H s) hs
      else
        evolvingGibbsMetriplecticSystem H_eq σ (H t) hH
  have hsys_t : sys t = evolvingGibbsMetriplecticSystem H_eq σ (H t) hH := by
    simp [sys, hH]
  have hrho_t : rho t = CblinfunMatrix.matrixOfOp D.rho := by
    simp [rho, D, faithfulGibbsDensity_rho_eq_normalizedExponential (H t) hH hZ]
  have htr_rho : Matrix.trace (rho t) = 1 := by
    rw [hrho_t]
    exact D.trace_one
  have hstar_rho : star (rho t) = rho t := by
    rw [hrho_t]
    have hD_sa : star D.rho = D.rho := D.strictlyPositive.isSelfAdjoint.star_eq
    change (CblinfunMatrix.matrixOfOp D.rho)ᴴ = CblinfunMatrix.matrixOfOp D.rho
    rw [← CblinfunMatrix.matrixOfOp_adjoint]
    exact congrArg CblinfunMatrix.matrixOfOp hD_sa
  have hstar_σ : star (CblinfunMatrix.matrixOfOp σ) = CblinfunMatrix.matrixOfOp σ := by
    change (CblinfunMatrix.matrixOfOp σ)ᴴ = CblinfunMatrix.matrixOfOp σ
    rw [← CblinfunMatrix.matrixOfOp_adjoint]
    exact congrArg CblinfunMatrix.matrixOfOp hσ.star_eq
  have hΦ :
      HasFDerivAt (traceNormalizedSquarePotential (CblinfunMatrix.matrixOfOp σ))
        (traceNormalizedSquarePotentialFDeriv (CblinfunMatrix.matrixOfOp σ) (rho t))
        (rho t) :=
    hasFDerivAt_traceNormalizedSquarePotential
      (CblinfunMatrix.matrixOfOp σ) (rho t) hstar_σ hstar_rho htr_rho
  have hdΦ :
      ∀ V,
        traceNormalizedSquarePotentialFDeriv (CblinfunMatrix.matrixOfOp σ) (rho t) V =
          (Matrix.trace (star (sys t).grad_F * V)).re := by
    intro V
    rw [hsys_t]
    have hgrad_eq :
        (evolvingGibbsMetriplecticSystem H_eq σ (H t) hH).grad_F =
          (rho t - CblinfunMatrix.matrixOfOp σ) -
            (Matrix.trace (rho t * (rho t - CblinfunMatrix.matrixOfOp σ))).re •
              (1 : Matrix (Fin n) (Fin n) ℂ) := by
      have htr_eq :
          finiteOperatorTrace (D.rho * (D.rho - σ)) =
            Matrix.trace (rho t * (rho t - CblinfunMatrix.matrixOfOp σ)) := by
        unfold finiteOperatorTrace
        rw [hrho_t, matrixOfOp_mul_local, matrixOfOp_sub_local]
      dsimp [evolvingGibbsMetriplecticSystem, centeredStatistic, expectationReal]
      rw [matrixOfOp_sub_local, matrixOfOp_sub_local, ← hrho_t, matrixOfOp_real_smul,
        show (1 : FiniteOperatorAlgebra n) =
          ContinuousLinearMap.id ℂ (FiniteHilbertSpace n) from rfl,
        CblinfunMatrix.matrixOfOp_id, htr_eq]
      congr 1
    have hgrad_star :
        star (evolvingGibbsMetriplecticSystem H_eq σ (H t) hH).grad_F =
          (evolvingGibbsMetriplecticSystem H_eq σ (H t) hH).grad_F := by
      rw [hgrad_eq, star_sub, star_sub, hstar_rho, hstar_σ, star_smul, star_one,
        star_trivial]
    rw [hgrad_star, hgrad_eq]
    simp only [traceNormalizedSquarePotentialFDeriv, matrixHilbertSchmidtRealCLM_apply]
    rw [← hgrad_eq, hgrad_star, hgrad_eq]
  have hrho_deriv :
      HasDerivAt rho (MetriplecticDissipation.stateEvolution (sys t)) t := by
    rw [hsys_t]
    exact hasDerivAt_matrixNormalizedExponential_metriplectic
      H_eq σ hH_eq hσ H hH hderiv
  have hrate :=
    hasDerivAt_freeEnergy_of_matrixKuboMoriMobility
      (traceNormalizedSquarePotential (CblinfunMatrix.matrixOfOp σ))
      (fun s => traceNormalizedSquarePotentialFDeriv (CblinfunMatrix.matrixOfOp σ) (rho s))
      rho sys hrho_deriv hΦ hdΦ
  rw [hsys_t] at hrate
  have hmob :
      ∀ X, (sys t).Onsager X = matrixKuboMoriMobility D hD X := by
    intro X
    rw [hsys_t]
    rfl
  have hrev :
      (Matrix.trace (star (sys t).grad_F *
        (-Complex.I • ((sys t).H * (sys t).rho - (sys t).rho * (sys t).H)))).re = 0 := by
    rw [hsys_t]
    have hgrad_sa :
        star (evolvingGibbsMetriplecticSystem H_eq σ (H t) hH).grad_F =
          (evolvingGibbsMetriplecticSystem H_eq σ (H t) hH).grad_F := by
      change (CblinfunMatrix.matrixOfOp (centeredStatistic D (D.rho - σ)))ᴴ =
        CblinfunMatrix.matrixOfOp (centeredStatistic D (D.rho - σ))
      rw [← CblinfunMatrix.matrixOfOp_adjoint]
      congr 1
      have hdiff_sa : IsSelfAdjoint (D.rho - σ) :=
        D.strictlyPositive.isSelfAdjoint.sub hσ
      have hcent_sa : IsSelfAdjoint (centeredStatistic D (D.rho - σ)) := by
        rw [isSelfAdjoint_iff]
        unfold centeredStatistic
        rw [real_smul_eq_complex_smul]
        change ContinuousLinearMap.adjoint
            ((D.rho - σ) - (expectationReal D (D.rho - σ) : ℂ) • (1 : FiniteOperatorAlgebra n)) =
          (D.rho - σ) - (expectationReal D (D.rho - σ) : ℂ) • (1 : FiniteOperatorAlgebra n)
        rw [map_sub]
        change star (D.rho - σ) -
            star ((expectationReal D (D.rho - σ) : ℂ) • (1 : FiniteOperatorAlgebra n)) =
          (D.rho - σ) - (expectationReal D (D.rho - σ) : ℂ) • (1 : FiniteOperatorAlgebra n)
        rw [hdiff_sa.star_eq, star_smul, star_one, Complex.star_def, Complex.conj_ofReal]
      exact hcent_sa.star_eq
    rw [hgrad_sa]
    dsimp [evolvingGibbsMetriplecticSystem]
    rw [← matrixOfOp_mul_local, ← matrixOfOp_mul_local,
      ← matrixOfOp_sub_local, ← matrixOfOp_complex_smul,
      ← matrixOfOp_mul_local]
    change (finiteOperatorTrace
      (centeredStatistic D (D.rho - σ) * (-Complex.I • (H_eq * D.rho - D.rho * H_eq)))).re = 0
    have h1 :
        finiteOperatorTrace (D.rho * (H_eq * D.rho - D.rho * H_eq)) = 0 :=
      finiteOperatorTrace_mul_commutator_eq_zero_of_commute D.rho D.rho H_eq (Commute.refl D.rho)
    have h2 :
        finiteOperatorTrace (σ * (H_eq * D.rho - D.rho * H_eq)) = 0 := by
      have h2a :=
        finiteOperatorTrace_mul_commutator_eq_zero_of_commute σ H_eq D.rho hcomm_σ
      have hneg : σ * (H_eq * D.rho - D.rho * H_eq) = -(σ * (D.rho * H_eq - H_eq * D.rho)) := by
        rw [mul_sub, mul_sub, neg_sub]
      change (finiteOperatorTraceLinear n) (σ * (H_eq * D.rho - D.rho * H_eq)) = 0
      rw [hneg, map_neg]
      change -(finiteOperatorTrace (σ * (D.rho * H_eq - H_eq * D.rho))) = 0
      rw [h2a, neg_zero]
    have h3 :
        finiteOperatorTrace ((1 : FiniteOperatorAlgebra n) * (H_eq * D.rho - D.rho * H_eq)) = 0 :=
      finiteOperatorTrace_mul_commutator_eq_zero_of_commute
        (1 : FiniteOperatorAlgebra n) D.rho H_eq (Commute.one_left D.rho)
    have hfull :
        finiteOperatorTrace
            (centeredStatistic D (D.rho - σ) * (-Complex.I • (H_eq * D.rho - D.rho * H_eq))) = 0 := by
      unfold centeredStatistic
      rw [mul_smul_comm, finiteOperatorTrace_complex_smul, real_smul_eq_complex_smul]
      change -Complex.I * (finiteOperatorTraceLinear n)
          (((D.rho - σ) - (expectationReal D (D.rho - σ) : ℂ) • (1 : FiniteOperatorAlgebra n)) *
            (H_eq * D.rho - D.rho * H_eq)) = 0
      rw [sub_mul, sub_mul, map_sub, map_sub, smul_mul_assoc]
      change -Complex.I *
          (((finiteOperatorTrace (D.rho * (H_eq * D.rho - D.rho * H_eq))) -
              finiteOperatorTrace (σ * (H_eq * D.rho - D.rho * H_eq))) -
            finiteOperatorTrace
              ((expectationReal D (D.rho - σ) : ℂ) •
                ((1 : FiniteOperatorAlgebra n) * (H_eq * D.rho - D.rho * H_eq)))) = 0
      rw [finiteOperatorTrace_complex_smul, h1, h2, h3]
      simp
    rw [hfull]
    simp
  have hnonpos :=
    deriv_freeEnergy_nonpos_of_matrixKuboMoriMobility_of_reversible_orthogonal
      (traceNormalizedSquarePotential (CblinfunMatrix.matrixOfOp σ))
      (fun s => traceNormalizedSquarePotentialFDeriv (CblinfunMatrix.matrixOfOp σ) (rho s))
      rho sys (fun _ => D) (fun _ => hD) hmob hrev hrho_deriv hΦ hdΦ
  exact ⟨hrate, hnonpos⟩

/-- Unconditional convex-interval `AntitoneOn` monotonicity of
`traceNormalizedSquarePotential (matrixOfOp σ)` along `rho t = matrixOfOp (normalizedExponential (H t))`
without assuming `[H_eq, H t] = 0`. -/
theorem antitoneOn_traceNormalizedSquarePotential_gibbsTrajectory
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n) (hH_eq : IsSelfAdjoint H_eq)
    (hσ : IsSelfAdjoint σ) (hcomm_σ : Commute σ H_eq)
    (H : ℝ → FiniteOperatorAlgebra n) {I : Set ℝ} (hI : Convex ℝ I)
    (hH : ∀ t ∈ I, IsSelfAdjoint (H t))
    (hflow : ∀ t (ht : t ∈ I),
      HasDerivAt H
        (gibbsUnitaryVectorField H_eq (H t) -
          ((faithfulGibbsDensity (H t) (hH t ht)
              (tracedExponential_re_pos_of_isSelfAdjoint (H t) (hH t ht))).rho - σ)) t) :
    AntitoneOn
      (fun s =>
        traceNormalizedSquarePotential (CblinfunMatrix.matrixOfOp σ)
          (CblinfunMatrix.matrixOfOp (normalizedExponential (H s)))) I := by
  have hcont :
      ContinuousOn
        (fun s =>
          traceNormalizedSquarePotential (CblinfunMatrix.matrixOfOp σ)
            (CblinfunMatrix.matrixOfOp (normalizedExponential (H s)))) I := by
    intro t ht
    exact (hasDerivAt_traceNormalizedSquarePotential_gibbsTrajectory
      H_eq σ hH_eq hσ hcomm_σ H (hH t ht) (hflow t ht)).1.continuousAt.continuousWithinAt
  apply antitoneOn_of_deriv_nonpos hI hcont
  · intro t ht
    exact (hasDerivAt_traceNormalizedSquarePotential_gibbsTrajectory
      H_eq σ hH_eq hσ hcomm_σ H (hH t (interior_subset ht))
      (hflow t (interior_subset ht))).1.differentiableAt.differentiableWithinAt
  · intro t ht
    exact (hasDerivAt_traceNormalizedSquarePotential_gibbsTrajectory
      H_eq σ hH_eq hσ hcomm_σ H (hH t (interior_subset ht))
      (hflow t (interior_subset ht))).2

end Layer3ConcreteGibbsInstantiation

end InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw
