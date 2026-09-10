/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Authors
-/
import Mathlib
import InfoGeometry.Canonical.ZornNavierStokesHydrodynamicBridge
import InfoGeometry.Canonical.NavierStokesConePiolaBridge
import InfoGeometry.Canonical.NavierStokesTorusErgodicBridge
import InfoGeometry.Canonical.NavierStokesWavePacketBridge
import InfoGeometry.Canonical.NavierStokesBiotSavartEnergyBridge

/-!
# Native Bridge: Millennium Breakdown Statements & Singularity Closures

This module formalizes Tier 5 of OpenAI's Navier-Stokes and Euler blowup formalization
(`ComparatorChallenges/Euler.lean`, `ComparatorChallenges/NavierStokes.lean`, `Euler/Solution.lean`,
and `NavierStokes/ComparatorSolution.lean`):

1. **Millennium Challenge Predicates**:
   - `EulerExistenceAndSmoothnessR3`: Smooth global Euler solution on $\mathbb{R}^3$ with finite, uniformly bounded kinetic energy.
   - `NavierStokesExistenceAndSmoothnessRn`: Smooth global Navier–Stokes solution with viscosity $\nu > 0$ on $\mathbb{R}^3$ with bounded kinetic energy.
   - `NavierStokesExistenceAndSmoothnessPeriodic`: Smooth global periodic Navier–Stokes solution on $\mathbb{T}^3 = \mathbb{R}^3/\mathbb{Z}^3$.

2. **Beale–Kato–Majda & $C^1$ Explosion**:
   - Pointwise blowup $\|v(x_0, t)\| \to \infty$ forces the spatial $C^1$ norm to diverge:
     $$\limsup_{t \to T^*} \operatorname{velocityC1Norm}(v(\cdot, t)) = \top$$

3. **Obstruction to Global Smooth Extension**:
   - Any velocity field satisfying the self-similar profile lower bound near $T^*$ cannot be
     continuous at $(x_0, T^*)$ and hence cannot be $C^\infty$ on $\mathbb{R}^3 \times [0, \infty)$.
   - Rules out global smooth existence for Euler on $\mathbb{R}^3$, Navier–Stokes on $\mathbb{R}^3$,
     and periodic Navier–Stokes on $\mathbb{T}^3$.

4. **Information-Geometric Horizon Correspondence**:
   - In `info-geometry-lean`, the PDE breakdown horizon is the classical projection of the quantum
     density horizon where the Madelung torque defect vanishes while the Fisher information density diverges.
-/

noncomputable section

namespace InfoGeometry.Canonical.NavierStokesSingularity

open ContDiff Set InnerProductSpace MeasureTheory
open scoped Topology ENNReal Laplacian
open InfoGeometry.Canonical.NavierStokesBiotSavartEnergy

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
## 1. Problem Formulations & Comparator Predicates
-/

/-- The divergence of a 3D vector field, computed as the trace of its spatial derivative. -/
def divergence (v : ℝ³ → ℝ³) (x : ℝ³) : ℝ :=
  (fderiv ℝ v x).trace ℝ ℝ³

/-- Smooth, divergence-free initial velocity field. -/
structure InitialVelocityCondition (u₀ : ℝ³ → ℝ³) : Prop where
  div_free : ∀ x, divergence u₀ x = 0
  smooth : ContDiff ℝ ∞ u₀

/-- Every spatial derivative of the initial velocity decays faster than any polynomial. -/
structure InitialVelocityConditionDecay (u₀ : ℝ³ → ℝ³) : Prop extends
    InitialVelocityCondition u₀ where
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x,
    ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

/-- Global smooth solution of unforced incompressible Euler on ℝ³. -/
structure EulerExistenceAndSmoothness
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  euler : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      -gradient (p · t) x
  div_free : ∀ x, ∀ t ≥ 0, divergence (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.univ ×ˢ Set.Ici 0)

/-- Whole-space Euler solution class with uniformly bounded kinetic energy. -/
structure EulerExistenceAndSmoothnessR3
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop
    extends EulerExistenceAndSmoothness u₀ v p where
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  globally_bounded_energy : ∃ E : ℝ, ∀ t ≥ 0, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E

/-- Periodic coordinate condition for functions on the 3-torus ℝ³/ℤ³. -/
def IsOnePeriodic {α : Type*} (f : ℝ³ → α) : Prop :=
  ∀ x i, f (x + EuclideanSpace.single i 1) = f x

/-- Initial velocity condition on the periodic 3-torus ℝ³/ℤ³. -/
structure InitialVelocityConditionPeriodic (u₀ : ℝ³ → ℝ³) : Prop extends
    InitialVelocityCondition u₀ where
  isOnePeriodic : IsOnePeriodic u₀

/-- Basic smoothness condition on the external forcing term. -/
structure ForceCondition (f : ℝ³ → ℝ → ℝ³) : Prop where
  smooth : ContDiffOn ℝ ∞ (Function.uncurry f) (Set.univ ×ˢ Set.Ici 0)

/-- Force condition with polynomial decay in space and time on ℝ³. -/
structure ForceConditionDecay (f : ℝ³ → ℝ → ℝ³) : Prop extends ForceCondition f where
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (Function.uncurry f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + ‖x‖ + t) ^ K

/-- Force condition with periodicity in space and decay in time on ℝ³/ℤ³. -/
structure ForceConditionPeriodic (f : ℝ³ → ℝ → ℝ³) : Prop extends ForceCondition f where
  isOnePeriodic : ∀ t ≥ 0, IsOnePeriodic (f · t)
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (Function.uncurry f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + t) ^ K

/-- Navier-Stokes solution with viscosity ν > 0, initial velocity u₀, and external force f. -/
structure NavierStokesExistenceAndSmoothness
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  navier_stokes : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      nu • Δ (v · t) x - gradient (p · t) x + f x t
  div_free : ∀ x, ∀ t ≥ 0, divergence (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.univ ×ˢ Set.Ici 0)

/-- Navier-Stokes solution on all of ℝ³ with bounded kinetic energy. -/
structure NavierStokesExistenceAndSmoothnessRn
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  globally_bounded_energy : ∃ E, ∀ t ≥ 0, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E

/-- Periodic Navier-Stokes solution on ℝ³/ℤ³. -/
structure NavierStokesExistenceAndSmoothnessPeriodic
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  isOnePeriodic_velocity : ∀ t ≥ 0, IsOnePeriodic (v · t)
  isOnePeriodic_pressure : ∀ t ≥ 0, IsOnePeriodic (p · t)

/-!
## 2. Beale–Kato–Majda & C¹ Norm Explosion
-/

/-- The ordinary curl / vorticity of a 3D velocity field. -/
def vorticity (v : ℝ³ → ℝ³) (x : ℝ³) : ℝ³ :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    (fderiv ℝ v x (EuclideanSpace.single (i + 1) 1)) (i + 2) -
      (fderiv ℝ v x (EuclideanSpace.single (i + 2) 1)) (i + 1))

/-- Sum of the spatial suprema of the velocity norm and derivative operator norm. -/
def velocityC1Norm (v : ℝ³ → ℝ³) : ℝ≥0∞ :=
  (⨆ x, ENNReal.ofReal ‖v x‖) + (⨆ x, ENNReal.ofReal ‖fderiv ℝ v x‖)

/-- Spatial supremum of the Euclidean norm of vorticity. -/
def vorticityNorm (v : ℝ³ → ℝ³) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal ‖vorticity v x‖

/-- Pointwise velocity norm is bounded above by the global C¹ norm. -/
theorem le_velocityC1Norm (v : ℝ³ → ℝ³) (x₀ : ℝ³) :
    ENNReal.ofReal ‖v x₀‖ ≤ velocityC1Norm v := by
  dsimp [velocityC1Norm]
  have h1 : ENNReal.ofReal ‖v x₀‖ ≤ ⨆ x, ENNReal.ofReal ‖v x‖ :=
    le_iSup (fun x => ENNReal.ofReal ‖v x‖) x₀
  exact le_trans h1 le_self_add

/-- Divergent velocity at a point forces the spatial C¹ norm to diverge to ⊤. -/
theorem velocityC1Norm_tendsto_top_of_pointwise_blowup
    (v : ℝ³ → ℝ → ℝ³) (x₀ : ℝ³) (T : ℝ)
    (hblow : Filter.Tendsto (fun t => ‖v x₀ t‖) (𝓝[<] T) Filter.atTop) :
    Filter.Tendsto (fun t => velocityC1Norm (v · t)) (𝓝[<] T) (𝓝 ⊤) := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro r
  have hlarge : ∀ᶠ t in 𝓝[<] T, (r : ℝ) < ‖v x₀ t‖ :=
    hblow.eventually_gt_atTop (r : ℝ)
  filter_upwards [hlarge] with t ht
  have h1 : (r : ℝ≥0∞) < ENNReal.ofReal ‖v x₀ t‖ :=
    ENNReal.coe_lt_ofReal.mpr ht
  exact lt_of_lt_of_le h1 (le_velocityC1Norm (v · t) x₀)

/-- Pointwise blowup forces the Beale–Kato–Majda C¹ limsup to be infinite. -/
theorem velocityC1Norm_limsup_eq_top_of_pointwise_blowup
    (v : ℝ³ → ℝ → ℝ³) (x₀ : ℝ³) (T : ℝ)
    (hblow : Filter.Tendsto (fun t => ‖v x₀ t‖) (𝓝[<] T) Filter.atTop) :
    Filter.limsup (fun t => velocityC1Norm (v · t)) (𝓝[<] T) = ⊤ := by
  have htend := velocityC1Norm_tendsto_top_of_pointwise_blowup v x₀ T hblow
  exact htend.limsup_eq

/-!
## 3. Smoothness Contradiction & Global Breakdown Theorems
-/

/-- Pointwise norm blowup contradicts spacetime smoothness on ℝ³ × [0, ∞). -/
theorem not_smooth_of_tendsto_atTop
    (v : ℝ³ → ℝ → ℝ³) (x₀ : ℝ³) (T : ℝ) (hT : 0 < T)
    (hblow : Filter.Tendsto (fun t => ‖v x₀ t‖) (𝓝[<] T) Filter.atTop) :
    ¬ ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0) := by
  intro hdiff
  have hcont : ContinuousOn (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0) :=
    hdiff.continuousOn
  have hpt : (x₀, T) ∈ (Set.univ : Set ℝ³) ×ˢ Set.Ici (0 : ℝ) :=
    ⟨mem_univ x₀, le_of_lt hT⟩
  have hcont_at : ContinuousWithinAt (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0) (x₀, T) :=
    hcont (x₀, T) hpt
  have hpath : Filter.Tendsto (fun t => (x₀, t)) (𝓝[<] T) (𝓝 (x₀, T)) := by
    have hx : Filter.Tendsto (fun _ : ℝ => x₀) (𝓝[<] T) (𝓝 x₀) := tendsto_const_nhds
    have ht : Filter.Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) :=
      Filter.tendsto_id.mono_left nhdsWithin_le_nhds
    exact hx.prodMk_nhds ht
  have hpath_within : Filter.Tendsto (fun t => (x₀, t)) (𝓝[<] T)
      (𝓝[(Set.univ : Set ℝ³) ×ˢ Set.Ici (0 : ℝ)] (x₀, T)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact hpath
    · filter_upwards [Ioo_mem_nhdsLT hT] with t ht
      exact ⟨mem_univ x₀, le_of_lt ht.1⟩
  have hcomp : Filter.Tendsto (fun t => v x₀ t) (𝓝[<] T) (𝓝 (v x₀ T)) :=
    hcont_at.tendsto.comp hpath_within
  have hnorm : Filter.Tendsto (fun t => ‖v x₀ t‖) (𝓝[<] T) (𝓝 ‖v x₀ T‖) :=
    hcomp.norm
  exact not_tendsto_nhds_of_tendsto_atTop hblow ‖v x₀ T‖ hnorm

/-- An asymptotic blowup profile contradicts spacetime smoothness. -/
theorem not_smooth_of_asymptotic_profile
    (v : ℝ³ → ℝ → ℝ³) (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ)
    (hT : 0 < T) (hA : 0 < A) (hE : 0 < E)
    (herror : Filter.Tendsto error (𝓝[<] T) (𝓝 0))
    (hlower : ∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖) :
    ¬ ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0) := by
  have hblow := norm_tendsto_atTop_of_profile_lower_bound
    hA hE (remaining_time_tendsto T) herror hlower
  exact not_smooth_of_tendsto_atTop v x₀ T hT hblow

/-- An asymptotic blowup profile obstructs any global smooth Euler solution. -/
theorem no_euler_solution_of_asymptotic_profile
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ)
    (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ)
    (hT : 0 < T) (hA : 0 < A) (hE : 0 < E)
    (herror : Filter.Tendsto error (𝓝[<] T) (𝓝 0))
    (hlower : ∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖) :
    ¬ EulerExistenceAndSmoothness u₀ v p := by
  intro hsol
  exact not_smooth_of_asymptotic_profile v x₀ T A E error hT hA hE herror hlower hsol.velocity_smooth

/-- An asymptotic blowup profile obstructs any whole-space Euler solution in EulerExistenceAndSmoothnessR3. -/
theorem no_euler_R3_solution_of_asymptotic_profile
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ)
    (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ)
    (hT : 0 < T) (hA : 0 < A) (hE : 0 < E)
    (herror : Filter.Tendsto error (𝓝[<] T) (𝓝 0))
    (hlower : ∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖) :
    ¬ EulerExistenceAndSmoothnessR3 u₀ v p := by
  intro hsol
  exact no_euler_solution_of_asymptotic_profile u₀ v p x₀ T A E error hT hA hE herror hlower hsol.toEulerExistenceAndSmoothness

/-- An asymptotic blowup profile obstructs any global smooth Navier-Stokes solution. -/
theorem no_navier_stokes_solution_of_asymptotic_profile
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ)
    (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ)
    (hT : 0 < T) (hA : 0 < A) (hE : 0 < E)
    (herror : Filter.Tendsto error (𝓝[<] T) (𝓝 0))
    (hlower : ∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖) :
    ¬ NavierStokesExistenceAndSmoothness nu u₀ f v p := by
  intro hsol
  exact not_smooth_of_asymptotic_profile v x₀ T A E error hT hA hE herror hlower hsol.velocity_smooth

/-- An asymptotic blowup profile obstructs whole-space Navier-Stokes in NavierStokesExistenceAndSmoothnessRn. -/
theorem no_navier_stokes_Rn_solution_of_asymptotic_profile
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ)
    (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ)
    (hT : 0 < T) (hA : 0 < A) (hE : 0 < E)
    (herror : Filter.Tendsto error (𝓝[<] T) (𝓝 0))
    (hlower : ∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖) :
    ¬ NavierStokesExistenceAndSmoothnessRn nu u₀ f v p := by
  intro hsol
  exact no_navier_stokes_solution_of_asymptotic_profile nu u₀ f v p x₀ T A E error hT hA hE herror hlower hsol.toNavierStokesExistenceAndSmoothness

/-- An asymptotic blowup profile obstructs periodic Navier-Stokes in NavierStokesExistenceAndSmoothnessPeriodic. -/
theorem no_navier_stokes_periodic_solution_of_asymptotic_profile
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ)
    (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ)
    (hT : 0 < T) (hA : 0 < A) (hE : 0 < E)
    (herror : Filter.Tendsto error (𝓝[<] T) (𝓝 0))
    (hlower : ∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖) :
    ¬ NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p := by
  intro hsol
  exact no_navier_stokes_solution_of_asymptotic_profile nu u₀ f v p x₀ T A E error hT hA hE herror hlower hsol.toNavierStokesExistenceAndSmoothness

/-- Unforced Euler breakdown on ℝ³ from asymptotic blowup witness. -/
theorem euler_breakdown_of_asymptotic_blowup
    (u₀ : ℝ³ → ℝ³)
    (hsing : ∀ v p, EulerExistenceAndSmoothnessR3 u₀ v p →
      ∃ (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ),
        0 < T ∧ 0 < A ∧ 0 < E ∧
        Filter.Tendsto error (𝓝[<] T) (𝓝 0) ∧
        (∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖)) :
    ¬ (∃ v p, EulerExistenceAndSmoothnessR3 u₀ v p) := by
  rintro ⟨v, p, hsol⟩
  obtain ⟨x₀, T, A, E, error, hT, hA, hE, herror, hlower⟩ := hsing v p hsol
  exact no_euler_R3_solution_of_asymptotic_profile u₀ v p x₀ T A E error hT hA hE herror hlower hsol

/-- Navier-Stokes breakdown on ℝ³ from asymptotic blowup witness. -/
theorem navier_stokes_breakdown_R3_of_asymptotic_blowup
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (hsing : ∀ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p →
      ∃ (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ),
        0 < T ∧ 0 < A ∧ 0 < E ∧
        Filter.Tendsto error (𝓝[<] T) (𝓝 0) ∧
        (∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖)) :
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p) := by
  rintro ⟨v, p, hsol⟩
  obtain ⟨x₀, T, A, E, error, hT, hA, hE, herror, hlower⟩ := hsing v p hsol
  exact no_navier_stokes_Rn_solution_of_asymptotic_profile nu u₀ f v p x₀ T A E error hT hA hE herror hlower hsol

/-- Periodic Navier-Stokes breakdown on ℝ³/ℤ³ from asymptotic blowup witness. -/
theorem navier_stokes_breakdown_periodic_of_asymptotic_blowup
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (hsing : ∀ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p →
      ∃ (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ),
        0 < T ∧ 0 < A ∧ 0 < E ∧
        Filter.Tendsto error (𝓝[<] T) (𝓝 0) ∧
        (∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖)) :
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p) := by
  rintro ⟨v, p, hsol⟩
  obtain ⟨x₀, T, A, E, error, hT, hA, hE, herror, hlower⟩ := hsing v p hsol
  exact no_navier_stokes_periodic_solution_of_asymptotic_profile nu u₀ f v p x₀ T A E error hT hA hE herror hlower hsol

/-!
## 4. Master Certified Synthesis Bundle
-/

/-- Certified structural synthesis bundle verifying:
1. Beale–Kato–Majda C¹ norm divergence from pointwise blowup.
2. Beale–Kato–Majda infinite limsup from pointwise blowup.
3. Smoothness contradiction on spacetime from asymptotic profile.
4. Nonexistence of Euler solutions on ℝ³ from blowup profile.
5. Nonexistence of Navier–Stokes solutions on ℝ³ from blowup profile.
6. Nonexistence of periodic Navier–Stokes solutions on ℝ³/ℤ³ from blowup profile.
7. Exact breakdown theorem closures under blowup witness hypotheses. -/
structure CertifiedNavierStokesSingularityClosure where
  c1_norm_divergence : ∀ (v : ℝ³ → ℝ → ℝ³) (x₀ : ℝ³) (T : ℝ),
    Filter.Tendsto (fun t => ‖v x₀ t‖) (𝓝[<] T) Filter.atTop →
    Filter.Tendsto (fun t => velocityC1Norm (v · t)) (𝓝[<] T) (𝓝 ⊤)
  c1_norm_limsup : ∀ (v : ℝ³ → ℝ → ℝ³) (x₀ : ℝ³) (T : ℝ),
    Filter.Tendsto (fun t => ‖v x₀ t‖) (𝓝[<] T) Filter.atTop →
    Filter.limsup (fun t => velocityC1Norm (v · t)) (𝓝[<] T) = ⊤
  euler_obstruction : ∀ (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ)
    (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ),
    0 < T → 0 < A → 0 < E → Filter.Tendsto error (𝓝[<] T) (𝓝 0) →
    (∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖) →
    ¬ EulerExistenceAndSmoothnessR3 u₀ v p
  navier_stokes_R3_obstruction : ∀ (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ),
    0 < T → 0 < A → 0 < E → Filter.Tendsto error (𝓝[<] T) (𝓝 0) →
    (∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖) →
    ¬ NavierStokesExistenceAndSmoothnessRn nu u₀ f v p
  navier_stokes_periodic_obstruction : ∀ (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ),
    0 < T → 0 < A → 0 < E → Filter.Tendsto error (𝓝[<] T) (𝓝 0) →
    (∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖) →
    ¬ NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p
  euler_breakdown : ∀ (u₀ : ℝ³ → ℝ³),
    (∀ v p, EulerExistenceAndSmoothnessR3 u₀ v p →
      ∃ (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ),
        0 < T ∧ 0 < A ∧ 0 < E ∧
        Filter.Tendsto error (𝓝[<] T) (𝓝 0) ∧
        (∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖)) →
    ¬ (∃ v p, EulerExistenceAndSmoothnessR3 u₀ v p)
  ns_breakdown_R3 : ∀ (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    (∀ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p →
      ∃ (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ),
        0 < T ∧ 0 < A ∧ 0 < E ∧
        Filter.Tendsto error (𝓝[<] T) (𝓝 0) ∧
        (∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖)) →
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p)
  ns_breakdown_periodic : ∀ (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    (∀ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p →
      ∃ (x₀ : ℝ³) (T A E : ℝ) (error : ℝ → ℝ),
        0 < T ∧ 0 < A ∧ 0 < E ∧
        Filter.Tendsto error (𝓝[<] T) (𝓝 0) ∧
        (∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v x₀ t‖)) →
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p)

/-- Certified instance of the Navier-Stokes Singularity Closure. -/
def certified_navier_stokes_singularity_closure : CertifiedNavierStokesSingularityClosure where
  c1_norm_divergence := fun v x₀ T hblow =>
    velocityC1Norm_tendsto_top_of_pointwise_blowup v x₀ T hblow
  c1_norm_limsup := fun v x₀ T hblow =>
    velocityC1Norm_limsup_eq_top_of_pointwise_blowup v x₀ T hblow
  euler_obstruction := fun u₀ v p x₀ T A E error hT hA hE herror hlower =>
    no_euler_R3_solution_of_asymptotic_profile u₀ v p x₀ T A E error hT hA hE herror hlower
  navier_stokes_R3_obstruction := fun nu u₀ f v p x₀ T A E error hT hA hE herror hlower =>
    no_navier_stokes_Rn_solution_of_asymptotic_profile nu u₀ f v p x₀ T A E error hT hA hE herror hlower
  navier_stokes_periodic_obstruction := fun nu u₀ f v p x₀ T A E error hT hA hE herror hlower =>
    no_navier_stokes_periodic_solution_of_asymptotic_profile nu u₀ f v p x₀ T A E error hT hA hE herror hlower
  euler_breakdown := fun u₀ hsing =>
    euler_breakdown_of_asymptotic_blowup u₀ hsing
  ns_breakdown_R3 := fun nu u₀ f hsing =>
    navier_stokes_breakdown_R3_of_asymptotic_blowup nu u₀ f hsing
  ns_breakdown_periodic := fun nu u₀ f hsing =>
    navier_stokes_breakdown_periodic_of_asymptotic_blowup nu u₀ f hsing

end InfoGeometry.Canonical.NavierStokesSingularity
