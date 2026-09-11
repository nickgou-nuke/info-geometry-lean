/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Authors
-/
import Mathlib.Topology.Instances.AddCircle.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Tactic
import InfoGeometry.Canonical.ZornNavierStokesHydrodynamicBridge

/-!
# Native Bridge: Torus Dynamics, Haar Invariance & Ergodic Reynolds Flow

This module backports and formalizes the 2-torus covering dynamics and ergodic spatial
averaging from OpenAI's Navier-Stokes formalization (`NavierStokes.TorusAverages` & `SmoothLoop`):

1. **2-Torus Geometry & Haar Probability Measure**:
   The compact torus $\mathbb{T}^2 = \operatorname{UnitAddCircle} \times \operatorname{UnitAddCircle}$
   equipped with the product Haar probability measure `torusMeasure`.

2. **Hyperbolic Endomorphism $J_g$**:
   The integer matrix $J_g = \begin{pmatrix} 3 & 1 \\ 1 & 5 \end{pmatrix}$ from
   `ZornNavierStokesHydrodynamicBridge` induces:
   - A real covering map on $\mathbb{R}^2$: $\operatorname{covering}(z) = (3 z_1 + z_2, z_1 + 5 z_2)$.
   - An additive group endomorphism $\operatorname{torusCovering} : \mathbb{T}^2 \to^+ \mathbb{T}^2$.
   - Universal projection intertwining: $q(\operatorname{covering}(z)) = \operatorname{torusCovering}(q(z))$.

3. **Haar Measure Preservation & Ergodic Invariance**:
   - `torusCovering_measurePreserving`: $\operatorname{torusCovering}_* \mu_{\mathbb{T}^2} = \mu_{\mathbb{T}^2}$.
   - `integral_torusCovering_iterate`: For any continuous observable $f \in C(\mathbb{T}^2, V)$,
     $$\int_{\mathbb{T}^2} f(J_g^n z) \, d\mu = \int_{\mathbb{T}^2} f(z) \, d\mu$$
     This guarantees that fast spatial oscillations do not deplete total kinetic energy.

4. **Angular Harmonic Averaging (The Reynolds $1/2$ Factor)**:
   - `angularMean_cos_sq_harmonic`: For any nonzero integer harmonic $j \in \mathbb{Z} \setminus \{0\}$
     and arbitrary phase shift $\phi \in \mathbb{R}$:
     $$\frac{1}{2\pi} \int_0^{2\pi} \cos^2(j \theta + \phi) \, d\theta = \frac{1}{2}$$
     This exact $1/2$ factor governs the conversion of high-frequency wave fluctuations into
     the macroscopic Reynolds stress tensor.
-/

noncomputable section

namespace InfoGeometry.Canonical.NavierStokesTorusErgodic

open MeasureTheory Set Function Matrix
open scoped BigOperators Topology ContDiff

local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- Universal cover of the 2-torus. -/
abbrev Plane := ℝ × ℝ

/-- The compact 2-torus $\mathbb{T}^2 = (\mathbb{R}/\mathbb{Z}) \times (\mathbb{R}/\mathbb{Z})$. -/
abbrev Torus := UnitAddCircle × UnitAddCircle

/-- Normalized Haar probability measure on the 2-torus. -/
def torusMeasure : Measure Torus :=
  (AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle

/-- The Haar measure on $\mathbb{T}^2$ is a probability measure. -/
instance : IsProbabilityMeasure torusMeasure := by
  unfold torusMeasure
  infer_instance

/-- Canonical quotient projection from $\mathbb{R}^2$ to $\mathbb{T}^2$. -/
def quotientPoint (z : Plane) : Torus := ((z.1 : UnitAddCircle), (z.2 : UnitAddCircle))

/-- Real linear covering transformation induced by the hyperbolic matrix $J_g$. -/
def covering (z : Plane) : Plane := (3 * z.1 + z.2, z.1 + 5 * z.2)

/-- Matrix multiplication identity: `covering` is the action of $J_g$. -/
theorem covering_eq_J_g_mulVec (z : Plane) :
    let v : Fin 2 → ℝ := ![z.1, z.2]
    covering z = ((InfoGeometry.Canonical.ZornNavierStokesHydrodynamic.J_g.mulVec v) 0,
                  (InfoGeometry.Canonical.ZornNavierStokesHydrodynamic.J_g.mulVec v) 1) := by
  dsimp [covering, InfoGeometry.Canonical.ZornNavierStokesHydrodynamic.J_g]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The covering map is continuous on the plane. -/
theorem covering_continuous : Continuous covering :=
  ((continuous_const.mul continuous_fst).add continuous_snd).prodMk
    (continuous_fst.add (continuous_const.mul continuous_snd))

/-- Additive group endomorphism on the torus induced by $J_g$. -/
def torusCovering : Torus →+ Torus where
  toFun z := ((3 : ℕ) • z.1 + z.2, z.1 + (5 : ℕ) • z.2)
  map_zero' := by simp
  map_add' := by
    intro z w
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, nsmul_add] <;> abel

/-- The torus endomorphism is continuous. -/
theorem torusCovering_continuous : Continuous torusCovering :=
  ((continuous_fst.nsmul 3).add continuous_snd).prodMk
    (continuous_fst.add (continuous_snd.nsmul 5))

/-- Intertwining relation: the quotient projection commutes with the covering map. -/
theorem quotient_covering (z : Plane) :
    quotientPoint (covering z) = torusCovering (quotientPoint z) := by
  apply Prod.ext
  · change (((3 * z.1 + z.2 : ℝ) : UnitAddCircle)) =
      (3 : ℕ) • (z.1 : UnitAddCircle) + (z.2 : UnitAddCircle)
    rw [AddCircle.coe_add, ← AddCircle.coe_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
  · change (((z.1 + 5 * z.2 : ℝ) : UnitAddCircle)) =
      (z.1 : UnitAddCircle) + (5 : ℕ) • (z.2 : UnitAddCircle)
    rw [AddCircle.coe_add, ← AddCircle.coe_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]

/-- Surjectivity of the torus covering map: explicitly lifted via the inverse matrix
$J_g^{-1} = \frac{1}{14} \begin{pmatrix} 5 & -1 \\ -1 & 3 \end{pmatrix}$. -/
theorem torusCovering_surjective : Surjective torusCovering := by
  rintro ⟨x, y⟩
  refine Quotient.inductionOn' x (fun a => ?_)
  refine Quotient.inductionOn' y (fun b => ?_)
  refine ⟨quotientPoint ((5 * a - b) / 14, (-a + 3 * b) / 14), ?_⟩
  rw [← quotient_covering]
  have heq : covering ((5 * a - b) / 14, (-a + 3 * b) / 14) = (a, b) := by
    apply Prod.ext <;> dsimp [covering] <;> ring
  rw [heq]
  rfl

/-- Iterated quotient intertwining identity. -/
theorem quotient_covering_iterate (n : ℕ) (z : Plane) :
    quotientPoint (covering^[n] z) = torusCovering^[n] (quotientPoint z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', quotient_covering, ih]

local instance : Measure.IsAddHaarMeasure torusMeasure := by
  unfold torusMeasure
  infer_instance

/-- The hyperbolic torus covering preserves the Haar measure on $\mathbb{T}^2$. -/
theorem torusCovering_measurePreserving :
    MeasurePreserving torusCovering torusMeasure torusMeasure :=
  torusCovering.measurePreserving torusCovering_continuous torusCovering_surjective rfl

/-- Ergodic invariance: every iterate of the covering map preserves the Haar integral
of any continuous observable. -/
theorem integral_torusCovering_iterate {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : Torus → V) (hf : Continuous f) (n : ℕ) :
    (∫ z, f (torusCovering^[n] z) ∂torusMeasure) = ∫ z, f z ∂torusMeasure := by
  have hp := torusCovering_measurePreserving.iterate n
  rw [← integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable, hp.map_eq]

/-!
## Angular Harmonic Averaging & The Reynolds $1/2$ Pre-factor
-/

/-- Angular average of a $2\pi$-periodic function over one full period. -/
def angularMean (f : ℝ → ℝ) : ℝ := (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) / (2 * Real.pi)

/-- The angular average of a constant is the constant itself. -/
theorem angularMean_const (c : ℝ) : angularMean (fun _ => c) = c := by
  simp only [angularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp [hpi]

/-- Homogeneity of the angular average under scalar multiplication. -/
theorem angularMean_const_mul (c : ℝ) (f : ℝ → ℝ) :
    angularMean (fun θ => c * f θ) = c * angularMean f := by
  unfold angularMean
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Fundamental Harmonic Averaging Lemma:
The angular average of $\cos^2(j \theta + \phi)$ is identically $1/2$ for any nonzero
integer harmonic $j \in \mathbb{Z} \setminus \{0\}$ and any phase shift $\phi \in \mathbb{R}$. -/
theorem angularMean_cos_sq_harmonic (j : ℤ) (hj : j ≠ 0) (phase : ℝ) :
    angularMean (fun θ => Real.cos ((j : ℝ) * θ + phase) ^ 2) = 1 / 2 := by
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hs : Real.sin ((j : ℝ) * (2 * Real.pi) + phase) = Real.sin phase := by
    rw [add_comm]
    exact Real.sin_add_int_mul_two_pi phase j
  have hc : Real.cos ((j : ℝ) * (2 * Real.pi) + phase) = Real.cos phase := by
    rw [add_comm]
    exact Real.cos_add_int_mul_two_pi phase j
  unfold angularMean
  rw [intervalIntegral.integral_comp_mul_add (fun θ => Real.cos θ ^ 2) hjR phase,
    integral_cos_sq]
  simp only [mul_zero, zero_add, hs, hc, smul_eq_mul]
  field_simp [hjR, Real.pi_ne_zero]
  ring

/-!
## Certified Synthesis Bundle
-/

/-- Certified structural synthesis bundle verifying:
1. Covering map coincides with the matrix action of $J_g$.
2. Torus projection commutes with the covering dynamics.
3. Surjectivity via explicit inverse lift $J_g^{-1}$.
4. Exact Haar measure preservation $\operatorname{torusCovering}_* \mu = \mu$.
5. Integral ergodic invariance of iterates.
6. Angular harmonic averaging yielding the exact $1/2$ Reynolds factor. -/
structure CertifiedNavierStokesTorusErgodicBridge where
  covering_matrix : ∀ z : Plane,
    let v : Fin 2 → ℝ := ![z.1, z.2]
    covering z = ((InfoGeometry.Canonical.ZornNavierStokesHydrodynamic.J_g.mulVec v) 0,
                  (InfoGeometry.Canonical.ZornNavierStokesHydrodynamic.J_g.mulVec v) 1)
  quotient_commutes : ∀ z : Plane,
    quotientPoint (covering z) = torusCovering (quotientPoint z)
  surjective_covering : Surjective torusCovering
  measure_preserving : MeasurePreserving torusCovering torusMeasure torusMeasure
  integral_invariance : ∀ (f : Torus → ℝ), Continuous f → ∀ n : ℕ,
    (∫ z, f (torusCovering^[n] z) ∂torusMeasure) = ∫ z, f z ∂torusMeasure
  harmonic_mean_half : ∀ (j : ℤ), j ≠ 0 → ∀ (phase : ℝ),
    angularMean (fun θ => Real.cos ((j : ℝ) * θ + phase) ^ 2) = 1 / 2

/-- Certified instance of the Navier-Stokes Torus Ergodic Bridge. -/
def certified_navier_stokes_torus_ergodic_bridge : CertifiedNavierStokesTorusErgodicBridge where
  covering_matrix := covering_eq_J_g_mulVec
  quotient_commutes := quotient_covering
  surjective_covering := torusCovering_surjective
  measure_preserving := torusCovering_measurePreserving
  integral_invariance := fun f hf n => integral_torusCovering_iterate f hf n
  harmonic_mean_half := angularMean_cos_sq_harmonic

end InfoGeometry.Canonical.NavierStokesTorusErgodic
