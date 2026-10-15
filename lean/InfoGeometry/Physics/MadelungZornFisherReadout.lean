import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.SplitOctonionZornAlgebra

/-!
# Finite Fisher variation and a Zorn quadratic readout

This module formalizes two finite algebraic statements from the Madelung--Zorn
proposal, using the repository's existing split-octonion carrier.

* For a positive density `ρ = f²`, the finite Fisher energy built from a
  supplied derivative `dρ = 2 f df` equals `4 ∑ (df)²`. Its exact quadratic
  variation along an amplitude direction is computed. Under an explicit
  summation-by-parts hypothesis, pairing the Bohm potential with the induced
  density variation is `c / 4` times that first-variation coefficient.
* Four scalar/vector coordinates are sent to the existing Zorn
  `SplitOctonion`; its determinant has the stated quadratic expansion.

The finite derivative data and summation-by-parts identity are hypotheses.
This does not prove a continuum functional derivative, Schrödinger evolution,
incompressibility, a Hall-viscosity law, or a physical identification of the
Zorn coordinates. The split `(4,4)` signature is already proved by
`SplitOctonion.zornDet_ofBasis8` and is not redefined here.
-/

namespace InfoGeometry.Physics.MadelungZornFisherReadout

open scoped BigOperators

noncomputable section

variable {α : Type*} [Fintype α]

/-- Finite Fisher energy of a positive density and a supplied density derivative. -/
def fisherEnergy (ρ dρ : α → ℝ) : ℝ :=
  ∑ i, (dρ i) ^ 2 / ρ i

/-- Amplitude Dirichlet energy in the same finite coordinate model. -/
def amplitudeEnergy (df : α → ℝ) : ℝ :=
  4 * ∑ i, (df i) ^ 2

/-- The Fisher density energy is the amplitude energy when `ρ = f²` and
`dρ = 2 f df` coordinatewise. -/
theorem fisherEnergy_eq_amplitudeEnergy
    (f df ρ dρ : α → ℝ)
    (hρ : ∀ i, ρ i = f i ^ 2)
    (hdρ : ∀ i, dρ i = 2 * f i * df i)
    (hf : ∀ i, f i ≠ 0) :
    fisherEnergy ρ dρ = amplitudeEnergy df := by
  unfold fisherEnergy amplitudeEnergy
  calc
    (∑ i, (dρ i) ^ 2 / ρ i) = ∑ i, 4 * (df i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hdρ i, hρ i]
      have hfi : f i ≠ 0 := hf i
      field_simp [hfi]
      ring
    _ = 4 * ∑ i, (df i) ^ 2 := by rw [Finset.mul_sum]

/-- Fisher amplitude energy along the affine amplitude variation `f + t g`,
written in terms of its supplied derivative `df + t dg`. -/
def fisherEnergyAlong (df dg : α → ℝ) (t : ℝ) : ℝ :=
  4 * ∑ i, (df i + t * dg i) ^ 2

/-- The coefficient of the linear term in the exact quadratic variation. -/
def fisherVariationCoefficient (df dg : α → ℝ) : ℝ :=
  8 * ∑ i, df i * dg i

/-- Exact finite variation formula; in particular no limiting or analytic
assumption is hidden in the first-order coefficient. -/
theorem fisherEnergyAlong_variation
    (df dg : α → ℝ) (t : ℝ) :
    fisherEnergyAlong df dg t - fisherEnergyAlong df dg 0 =
      t * fisherVariationCoefficient df dg +
        t ^ 2 * (4 * ∑ i, (dg i) ^ 2) := by
  unfold fisherEnergyAlong fisherVariationCoefficient
  have hpoint (i : α) :
      (df i + t * dg i) ^ 2 - (df i) ^ 2 =
        t * (2 * (df i * dg i)) + t ^ 2 * (dg i) ^ 2 := by ring
  simp only [zero_mul, add_zero]
  calc
    4 * (∑ i, (df i + t * dg i) ^ 2) - 4 * (∑ i, (df i) ^ 2) =
        4 * ∑ i, ((df i + t * dg i) ^ 2 - (df i) ^ 2) := by
          rw [Finset.sum_sub_distrib]
          ring
    _ = 4 * ∑ i, (t * (2 * (df i * dg i)) + t ^ 2 * (dg i) ^ 2) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact hpoint i
    _ = t * (8 * ∑ i, df i * dg i) +
          t ^ 2 * (4 * ∑ i, (dg i) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          have hfactor : (∑ i, t ^ 2 * (dg i) ^ 2) =
              t ^ 2 * ∑ i, (dg i) ^ 2 := by rw [Finset.mul_sum]
          rw [hfactor]
          ring

/-- Bohm potential `-c Δf/f` evaluated at each finite coordinate. -/
def bohmPotential (c : ℝ) (f ddf : α → ℝ) (i : α) : ℝ :=
  -c * (ddf i / f i)

/-- First-order density variation induced by the amplitude variation `g`. -/
def densityVariation (f g : α → ℝ) (i : α) : ℝ :=
  2 * f i * g i

/-- Finite variational identity. The summation-by-parts hypothesis is the
precise bridge from the amplitude Fisher variation to the Bohm potential. -/
theorem bohmPotential_pairing_eq_scaled_fisherVariation
    (c : ℝ) (f df ddf g dg : α → ℝ)
    (hf : ∀ i, f i ≠ 0)
    (hparts : (∑ i, df i * dg i) = -(∑ i, ddf i * g i)) :
    (∑ i, bohmPotential c f ddf i * densityVariation f g i) =
      (c / 4) * fisherVariationCoefficient df dg := by
  unfold bohmPotential densityVariation fisherVariationCoefficient
  calc
    (∑ i, (-c * (ddf i / f i)) * (2 * f i * g i)) =
        ∑ i, (-2 * c) * (ddf i * g i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hfi : f i ≠ 0 := hf i
      field_simp [hfi]
    _ = (-2 * c) * ∑ i, ddf i * g i := by rw [Finset.mul_sum]
    _ = (c / 4) * (8 * ∑ i, df i * dg i) := by rw [hparts]; ring

/-- Coordinate packaging of action, information potential, gauge vector, and
momentum vector into the repository's existing split-octonion Zorn carrier.
This is a linear-coordinate construction, not an operator or a derived field
equation. -/
def toZornPotential
    (S Q : ℝ)
    (A momentum : InfoGeometry.Algebra.SplitOctonionZorn.Vector3) :
    InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion where
  a := S + Q
  u := ⟨A.x + momentum.x, A.y + momentum.y, A.z + momentum.z⟩
  v := ⟨A.x - momentum.x, A.y - momentum.y, A.z - momentum.z⟩
  d := S - Q

open InfoGeometry.Algebra.SplitOctonionZorn

/-- The Zorn determinant of the packaged coordinates is the corresponding
split quadratic expression. -/
theorem zornDet_toZornPotential
    (S Q : ℝ) (A momentum : Vector3) :
    SplitOctonion.zornDet (toZornPotential S Q A momentum) =
      S ^ 2 - Q ^ 2 - Vector3.dot A A + Vector3.dot momentum momentum := by
  cases A with
  | mk ax ay az =>
    cases momentum with
    | mk px py pz =>
      dsimp [toZornPotential, SplitOctonion.zornDet, Vector3.dot]
      ring

end

end InfoGeometry.Physics.MadelungZornFisherReadout
