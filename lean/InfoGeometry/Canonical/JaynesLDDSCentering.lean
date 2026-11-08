import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.NoncommRing

/-!
# InfoGeometry.Canonical.JaynesLDDSCentering

Finite Jaynes LDDS centering and algebraic identity coordinates.

This file formalizes the safe finite core of the LDDS intuition:

* a finite density is compared to a finite reference density pointwise;
* the centered relative score is `pᵢ / mᵢ - 1`;
* multiplying back by the reference weight gives the signed fluctuation
  `pᵢ - mᵢ`;
* if both finite densities have the same total mass, the reference-weighted
  centered score has zero total mass;
* around the algebraic identity, a square-zero fluctuation has exact truncated
  exponential and inverse formulas.

No continuous entropy theorem.
No measure-theoretic LDDS limit.
No normal state or von Neumann algebra theorem.
No spectral theorem or analytic completion.
-/

namespace InfoGeometry.Canonical.JaynesLDDSCentering

open Finset

/-! ## Finite Jaynes/LDDS centering -/

/-- Finite density data relative to a finite reference density. -/
structure FiniteLDDSDatum (ι : Type*) where
  /-- The measured/discrete density. -/
  density : ι → ℝ
  /-- The reference limiting-density-of-discrete-states weight. -/
  reference : ι → ℝ

namespace FiniteLDDSDatum

variable {ι : Type*} [Fintype ι]

/-- Pointwise relative density `pᵢ / mᵢ`. -/
noncomputable def relativeDensity (D : FiniteLDDSDatum ι) (i : ι) : ℝ :=
  D.density i / D.reference i

/-- Centered LDDS score `pᵢ / mᵢ - 1`. -/
noncomputable def centeredScore (D : FiniteLDDSDatum ι) (i : ι) : ℝ :=
  D.relativeDensity i - 1

/-- Total mass of the measured density. -/
def densityMass (D : FiniteLDDSDatum ι) : ℝ :=
  ∑ i : ι, D.density i

/-- Total mass of the reference density. -/
def referenceMass (D : FiniteLDDSDatum ι) : ℝ :=
  ∑ i : ι, D.reference i

/-- Reference-weighted centered score. -/
noncomputable def weightedCenteredScore (D : FiniteLDDSDatum ι) (i : ι) : ℝ :=
  D.reference i * D.centeredScore i

omit [Fintype ι] in
/-- Multiplying the centered relative score by the reference weight gives `pᵢ - mᵢ`. -/
theorem weightedCenteredScore_eq_density_sub_reference
    (D : FiniteLDDSDatum ι) {i : ι} (href : D.reference i ≠ 0) :
    D.weightedCenteredScore i = D.density i - D.reference i := by
  unfold weightedCenteredScore centeredScore relativeDensity
  field_simp [href]

/-- The total weighted centered score is the mass difference, assuming nonzero references. -/
theorem sum_weightedCenteredScore_eq_mass_sub
    (D : FiniteLDDSDatum ι) (href : ∀ i : ι, D.reference i ≠ 0) :
    (∑ i : ι, D.weightedCenteredScore i) = D.densityMass - D.referenceMass := by
  unfold densityMass referenceMass
  calc
    (∑ i : ι, D.weightedCenteredScore i) = ∑ i : ι, (D.density i - D.reference i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact D.weightedCenteredScore_eq_density_sub_reference (href i)
    _ = (∑ i : ι, D.density i) - ∑ i : ι, D.reference i := by
      rw [Finset.sum_sub_distrib]

/-- If the measured and reference masses agree, the centered score has zero reference mass. -/
theorem sum_weightedCenteredScore_eq_zero_of_equal_mass
    (D : FiniteLDDSDatum ι) (href : ∀ i : ι, D.reference i ≠ 0)
    (hmass : D.densityMass = D.referenceMass) :
    (∑ i : ι, D.weightedCenteredScore i) = 0 := by
  rw [D.sum_weightedCenteredScore_eq_mass_sub href, hmass]
  ring

end FiniteLDDSDatum

/-! ## Identity-centered algebraic fluctuations -/

section IdentityCentered

variable {A : Type*} [Ring A]

/-- Centering a multiplicative element at the algebraic identity. -/
def centeredAtIdentity (x : A) : A :=
  x - 1

/-- Reconstructing from the centered identity coordinate. -/
def uncenterAtIdentity (y : A) : A :=
  1 + y

@[simp]
theorem uncenter_centeredAtIdentity (x : A) :
    uncenterAtIdentity (centeredAtIdentity x) = x := by
  unfold uncenterAtIdentity centeredAtIdentity
  abel

@[simp]
theorem centered_uncenterAtIdentity (y : A) :
    centeredAtIdentity (uncenterAtIdentity y) = y := by
  unfold centeredAtIdentity uncenterAtIdentity
  abel

/-- A square-zero tangent fluctuation. -/
def SquareZeroFluctuation (y : A) : Prop :=
  y * y = 0

/-- For a square-zero fluctuation, `(1 + y) * (1 - y) = 1`. -/
theorem one_add_mul_one_sub_of_squareZero {y : A}
    (hy : SquareZeroFluctuation y) :
    (1 + y) * (1 - y) = 1 := by
  unfold SquareZeroFluctuation at hy
  noncomm_ring [hy]

/-- For a square-zero fluctuation, `(1 - y) * (1 + y) = 1`. -/
theorem one_sub_mul_one_add_of_squareZero {y : A}
    (hy : SquareZeroFluctuation y) :
    (1 - y) * (1 + y) = 1 := by
  unfold SquareZeroFluctuation at hy
  noncomm_ring [hy]

/-- Exact second-order truncation for square-zero identity fluctuations. -/
theorem square_of_one_add_squareZero {y : A}
    (hy : SquareZeroFluctuation y) :
    (1 + y) * (1 + y) = 1 + 2 • y := by
  unfold SquareZeroFluctuation at hy
  noncomm_ring [hy]

end IdentityCentered

end InfoGeometry.Canonical.JaynesLDDSCentering
