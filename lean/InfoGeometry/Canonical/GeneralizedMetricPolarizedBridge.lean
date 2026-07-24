import InfoGeometry.Canonical.GeneralizedMetricCore
import InfoGeometry.Canonical.RelativeModularPolarizedBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.GeneralizedMetricPolarizedBridge

Adjacency bridge from the doubled/Krein generalized-metric seed to the existing
polarized relative-modular carrier package.

This file keeps the scope narrow:
- the canonical generalized-metric projectors are the spectral plus/minus projectors,
- hence polarized lifts are fixed by those projectors,
- and a polarized relative-modular pair canonically induces a generalized-metric
  witness package without changing the underlying carrier data.
-/

namespace InfoGeometry.Canonical.GeneralizedMetricPolarizedBridge

open InfoGeometry.Canonical.GeneralizedMetricCore
open InfoGeometry.Canonical.RelativeModularPolarizedBridge
open InfoGeometry.Krein
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Krein.SplitQuadraticSheets

section PolarizedWitness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {betaPlus : Type*} [Fintype betaPlus] [Nonempty betaPlus]
variable {betaMinus : Type*} [Fintype betaMinus] [Nonempty betaMinus]

/-- A polarized relative-modular pair together with its canonical generalized-metric
fixpoint realization on the doubled carrier. -/
structure GeneralizedMetricPolarizedWitness
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (α : Type*) [Fintype α] [Nonempty α]
    (betaPlus : Type*) [Fintype betaPlus] [Nonempty betaPlus]
    (betaMinus : Type*) [Fintype betaMinus] [Nonempty betaMinus] where
  polarized : PolarizedRelativeModularPair H α betaPlus betaMinus
  plus_fixed :
    ∀ b : betaPlus,
      GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (polarized.plus.lift b) = polarized.plus.lift b
  minus_fixed :
    ∀ b : betaMinus,
      GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (polarized.minus.lift b) = polarized.minus.lift b

@[rep_depth krein]
noncomputable def PolarizedRelativeModularPair.toGeneralizedMetricWitness
    (R : PolarizedRelativeModularPair H α betaPlus betaMinus) :
    GeneralizedMetricPolarizedWitness H α betaPlus betaMinus where
  polarized := R
  plus_fixed := fun b =>
    tomitaGeneralizedMetricSeed_plusProjector_eq_self_of_mem_plusSheet
      (H := H) (u := R.plus.lift b) (R.plus.lift_mem b)
  minus_fixed := fun b =>
    tomitaGeneralizedMetricSeed_minusProjector_eq_self_of_mem_minusSheet
      (H := H) (u := R.minus.lift b) (R.minus.lift_mem b)

@[rep_depth krein, simp] theorem
    PolarizedRelativeModularPair.plus_lift_fixed_by_tomitaGeneralizedMetric
    (R : PolarizedRelativeModularPair H α betaPlus betaMinus) (b : betaPlus) :
    GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
      (R.plus.lift b) = R.plus.lift b := by
  simpa using
    (PolarizedRelativeModularPair.toGeneralizedMetricWitness (R := R)).plus_fixed b

@[rep_depth krein, simp] theorem
    PolarizedRelativeModularPair.minus_lift_fixed_by_tomitaGeneralizedMetric
    (R : PolarizedRelativeModularPair H α betaPlus betaMinus) (b : betaMinus) :
    GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
      (R.minus.lift b) = R.minus.lift b := by
  simpa using
    (PolarizedRelativeModularPair.toGeneralizedMetricWitness (R := R)).minus_fixed b

end PolarizedWitness

end InfoGeometry.Canonical.GeneralizedMetricPolarizedBridge
