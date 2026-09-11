import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.Canonical.MaurerCartanFactorization
import InfoGeometry.Canonical.RedlineGrandSynthesis
import InfoGeometry.Canonical.DeRhamThermodynamicPotential
import InfoGeometry.KMSGNS

/-!
# Inner derivations, quotient classes, and positive relative densities

The historical thermodynamic names below denote three algebraic statements:

* a derivation has zero quotient class exactly when it is inner;
* the commutator of a derivation `D` with `ad K` equals `ad (D K)`;
* the positive relative density equals the exponential of the negative
  relative modular potential.

The quotient statement does not choose a splitting or a unique inner
representative. The commutator may vanish. The density identity is pointwise
on canonical gauge sections of positive rays; it is not a differential-form
or evolution equation. No physical interpretation is needed for these claims.
-/

noncomputable section

namespace InfoGeometry.Canonical.Thermodynamics

open InfoGeometry.Modular.ExactSequence
open InfoGeometry.Canonical.MaurerCartanFactorization
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.DeRhamPotential

variable {A : Type*} [Ring A]

/-- The additive derivations of the underlying ring. -/
abbrev TotalDynamics (A : Type*) [Ring A] := Derivation A

/-- The historical predicate `isHeatFlow` means that the derivation is inner. -/
def isHeatFlow (D : Derivation A) : Prop :=
  ∃ K : A, ∀ x : A, D x = (modularDerivation K) x

/-- Quotient of derivations by the native inner-derivation relation. -/
abbrev MacroscopicWork (A : Type*) [Ring A] :=
  ModularFlowHomogeneousSpace A

/-- The zero quotient class consists precisely of inner derivations. -/
theorem first_law_exact_sequence (D : Derivation A) :
    modularFlowProjection D = outZero ↔ isHeatFlow D :=
  exact_sequence_inner_iff_kernel D

/-- Commuting a derivation with an inner derivation gives an inner derivation. -/
theorem work_induces_heat_friction (D : Derivation A) (K : A) :
    Derivation.derivationCommutator D (modularDerivation K) = modularDerivation (D K) := by
  ext X
  exact dual_flow_commutator D K X

/-- Pointwise exponential recovery of the relative density from its potential. -/
theorem heat_is_logarithmic_volume_dilation
    {α : Type*} [Fintype α] [Nonempty α]
    (q q₁ : PositiveRay α) (a : α) :
    relativeDensity q q₁ a = Real.exp (- relativeModularPotential q q₁ a) := by
  rw [relativeDensity_eq_exp_relativeLogDensity,
    relativeModularPotential_eq_neg_relativeLogDensity, neg_neg]

end InfoGeometry.Canonical.Thermodynamics

end noncomputable section
