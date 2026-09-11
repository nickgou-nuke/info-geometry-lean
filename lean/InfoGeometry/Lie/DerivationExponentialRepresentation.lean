import InfoGeometry.Lie.ContinuousDerivationExponential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornDerivationExponential
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Representation functoriality of derivation exponential flows

This module proves the exact analytic identity needed to transport a finite
exponential derivation flow through a represented operator algebra.

For complete real normed spaces `V` and `W`, let

`ρ : (V →L[ℝ] V) →A[ℝ] (W →L[ℝ] W)`

be a continuous real-algebra homomorphism.  Then

`ρ (exp (t • D)) = exp (t • ρ D)`.

Equivalently, with the derivation flow from
`InfoGeometry.Lie.ContinuousDerivationExponential`,

`ρ (flow D t) = flow (ρ D) t`.

The proof is native Mathlib: it is an application of `NormedSpace.map_exp`
together with real-linearity of `ρ`.

The final section specializes this theorem to the already constructed
coordinate endomorphism algebra of the canonical real Zorn carrier.  It does
not postulate a derivation-to-spin or derivation-to-BdG representation; such a
map must be supplied by a separate theorem owner.
-/

noncomputable section

namespace InfoGeometry.Lie.DerivationExponentialRepresentation

open InfoGeometry.Lie.ContinuousDerivationExponential
open InfoGeometry.Lie.CanonicalZornDerivationExponential
open InfoGeometry.Lie.CanonicalZornDerivation

section EndomorphismRepresentation

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

local notation "EndV" => V →L[ℝ] V
local notation "EndW" => W →L[ℝ] W

noncomputable local instance : NormedRing EndV := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndV := inferInstance
local instance : IsTopologicalRing EndV := inferInstance
local instance : CompleteSpace EndV := inferInstance

noncomputable local instance : NormedRing EndW := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndW := inferInstance
local instance : IsTopologicalRing EndW := inferInstance
local instance : CompleteSpace EndW := inferInstance

/--
A continuous algebra representation between bounded endomorphism algebras
commutes with the Banach-algebra exponential.
-/
theorem continuousAlgHom_map_exp
    (ρ : EndV →A[ℝ] EndW)
    (D : EndV) :
    ρ (NormedSpace.exp D) = NormedSpace.exp (ρ D) := by
  letI : NormedAlgebra ℚ EndV := NormedAlgebra.restrictScalars ℚ ℝ EndV
  letI : NormedAlgebra ℚ EndW := NormedAlgebra.restrictScalars ℚ ℝ EndW
  exact NormedSpace.map_exp ρ ρ.continuous D

/--
Time-scaled exponential functoriality:

`ρ (exp (tD)) = exp (t ρ(D))`.
-/
theorem continuousAlgHom_map_exp_smul
    (ρ : EndV →A[ℝ] EndW)
    (D : EndV)
    (t : ℝ) :
    ρ (NormedSpace.exp (t • D)) =
      NormedSpace.exp (t • ρ D) := by
  rw [continuousAlgHom_map_exp ρ (t • D)]
  rw [ρ.map_smul]

/-- The represented exponential flow. -/
noncomputable def representedFlow
    (ρ : EndV →A[ℝ] EndW)
    (D : EndV)
    (t : ℝ) : EndW :=
  InfoGeometry.Lie.ContinuousDerivationExponential.flow (ρ D) t

/--
Main representation-intertwining theorem:

`ρ (flow D t) = flow (ρ D) t`.
-/
theorem map_flow
    (ρ : EndV →A[ℝ] EndW)
    (D : EndV)
    (t : ℝ) :
    ρ (InfoGeometry.Lie.ContinuousDerivationExponential.flow D t) = representedFlow ρ D t := by
  simpa [InfoGeometry.Lie.ContinuousDerivationExponential.flow, representedFlow] using
    continuousAlgHom_map_exp_smul ρ D t

/-- Time-one form of the representation-intertwining theorem. -/
theorem map_exp_generator
    (ρ : EndV →A[ℝ] EndW)
    (D : EndV) :
    ρ (InfoGeometry.Lie.ContinuousDerivationExponential.flow D 1) = InfoGeometry.Lie.ContinuousDerivationExponential.flow (ρ D) 1 := by
  simpa [representedFlow] using map_flow ρ D 1

/-- The represented flow starts at the identity. -/
@[simp]
theorem representedFlow_zero
    (ρ : EndV →A[ℝ] EndW)
    (D : EndV) :
    representedFlow ρ D 0 = 1 := by
  exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_zero (ρ D)

/-- The represented flow has the one-parameter group law. -/
theorem representedFlow_add
    (ρ : EndV →A[ℝ] EndW)
    (D : EndV)
    (s t : ℝ) :
    representedFlow ρ D (s + t) =
      representedFlow ρ D s * representedFlow ρ D t := by
  exact InfoGeometry.Lie.ContinuousDerivationExponential.flow_add (ρ D) s t

/-- Negating the source generator reverses represented time. -/
@[simp]
theorem representedFlow_neg_generator
    (ρ : EndV →A[ℝ] EndW)
    (D : EndV)
    (t : ℝ) :
    representedFlow ρ (-D) t = representedFlow ρ D (-t) := by
  simp [representedFlow, InfoGeometry.Lie.ContinuousDerivationExponential.flow_neg_generator]

/-- The represented positive and negative flows multiply to the identity. -/
theorem representedFlow_mul_neg
    (ρ : EndV →A[ℝ] EndW)
    (D : EndV)
    (t : ℝ) :
    representedFlow ρ D t * representedFlow ρ (-D) t = 1 := by
  rw [representedFlow_neg_generator]
  simpa [representedFlow] using InfoGeometry.Lie.ContinuousDerivationExponential.flow_mul_flow_neg (ρ D) t

/-- Reverse inverse identity for the represented flow. -/
theorem representedFlow_neg_mul
    (ρ : EndV →A[ℝ] EndW)
    (D : EndV)
    (t : ℝ) :
    representedFlow ρ (-D) t * representedFlow ρ D t = 1 := by
  rw [representedFlow_neg_generator]
  simpa [representedFlow] using InfoGeometry.Lie.ContinuousDerivationExponential.flow_neg_mul_flow (ρ D) t

/-- The infinitesimal generator of the represented finite flow is `ρ D`. -/
theorem deriv_representedFlow_at_zero
    (ρ : EndV →A[ℝ] EndW)
    (D : EndV) :
    deriv (representedFlow ρ D) 0 = ρ D := by
  simpa [representedFlow] using InfoGeometry.Lie.ContinuousDerivationExponential.deriv_flow_at_zero (ρ D)

/-- Continuous algebra representations preserve operator commutators. -/
theorem map_commutator
    (ρ : EndV →A[ℝ] EndW)
    (D E : EndV) :
    ρ (D * E - E * D) =
      ρ D * ρ E - ρ E * ρ D := by
  simp

/-- Lie-bracket form of `map_commutator`. -/
theorem map_lie
    (ρ : EndV →A[ℝ] EndW)
    (D E : EndV) :
    ρ ⁅D, E⁆ = ⁅ρ D, ρ E⁆ := by
  simp [Ring.lie_def]

/--
Exponential functoriality for a commutator generator.  This is the finite-flow
counterpart of preservation of the represented curvature/commutator.
-/
theorem map_commutator_flow
    (ρ : EndV →A[ℝ] EndW)
    (D E : EndV)
    (t : ℝ) :
    ρ (InfoGeometry.Lie.ContinuousDerivationExponential.flow (D * E - E * D) t) =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow (ρ D * ρ E - ρ E * ρ D) t := by
  rw [map_flow]
  simp [representedFlow, map_commutator]

/-- Lie-bracket version of `map_commutator_flow`. -/
theorem map_lie_flow
    (ρ : EndV →A[ℝ] EndW)
    (D E : EndV)
    (t : ℝ) :
    ρ (InfoGeometry.Lie.ContinuousDerivationExponential.flow ⁅D, E⁆ t) =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow ⁅ρ D, ρ E⁆ t := by
  rw [map_flow]
  simp [representedFlow, map_lie]

end EndomorphismRepresentation

section CanonicalZornCoordinateRepresentation

open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal

abbrev V8 := InfoGeometry.Algebra.FiniteSpin.Vec8R
local notation "EndV8" => V8 →L[ℝ] V8

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
local notation "EndW" => W →L[ℝ] W

noncomputable local instance : NormedRing EndV8 := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndV8 := inferInstance
local instance : IsTopologicalRing EndV8 := inferInstance
local instance : CompleteSpace EndV8 := inferInstance

noncomputable local instance : NormedRing EndW := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndW := inferInstance
local instance : IsTopologicalRing EndW := inferInstance
local instance : CompleteSpace EndW := inferInstance

/--
Any genuine continuous algebra representation of the canonical Zorn coordinate
endomorphism algebra transports the already constructed Zorn derivation flow to
the exponential of the represented generator.
-/
theorem map_canonicalZorn_coordFlow
    (ρ : EndV8 →A[ℝ] EndW)
    (D : InfoGeometry.Lie.CanonicalZornDerivation.EndCZ)
    (t : ℝ) :
    ρ (InfoGeometry.Lie.CanonicalZornDerivationExponential.coordFlow D t) =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow (ρ (InfoGeometry.Lie.CanonicalZornDerivationExponential.coordEnd D)) t := by
  simpa [InfoGeometry.Lie.CanonicalZornDerivationExponential.coordFlow, representedFlow] using
    map_flow ρ (InfoGeometry.Lie.CanonicalZornDerivationExponential.coordEnd D) t

/-- Time-one specialization of `map_canonicalZorn_coordFlow`. -/
theorem map_canonicalZorn_coordFlow_one
    (ρ : EndV8 →A[ℝ] EndW)
    (D : InfoGeometry.Lie.CanonicalZornDerivation.EndCZ) :
    ρ (InfoGeometry.Lie.CanonicalZornDerivationExponential.coordFlow D 1) =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow (ρ (InfoGeometry.Lie.CanonicalZornDerivationExponential.coordEnd D)) 1 := by
  exact map_canonicalZorn_coordFlow ρ D 1

/--
For a bundled canonical Zorn derivation, every supplied continuous operator
representation therefore intertwines its complete finite exponential flow.
-/
theorem canonicalZorn_derivation_representation_packet
    (ρ : EndV8 →A[ℝ] EndW)
    (D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations)
    (t : ℝ) :
    ρ (InfoGeometry.Lie.CanonicalZornDerivationExponential.coordFlow D.1 t) =
      InfoGeometry.Lie.ContinuousDerivationExponential.flow (ρ (InfoGeometry.Lie.CanonicalZornDerivationExponential.coordEnd D.1)) t := by
  exact map_canonicalZorn_coordFlow ρ D.1 t

end CanonicalZornCoordinateRepresentation

end InfoGeometry.Lie.DerivationExponentialRepresentation

end noncomputable section
