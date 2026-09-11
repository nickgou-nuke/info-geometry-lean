import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Krein.PolarizedSector
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.StandardFormCore

Minimal owner interfaces for a future standard-form / relative-modular layer.

This file deliberately stops short of a full Tomita-Takesaki standard-form
development. It packages:
- vector states on the doubled carrier,
- the current split-`Cl(1,1)` modular atom as a standard-form seed,
- a generator-based carrier for future modular operators,
- a bridge from operator cocycles to projective relative potentials.
-/

namespace InfoGeometry.Canonical.StandardFormCore

open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Volume.ConnesCocycle
open InfoGeometry.Krein
open PolarizedSector
open SplitQuadraticSheets

section OperatorCarrier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H2" => InfoGeometry.Krein.DoubledSpace H
local notation "EndH" => AlgebraEnd H

/-- Real vector state on the doubled carrier. -/
structure VectorState
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  vector : InfoGeometry.Krein.DoubledSpace H

/-- Expectation of an operator against a doubled-space vector state. -/
@[rep_depth krein]
noncomputable def VectorState.expectation
    (ω : VectorState H) (A : EndH) : ℝ :=
  ⟪A ω.vector, ω.vector⟫_ℝ

/--
Split-`Cl(1,1)` modular seed currently available in the repo:
conjugation `J`, sign `ε`, internal phase axis `Jε`, and the induced additive
modular flow on doubled-space endomorphisms.
-/
structure StandardFormSeed
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  J : AlgebraEnd H
  ε : AlgebraEnd H
  phaseAxis : AlgebraEnd H
  modularFlow : AdditiveModularFlow (H := H)
  J_sq : J.comp J = ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace H)
  eps_sq : ε.comp ε = ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace H)
  phase_sq : phaseAxis.comp phaseAxis =
    -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace H))
  J_phase_anticommute : J.comp phaseAxis = -(phaseAxis.comp J)

/-- The `+1` projector associated to the seed grading operator. -/
@[rep_depth krein]
noncomputable def StandardFormSeed.plusProjector (S : StandardFormSeed H) : EndH :=
  (⅟ (2 : ℝ)) • ((ContinuousLinearMap.id ℝ H2) + S.ε)

/-- The `-1` projector associated to the seed grading operator. -/
@[rep_depth krein]
noncomputable def StandardFormSeed.minusProjector (S : StandardFormSeed H) : EndH :=
  (⅟ (2 : ℝ)) • ((ContinuousLinearMap.id ℝ H2) - S.ε)

/-- The current modular atom packaged as a standard-form seed. -/
@[rep_depth krein]
noncomputable def tomitaAtomSeed : StandardFormSeed H where
  J := modularConjugationJ (E := H)
  ε := modularSignEpsilon (E := H)
  phaseAxis := modularComplexI (E := H)
  modularFlow := modularSignAdditiveModularFlow (E := H)
  J_sq := modularConjugationJ_sq (E := H)
  eps_sq := modularSignEpsilon_sq (E := H)
  phase_sq := modularComplexI_sq (E := H)
  J_phase_anticommute := modularConjugationJ_anticommutes_modularComplexI (E := H)

@[rep_depth krein, simp] theorem tomitaAtomSeed_modularFlow_eq :
    (tomitaAtomSeed (H := H)).modularFlow = modularSignAdditiveModularFlow (E := H) := rfl

/-- The seed phase axis is exactly the doubled-space dilation operator. -/
@[rep_depth krein, simp] theorem tomitaAtomSeed_phaseAxis_eq_dilationOperator :
    (tomitaAtomSeed (H := H)).phaseAxis = InfoGeometry.Krein.dilationOperator (E := H) :=
  modularComplexI_eq_dilationOperator (E := H)

@[rep_depth krein, simp] theorem tomitaAtomSeed_J_eq_modular_j :
    (tomitaAtomSeed (H := H)).J = modular_j (E := H) := rfl

@[rep_depth krein, simp] theorem tomitaAtomSeed_eps_eq_spectral_epsilon :
    (tomitaAtomSeed (H := H)).ε = spectral_epsilon (E := H) := rfl

@[rep_depth krein, simp] theorem tomitaAtomSeed_phaseAxis_eq_complex_i :
    (tomitaAtomSeed (H := H)).phaseAxis = complex_i (E := H) := by
  change modularComplexI (E := H) = complex_i (E := H)
  exact InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i (E := H)

@[rep_depth krein, simp] theorem tomitaAtomSeed_phaseAxis_eq_J_comp_eps :
    (tomitaAtomSeed (H := H)).phaseAxis =
      (tomitaAtomSeed (H := H)).J.comp (tomitaAtomSeed (H := H)).ε := by
  rfl

@[rep_depth krein, simp] theorem tomitaAtomSeed_J_comp_phaseAxis_eq_eps :
    (tomitaAtomSeed (H := H)).J.comp (tomitaAtomSeed (H := H)).phaseAxis
      = (tomitaAtomSeed (H := H)).ε := by
  change (modularConjugationJ (E := H)).comp (modularComplexI (E := H))
      = modularSignEpsilon (E := H)
  simpa using (InfoGeometry.Krein.modular_j_comp_complex_i (E := H))

@[rep_depth krein, simp] theorem tomitaAtomSeed_phaseAxis_comp_J_eq_neg_eps :
    (tomitaAtomSeed (H := H)).phaseAxis.comp (tomitaAtomSeed (H := H)).J
      = -((tomitaAtomSeed (H := H)).ε) := by
  change (modularComplexI (E := H)).comp (modularConjugationJ (E := H))
      = -(modularSignEpsilon (E := H))
  simpa using (InfoGeometry.Krein.complex_i_comp_modular_j (E := H))

@[rep_depth krein, simp] theorem tomitaAtomSeed_phaseAxis_comp_eps_eq_J :
    (tomitaAtomSeed (H := H)).phaseAxis.comp (tomitaAtomSeed (H := H)).ε
      = (tomitaAtomSeed (H := H)).J := by
  change (modularComplexI (E := H)).comp (modularSignEpsilon (E := H))
      = modularConjugationJ (E := H)
  simpa using (InfoGeometry.Krein.complex_i_comp_spectral_epsilon (E := H))

@[rep_depth krein, simp] theorem tomitaAtomSeed_eps_comp_phaseAxis_eq_neg_J :
    (tomitaAtomSeed (H := H)).ε.comp (tomitaAtomSeed (H := H)).phaseAxis
      = -((tomitaAtomSeed (H := H)).J) := by
  change (modularSignEpsilon (E := H)).comp (modularComplexI (E := H))
      = -(modularConjugationJ (E := H))
  simpa using (InfoGeometry.Krein.spectral_epsilon_comp_complex_i (E := H))

@[rep_depth krein, simp] theorem tomitaAtomSeed_eps_comp_J_eq_neg_phaseAxis :
    (tomitaAtomSeed (H := H)).ε.comp (tomitaAtomSeed (H := H)).J
      = -((tomitaAtomSeed (H := H)).phaseAxis) := by
  change (modularSignEpsilon (E := H)).comp (modularConjugationJ (E := H))
      = -(modularComplexI (E := H))
  simpa using (InfoGeometry.Krein.spectral_epsilon_comp_modular_j (E := H))

@[rep_depth krein, simp] theorem tomitaAtomSeed_plusProjector_eq_spectralPlusProj :
    StandardFormSeed.plusProjector (tomitaAtomSeed (H := H)) = spectralPlusProj (E := H) := rfl

@[rep_depth krein, simp] theorem tomitaAtomSeed_minusProjector_eq_spectralMinusProj :
    StandardFormSeed.minusProjector (tomitaAtomSeed (H := H)) = spectralMinusProj (E := H) := rfl

@[rep_depth krein] theorem tomitaAtomSeed_plusProjector_mem_plusSheet (u : H2) :
    StandardFormSeed.plusProjector (tomitaAtomSeed (H := H)) u ∈ plusSheet (E := H) := by
  simpa using spectralPlusProj_mem_plusSheet (E := H) u

@[rep_depth krein] theorem tomitaAtomSeed_minusProjector_mem_minusSheet (u : H2) :
    StandardFormSeed.minusProjector (tomitaAtomSeed (H := H)) u ∈ minusSheet (E := H) := by
  simpa using spectralMinusProj_mem_minusSheet (E := H) u

@[rep_depth krein] theorem VectorState.expectation_id
    (ω : VectorState H) :
    ω.expectation (ContinuousLinearMap.id ℝ H2) = ⟪ω.vector, ω.vector⟫_ℝ := by
  simp [VectorState.expectation]

@[rep_depth krein] theorem VectorState.expectation_neg_id
    (ω : VectorState H) :
    ω.expectation (-(ContinuousLinearMap.id ℝ H2)) = -⟪ω.vector, ω.vector⟫_ℝ := by
  simp [VectorState.expectation]

@[rep_depth krein] theorem tomitaAtomSeed_phaseAxis_sq_expectation
    (ω : VectorState H) :
    ω.expectation ((tomitaAtomSeed (H := H)).phaseAxis.comp (tomitaAtomSeed (H := H)).phaseAxis)
      = -⟪ω.vector, ω.vector⟫_ℝ := by
  rw [(tomitaAtomSeed (H := H)).phase_sq]
  simpa using (VectorState.expectation_neg_id (H := H) ω)

/--
Generator-based carrier for a future standard-form layer.

`Delta` is a concrete carrier generator for this finite doubled-space model,
while `seed.modularFlow` is required to be the flow generated by `Delta`.
This is a finite carrier interface, not a replacement for a Tomita theorem.
Later files can connect it to cyclic/separating hypotheses and relative
modular operators through proved construction lemmas.
-/
structure StandardFormCarrier
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  seed : StandardFormSeed H
  Delta : AlgebraEnd H
  referenceState : VectorState H
  modularFlow_eq_generator :
    seed.modularFlow = additiveModularFlowOfGenerator (H := H) Delta

/--
The carrier modular flow is spatially implemented by the concrete generator
`Delta` in this concrete doubled-space carrier.

This is not a general assertion that Tomita modular automorphisms are inner
inside an arbitrary von Neumann algebra; type III modular flows are typically
outer at the algebra level.
-/
@[rep_depth operator, simp] theorem StandardFormCarrier.modularFlow_apply
    (S : StandardFormCarrier H) (t : ℝ) (A : EndH) :
    S.seed.modularFlow t A = InfoGeometry.Krein.modular_shift (E := H) S.Delta t A := by
  have h :=
    congrArg (fun σ : AdditiveModularFlow (H := H) => σ t A) S.modularFlow_eq_generator
  simpa [additiveModularFlowOfGenerator_apply] using h

end OperatorCarrier

section ProjectiveBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]

local notation "EndH" => AlgebraEnd H

/--
Bridge package joining:
- a generator-based modular carrier on doubled-space operators,
- a Connes cocycle on that carrier,
- a pair of projective positive states in the relative-potential layer.
-/
structure RelativeModularBridge
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (α : Type*) [Fintype α] [Nonempty α] where
  carrier : StandardFormCarrier H
  source : PositiveRay α
  target : PositiveRay α
  cocycle : ℝ → AlgebraEnd H
  scalarBridge : ScalarCocycleBridge (H := H) carrier.seed.modularFlow
  isCocycle : IsConnesCocycle carrier.seed.modularFlow cocycle

/-- Projective relative log-density attached to the source/target pair. -/
@[rep_depth projective]
noncomputable def RelativeModularBridge.projectiveLogDensity
    (R : RelativeModularBridge (H := H) (α := α)) : α → ℝ :=
  relativeLogDensity R.source R.target

/-- Projective modular potential attached to the source/target pair. -/
@[rep_depth projective]
noncomputable def RelativeModularBridge.projectiveModularPotential
    (R : RelativeModularBridge (H := H) (α := α)) : α → ℝ :=
  relativeModularPotential R.source R.target

/-- Scalar logarithmic cocycle potential induced from the operator cocycle. -/
@[rep_depth operator]
noncomputable def RelativeModularBridge.operatorLogPotential
    (R : RelativeModularBridge (H := H) (α := α)) : ℝ → ℝ :=
  cocycleLogPotential (H := H) R.carrier.seed.modularFlow R.cocycle R.scalarBridge

/-- The operator cocycle log-potential is additive in time. -/
theorem RelativeModularBridge.operatorLogPotential_add
    (R : RelativeModularBridge (H := H) (α := α)) (s t : ℝ) :
    R.operatorLogPotential (s + t)
      = R.operatorLogPotential s + R.operatorLogPotential t := by
  simpa [RelativeModularBridge.operatorLogPotential] using
    cocycleLogPotential_add
      (H := H) R.carrier.seed.modularFlow R.cocycle R.isCocycle R.scalarBridge s t

/-- The projective modular potential is the negative projective log-density. -/
@[rep_depth projective, simp] theorem
    RelativeModularBridge.projectiveModularPotential_eq_neg_projectiveLogDensity
    (R : RelativeModularBridge (H := H) (α := α)) (a : α) :
    R.projectiveModularPotential a = -R.projectiveLogDensity a := by
  exact relativeModularPotential_eq_neg_relativeLogDensity R.source R.target a

/--
The projective modular potential is the target/source log-density difference on
the canonical gauge slice.
-/
@[rep_depth projective, simp] theorem
    RelativeModularBridge.projectiveModularPotential_eq_logDensity_target_sub_source
    (R : RelativeModularBridge (H := H) (α := α)) (a : α) :
    R.projectiveModularPotential a
      = InfoGeometry.Canonical.PositiveRayCore.logDensity (α := α) R.target a
        - InfoGeometry.Canonical.PositiveRayCore.logDensity (α := α) R.source a := by
  exact relativeModularPotential_eq_logDensity_base_sub_logDensity R.source R.target a

end ProjectiveBridge

end InfoGeometry.Canonical.StandardFormCore
