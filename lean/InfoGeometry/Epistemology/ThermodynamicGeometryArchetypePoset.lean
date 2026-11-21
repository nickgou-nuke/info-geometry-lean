/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Order.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype

/-!
# Source-grounded thermodynamic geometry archetypes

This finite poset is an index of proved owner-level archetypes and one explicit
open target. Its edges record only source-level derivation/dependency relations
confirmed in the current checkout; related vocabulary alone creates no edge.

The owner audit behind these labels is:

* `OperatorAlgebra/PeirceSpine/RealBdGKreinChiralIdealTwoSheetBridge.lean`:
  the two directed Peirce wings yield the symmetric product `metricGV` and
  commutator `curvSigmaV`, with `framePhiV_sq_eq_metricGV`,
  `frameJV_mul_framePhiV`, and `emergent_cartan_curvature_torsion_split`.
  This is an algebraic ring-level readout, not yet a spacetime metric tensor.
* `Canonical/NoncommutativeGibbsBKMHessianBridge.lean`:
  differentiating the additive Gibbs log-partition gives the centered BKM
  covariance under the explicit self-adjointness and positive-partition
  hypotheses (`secondFDeriv_logPartition_apply_eq_centeredBKM`).
* `Canonical/SouriauOnsagerBKMFilteredColimit.lean` and
  `Canonical/SouriauOnsagerBKMHestenesAnalyticColimit.lean`:
  filtered BKM kernels descend to a Hestenes--Krein colimit under the stated
  direct-system and functional-descent premises.
* `Canonical/FilteredHestenesKreinColimit.lean` and
  `Canonical/HestenesKreinSouriauCalibrationColimit.lean`:
  compatible real doubled carriers support stage/limit readout identities;
  the zeta calibration identity remains a supplied premise.
* `OperatorAlgebra/RealDoubledChiralKreinGravity.lean`:
  finite graph-section data induces the symmetric matrix `H + Hᵀ` and dual
  connection compatibility. The owner explicitly does not prove curvature
  or Einstein dynamics.
* `Canonical/ParaKahlerMaurerCartanQGT.lean` and
  `Canonical/RealGradedTensorSuperGrassmannianBridge.lean`:
  algebraic para-Kähler identities and real graded CAR/superbracket
  intertwiners, respectively. Neither constructs the thermodynamic
  spacetime target below.
* `Geometry/Statistical/DualFlatCurvature.lean`:
  the curvature commutator identity is derived from a datum whose curvature
  sum and both flatness laws are explicit fields. `Canonical/
  SouriauOperatorialLogPotential.lean` defines an operatorial exponential
  family as parameterized maps; it does not construct a smooth statistical
  manifold from the doubled sheets.
* `QuantumGeometry/Projective/QGT.lean`:
  Fubini--Study metric, Berry curvature, and phase invariance on normalized
  complex Hilbert vectors. This proved complex projective owner is kept
  distinct from the real doubled/Krein carrier.
* `Canonical/SuperGrassmannianFiveGradedEightByEight.lean` and
  `Canonical/RealGradedTensorSuperGrassmannianBridge.lean`:
  a finite real 8-dimensional Fock representation and its real graded
  tensor/Krein intertwiners.
* `Canonical/SouriauKillingLipschitzBridge.lean` and
  `Canonical/SouriauHestenesRealTensorBridge.lean`:
  finite flat Rindler/Lipschitz and real Hestenes tensor rotor identities.
  The former also constructs a salient future cone on the actual real
  `Vec11` carrier and proves that the concrete `Cl(1,1)` Lipschitz rotor
  preserves it. It also proves that the full real `(1,3)` Rindler boost
  preserves the future causal cone, including the transverse bound, while
  its longitudinal projection is the `Cl(1,1)` Lipschitz action. These are
  finite-dimensional flow statements, not a curved spacetime equilibrium
  theorem.
* `Canonical/SpinorLieDerivative.lean` packages a spinor bilinear action as
  data and proves the conformal/equilibrium readout from its supplied
  bilinear law. `SouriauKillingLipschitzBridge.lean` separately proves the
  finite matrix Rindler Kosmann correction identity. These are conditional
  and finite-carrier results: neither constructs a spinor bundle with its
  induced connection or proves the geometric Kosmann formula on a curved
  manifold.
* `Dynamics/BisognanoWichmann.lean` and `Holography/ModularFlowKMS.lean`
  provide finite imaginary-rapidity and algebraic KMS-phase models. Their
  module contracts explicitly exclude the analytic Bisognano--Wichmann
  theorem, standard-form modular conjugation, and horizon/commutant duality.
  The word “horizon” in the finite Cuntz crossing is a name for an algebraic
  invariant, not a spacetime horizon.
* `Canonical/NoncommutativeGibbsBKMHessianBridge.lean` proves the finite
  additive Gibbs log-partition Hessian/centered-BKM identity under
  self-adjointness and positive-partition hypotheses. This does not identify
  the Hessian with a geometric Killing-temperature cone. The separate
  Onsager and Souriau operator-form owners do not by themselves identify a
  symplectic cocycle with Casimir/Onsager curvature.
* `Canonical/FisherKreinVielbeinEinsteinBridge.lean`:
  the finite calibrated Fisher--Krein/vielbein/Einstein readout, with its
  explicit sign calibration.

The nodes remain incomparable where the owners expose no proved map or
derivation. In particular, `emergentThermodynamicSpacetime` is marked open and
has no incoming proof edge: the existing finite algebraic, Hessian, frame, and
colimit results do not yet construct that unified geometric object.
-/

namespace InfoGeometry.Epistemology.ThermodynamicGeometryArchetypePoset

/-- Archetypes named by their actual owner-level mathematical content. -/
inductive Archetype where
  | peirceWingPair
  | peirceMetricCurvatureReadout
  | finiteGibbsMassieuVariation
  | operatorExponentialFamilyDefinition
  | centeredBKMHessian
  | filteredBKMKernel
  | realHestenesKreinCone
  | bkmHestenesColimitDescent
  | thermalCalibrationPremise
  | realMassieuCalibrationReadout
  | finiteDoubledKreinFrame
  | finiteKreinGravityDatum
  | graphSectionMetricReadout
  | paraKahlerModule
  | dualFlatCurvatureDatum
  | complexFubiniStudyQGT
  | fiveGradedFockRepresentation
  | realGradedFockTensor
  | souriauRindlerKillingRotor
  | finiteKosmannCorrection
  | assumedSpinorBilinearAction
  | curvedSpinorBundleKosmannTheorem
  | kerrLoxodromicHorizonIdentification
  | finiteBisognanoWichmannModel
  | analyticBisognanoWichmannKMSTheorem
  | finiteHorizonKMSCrossing
  | horizonCommutantDuality
  | finiteGibbsBKMHessian
  | killingConeBKMIdentification
  | finiteOnsagerCasimirReciprocity
  | symplecticCocycleOnsagerCurvatureIdentification
  | futureRindlerTemperatureCone
  | fullMinkowskiRindlerFutureCone
  | hestenesRealTensorRotor
  | fisherRaoMetric
  | solderingVielbeinCalibration
  | fisherKreinEinsteinReadout
  | emergentThermodynamicSpacetime
  deriving DecidableEq, Repr

open Archetype

/-- The strict dependency edges supported by the owner audit in this file's
module documentation. Branches without an established bridge are left apart. -/
def dependencyEdgeCode : Archetype → Archetype → Bool
  | .peirceWingPair, .peirceMetricCurvatureReadout => true
  | .finiteGibbsMassieuVariation, .centeredBKMHessian => true
  | .filteredBKMKernel, .bkmHestenesColimitDescent => true
  | .realHestenesKreinCone, .bkmHestenesColimitDescent => true
  | .realHestenesKreinCone, .realMassieuCalibrationReadout => true
  | .thermalCalibrationPremise, .realMassieuCalibrationReadout => true
  | .finiteKreinGravityDatum, .graphSectionMetricReadout => true
  | .fiveGradedFockRepresentation, .realGradedFockTensor => true
  | .souriauRindlerKillingRotor, .hestenesRealTensorRotor => true
  | .souriauRindlerKillingRotor, .futureRindlerTemperatureCone => true
  | .souriauRindlerKillingRotor, .fullMinkowskiRindlerFutureCone => true
  | .souriauRindlerKillingRotor, .finiteKosmannCorrection => true
  | .finiteGibbsMassieuVariation, .finiteGibbsBKMHessian => true
  | .fisherRaoMetric, .fisherKreinEinsteinReadout => true
  | .solderingVielbeinCalibration, .fisherKreinEinsteinReadout => true
  | _, _ => false

/-- A proposition-valued view of the finite adjacency code. -/
def dependencyEdge (a b : Archetype) : Prop := dependencyEdgeCode a b = true

/-- A stage number witnessing acyclicity; equal stages deliberately do not
order distinct independent archetypes. -/
def rank : Archetype → ℕ
  | .peirceWingPair => 0
  | .peirceMetricCurvatureReadout => 1
  | .finiteGibbsMassieuVariation => 0
  | .operatorExponentialFamilyDefinition => 0
  | .centeredBKMHessian => 1
  | .filteredBKMKernel => 0
  | .realHestenesKreinCone => 0
  | .bkmHestenesColimitDescent => 1
  | .thermalCalibrationPremise => 0
  | .realMassieuCalibrationReadout => 1
  | .finiteDoubledKreinFrame => 0
  | .finiteKreinGravityDatum => 0
  | .graphSectionMetricReadout => 1
  | .paraKahlerModule => 0
  | .dualFlatCurvatureDatum => 0
  | .complexFubiniStudyQGT => 0
  | .fiveGradedFockRepresentation => 0
  | .realGradedFockTensor => 1
  | .souriauRindlerKillingRotor => 0
  | .finiteKosmannCorrection => 1
  | .assumedSpinorBilinearAction => 0
  | .curvedSpinorBundleKosmannTheorem => 0
  | .kerrLoxodromicHorizonIdentification => 0
  | .finiteBisognanoWichmannModel => 0
  | .analyticBisognanoWichmannKMSTheorem => 0
  | .finiteHorizonKMSCrossing => 1
  | .horizonCommutantDuality => 0
  | .finiteGibbsBKMHessian => 1
  | .killingConeBKMIdentification => 0
  | .finiteOnsagerCasimirReciprocity => 0
  | .symplecticCocycleOnsagerCurvatureIdentification => 0
  | .futureRindlerTemperatureCone => 1
  | .fullMinkowskiRindlerFutureCone => 1
  | .hestenesRealTensorRotor => 1
  | .fisherRaoMetric => 0
  | .solderingVielbeinCalibration => 0
  | .fisherKreinEinsteinReadout => 1
  | .emergentThermodynamicSpacetime => 0

theorem dependencyEdge_rank_lt {a b : Archetype} (h : dependencyEdge a b) :
    rank a < rank b := by
  cases a <;> cases b <;> simp [dependencyEdge, dependencyEdgeCode, rank] at h ⊢

private theorem rank_lt_of_transGen {a b : Archetype}
    (h : Relation.TransGen dependencyEdge a b) : rank a < rank b := by
  induction h using Relation.TransGen.trans_induction_on with
  | single h => exact dependencyEdge_rank_lt h
  | trans h₁ h₂ ih₁ ih₂ => exact Nat.lt_trans ih₁ ih₂

/-- Nonempty dependency reachability, hence the strict causal relation. -/
def causalBefore (a b : Archetype) : Prop :=
  Relation.TransGen dependencyEdge a b

/-- Reflexive dependency reachability is the non-strict order. -/
def causallyAtMost (a b : Archetype) : Prop :=
  a = b ∨ causalBefore a b

instance : PartialOrder Archetype where
  le := causallyAtMost
  lt a b := causallyAtMost a b ∧ ¬ causallyAtMost b a
  le_refl a := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | hab
    · exact hbc
    · rcases hbc with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr (Relation.TransGen.trans hab hbc)
  le_antisymm a b hab hba := by
    rcases hab with hab | hab
    · exact hab
    · rcases hba with hba | hba
      · exact hba.symm
      · exact False.elim (Nat.lt_asymm
          (rank_lt_of_transGen hab) (rank_lt_of_transGen hba))
  lt_iff_le_not_ge a b := by
    rfl

@[simp] theorem le_iff_eq_or_causalBefore (a b : Archetype) :
    a ≤ b ↔ a = b ∨ causalBefore a b := Iff.rfl

theorem causalBefore_rank_lt {a b : Archetype} (h : a < b) :
    rank a < rank b := by
  rcases h.1 with hab | hab
  · subst b
    exact False.elim (h.2 (Or.inl rfl))
  · exact rank_lt_of_transGen hab

/-- Distinct archetypes at the same stage are incomparable. -/
theorem incomparable_of_rank_eq {a b : Archetype}
    (hr : rank a = rank b) (hne : a ≠ b) :
    ¬ a ≤ b ∧ ¬ b ≤ a := by
  constructor
  · intro h
    rcases h with h | h
    · exact hne h
    · have hlt := rank_lt_of_transGen h
      rw [hr] at hlt
      exact Nat.lt_irrefl _ hlt
  · intro h
    rcases h with h | h
    · exact hne h.symm
    · have hlt := rank_lt_of_transGen h
      rw [hr] at hlt
      exact Nat.lt_irrefl _ hlt

theorem peirceReadout_follows_wingPair :
    causalBefore .peirceWingPair .peirceMetricCurvatureReadout :=
  Relation.TransGen.single (by simp [dependencyEdge, dependencyEdgeCode])

theorem bkmHestenesDescent_has_both_prerequisites :
    causalBefore .filteredBKMKernel .bkmHestenesColimitDescent ∧
    causalBefore .realHestenesKreinCone .bkmHestenesColimitDescent := by
  constructor <;> exact Relation.TransGen.single
    (by simp [dependencyEdge, dependencyEdgeCode])

theorem souriauRotor_preserves_futureTemperatureCone_archetype_edge :
    causalBefore .souriauRindlerKillingRotor .futureRindlerTemperatureCone :=
  Relation.TransGen.single (by simp [dependencyEdge, dependencyEdgeCode])

theorem souriauRindlerFlow_preserves_fullFutureCone_archetype_edge :
    causalBefore .souriauRindlerKillingRotor .fullMinkowskiRindlerFutureCone :=
  Relation.TransGen.single (by simp [dependencyEdge, dependencyEdgeCode])

theorem independent_geometry_lanes_not_ordered :
    ¬ Archetype.paraKahlerModule ≤ Archetype.fisherKreinEinsteinReadout ∧
    ¬ Archetype.finiteDoubledKreinFrame ≤ Archetype.graphSectionMetricReadout := by
  constructor
  · intro h
    rcases h with h | h
    · cases h
    · rcases Relation.TransGen.head'_iff.mp h with ⟨c, hc, _⟩
      cases c <;> simp [dependencyEdge, dependencyEdgeCode] at hc
  · intro h
    rcases h with h | h
    · cases h
    · rcases Relation.TransGen.head'_iff.mp h with ⟨c, hc, _⟩
      cases c <;> simp [dependencyEdge, dependencyEdgeCode] at hc

theorem complex_fubini_study_owner_is_separate_from_real_krein_frame :
    ¬ Archetype.complexFubiniStudyQGT ≤ Archetype.finiteDoubledKreinFrame ∧
    ¬ Archetype.finiteDoubledKreinFrame ≤ Archetype.complexFubiniStudyQGT := by
  exact incomparable_of_rank_eq rfl (by decide)

theorem emergent_thermodynamic_spacetime_has_no_proved_predecessor
    (a : Archetype) : ¬ a < .emergentThermodynamicSpacetime := by
  intro h
  rcases h.1 with hab | hab
  · subst a
    exact h.2 (Or.inl rfl)
  · rcases Relation.TransGen.tail'_iff.mp hab with ⟨c, _, hc⟩
    cases c <;> simp [dependencyEdge, dependencyEdgeCode] at hc

/-- Epistemic status distinguishes a proved owner result from a conditional
owner theorem or a target not yet constructed in this checkout. -/
inductive EvidenceStatus where
  | ownerProved
  | conditionalOwnerTheorem
  | openTarget
  deriving DecidableEq, Repr

def evidenceStatus : Archetype → EvidenceStatus
  | .bkmHestenesColimitDescent => .conditionalOwnerTheorem
  | .realMassieuCalibrationReadout => .conditionalOwnerTheorem
  | .dualFlatCurvatureDatum => .conditionalOwnerTheorem
  | .assumedSpinorBilinearAction => .conditionalOwnerTheorem
  | .finiteKosmannCorrection => .conditionalOwnerTheorem
  | .finiteGibbsBKMHessian => .conditionalOwnerTheorem
  | .emergentThermodynamicSpacetime => .openTarget
  | .curvedSpinorBundleKosmannTheorem => .openTarget
  | .kerrLoxodromicHorizonIdentification => .openTarget
  | .analyticBisognanoWichmannKMSTheorem => .openTarget
  | .horizonCommutantDuality => .openTarget
  | .killingConeBKMIdentification => .openTarget
  | .symplecticCocycleOnsagerCurvatureIdentification => .openTarget
  | _ => .ownerProved

@[simp] theorem emergentThermodynamicSpacetime_is_open :
    evidenceStatus .emergentThermodynamicSpacetime = .openTarget := rfl

end InfoGeometry.Epistemology.ThermodynamicGeometryArchetypePoset
