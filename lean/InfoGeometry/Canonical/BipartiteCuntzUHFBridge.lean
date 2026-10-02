import Mathlib.Tactic

import InfoGeometry.Algebra.CuntzLeftRightCommutant
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Canonical.UHFCuntzGNSColimit
import InfoGeometry.Canonical.UHFTomitaTakesakiColimitBridge

/-!
# Doubled Cuntz/UHF horizon interoperability

This module consolidates existing theorem-bearing owners without introducing a
parallel Cuntz presentation or a duplicate inductive-limit construction.

Closed here:
* left/right regular Cuntz actions commute;
* the full commutant of the left regular action is exactly the range of right
  multiplication;
* the concrete matrix tower preserves the normalized trace under every
  finite transition;
* the compatible trace descends to the genuine ModuleCat colimit functional;
* the existing Cuntz GNS Hilbert colimit has dense stage images and is complete;
* the existing closed Tomita modular forms are transition-compatible under the
  explicit closability hypotheses.

This does NOT prove that the resulting von Neumann algebra is the hyperfinite
Type III_1 factor, does not identify the native finite-n Cuntz quotient with
O_infinity, and does not prove uniqueness of a tracial state on a C*-inductive
limit beyond the compatible functional actually constructed.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipartiteCuntzUHFBridge

open InfoGeometry.Algebra.CuntzLeftRightCommutant
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.UHFCuntzGNSColimit
open InfoGeometry.Canonical.UHFTomitaTakesakiColimitBridge
open InfoGeometry.Algebra.CuntzTensorQuotient
open CStarStateColimit.Native
open InfoGeometry.Canonical.CuntzStarInductiveSystem

/-! ## 1. Native finite Cuntz left/right commutant -/

variable {n : ℕ}

/-- Left and right native Cuntz multiplications commute pointwise. -/
theorem cuntz_left_right_commute
    (a b x : CuntzAlg n) :
    leftMultiplication n a (rightMultiplication n b x) =
      rightMultiplication n b (leftMultiplication n a x) :=
  left_right_commute n a b x

/-- The full commutant of the left regular Cuntz action is exactly the range
of right multiplication. -/
theorem cuntz_left_commutant_eq_right_range :
    leftRegularCommutant n =
      {T | ∃ b : CuntzAlg n, T = rightMultiplication n b} :=
  leftRegularCommutant_eq_rightMultiplicationRange n

/-- Native algebraic star mirror takes left multiplication to right
multiplication by the starred element. -/
theorem cuntz_star_left_to_right
    (a x : CuntzAlg n) :
    star (a * star x) = rightMultiplication n (star a) x :=
  star_conjugates_left_to_right n a x

/-! ## 2. Concrete UHF matrix tower trace compatibility -/

/-- One concrete successor embedding doubles the raw matrix trace. -/
theorem matrix_step_trace
    (n : ℕ)
    (A : InfoGeometry.Canonical.CuntzMatrixTowerInstantiation.MatrixStage n) :
    Matrix.trace (concreteStep n A) = 2 * Matrix.trace A :=
  concreteStep_trace n A

/-- Normalized matrix trace is preserved along every concrete finite tower
transition. -/
theorem normalized_trace_transition
    {i j : ℕ} (hij : i ≤ j)
    (A : InfoGeometry.Canonical.CuntzMatrixTowerInstantiation.MatrixStage i) :
    InfoGeometry.Canonical.CuntzMatrixTowerInstantiation.matrixTraceState j
        (concreteMap hij A) =
      InfoGeometry.Canonical.CuntzMatrixTowerInstantiation.matrixTraceState i A :=
  concreteMap_trace hij A

/-- The colimit trace functional restricts to the finite-stage normalized trace
functional on every inclusion. -/
theorem colimit_trace_restricts_to_stage
    (n : ℕ)
    (A : InfoGeometry.Canonical.CuntzMatrixTowerInstantiation.MatrixStage n) :
    traceColimitFunctional concreteData
        (traceColimitInclusion concreteData n A) =
      InfoGeometry.Canonical.CuntzMatrixTowerInstantiation.matrixTraceFunctional n A :=
  traceColimitFunctional_inclusion concreteData n A

/-! ## 3. Existing filtered GNS/Tomita colimit route -/

section GNS

variable (Stage : ℕ → Type)
variable [∀ k, CStarAlgebra (Stage k)]
variable [∀ k, PartialOrder (Stage k)]
variable [∀ k, StarOrderedRing (Stage k)]
variable (T : CuntzStarTower Stage)
variable
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily
    Stage (cuntzSystem Stage T))

/-- Finite-stage GNS images are dense in the native Cuntz Hilbert colimit. -/
theorem gns_stage_images_dense :
    Dense (⋃ k : ℕ, Set.range (cuntzStageToColimit Stage T ω k)) :=
  dense_range_cuntzGNSColimit Stage T ω

/-- The native Cuntz GNS Hilbert colimit is complete. -/
theorem gns_colimit_complete :
    CompleteSpace (CuntzKMSHilbertColimit Stage T ω) :=
  cuntzGNSColimit_complete Stage T ω

/-- Closed Tomita modular forms are functorially compatible along the tower
when the stagewise Tomita cores are closable. -/
theorem tomita_form_transition
    (hclos : ∀ k, IsClosableTomitaCore (ω.state k))
    {i j : ℕ} (hij : i ≤ j)
    (x y : closedTomitaDomain (ω.state i)) :
    uhfClosedTomitaModularForm Stage T ω hclos j
        (filteredClosedTomitaDomainMap
          Stage (cuntzSystem Stage T) ω hij x)
        (filteredClosedTomitaDomainMap
          Stage (cuntzSystem Stage T) ω hij y) =
      uhfClosedTomitaModularForm Stage T ω hclos i x y :=
  uhfClosedTomitaModularForm_transition
    Stage T ω hclos hij x y

end GNS

/-! ## 4. Explicit classification boundary -/

/-- Conditional readout for any downstream von Neumann-factor classification.

The bridge does not derive Type III_1.  A downstream theorem may supply that
classification and use this socket without changing the finite/UHF/GNS layer. -/
theorem typeIII1_of_supplied_classification
    (P : Prop)
    (hP : P) :
    P :=
  hP

end InfoGeometry.Canonical.BipartiteCuntzUHFBridge
