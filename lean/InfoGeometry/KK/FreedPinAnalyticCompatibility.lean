/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KK.PinFredholmTransport

/-!
# Analytic compatibility of the actual ordered Pin suspensions

The even Pin target is included into the ambient normalized-vector Pin group.
The resulting continuous linear action agrees with the pulled-back action as
an actual equivalence. Consequently the two routes give equal image domains,
ambient operator graphs, bounded conjugates, compact resolvents, and continuous
native Fredholm families. Both suspension signs retain their declared source
quadratic forms and ordered vector products.

The analytic source data remain explicit inputs. These comparison theorems do
not assert that an unspecified geometric operator supplies a closed domain,
compact resolvent, or bounded Fredholm seed.
-/

noncomputable section

namespace InfoGeometry.KK.FreedPinAnalyticCompatibility

open InfoGeometry.Clifford.FreedCliffordSuspension
open InfoGeometry.Clifford.NormalizedVectorPin
open InfoGeometry.Clifford.FreedPinRepresentation
open InfoGeometry.KK.LinearDiracTransport
open InfoGeometry.KK.PinFredholmTransport
open InfoGeometry.KK.RealSplitKreinLinearResolventBridge

variable {N H : Type*} [AddCommGroup N] [Module ℝ N]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The actual subgroup inclusion, retaining the proved Pin membership. -/
def evenPinInclusion (Q : QuadraticForm ℝ N) : evenPin Q →* pin Q where
  toFun g := ⟨evenPinToUnits Q g, evenPinToUnits_mem Q g⟩
  map_one' := by apply Subtype.ext; exact map_one (evenPinToUnits Q)
  map_mul' g h := by apply Subtype.ext; exact map_mul (evenPinToUnits Q) g h

/-- The positive ordered suspension as an ambient Pin homomorphism. -/
def positiveAmbientPin (Q : QuadraticForm ℝ N) : pin Q →* pin (positiveForm Q) :=
  (evenPinInclusion (positiveForm Q)).comp (positivePinHom Q)

/-- The negative ordered suspension has source `pin (-Q)`. -/
def negativeAmbientPin (Q : QuadraticForm ℝ N) : pin (-Q) →* pin (negativeForm Q) :=
  (evenPinInclusion (negativeForm Q)).comp (negativePinHom Q)

section Positive

variable (Q : QuadraticForm ℝ N)
variable (ρ : CliffordAlgebra (positiveForm Q) →ₐ[ℝ] (H →L[ℝ] H))

/-- Equality of actual continuous frame equivalences, including their inverses. -/
theorem positive_action (g : pin Q) :
    continuousPinAction Q (positiveRepresentation Q ρ) g =
      continuousPinAction (positiveForm Q) ρ (positiveAmbientPin Q g) := by
  ext x
  rfl

/-- The two representation routes give the same actual transported domain. -/
theorem positive_domain (S : Submodule ℝ H) (g : pin Q) :
    domain (continuousPinAction Q (positiveRepresentation Q ρ) g) S =
      domain (continuousPinAction (positiveForm Q) ρ (positiveAmbientPin Q g)) S := by
  rw [positive_action]

/-- Both operator transports agree after the explicit source-domain maps. -/
theorem positive_operator {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) (g : pin Q) :
    (operator (continuousPinAction Q (positiveRepresentation Q ρ) g) D).comp
        (domainEquiv (continuousPinAction Q (positiveRepresentation Q ρ) g) S).toLinearMap =
      (operator (continuousPinAction (positiveForm Q) ρ (positiveAmbientPin Q g)) D).comp
        (domainEquiv (continuousPinAction (positiveForm Q) ρ
          (positiveAmbientPin Q g)) S).toLinearMap := by
  rw [positive_action]

/-- The ambient graphs agree, without a dependent-domain identification hypothesis. -/
theorem positive_graph {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) (g : pin Q) :
    graph (operator (continuousPinAction Q (positiveRepresentation Q ρ) g) D) =
      graph (operator (continuousPinAction (positiveForm Q) ρ (positiveAmbientPin Q g)) D) := by
  rw [positive_action]

/-- In particular, the comparison is compatible with any bounded grading or operator. -/
theorem positive_conjugate (A : H →L[ℝ] H) (g : pin Q) :
    (continuousPinAction Q (positiveRepresentation Q ρ) g).conjContinuousAlgEquiv A =
      (continuousPinAction (positiveForm Q) ρ
        (positiveAmbientPin Q g)).conjContinuousAlgEquiv A := by
  rw [positive_action]

variable [CompleteSpace H]

theorem positive_resolvent {S : Submodule ℝ H} {D : S →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData S D) (g : pin Q) :
    (resolvent (continuousPinAction Q (positiveRepresentation Q ρ) g) R).resolvent =
      (resolvent (continuousPinAction (positiveForm Q) ρ
        (positiveAmbientPin Q g)) R).resolvent := by
  rw [positive_action]

/-- Parameter continuity is the same condition along either representation route. -/
theorem positive_continuous_iff {B : Type*} [TopologicalSpace B] (g : B → pin Q) :
    Continuous (fun b => (pinRepresentation Q (positiveRepresentation Q ρ) (g b) :
      H →L[ℝ] H)) ↔
    Continuous (fun b => (pinRepresentation (positiveForm Q) ρ
      (positiveAmbientPin Q (g b)) : H →L[ℝ] H)) := Iff.rfl

/-- The constructed continuous maps into the native Fredholm subtype agree. -/
theorem positive_fredholmFamily {B : Type*} [TopologicalSpace B] (g : B → pin Q)
    (hg : Continuous (fun b => (pinRepresentation Q (positiveRepresentation Q ρ) (g b) :
      H →L[ℝ] H))) (A : H →L[ℝ] H) (hA : A.IsFredholm) :
    pinFredholmFamily Q (positiveRepresentation Q ρ) g hg A hA =
      pinFredholmFamily (positiveForm Q) ρ (fun b => positiveAmbientPin Q (g b))
        ((positive_continuous_iff Q ρ g).mp hg) A hA := by
  apply ContinuousMap.ext
  intro b
  apply Subtype.ext
  exact positive_conjugate Q ρ A (g b)

end Positive

section Negative

variable (Q : QuadraticForm ℝ N)
variable (ρ : CliffordAlgebra (negativeForm Q) →ₐ[ℝ] (H →L[ℝ] H))

theorem negative_action (g : pin (-Q)) :
    continuousPinAction (-Q) (negativeRepresentation Q ρ) g =
      continuousPinAction (negativeForm Q) ρ (negativeAmbientPin Q g) := by
  ext x
  rfl

theorem negative_domain (S : Submodule ℝ H) (g : pin (-Q)) :
    domain (continuousPinAction (-Q) (negativeRepresentation Q ρ) g) S =
      domain (continuousPinAction (negativeForm Q) ρ (negativeAmbientPin Q g)) S := by
  rw [negative_action]

theorem negative_operator {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) (g : pin (-Q)) :
    (operator (continuousPinAction (-Q) (negativeRepresentation Q ρ) g) D).comp
        (domainEquiv (continuousPinAction (-Q) (negativeRepresentation Q ρ) g) S).toLinearMap =
      (operator (continuousPinAction (negativeForm Q) ρ (negativeAmbientPin Q g)) D).comp
        (domainEquiv (continuousPinAction (negativeForm Q) ρ
          (negativeAmbientPin Q g)) S).toLinearMap := by
  rw [negative_action]

theorem negative_graph {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) (g : pin (-Q)) :
    graph (operator (continuousPinAction (-Q) (negativeRepresentation Q ρ) g) D) =
      graph (operator (continuousPinAction (negativeForm Q) ρ (negativeAmbientPin Q g)) D) := by
  rw [negative_action]

theorem negative_conjugate (A : H →L[ℝ] H) (g : pin (-Q)) :
    (continuousPinAction (-Q) (negativeRepresentation Q ρ) g).conjContinuousAlgEquiv A =
      (continuousPinAction (negativeForm Q) ρ
        (negativeAmbientPin Q g)).conjContinuousAlgEquiv A := by
  rw [negative_action]

variable [CompleteSpace H]

theorem negative_resolvent {S : Submodule ℝ H} {D : S →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData S D) (g : pin (-Q)) :
    (resolvent (continuousPinAction (-Q) (negativeRepresentation Q ρ) g) R).resolvent =
      (resolvent (continuousPinAction (negativeForm Q) ρ
        (negativeAmbientPin Q g)) R).resolvent := by
  rw [negative_action]

theorem negative_continuous_iff {B : Type*} [TopologicalSpace B] (g : B → pin (-Q)) :
    Continuous (fun b => (pinRepresentation (-Q) (negativeRepresentation Q ρ) (g b) :
      H →L[ℝ] H)) ↔
    Continuous (fun b => (pinRepresentation (negativeForm Q) ρ
      (negativeAmbientPin Q (g b)) : H →L[ℝ] H)) := Iff.rfl

theorem negative_fredholmFamily {B : Type*} [TopologicalSpace B] (g : B → pin (-Q))
    (hg : Continuous (fun b => (pinRepresentation (-Q) (negativeRepresentation Q ρ) (g b) :
      H →L[ℝ] H))) (A : H →L[ℝ] H) (hA : A.IsFredholm) :
    pinFredholmFamily (-Q) (negativeRepresentation Q ρ) g hg A hA =
      pinFredholmFamily (negativeForm Q) ρ (fun b => negativeAmbientPin Q (g b))
        ((negative_continuous_iff Q ρ g).mp hg) A hA := by
  apply ContinuousMap.ext
  intro b
  apply Subtype.ext
  exact negative_conjugate Q ρ A (g b)

end Negative

end InfoGeometry.KK.FreedPinAnalyticCompatibility

end
