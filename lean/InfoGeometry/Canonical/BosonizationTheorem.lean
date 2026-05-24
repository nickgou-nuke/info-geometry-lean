import InfoGeometry.Canonical.BoundaryMajoranaCircuitModel
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.SplitCliffordCurrentLift
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# InfoGeometry.Canonical.BosonizationTheorem

Canonical bosonization synthesis surface.

This file does not reprove the source-side CAR/Wick current theorem and it does
not construct a new current algebra.  It packages the already-owned boundary
Majorana/PHS surface, the constructive Heisenberg current theorem, and the
Sugawara bridge into one theorem-only bundle.
-/

namespace InfoGeometry.Canonical.BosonizationTheorem

open InfoGeometry.Canonical.BoundaryMajoranaCircuitModel
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.SplitCliffordCurrentLift
open InfoGeometry.Canonical.CurrentSugawaraBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {A : Type*} [Ring A]
variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/--
Canonical bosonization theorem surface.

The theorem packages the finite boundary Majorana/PHS and zero-mode circuit
surface, the constructive Heisenberg current law, and the Sugawara
current-to-Virasoro bridge.  It does not claim a new raw algebra isomorphism.
-/
theorem bosonizationTheorem
    (C : RawCARModeCompletion A)
    (H : CurrentHeisenbergRep 𝕜 V)
    (m n : Int) :
    (MajoranaPHSZeroMode.IsPHSInvariant
        ((InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARCreation +
            InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARAnnihilation) :
          InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E) ∧
      MajoranaPHSZeroMode.IsBoundaryZeroMode
        (InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp (E := E))
        (InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp (E := E)) ∧
      (∀ {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
        (occ : ι → ℤ) (a b c d : ι),
        NormalOrderedCurrent.algebraCommutator
            (NormalOrderedCurrent.normalOrderedMatrixUnit occ a b)
            (NormalOrderedCurrent.normalOrderedMatrixUnit occ c d) =
          ((if b = c then NormalOrderedCurrent.normalOrderedMatrixUnit occ a d
              else (0 : Matrix ι ι R)) -
              if a = d then NormalOrderedCurrent.normalOrderedMatrixUnit occ c b
              else (0 : Matrix ι ι R)) +
            NormalOrderedCurrent.wickCorrection occ a b c d) ∧
      (∀ {A : Type*} [Ring A] (C : RawCARModeCompletion A) (m n : Int),
        CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
          if m + n = 0 then m • completedCentral C else 0)) ∧
    (CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      if m + n = 0 then m • completedCentral C else 0) ∧
    ((H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) =
      (m - n) • H.sugawaraStressMode (m + n)
        + if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
          else 0) ∧
      (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.cgen 𝕜) =
      (1 : V →ₗ[𝕜] V)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (BoundaryMajoranaCircuitModel.boundaryMajoranaCircuitModel (E := E))
  · exact bosonization_constructive_heisenberg_current C m n
  · exact H.sugawaraStressMode_virasoroBracket m n
  · exact H.currentSugawaraRepresentation_central

/--
Packaged boundary theorem for the split completion and the Heisenberg/Sugawara
bridge.

This is the strongest theorem surface currently supported by the repository:
the split completion has a current boundary package, and any supplied
Heisenberg current datum canonically yields the external Sugawara morphism
package.
-/
theorem splitClifford_current_boundary_and_sugawara_morphism
    (H : CurrentHeisenbergRep 𝕜 V) :
    Nonempty SplitCliffordCurrentMorphism ∧
    Nonempty (CurrentSugawaraMorphism 𝕜 V) := by
  constructor
  · exact ⟨splitCliffordInfinityCurrentMorphism⟩
  · exact CurrentSugawaraMorphism.nonempty H

end Core

end InfoGeometry.Canonical.BosonizationTheorem
