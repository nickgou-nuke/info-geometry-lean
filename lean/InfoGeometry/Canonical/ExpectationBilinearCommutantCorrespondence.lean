import InfoGeometry.Canonical.OperatorErlangenFierzKlein
import InfoGeometry.Canonical.OperatorObservationPrequantumBridge

/-!
# Expectation/bilinear commutant correspondence

This owner makes the separation boundary explicit.  An operator family is
identified only after passing to its expectation readout; the Fierz--Klein
coordinates are then an invariant of that readout.  A projective/prequantum
lift is supplied separately, because neither commutation nor expectation
values alone construct a line bundle.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExpectationBilinearCommutantCorrespondence

open InfoGeometry.Canonical.OperatorErlangenFierzKlein
open InfoGeometry.Canonical.OperatorObservationPrequantumBridge
open InfoGeometry.Topology
open InfoGeometry.Prequantum
open InfoGeometry.OperatorAlgebra.Thermodynamics
open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Canonical.DrazinModularPersistence

universe u

variable {Obs : Type u} [Ring Obs] [Star Obs]

/-! ## Concrete expectation-valued bilinear readout -/

/-- The measured Fierz bilinears of an arbitrary commutant observable.  The
channel maps and expectation state are explicit inputs; no operator
injectivity is silently assumed. -/
def expectationBilinearReadout
    (φ : RealExpectationState Obs)
    (C : OperatorFierzChannelMaps Obs) (A : Obs) : FierzBilinears where
  sigma := φ.expect (C.scalar A)
  omega := φ.expect (C.phase A)
  J := fun μ => φ.expect (C.vector μ A)
  K := fun μ => φ.expect (C.axial μ A)
  S := C.area A

theorem expectationBilinearReadout_eq_zero_iff
    (φ : RealExpectationState Obs) (C : OperatorFierzChannelMaps Obs)
    (A : Obs) :
    expectationBilinearReadout φ C A = trivialFierzBilinears ↔
      φ.expect (C.scalar A) = 0 ∧
      φ.expect (C.phase A) = 0 ∧
      (∀ μ : I4, φ.expect (C.vector μ A) = 0) ∧
      (∀ μ : I4, φ.expect (C.axial μ A) = 0) ∧
      C.area A = default := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact congrArg FierzBilinears.sigma h
    · exact congrArg FierzBilinears.omega h
    · intro μ
      exact congrArg (fun F => F.J μ) h
    · intro μ
      exact congrArg (fun F => F.K μ) h
    · exact congrArg FierzBilinears.S h
  · rintro ⟨hs, ho, hJ, hK, hS⟩
    change
      { sigma := φ.expect (C.scalar A), omega := φ.expect (C.phase A),
        J := fun μ => φ.expect (C.vector μ A),
        K := fun μ => φ.expect (C.axial μ A), S := C.area A } =
      trivialFierzBilinears
    rw [FierzBilinears.mk.injEq]
    refine ⟨hs, ho, ?_, ?_, hS⟩
    · funext μ
      exact hJ μ
    · funext μ
      exact hK μ

theorem expectationBilinearReadout_kernel_characterization
    (φ : RealExpectationState Obs) (C : OperatorFierzChannelMaps Obs) :
    {A : Obs | expectationBilinearReadout φ C A = trivialFierzBilinears} =
      {A : Obs |
        φ.expect (C.scalar A) = 0 ∧
        φ.expect (C.phase A) = 0 ∧
        (∀ μ : I4, φ.expect (C.vector μ A) = 0) ∧
        (∀ μ : I4, φ.expect (C.axial μ A) = 0) ∧
        C.area A = default} := by
  ext A
  exact expectationBilinearReadout_eq_zero_iff φ C A

/-- The expectation-valued bilinear package attached to an admissible modular
operator socket. -/
def expectationBilinears (E : OperatorErlangenFierzKlein Obs) :
    InfoGeometry.Canonical.FierzKleinFoundation.FierzBilinears :=
  E.fierzBilinears

theorem expectationBilinears_on_klein (E : OperatorErlangenFierzKlein Obs) :
    InfoGeometry.Canonical.FierzKleinFoundation.IsOnKleinQuadric E.kleinLift :=
  E.klein_lift_on_quadric

theorem expectationBilinears_on_fierz_variety
    (E : OperatorErlangenFierzKlein Obs) :
    InfoGeometry.Canonical.FierzKleinFoundation.IsOnFierzKleinVariety E.coordinates :=
  E.operator_erlangen_fierz_klein_holds

/-! ## Quotient/range correspondence with an explicit projective lift -/

variable {X A : Type u} {ι : Type u} {E' : Type}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [Fintype ι]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']

structure CorrespondenceData
    (S : NoncommutativeObservableSystem X A ι) where
  prequantumLift : ReadoutPrequantumLift S E'

variable (S : NoncommutativeObservableSystem X A ι)

def bundleReadoutCorrespondence
    (D : CorrespondenceData (E' := E') S) :
    OperatorObservationalQuotient S → ProjectivePrequantumBundle E' :=
  bundleOnObservationQuotient S D.prequantumLift

theorem bundleReadoutCorrespondence_factorization
    (D : CorrespondenceData (E' := E') S)
    (q : OperatorObservationalQuotient S) :
    bundleReadoutCorrespondence S D q =
      bundleOnObservationRange S D.prequantumLift
        (operatorObservationQuotientRangeEquiv S q) := by
  exact bundleOnObservationQuotient_factorization S D.prequantumLift q

theorem commutant_observation_one_to_one :
    Function.Bijective (operatorObservationQuotientRangeMap S) := by
  exact observational_one_to_one_readout_range S

end InfoGeometry.Canonical.ExpectationBilinearCommutantCorrespondence

end noncomputable section
