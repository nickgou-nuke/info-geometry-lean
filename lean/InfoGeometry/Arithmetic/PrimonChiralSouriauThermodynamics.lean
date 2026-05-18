import Mathlib
import InfoGeometry.Thermo.SplitChiralPolarizationBasis
import InfoGeometry.Arithmetic.ZetaSouriauComplexLift
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Canonical.BogoliubovFockSuper

/-!
# InfoGeometry.Arithmetic.PrimonChiralSouriauThermodynamics

Native chiral Souriau thermodynamics for the finite primon gas.

This module keeps the proof surface finite and algebraic:

* chiral cone coordinates are taken from the split-temperature lift;
* prime-register particle counts are taken from the finite prime-bit carrier;
* the hyperbolic Bogoliubov bracket closure is imported from the canonical
  projector-super algebra;
* no sockets, certificates, or CFT central-charge claims are introduced here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonChiralSouriauThermodynamics

open InfoGeometry.Thermo.SplitChiralPolarizationBasis
open InfoGeometry.Arithmetic.ZetaSouriauComplexLift
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Canonical.BogoliubovFockSuper

/-! ## 1. Chiral cone coordinates -/

/-- Chiral cone angle extracted from the split temperature. -/
@[rep_depth thermo]
def chiralConeAngle (s : ℂ) : ℝ :=
  (splitTemperature s).tau

/-- The chiral cone angle is the imaginary part of the complex temperature. -/
@[simp, rep_depth thermo]
theorem chiralConeAngle_eq_im (s : ℂ) :
    chiralConeAngle s = s.im := by
  rfl

/-- Hyperbolic Bogoliubov parameter obtained from the chiral cone angle. -/
@[rep_depth thermo]
def chiralBogoliubovParams (s : ℂ) : HyperbolicMixingParams :=
  HyperbolicMixingParams.ofAngle (chiralConeAngle s)

/-! ## 2. Particle numbers on the finite prime carrier -/

/-- The prime-register particle number is its finite cardinality. -/
@[simp, rep_depth thermo]
theorem primeRegister_fermionNumber_eq_card (P : PrimeRegister) :
    fermionNumber P = P.primes.card := by
  rfl

/-- The occupied prime-state particle number is its occupied cardinality. -/
@[simp, rep_depth thermo]
theorem primeState_fermionNumberOfState_eq_card
    (P : PrimeRegister) (ψ : PrimeBitState P) :
    fermionNumberOfState P ψ = (occupiedPrimeSet P ψ).card := by
  rfl

/-! ## 3. Chiral Bogoliubov bracket closure -/

section Bogoliubov

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The chiral cone parameter induces the finite projector-super algebra closure:
the odd-odd anticommutator is hyperbolic, while the mixed commutator vanishes.
-/
@[rep_depth thermo]
theorem chiralCone_bogoliubov_projector_superalgebra
    (s : ℂ) :
    anticommutator (E := E)
        (bogoliubovAnnihilation (E := E) (chiralBogoliubovParams s))
        (bogoliubovCreation (E := E) (chiralBogoliubovParams s))
      =
      (Real.sinh (2 * chiralConeAngle s)) •
        ContinuousLinearMap.id ℝ (DoubledSpace E)
    ∧
    commutator (E := E)
        (bogoliubovAnnihilation (E := E) (chiralBogoliubovParams s))
        (bogoliubovCreation (E := E) (chiralBogoliubovParams s)) = 0 := by
  refine ⟨?_, ?_⟩
  · simpa [chiralBogoliubovParams, chiralConeAngle] using
      (anticommutator_ofAngle_projector_model (E := E)
        (θ := chiralConeAngle s))
  · simpa [chiralBogoliubovParams, chiralConeAngle] using
      (commutator_bogoliubov_projector_model (E := E)
        (B := HyperbolicMixingParams.ofAngle (chiralConeAngle s)))

end Bogoliubov

/-! ## 4. Finite primon gas readout -/

/-- The finite primon gas particle count is the number of occupied primes. -/
@[simp, rep_depth thermo]
theorem primeGasParticleNumber_eq_fermionNumber (P : PrimeRegister) :
    PrimeBitWittenIndex.fermionNumber P = P.primes.card := by
  rfl

/-- The finite primon gas occupancy count is the occupied-set cardinality. -/
@[simp, rep_depth thermo]
theorem primeGasParticleNumberOfState_eq_fermionNumberOfState
    (P : PrimeRegister) (ψ : PrimeBitState P) :
    PrimeBitWittenIndex.fermionNumberOfState P ψ =
      (occupiedPrimeSet P ψ).card := by
  rfl

end InfoGeometry.Arithmetic.PrimonChiralSouriauThermodynamics
