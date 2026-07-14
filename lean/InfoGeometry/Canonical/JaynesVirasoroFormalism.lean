import InfoGeometry.Canonical.JaynesFormalism
import InfoGeometry.Canonical.JaynesRNModularBridge
import InfoGeometry.Canonical.VirasoroWardEquilibrium
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# InfoGeometry.Canonical.JaynesVirasoroFormalism

Jaynes-to-Virasoro/Sugawara bridge in the repo-native finite/algebraic sense.

The safe content is:

* Jaynes free energy / modular potential are the scalar readouts on the Jaynes side;
* Virasoro Ward equilibrium is the symmetry-constraint side;
* current/Sugawara remains the mode-closure backend with explicit truncation;
* the bridge only identifies compatible scalar readouts and residuals.

This file does not claim an analytic completion, a full CFT construction, or a
new Virasoro theorem. It packages the existing owners into a single Jaynes-
adapted formalism surface.
-/

namespace JaynesVirasoroFormalism

open MeasureTheory
open InfoGeometry.Canonical.JaynesFormalism
open InfoGeometry.Canonical.JaynesRNMaxEnt
open InfoGeometry.Canonical.VirasoroWardEquilibrium
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.MaxEnt.JaynesRNMaxEnt

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀]

/-! ## Jaynes-to-Ward packet -/

section Ward

variable {Alg Op : Type*}
variable [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
variable [NormedAddCommGroup Op] [NormedSpace ℝ Op]

/--
Jaynes/Virasoro Ward packet:

* `jaynes` is the thermodynamic Jaynes packet;
* `ward` is the Virasoro Ward equilibrium packet;
* `freeEnergy_eq` identifies the two free-energy readouts.

The Virasoro residual structure is supplied by the Ward packet itself.
-/
structure JaynesVirasoroWardPacket where
  /-- Jaynes thermodynamic packet. -/
  jaynes : InfoGeometry.Canonical.OperatorThermodynamics.OperatorThermodynamicsPacket Op
  /-- Virasoro Ward equilibrium packet. -/
  ward : VirasoroWardEquilibriumPacket Alg Op
  /-- Compatibility of the free-energy readout. -/
  freeEnergy_eq :
    ward.thermodynamics.freeEnergy = jaynes.freeEnergy

namespace JaynesVirasoroWardPacket

variable (P : JaynesVirasoroWardPacket (Alg := Alg) (Op := Op))

/-- The Ward residual is the Ward residual of the underlying packet. -/
theorem wardResidual_eq_zero_of_globalMode
    (n : ℤ) (hn : n ≥ -1) :
    P.ward.wardResidual n = 0 :=
  P.ward.wardResidual_eq_zero_of_globalMode n hn

/-- The Ward action vanishes on the Jaynes free energy whenever the Ward packet is global. -/
theorem wardAction_eq_zero_of_globalMode_freeEnergy
    (n : ℤ) (hn : n ≥ -1) :
    P.ward.wardAction n P.jaynes.freeEnergy = 0 := by
  rw [← P.freeEnergy_eq]
  rw [P.ward.thermodynamics.freeEnergy_eq_neg_log_partition]
  exact P.ward.wardAction_eq_zero_of_globalMode_negLogPartition n hn

/-- The Jaynes free energy is the Ward free-energy readout. -/
theorem jaynes_freeEnergy_eq_ward_freeEnergy :
    P.jaynes.freeEnergy = P.ward.thermodynamics.freeEnergy :=
  P.freeEnergy_eq.symm

end JaynesVirasoroWardPacket

/-! ## RN modular side -/

section Modular

variable {ι : Type*} [Fintype ι]
variable (C : MomentFamily (Ω := Ω) ι)

/-- Jaynes potential is the modular potential shifted by `log Z`. -/
theorem jaynesPotential_eq_log_rnDeriv_gibbsMeasure_toReal_add_logPartition
    (lam : ι → ℝ) (hInt : PartitionIntegrable (μ₀ := μ₀) (C := C) lam) :
    (InfoGeometry.MaxEnt.JaynesRNMaxEnt.potential (C := C) lam)
      =ᵐ[μ₀]
        fun x =>
          Real.log (((gibbsMeasure (μ₀ := μ₀) (C := C) lam).rnDeriv μ₀ x).toReal) +
            Real.log (partitionFunction (μ₀ := μ₀) (C := C) lam) :=
  InfoGeometry.Canonical.JaynesRNMaxEnt.potential_eq_log_rnDeriv_gibbsMeasure_toReal_add_logPartition
    (μ₀ := μ₀) (C := C) lam hInt

/-- The modular scalar potential is the negative logarithm of the Gibbs density. -/
theorem jaynesNegLogRnDeriv_eq_negPotential_add_logPartition
    (lam : ι → ℝ) (hInt : PartitionIntegrable (μ₀ := μ₀) (C := C) lam) :
    (fun x =>
      -Real.log (((gibbsMeasure (μ₀ := μ₀) (C := C) lam).rnDeriv μ₀ x).toReal))
      =ᵐ[μ₀]
        fun x =>
          -(InfoGeometry.MaxEnt.JaynesRNMaxEnt.potential (C := C) lam x) +
            Real.log (partitionFunction (μ₀ := μ₀) (C := C) lam) :=
  InfoGeometry.Canonical.JaynesRNMaxEnt.neg_log_rnDeriv_gibbsMeasure_toReal_eq_neg_potential_add_logPartition
    (μ₀ := μ₀) (C := C) lam hInt

end Modular

/-! ## Current/Sugawara backend -/

section Sugawara

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-- The Sugawara stress mode bracket on a current datum is the Virasoro law. -/
theorem sugawaraStressMode_virasoroBracket
    (H : CurrentHeisenbergRep 𝕜 V) (m n : Int) :
    (H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) =
      (m - n) • H.sugawaraStressMode (m + n)
        + if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
          else 0 :=
  H.sugawaraStressMode_virasoroBracket m n

/-- The global conformal modes are central-free in the Sugawara readout. -/
theorem sugawaraStressMode_virasoroBracket_global_mode
    (H : CurrentHeisenbergRep 𝕜 V)
    {m n : Int}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    (H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) =
      (m - n) • H.sugawaraStressMode (m + n) :=
  H.sugawaraStressMode_virasoroBracket_global_mode hm

end Sugawara

end Ward

end JaynesVirasoroFormalism
