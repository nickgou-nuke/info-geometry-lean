import InfoGeometry.Canonical.SuperchargeTransportBridge

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SuperchargeGapBridge

Canonical coherence surface exposing the transported parity/modular gap.

The current doubled-carrier canonical multiplet is flat at the base point:
its primitive parity/modular anticommutator vanishes there. This file makes
the non-flat continuation explicit. Under Bogoliubov transport the same
odd-odd pair develops a first-order anomaly seed, so the zero-gap value is a
special normalization point rather than the whole supercharge story.
-/

namespace SuperchargeGapBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.SuperchargeTransportBridge
open InfoGeometry.Canonical.BogoliubovFockSuper

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Flat parity/modular gap on the doubled carrier. -/
@[rep_depth transport]
noncomputable def flatParityModularGap : EndH :=
  BogoliubovFockSuper.fockAnticommutator (E := E)
    (modular_j (E := E)) (spectral_epsilon (E := E))

/-- Transported parity/modular gap against the static modular mirror `ε`. -/
@[rep_depth transport]
noncomputable def transportedParityModularGap
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (t : ℝ) : EndH :=
  BogoliubovFockSuper.fockAnticommutator (E := E)
    (transportedParitySupercharge (E := E) V t)
    (spectral_epsilon (E := E))

/-- The canonical flat parity/modular gap vanishes at the undeformed base point. -/
@[simp, rep_depth transport]
theorem flatParityModularGap_eq_zero :
    flatParityModularGap (E := E) = 0 := by
  simpa [flatParityModularGap] using
    (parity_modular_anticommutator_eq_zero (E := E))

/-- Transported gap specializes to the flat parity/modular gap at time `0`. -/
@[simp, rep_depth transport]
theorem transportedParityModularGap_zero
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedParityModularGap (E := E) V 0 = flatParityModularGap (E := E) := by
  simp [transportedParityModularGap, flatParityModularGap]

/-- The transported parity/modular gap also vanishes at the undeformed base point. -/
@[simp, rep_depth transport]
theorem transportedParityModularGap_zero_eq_zero
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedParityModularGap (E := E) V 0 = 0 := by
  rw [transportedParityModularGap_zero]
  exact flatParityModularGap_eq_zero (E := E)

/--
First-order transported gap seed. This is the object that survives once the
flat basepoint normalization is deformed by the connection generator.
-/
@[rep_depth transport]
noncomputable def transportedParityModularGapSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) : EndH :=
  deriv (fun t => transportedParityModularGap (E := E) V t) 0

/-- The gap seed is exactly the transported odd-odd anomaly source at time `0`. -/
@[rep_depth transport]
theorem transportedParityModularGapSeed_eq_transportSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedParityModularGapSeed (E := E) V
      =
    BogoliubovFockSuper.fockAnticommutator (E := E)
      (transportCommutator (E := E) V.connectionGenerator (modular_j (E := E)))
      (spectral_epsilon (E := E)) := by
  unfold transportedParityModularGapSeed transportedParityModularGap
  simpa using deriv_anticommutator_transportedParity_staticModular_at_zero V

/-- The first-order gap seed splits functorially along the connection-generator decomposition. -/
@[rep_depth transport]
theorem transportedParityModularGapSeed_eq_split_generator
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedParityModularGapSeed (E := E) V
      =
    BogoliubovFockSuper.fockAnticommutator (E := E)
      (transportCommutator (E := E)
        (phaseLinearPart (E := E) V.connectionGenerator)
        (modular_j (E := E)))
      (spectral_epsilon (E := E))
      +
    BogoliubovFockSuper.fockAnticommutator (E := E)
      (transportCommutator (E := E)
        (phaseAntilinearPart (E := E) V.connectionGenerator)
        (modular_j (E := E)))
      (spectral_epsilon (E := E)) := by
  unfold transportedParityModularGapSeed transportedParityModularGap
  simpa using deriv_anticommutator_transportedParity_staticModular_at_zero_eq_split_generator V

/--
If the phase-linear part commutes with `J`, the non-flat gap seed is carried
purely by the phase-antilinear transport channel.
-/
@[rep_depth transport]
theorem transportedParityModularGapSeed_eq_phaseAntilinearSeed_of_commute_phaseLinearPart
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm :
      Commute (modular_j (E := E))
        (phaseLinearPart (E := E) V.connectionGenerator)) :
    transportedParityModularGapSeed (E := E) V
      =
    BogoliubovFockSuper.fockAnticommutator (E := E)
      (transportCommutator (E := E)
        (phaseAntilinearPart (E := E) V.connectionGenerator)
        (modular_j (E := E)))
      (spectral_epsilon (E := E)) := by
  unfold transportedParityModularGapSeed transportedParityModularGap
  simpa using
    deriv_anticommutator_transportedParity_staticModular_at_zero_eq_phaseAntilinearSeed_of_commute_phaseLinearPart
      V hComm

/--
Commuting connection generators are the genuinely flat case: they kill the
transported parity/modular gap seed.
-/
@[rep_depth transport]
theorem transportedParityModularGapSeed_eq_zero_of_commute_modularJ
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm : Commute (modular_j (E := E)) V.connectionGenerator) :
    transportedParityModularGapSeed (E := E) V = 0 := by
  unfold transportedParityModularGapSeed transportedParityModularGap
  simpa using
    deriv_anticommutator_transportedParity_staticModular_at_zero_eq_zero_of_commute_modularJ V hComm

end Core

end SuperchargeGapBridge
