import InfoGeometry.Canonical.InformationalLichnerowicz
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Quantum.SuperchargeMultiplet
import Mathlib.Analysis.Calculus.Deriv.Mul

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SuperchargeTransportBridge

Canonical transport bridge from the doubled-carrier supercharge multiplet to
the quasilattice Dirac transport lane.

This file does not introduce a new supergravity shell. It only packages what
the repository already owns on the same doubled carrier:

- the canonical parity supercharge representative `Q_Π = J`,
- the canonical modular supercharge representative `Q_J = ε`,
- the quasilattice transport `quasilatticeDirac`,
- and the weak-owner Lichnerowicz split from the transported Dirac lane.
-/

namespace InfoGeometry.Canonical.SuperchargeTransportBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.QuasilatticeDirac
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Quantum

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- The canonical transported parity/triality supercharge, represented on `EndH` by `J`. -/
@[rep_depth transport]
noncomputable abbrev transportedParitySupercharge
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (t : ℝ) : EndH :=
  quasilatticeDirac V (modular_j (E := E)) t

/-- The canonical transported modular supercharge, represented on `EndH` by `ε`. -/
@[rep_depth transport]
noncomputable abbrev transportedModularSupercharge
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (t : ℝ) : EndH :=
  quasilatticeDirac V (spectral_epsilon (E := E)) t

@[simp, rep_depth transport] theorem transportedParitySupercharge_zero
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedParitySupercharge (E := E) V 0 = modular_j (E := E) := by
  simp [transportedParitySupercharge]

@[simp, rep_depth transport] theorem transportedModularSupercharge_zero
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportedModularSupercharge (E := E) V 0 = spectral_epsilon (E := E) := by
  simp [transportedModularSupercharge]

/-- On the continuous doubled carrier, the primitive odd-odd parity/modular anticommutator vanishes. -/
@[rep_depth krein]
theorem parity_modular_anticommutator_eq_zero :
    fockAnticommutator (E := E) (modular_j (E := E)) (spectral_epsilon (E := E)) = 0 := by
  rw [fockAnticommutator, anticommutator, superBracket_odd_odd]
  calc
    (modular_j (E := E)).comp (spectral_epsilon (E := E))
        + (spectral_epsilon (E := E)).comp (modular_j (E := E))
      =
      -((spectral_epsilon (E := E)).comp (modular_j (E := E)))
        + (spectral_epsilon (E := E)).comp (modular_j (E := E)) := by
          rw [modular_j_spectral_epsilon_anticommute (E := E)]
    _ = 0 := by simp

/-- The transported parity supercharge obeys the same infinitesimal commutator law as the Dirac lane. -/
@[rep_depth transport]
theorem deriv_transportedParitySupercharge
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (t : ℝ) :
    deriv (fun s => transportedParitySupercharge (E := E) V s) t
      =
    transportCommutator (E := E)
      V.connectionGenerator
      (transportedParitySupercharge (E := E) V t) := by
  simpa [transportedParitySupercharge] using
    (deriv_quasilatticeDirac (E := E) V (modular_j (E := E)) t)

/-- The transported modular supercharge obeys the same infinitesimal commutator law as the Dirac lane. -/
@[rep_depth transport]
theorem deriv_transportedModularSupercharge
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (t : ℝ) :
    deriv (fun s => transportedModularSupercharge (E := E) V s) t
      =
    transportCommutator (E := E)
      V.connectionGenerator
      (transportedModularSupercharge (E := E) V t) := by
  simpa [transportedModularSupercharge] using
    (deriv_quasilatticeDirac (E := E) V (spectral_epsilon (E := E)) t)

/--
If the phase-linear part of the connection generator commutes with `J`, the
transported parity supercharge is sourced purely by the phase-antilinear
channel.
-/
@[rep_depth transport]
theorem deriv_transportedParitySupercharge_at_zero_eq_phaseAntilinear_of_commute_phaseLinearPart
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm :
      Commute (modular_j (E := E))
        (phaseLinearPart (E := E) V.connectionGenerator)) :
    deriv (fun s => transportedParitySupercharge (E := E) V s) 0
      =
    transportCommutator (E := E)
      (phaseAntilinearPart (E := E) V.connectionGenerator)
      (modular_j (E := E)) := by
  simpa [transportedParitySupercharge] using
    (deriv_quasilatticeDirac_at_zero_eq_phaseAntilinear_of_commute_phaseLinearPart
      (E := E) V (modular_j (E := E)) hComm)

/--
If the phase-linear part of the connection generator commutes with `ε`, the
transported modular supercharge is sourced purely by the phase-antilinear
channel.
-/
@[rep_depth transport]
theorem deriv_transportedModularSupercharge_at_zero_eq_phaseAntilinear_of_commute_phaseLinearPart
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm :
      Commute (spectral_epsilon (E := E))
        (phaseLinearPart (E := E) V.connectionGenerator)) :
    deriv (fun s => transportedModularSupercharge (E := E) V s) 0
      =
    transportCommutator (E := E)
      (phaseAntilinearPart (E := E) V.connectionGenerator)
      (spectral_epsilon (E := E)) := by
  simpa [transportedModularSupercharge] using
    (deriv_quasilatticeDirac_at_zero_eq_phaseAntilinear_of_commute_phaseLinearPart
      (E := E) V (spectral_epsilon (E := E)) hComm)

/-- The transported parity supercharge has the weak-owner Lichnerowicz Hessian landing. -/
@[rep_depth transport]
theorem deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    let X := V.connectionGenerator
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationHessian
      (E := E) X (modular_j (E := E)) := by
  simpa [transportedParitySupercharge] using
    (InfoGeometry.Canonical.InformationalLichnerowicz.deriv2_quasilatticeDirac_at_zero_eq_operatorInformationHessian
      (E := E) (V := V) (D := modular_j (E := E)))

/-- The transported parity supercharge has the weak-owner metric landing. -/
@[rep_depth transport]
theorem deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationMetricPart
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    let X := V.connectionGenerator
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMetricPart
      (E := E) X X (modular_j (E := E)) := by
  simpa [transportedParitySupercharge] using
    (InfoGeometry.Canonical.InformationalLichnerowicz.deriv2_quasilatticeDirac_at_zero_eq_operatorInformationMetricPart
      (E := E) (V := V) (D := modular_j (E := E)))

/-- The transported parity supercharge satisfies the weak-owner metric-plus-curvature split. -/
@[rep_depth transport]
theorem deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    let X := V.connectionGenerator
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMetricPart
      (E := E) X X (modular_j (E := E))
      + ((2 : ℝ)⁻¹) •
        InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart
          (E := E) X X (modular_j (E := E)) := by
  simpa [transportedParitySupercharge] using
    (InfoGeometry.Canonical.InformationalLichnerowicz.deriv2_quasilatticeDirac_at_zero_eq_metricPart_add_half_curvaturePart
      (E := E) (V := V) (D := modular_j (E := E)))

/--
The zero-time deformation of the flat odd-odd `(J, ε)` cross-term is exactly
the odd-odd bracket of the transported `J` infinitesimal with the static
modular mirror `ε`.
-/
@[rep_depth transport]
theorem deriv_anticommutator_transportedParity_staticModular_at_zero
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    deriv
        (fun t =>
          fockAnticommutator (E := E)
            (transportedParitySupercharge (E := E) V t)
            (spectral_epsilon (E := E)))
        0
      =
    fockAnticommutator (E := E)
      (transportCommutator (E := E) V.connectionGenerator (modular_j (E := E)))
      (spectral_epsilon (E := E)) := by
  have hA :
      HasDerivAt
        (fun t => transportedParitySupercharge (E := E) V t)
        (transportCommutator (E := E) V.connectionGenerator (modular_j (E := E)))
        0 := by
    simpa [transportedParitySupercharge, quasilatticeDirac,
      transportCommutator] using
      (InfoGeometry.Canonical.hasDerivAt_expTransport_at_zero
        (A := EndH) (X := V.connectionGenerator) (A₀ := modular_j (E := E)))
  have hLeft :
      HasDerivAt
        (fun t => transportedParitySupercharge (E := E) V t * spectral_epsilon (E := E))
        (transportCommutator (E := E) V.connectionGenerator (modular_j (E := E))
          * spectral_epsilon (E := E))
        0 := by
    simpa [transportedParitySupercharge] using hA.mul_const (spectral_epsilon (E := E))
  have hRight :
      HasDerivAt
        (fun t => spectral_epsilon (E := E) * transportedParitySupercharge (E := E) V t)
        (spectral_epsilon (E := E)
          * transportCommutator (E := E) V.connectionGenerator (modular_j (E := E)))
        0 := by
    simpa [transportedParitySupercharge] using hA.const_mul (spectral_epsilon (E := E))
  simpa [fockAnticommutator, superBracket_odd_odd] using (hLeft.add hRight).deriv

/--
The transported anomaly seed splits functorially along the phase-linear /
phase-antilinear decomposition of the connection generator.
-/
@[rep_depth transport]
theorem deriv_anticommutator_transportedParity_staticModular_at_zero_eq_split_generator
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    deriv
        (fun t =>
          fockAnticommutator (E := E)
            (transportedParitySupercharge (E := E) V t)
            (spectral_epsilon (E := E)))
        0
      =
    fockAnticommutator (E := E)
      (transportCommutator (E := E)
        (phaseLinearPart (E := E) V.connectionGenerator)
        (modular_j (E := E)))
      (spectral_epsilon (E := E))
      +
    fockAnticommutator (E := E)
      (transportCommutator (E := E)
        (phaseAntilinearPart (E := E) V.connectionGenerator)
        (modular_j (E := E)))
      (spectral_epsilon (E := E)) := by
  rw [deriv_anticommutator_transportedParity_staticModular_at_zero]
  rw [transportCommutator_split_generator (E := E) V.connectionGenerator (modular_j (E := E))]
  simpa [fockAnticommutator] using
    (superBracket_add_left (E := E) SuperParity.odd SuperParity.odd
      (transportCommutator (E := E)
        (phaseLinearPart (E := E) V.connectionGenerator)
        (modular_j (E := E)))
      (transportCommutator (E := E)
        (phaseAntilinearPart (E := E) V.connectionGenerator)
        (modular_j (E := E)))
      (spectral_epsilon (E := E)))

/--
If the phase-linear part of the connection generator commutes with `J`, the
transported anomaly seed is sourced purely by the phase-antilinear channel.
-/
@[rep_depth transport]
theorem deriv_anticommutator_transportedParity_staticModular_at_zero_eq_phaseAntilinearSeed_of_commute_phaseLinearPart
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm :
      Commute (modular_j (E := E))
        (phaseLinearPart (E := E) V.connectionGenerator)) :
    deriv
        (fun t =>
          fockAnticommutator (E := E)
            (transportedParitySupercharge (E := E) V t)
            (spectral_epsilon (E := E)))
        0
      =
    fockAnticommutator (E := E)
      (transportCommutator (E := E)
        (phaseAntilinearPart (E := E) V.connectionGenerator)
        (modular_j (E := E)))
      (spectral_epsilon (E := E)) := by
  rw [deriv_anticommutator_transportedParity_staticModular_at_zero_eq_split_generator (E := E) V]
  have hZero :
      transportCommutator (E := E)
        (phaseLinearPart (E := E) V.connectionGenerator)
        (modular_j (E := E)) = 0 := by
    unfold transportCommutator
    rw [show
      (phaseLinearPart (E := E) V.connectionGenerator).comp (modular_j (E := E))
        =
      (modular_j (E := E)).comp (phaseLinearPart (E := E) V.connectionGenerator) by
        simpa using hComm.eq.symm]
    simp
  simp [hZero]

/--
If the full connection generator commutes with the canonical triality/parity
supercharge `J`, the transported anomaly seed vanishes at the base point.
-/
@[rep_depth transport]
theorem deriv_anticommutator_transportedParity_staticModular_at_zero_eq_zero_of_commute_modularJ
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm : Commute (modular_j (E := E)) V.connectionGenerator) :
    deriv
        (fun t =>
          fockAnticommutator (E := E)
            (transportedParitySupercharge (E := E) V t)
            (spectral_epsilon (E := E)))
        0
      = 0 := by
  rw [deriv_anticommutator_transportedParity_staticModular_at_zero]
  have hZero :
      transportCommutator (E := E)
        V.connectionGenerator
        (modular_j (E := E)) = 0 := by
    unfold transportCommutator
    rw [show V.connectionGenerator.comp (modular_j (E := E))
        = (modular_j (E := E)).comp V.connectionGenerator by
          simpa using hComm.eq.symm]
    simp
  simp [hZero]

/--
Quasilattice odd-odd bracket readout whose continuum shadow is the translation
channel: the base-point anticommutator deformation of the transported `J`/static
`ε` pair.
-/
@[rep_depth transport]
noncomputable def quasilatticeTranslationCandidate
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) : EndH :=
  deriv
    (fun t =>
      fockAnticommutator (E := E)
        (transportedParitySupercharge (E := E) V t)
        (spectral_epsilon (E := E)))
    0

/--
Repo-native hopping/transport seed for the quasilattice translation candidate.
-/
@[rep_depth transport]
noncomputable def quasilatticeHoppingTranslationSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) : EndH :=
  fockAnticommutator (E := E)
    (transportCommutator (E := E) V.connectionGenerator (modular_j (E := E)))
    (spectral_epsilon (E := E))

/-- Alias emphasizing the hopping interpretation of the same translation lane. -/
@[rep_depth transport]
noncomputable def quasilatticeHoppingTranslationCandidate
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) : EndH :=
  quasilatticeTranslationCandidate (E := E) V

/-- Phase-linear contribution to the quasilattice translation seed. -/
@[rep_depth transport]
noncomputable def quasilatticePhaseLinearTranslationSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) : EndH :=
  fockAnticommutator (E := E)
    (transportCommutator (E := E)
      (phaseLinearPart (E := E) V.connectionGenerator)
      (modular_j (E := E)))
    (spectral_epsilon (E := E))

/-- Phase-antilinear contribution to the quasilattice translation seed. -/
@[rep_depth transport]
noncomputable def quasilatticePhaseAntilinearTranslationSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) : EndH :=
  fockAnticommutator (E := E)
    (transportCommutator (E := E)
      (phaseAntilinearPart (E := E) V.connectionGenerator)
      (modular_j (E := E)))
    (spectral_epsilon (E := E))

/-- The quasilattice translation candidate is exactly its hopping-seed formula. -/
@[rep_depth transport]
theorem quasilatticeTranslationCandidate_eq_hoppingSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    quasilatticeTranslationCandidate (E := E) V
      = quasilatticeHoppingTranslationSeed (E := E) V := by
  simpa [quasilatticeTranslationCandidate, quasilatticeHoppingTranslationSeed] using
    deriv_anticommutator_transportedParity_staticModular_at_zero (E := E) V

/--
The quasilattice translation candidate splits functorially into its phase-linear
and phase-antilinear hopping seeds.
-/
@[rep_depth transport]
theorem quasilatticeTranslationCandidate_eq_phaseLinearSeed_add_phaseAntilinearSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    quasilatticeTranslationCandidate (E := E) V
      = quasilatticePhaseLinearTranslationSeed (E := E) V
          + quasilatticePhaseAntilinearTranslationSeed (E := E) V := by
  simpa [quasilatticeTranslationCandidate, quasilatticePhaseLinearTranslationSeed,
      quasilatticePhaseAntilinearTranslationSeed] using
    deriv_anticommutator_transportedParity_staticModular_at_zero_eq_split_generator (E := E) V

/--
If the phase-linear part commutes with `J`, the quasilattice translation lane is
sourced purely by the phase-antilinear hopping seed.
-/
@[rep_depth transport]
theorem quasilatticeTranslationCandidate_eq_phaseAntilinearSeed_of_commute_phaseLinearPart
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm :
      Commute (modular_j (E := E))
        (phaseLinearPart (E := E) V.connectionGenerator)) :
    quasilatticeTranslationCandidate (E := E) V
      = quasilatticePhaseAntilinearTranslationSeed (E := E) V := by
  simpa [quasilatticeTranslationCandidate, quasilatticePhaseAntilinearTranslationSeed] using
    deriv_anticommutator_transportedParity_staticModular_at_zero_eq_phaseAntilinearSeed_of_commute_phaseLinearPart
      (E := E) V hComm

end Core

end InfoGeometry.Canonical.SuperchargeTransportBridge
