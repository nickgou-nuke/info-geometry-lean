import InfoGeometry.Canonical.KKTCore
import InfoGeometry.Canonical.Cl11LorentzAction
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.BogoliubovClosedForms
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.PhaseAxisCartanSymmetricLie
import InfoGeometry.Canonical.WeylGaugeField
import InfoGeometry.Core.CartanPhaseAxisForcing
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.WindingOrbitClosure

Formalization of the topological winding number $N$ in the $Cl(1,1)$ operator algebra.

This module implements the Drazin-branch covering map for the modular generator,
grounding the $2\pi N$ periodicity of the modular clock entirely within the
real geometric domain.

The clock tick $N$ represents the winding around the modular singularity,
mapping to the Drazin index of the operator flow.
-/

namespace InfoGeometry.Canonical.WindingOrbitClosure

open InfoGeometry.Krein
open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.Cl11LorentzAction
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Quantum
open InfoGeometry.Core

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => DoubledSpace H →L[ℝ] DoubledSpace H

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
The topological clock generator (unit bivector axis for rotation).
This is the Hestenes rotation axis $J \circ \epsilon$ on the doubled real lane.
-/
@[rep_depth transport]
noncomputable def clockAxis (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  (modular_j (E := E)).comp (spectral_epsilon (E := E))

/--
The multi-branched modular generator (The Drazin-Branch Covering Map).

$K_N = K_{principal} + 2\pi N J \epsilon$

Where:
- `K_principal` is the base modular Hamiltonian (regular core).
- `N` is the Winding Number (Clock Tick).
-/
@[rep_depth transport]
noncomputable def multiBranchedGenerator (K : EndH) (N : ℤ) : EndH :=
  K + (2 * Real.pi * (N : ℝ)) • clockAxis H

/--
The topo-shift between adjacent winding branches.
-/
@[rep_depth transport]
noncomputable def topoShift (N : ℤ) : EndH :=
  (2 * Real.pi * (N : ℝ)) • clockAxis H

/--
The topo-shift commutes with the base generator if the generator is grade-neutral
or commutes with the clock axis.
-/
theorem topoShift_commute_base
    (K : EndH) (N : ℤ)
    (hComm : Commute K (clockAxis H)) :
    Commute K (topoShift N) := by
  unfold topoShift
  exact hComm.smul_right (2 * Real.pi * (N : ℝ))

/--
The discrete topo-shift between winding branches $N$ and $N+1$ is additive.
-/
theorem multiBranchedGenerator_shift
    (K : EndH) (N : ℤ) :
    multiBranchedGenerator K (N + 1) =
      multiBranchedGenerator K N + (2 * Real.pi) • clockAxis H := by
  unfold multiBranchedGenerator
  have hCast : ((N + 1 : ℤ) : ℝ) = (N : ℝ) + 1 := by norm_num
  rw [hCast, mul_add, add_smul, mul_one]
  simp [add_left_comm, add_comm]

/--
The $2\pi$ modular rotation orbit identity.
In the real doubled representation, the rotation $e^{2\pi J\epsilon}$ resolves
to the identity on the state manifold.
-/
theorem modular_rotation_identity :
    NormedSpace.exp ((2 * Real.pi) • clockAxis H) = (1 : EndH) := by
  have hSq : (clockAxis H).comp (clockAxis H) = -(ContinuousLinearMap.id ℝ (DoubledSpace H)) := by
    simpa [clockAxis, InvolutiveSelfDualCarrier.K, doubledCarrier] using
      (InvolutiveSelfDualCarrier.K_sq (X := doubledCarrier (E := H)))
  have hExp := InfoGeometry.Canonical.BogoliubovClosedForms.exp_eq_cos_add_sin_of_sq_eq_neg_one
    (E := H) (G := clockAxis H) hSq (2 * Real.pi)
  simp [hExp, Real.cos_two_pi, Real.sin_two_pi]

/--
The Winding Number $N$ acts as a discrete shift that leaves the exponential
transport invariant (The Periodic Closure).
-/
theorem winding_orbit_periodicity (K : EndH) (N : ℤ)
    (hComm : Commute K (clockAxis H)) :
    NormedSpace.exp (multiBranchedGenerator K N) =
      NormedSpace.exp K := by
  unfold multiBranchedGenerator
  rw [NormedSpace.exp_add_of_commute (hComm.smul_right _)]
  have hPower : NormedSpace.exp ((2 * Real.pi * (N : ℝ)) • clockAxis H) = 1 := by
    have hSq : (clockAxis H).comp (clockAxis H) = -(ContinuousLinearMap.id ℝ (DoubledSpace H)) := by
      simpa [clockAxis, InvolutiveSelfDualCarrier.K, doubledCarrier] using
        (InvolutiveSelfDualCarrier.K_sq (X := doubledCarrier (E := H)))
    have hExp := InfoGeometry.Canonical.BogoliubovClosedForms.exp_eq_cos_add_sin_of_sq_eq_neg_one
      (E := H) (G := clockAxis H) hSq (2 * Real.pi * (N : ℝ))
    have hArg : 2 * Real.pi * (N : ℝ) = (N : ℝ) * (2 * Real.pi) := by ring
    have hCos : Real.cos (2 * Real.pi * (N : ℝ)) = 1 := by
      rw [hArg]
      exact Real.cos_int_mul_two_pi N
    have hSin : Real.sin (2 * Real.pi * (N : ℝ)) = 0 := by
      rw [hArg]
      simpa using (Real.sin_int_mul_two_pi_sub (x := (0 : ℝ)) N)
    calc
      NormedSpace.exp ((2 * Real.pi * (N : ℝ)) • clockAxis H)
          = Real.cos (2 * Real.pi * (N : ℝ)) • (1 : EndH)
              + Real.sin (2 * Real.pi * (N : ℝ)) • clockAxis H := hExp
      _ = (1 : EndH) := by simp [hCos, hSin]
  rw [hPower]
  simp

/--
Successor branch-cut periodicity: the `N → N + 1` step is one full winding
period and leaves the exponential branch value unchanged.
-/
theorem winding_orbit_periodicity_succ (K : EndH) (N : ℤ)
    (hComm : Commute K (clockAxis H)) :
    NormedSpace.exp (multiBranchedGenerator K (N + 1)) =
      NormedSpace.exp (multiBranchedGenerator K N) := by
  calc
    NormedSpace.exp (multiBranchedGenerator K (N + 1))
        = NormedSpace.exp K := winding_orbit_periodicity (H := H) K (N + 1) hComm
    _ = NormedSpace.exp (multiBranchedGenerator K N) := by
          symm
          exact winding_orbit_periodicity (H := H) K N hComm

/--
Owner forcing predicate for the modular transport lane:
phase-linearity of the seed enforces clock-axis commutation of the induced
transport generator.
-/
@[rep_depth transport]
def HasClockAxisForcingSeed (hMod : EndH) : Prop :=
  InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := H) hMod

/--
Commutator forcing theorem on the modular transport lane:
phase-linearity of the seed implies commutation with the winding clock axis.
-/
theorem modularTransportGenerator_commutes_clockAxis_of_forcingSeed
    (hMod : EndH)
    (hForce : HasClockAxisForcingSeed (H := H) hMod) :
    Commute
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      (clockAxis H) := by
  have hCommGlobal :
      Commute (InfoGeometry.Krein.clockAxis (E := H))
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) :=
    InfoGeometry.Canonical.BogoliubovTransport.modularComplexI_commutes_modularTransportGenerator_of_IsPhaseLinear
      (E := H) hMod hForce
  have hAxis : clockAxis H = InfoGeometry.Krein.clockAxis (E := H) := by
    rfl
  simpa [hAxis] using hCommGlobal.symm

/--
Winding periodicity obtained from the forcing predicate, with no explicit
commutation assumption in the theorem signature.
-/
theorem winding_orbit_periodicity_of_forcingSeed
    (hMod : EndH) (N : ℤ)
    (hForce : HasClockAxisForcingSeed (H := H) hMod) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) =
      NormedSpace.exp
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) := by
  have hCommLocal :
      Commute
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        (clockAxis H) :=
    modularTransportGenerator_commutes_clockAxis_of_forcingSeed (H := H) hMod hForce
  exact winding_orbit_periodicity
    (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (N := N) hCommLocal

/--
Derived periodic closure for the canonical modular transport generator: if the
seed is phase-linear, commutation with the clock axis is algebraically forced.
-/
theorem winding_orbit_periodicity_of_IsPhaseLinear_modularTransportGenerator
    (hMod : EndH) (N : ℤ)
    (hPhase :
      InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := H) hMod) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) =
      NormedSpace.exp
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) := by
  exact winding_orbit_periodicity_of_forcingSeed (H := H) hMod N hPhase

/--
Winding obstruction: deviation from exact branch-periodic closure at winding `N`.
-/
@[rep_depth transport]
noncomputable def windingOrbitObstruction (K : EndH) (N : ℤ) : EndH :=
  NormedSpace.exp (multiBranchedGenerator K N) - NormedSpace.exp K

/--
Clock-faithful exponential branch predicate.

This is the exact extra hypothesis needed for the reverse D1 direction. It is
not global injectivity of the exponential map, which would be false on winding
branches. It only says that, on the chosen branch and generator, zero winding
obstruction is a faithful detector of clock-axis commutation.
-/
@[rep_depth transport]
def IsClockFaithfulExponentialBranch (K : EndH) (N : ℤ) : Prop :=
  NormedSpace.exp (multiBranchedGenerator K N) = NormedSpace.exp K →
    Commute K (clockAxis H)

/--
Local gauge certificate for clock-faithful winding branches.

The Weyl field/shift/response fields record the local-gauge data. The only
non-formal analytic content required for D1 is the final faithful-readout field:
if the gauge readout cannot distinguish the two exponential branch values, then
the clock commutator must vanish. This isolates the needed local symmetry
hypothesis instead of replacing it with global exponential injectivity.
-/
@[rep_depth transport]
structure LocalClockGaugeSymmetryCertificate (K : EndH) (N : ℤ) where
  gaugeField : InfoGeometry.Canonical.WeylGaugeField EndH EndH
  gaugeShift : InfoGeometry.Canonical.WeylGaugeParameter EndH EndH
  response : InfoGeometry.Canonical.GeometricResponse EndH EndH
  logGenerator : InfoGeometry.Canonical.LogGenerator EndH EndH
  response_gaugeInvariant :
    InfoGeometry.Canonical.WeylGaugeField.IsGaugeInvariant response
  branch_readout_faithful :
    response.responseOf (NormedSpace.exp (multiBranchedGenerator K N)) =
      response.responseOf (NormedSpace.exp K) →
        Commute K (clockAxis H)

/--
The local Weyl gauge fields in a clock-gauge certificate have invariant
responses under the certified local shift.
-/
theorem localClockGauge_response_transform_eq
    {K : EndH} {N : ℤ}
    (C : LocalClockGaugeSymmetryCertificate (H := H) K N) :
    (C.gaugeField.transform C.gaugeShift).respond C.response C.logGenerator =
      C.gaugeField.respond C.response C.logGenerator := by
  exact InfoGeometry.Canonical.WeylGaugeField.respond_transform_eq_of_isGaugeInvariant
    C.gaugeField C.gaugeShift C.response C.logGenerator C.response_gaugeInvariant

/--
Local gauge symmetry plus faithful branch readout yields the clock-faithful
exponential branch required for the reverse D1 implication.
-/
theorem clockFaithfulExponentialBranch_of_localClockGaugeSymmetry
    {K : EndH} {N : ℤ}
    (C : LocalClockGaugeSymmetryCertificate (H := H) K N) :
    IsClockFaithfulExponentialBranch (H := H) K N := by
  intro hExp
  exact C.branch_readout_faithful (congrArg C.response.responseOf hExp)

/--
If the generator commutes with the modular clock axis, the winding obstruction
vanishes.
-/
theorem windingOrbitObstruction_eq_zero_of_commute
    (K : EndH) (N : ℤ)
    (hComm : Commute K (clockAxis H)) :
    windingOrbitObstruction K N = 0 := by
  unfold windingOrbitObstruction
  rw [winding_orbit_periodicity (K := K) (N := N) hComm]
  simp

/--
Phase-linearity of the modular seed forces zero winding obstruction for the
induced transport generator branch.
-/
theorem windingOrbitObstruction_modularTransportGenerator_eq_zero_of_forcingSeed
    (hMod : EndH) (N : ℤ)
    (hForce : HasClockAxisForcingSeed (H := H) hMod) :
    windingOrbitObstruction
      (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N = 0 := by
  exact windingOrbitObstruction_eq_zero_of_commute
    (H := H)
    (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (N := N)
    (modularTransportGenerator_commutes_clockAxis_of_forcingSeed (H := H) hMod hForce)

/--
Backward-compatible obstruction-zero export for the explicit
`IsPhaseLinear` transport seed surface.
-/
theorem windingOrbitObstruction_modularTransportGenerator_eq_zero_of_IsPhaseLinear
    (hMod : EndH) (N : ℤ)
    (hPhase :
      InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := H) hMod) :
    windingOrbitObstruction
      (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N = 0 := by
  exact windingOrbitObstruction_modularTransportGenerator_eq_zero_of_forcingSeed
    (H := H) hMod N hPhase

/--
Cartan-even (gauge) sector is automatically winding-periodic: no extra
commutation hypothesis is required.
-/
theorem winding_orbit_periodicity_modularGeneratorGaugePart
    (hMod : EndH) (N : ℤ) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorGaugePart (E := H) hMod) N) =
      NormedSpace.exp
        (InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorGaugePart (E := H) hMod) := by
  have hPhase :
      InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := H)
        (InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorGaugePart (E := H) hMod) :=
    InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorGaugePart_isPhaseLinear (E := H) hMod
  have hCommGlobal :
      Commute
        (InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorGaugePart (E := H) hMod)
        (InfoGeometry.Krein.clockAxis (E := H)) := by
    simpa [InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear, Commute] using hPhase
  have hAxis : clockAxis H = InfoGeometry.Krein.clockAxis (E := H) := by
    rfl
  have hCommLocal :
      Commute
        (InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorGaugePart (E := H) hMod)
        (clockAxis H) := by
    simpa [hAxis] using hCommGlobal
  exact winding_orbit_periodicity
    (K := InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorGaugePart (E := H) hMod)
    (N := N) hCommLocal

/--
Detailed-equilibrium predicate on the modular transport lane.
`scalePart = 0` means the Cartan-odd (noncommuting circular) channel is absent,
so only the commuting `g₀` channel remains.
-/
@[rep_depth transport]
def IsDetailedEquilibriumSeed (hMod : EndH) : Prop :=
  InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod = 0

/--
Backward-compatible alias for the Cartan-grade forcing predicate.
-/
@[rep_depth transport]
abbrev HasCartanGradeForcingSeed (hMod : EndH) : Prop :=
  IsDetailedEquilibriumSeed (H := H) hMod

/--
Proof-carrying witness for the detailed-equilibrium forcing surface.

This narrows the remaining bare `hEq : IsDetailedEquilibriumSeed ...` hypothesis
on the winding owner lane to an explicit witness object.
-/
@[rep_depth transport]
structure DetailedEquilibriumWitness (hMod : EndH) where
  hEq : IsDetailedEquilibriumSeed (H := H) hMod

namespace DetailedEquilibriumWitness

/-- Recover the detailed-equilibrium proposition from the proof-carrying witness. -/
@[rep_depth transport]
theorem detailedEquilibrium_of_witness
    {hMod : EndH}
    (W : DetailedEquilibriumWitness (H := H) hMod) :
    IsDetailedEquilibriumSeed (H := H) hMod :=
  W.hEq

end DetailedEquilibriumWitness

/--
Detailed-equilibrium forcing on the modular transport lane:
vanishing Cartan-odd scale sector forces commutation with the clock axis.
-/
theorem modularTransportGenerator_commutes_clockAxis_of_detailedEquilibrium
    (hMod : EndH)
    (hEq : IsDetailedEquilibriumSeed (H := H) hMod) :
    Commute
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      (clockAxis H) := by
  have hCommGlobal :
      Commute
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        (InfoGeometry.Krein.clockAxis (E := H)) :=
    InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator_commutes_clockAxis_of_scalePart_eq_zero
      (E := H) hMod hEq
  have hAxis : clockAxis H = InfoGeometry.Krein.clockAxis (E := H) := by
    rfl
  simpa [hAxis] using hCommGlobal

/--
Backward-compatible theorem surface for Cartan-grade forcing.
-/
theorem modularTransportGenerator_commutes_clockAxis_of_cartanGradeForcingSeed
    (hMod : EndH)
    (hForce : HasCartanGradeForcingSeed (H := H) hMod) :
    Commute
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      (clockAxis H) := by
  exact modularTransportGenerator_commutes_clockAxis_of_detailedEquilibrium
    (H := H) hMod hForce

/--
Witness-routed owner theorem for the detailed-equilibrium forcing lane.
This removes the bare `hEq` argument for callers that already own the explicit
proof-carrying detailed-equilibrium witness.
-/
theorem modularTransportGenerator_commutes_clockAxis_of_detailedEquilibriumWitness
    (hMod : EndH)
    (W : DetailedEquilibriumWitness (H := H) hMod) :
    Commute
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      (clockAxis H) := by
  exact modularTransportGenerator_commutes_clockAxis_of_detailedEquilibrium
    (H := H) hMod W.hEq

/--
Winding periodicity obtained from detailed equilibrium, with no explicit
commutation hypothesis in the theorem signature.
-/
theorem winding_orbit_periodicity_of_detailedEquilibrium
    (hMod : EndH) (N : ℤ)
    (hEq : IsDetailedEquilibriumSeed (H := H) hMod) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) =
      NormedSpace.exp
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) := by
  have hCommLocal :
      Commute
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        (clockAxis H) :=
    modularTransportGenerator_commutes_clockAxis_of_detailedEquilibrium
      (H := H) hMod hEq
  exact winding_orbit_periodicity
    (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (N := N) hCommLocal

/--
Branch-cut numbering theorem on the detailed-equilibrium lane:
`N → N + 1` is exactly one period winding.
-/
theorem winding_orbit_periodicity_succ_of_detailedEquilibrium
    (hMod : EndH) (N : ℤ)
    (hEq : IsDetailedEquilibriumSeed (H := H) hMod) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) (N + 1)) =
      NormedSpace.exp
        (multiBranchedGenerator
          (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) := by
  have hCommLocal :
      Commute
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        (clockAxis H) :=
    modularTransportGenerator_commutes_clockAxis_of_detailedEquilibrium
      (H := H) hMod hEq
  exact winding_orbit_periodicity_succ
    (H := H)
    (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (N := N) hCommLocal

/--
Backward-compatible API surface: Cartan-grade forcing routes through the
detailed-equilibrium owner theorem.
-/
theorem winding_orbit_periodicity_of_cartanGradeForcingSeed
    (hMod : EndH) (N : ℤ)
    (hForce : HasCartanGradeForcingSeed (H := H) hMod) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) =
      NormedSpace.exp
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) := by
  exact winding_orbit_periodicity_of_detailedEquilibrium
    (H := H) hMod N hForce

/--
Backward-compatible branch-cut numbering theorem for the Cartan-grade naming.
-/
theorem winding_orbit_periodicity_succ_of_cartanGradeForcingSeed
    (hMod : EndH) (N : ℤ)
    (hForce : HasCartanGradeForcingSeed (H := H) hMod) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) (N + 1)) =
      NormedSpace.exp
        (multiBranchedGenerator
          (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) := by
  exact winding_orbit_periodicity_succ_of_detailedEquilibrium
    (H := H) hMod N hForce

/--
Backward-compatible API surface: the previous scale-part statement now routes
through the detailed-equilibrium owner theorem.
-/
theorem winding_orbit_periodicity_modularTransportGenerator_of_scalePart_eq_zero
    (hMod : EndH) (N : ℤ)
    (hScaleZero :
      InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod = 0) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) =
      NormedSpace.exp
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) := by
  exact winding_orbit_periodicity_of_detailedEquilibrium
    (H := H) hMod N hScaleZero

/--
Commutator-forcing form of detailed equilibrium:
vanishing scaling sector forces zero clock-axis commutator of the modular
generator.
-/
theorem modularTransportGenerator_commutator_clockAxis_eq_zero_of_detailedEquilibrium
    (hMod : EndH)
    (hEq : IsDetailedEquilibriumSeed (H := H) hMod) :
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator (E := H)
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      (clockAxis H)
      = 0 := by
  have hCommLocal :
      Commute
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        (clockAxis H) :=
    modularTransportGenerator_commutes_clockAxis_of_detailedEquilibrium
      (H := H) hMod hEq
  unfold InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
  exact sub_eq_zero.mpr hCommLocal.eq

/--
Backward-compatible commutator forcing surface for Cartan-grade naming.
-/
theorem modularTransportGenerator_commutator_clockAxis_eq_zero_of_cartanGradeForcingSeed
    (hMod : EndH)
    (hForce : HasCartanGradeForcingSeed (H := H) hMod) :
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator (E := H)
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      (clockAxis H)
      = 0 := by
  exact modularTransportGenerator_commutator_clockAxis_eq_zero_of_detailedEquilibrium
    (H := H) hMod hForce

/--
Cartan-grade forcing bridge for the winding owner:
if an explicit Cartan symmetric-pair certificate places the modular generator
and clock axis in the phase-axis forcing pattern, and the same commutator is
also forced into the even sector, then the concrete transport commutator
vanishes by the real even/odd intersection rule.
-/
theorem modularTransportGenerator_commutator_clockAxis_eq_zero_of_cartanDualGrade
    (hMod : EndH)
    (D : InfoGeometry.Core.SymmetricLieAlgebra.CartanPhaseAxisForcingData EndH)
    (hK :
      D.K =
        InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (hI : D.I = clockAxis H)
    (hEven : ⁅D.K, D.I⁆ ∈ D.S.𝔨) :
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator (E := H)
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      (clockAxis H)
      = 0 := by
  have hZero :
      ⁅D.K, D.I⁆ = 0 :=
    InfoGeometry.Core.SymmetricLieAlgebra.commutator_KI_eq_zero_of_dual_grade_forcing
      D hEven
  simpa [InfoGeometry.Canonical.BogoliubovTransport.lieBracket_eq_transportCommutator,
    hK, hI] using hZero

theorem modularTransportGenerator_commutator_clockAxis_eq_zero_of_scalePart_eq_zero
    (hMod : EndH)
    (hScaleZero :
      InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod = 0) :
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator (E := H)
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      (clockAxis H)
      = 0 := by
  exact modularTransportGenerator_commutator_clockAxis_eq_zero_of_detailedEquilibrium
    (H := H) hMod hScaleZero

/--
Non-equilibrium clock defect on the modular lane:
the commutator of the full transport generator with the clock axis.
-/
@[rep_depth transport]
noncomputable def nonEquilibriumClockDefect (hMod : EndH) : EndH :=
  InfoGeometry.Canonical.BogoliubovTransport.transportCommutator (E := H)
    (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (clockAxis H)

/--
Definition-level predicate for the noncommuting scale lane.
-/
def IsNoncommutingScaleLane (hMod : EndH) : Prop :=
  nonEquilibriumClockDefect (H := H) hMod ≠ 0

/--
Equilibrium clock lane: the modular transport generator has zero clock defect.
This is the exact equilibrium boundary for D1, not a generic
non-equilibrium claim.
-/
@[rep_depth transport]
def IsClockEquilibriumLane (hMod : EndH) : Prop :=
  nonEquilibriumClockDefect (H := H) hMod = 0

/--
The non-equilibrium predicate is exactly the negation of the clock-equilibrium
predicate.
-/
theorem isNoncommutingScaleLane_iff_not_clockEquilibrium
    (hMod : EndH) :
    IsNoncommutingScaleLane (H := H) hMod ↔
      ¬ IsClockEquilibriumLane (H := H) hMod := by
  rfl

/--
The non-equilibrium clock defect is exactly the commutation defect.
-/
theorem nonEquilibriumClockDefect_eq_zero_iff_commute
    (hMod : EndH) :
    nonEquilibriumClockDefect (H := H) hMod = 0 ↔
      Commute
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        (clockAxis H) := by
  unfold nonEquilibriumClockDefect
  unfold InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
  constructor
  · intro hZero
    exact sub_eq_zero.mp hZero
  · intro hComm
    exact sub_eq_zero.mpr hComm.eq

/--
Cartan dual-grade forcing produces the actual `Commute` witness required by
the winding periodicity owner theorem.
-/
theorem modularTransportGenerator_commutes_clockAxis_of_cartanDualGrade
    (hMod : EndH)
    (D : InfoGeometry.Core.SymmetricLieAlgebra.CartanPhaseAxisForcingData EndH)
    (hK :
      D.K =
        InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (hI : D.I = clockAxis H)
    (hEven : ⁅D.K, D.I⁆ ∈ D.S.𝔨) :
    Commute
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      (clockAxis H) := by
  exact (nonEquilibriumClockDefect_eq_zero_iff_commute (H := H) hMod).1
    (modularTransportGenerator_commutator_clockAxis_eq_zero_of_cartanDualGrade
      (H := H) hMod D hK hI hEven)

/--
Winding periodicity obtained directly from an explicit Cartan dual-grade
certificate, without an exposed raw commutation hypothesis.
-/
theorem winding_orbit_periodicity_of_cartanDualGrade
    (hMod : EndH) (N : ℤ)
    (D : InfoGeometry.Core.SymmetricLieAlgebra.CartanPhaseAxisForcingData EndH)
    (hK :
      D.K =
        InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (hI : D.I = clockAxis H)
    (hEven : ⁅D.K, D.I⁆ ∈ D.S.𝔨) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) =
      NormedSpace.exp
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) := by
  exact winding_orbit_periodicity
    (H := H)
    (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (N := N)
    (modularTransportGenerator_commutes_clockAxis_of_cartanDualGrade
      (H := H) hMod D hK hI hEven)

/--
Successor branch periodicity obtained directly from the Cartan dual-grade
certificate.
-/
theorem winding_orbit_periodicity_succ_of_cartanDualGrade
    (hMod : EndH) (N : ℤ)
    (D : InfoGeometry.Core.SymmetricLieAlgebra.CartanPhaseAxisForcingData EndH)
    (hK :
      D.K =
        InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (hI : D.I = clockAxis H)
    (hEven : ⁅D.K, D.I⁆ ∈ D.S.𝔨) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) (N + 1)) =
      NormedSpace.exp
        (multiBranchedGenerator
          (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) := by
  exact winding_orbit_periodicity_succ
    (H := H)
    (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (N := N)
    (modularTransportGenerator_commutes_clockAxis_of_cartanDualGrade
      (H := H) hMod D hK hI hEven)

/--
The non-equilibrium defect is sourced exactly by the Cartan-odd scale channel.
-/
theorem nonEquilibriumClockDefect_eq_two_smul_scalePart_comp_clockAxis
    (hMod : EndH) :
    nonEquilibriumClockDefect (H := H) hMod
      =
    (2 : ℝ) •
      ((InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod).comp
        (clockAxis H)) := by
  have hSource :
      InfoGeometry.Canonical.BogoliubovTransport.phaseAxisForce (E := H)
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        =
      (2 : ℝ) •
        ((InfoGeometry.Canonical.BogoliubovTransport.phaseAntilinearPart (E := H)
            (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)).comp
          (InfoGeometry.Krein.clockAxis (E := H))) := by
    simpa using
      (InfoGeometry.Canonical.BogoliubovTransport.phaseAxisForce_eq_from_phaseAntilinearPart
        (E := H) (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod))
  simpa [nonEquilibriumClockDefect,
    InfoGeometry.Canonical.BogoliubovTransport.phaseAxisForce,
    InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart,
    clockAxis] using hSource

/--
Right-composition by the clock axis is injective because the doubled-real
clock axis squares to `-1`.  This is the constructive cancellation step that
lets the clock defect detect the scale part itself, not just its right action.
-/
theorem right_comp_clockAxis_eq_zero_iff
    (A : EndH) :
    A.comp (clockAxis H) = 0 ↔ A = 0 := by
  constructor
  · intro hAK
    have hSq : (clockAxis H).comp (clockAxis H) =
        -(ContinuousLinearMap.id ℝ (DoubledSpace H)) := by
      simpa [clockAxis, InvolutiveSelfDualCarrier.K, doubledCarrier] using
        (InvolutiveSelfDualCarrier.K_sq (X := doubledCarrier (E := H)))
    have hAKK : A.comp ((clockAxis H).comp (clockAxis H)) = 0 := by
      rw [← ContinuousLinearMap.comp_assoc, hAK]
      simp
    have hNegA : A.comp ((clockAxis H).comp (clockAxis H)) = -A := by
      rw [hSq]
      simp
    exact neg_eq_zero.mp (hNegA.symm.trans hAKK)
  · intro hA
    simp [hA]

/--
The non-equilibrium clock defect vanishes exactly on detailed equilibrium:
the defect is `2 • scalePart ∘ clockAxis`, and the clock axis is invertible
up to sign.
-/
theorem nonEquilibriumClockDefect_eq_zero_iff_detailedEquilibrium
    (hMod : EndH) :
    nonEquilibriumClockDefect (H := H) hMod = 0 ↔
      IsDetailedEquilibriumSeed (H := H) hMod := by
  rw [nonEquilibriumClockDefect_eq_two_smul_scalePart_comp_clockAxis (H := H) hMod]
  constructor
  · intro hZero
    have hComp :
        (InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod).comp
          (clockAxis H) = 0 :=
      (smul_eq_zero.mp hZero).resolve_left (by norm_num)
    simpa [IsDetailedEquilibriumSeed] using
      (right_comp_clockAxis_eq_zero_iff
        (H := H)
        (A := InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod)).1 hComp
  · intro hEq
    change (2 : ℝ) •
        ((InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod).comp
          (clockAxis H)) = 0
    rw [hEq]
    simp

/--
Named Cartan scale-split source law for D1:
the winding clock commutator is sourced exactly by the Cartan-odd
phase-antilinear scale sector of the modular generator.
-/
theorem modularTransportGenerator_clockAxis_commutator_eq_cartanScaleSource
    (hMod : EndH) :
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator (E := H)
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      (clockAxis H)
      =
    (2 : ℝ) •
      ((InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod).comp
        (clockAxis H)) := by
  simpa [nonEquilibriumClockDefect] using
    nonEquilibriumClockDefect_eq_two_smul_scalePart_comp_clockAxis (H := H) hMod

/--
Equilibrium/non-equilibrium boundary in source form:
the clock lane is at equilibrium exactly when the Cartan scale-source readout
`2 • scalePart ∘ clockAxis` vanishes.
-/
theorem clockEquilibrium_iff_cartanScaleSource_eq_zero
    (hMod : EndH) :
    IsClockEquilibriumLane (H := H) hMod ↔
      (2 : ℝ) •
        ((InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod).comp
          (clockAxis H)) = 0 := by
  unfold IsClockEquilibriumLane
  rw [nonEquilibriumClockDefect_eq_two_smul_scalePart_comp_clockAxis]

/--
The non-equilibrium clock lane is exactly non-vanishing of the Cartan
scale-source readout.
-/
theorem noncommutingScaleLane_iff_cartanScaleSource_ne_zero
    (hMod : EndH) :
    IsNoncommutingScaleLane (H := H) hMod ↔
      (2 : ℝ) •
        ((InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod).comp
          (clockAxis H)) ≠ 0 := by
  unfold IsNoncommutingScaleLane
  rw [nonEquilibriumClockDefect_eq_two_smul_scalePart_comp_clockAxis]

/--
Concrete phase-axis Cartan closure for D1:
the full modular-generator clock commutator vanishes once the scale-clock
source commutator is certified in the even sector.  The scale-clock commutator
is already odd by `PhaseAxisCartanSymmetricLie`; this theorem is the maintained
bridge from that dual-grade certificate to the winding owner.
-/
theorem modularTransportGenerator_commutator_clockAxis_eq_zero_of_scaleClock_mem_phaseAxis_even
    (hMod : EndH)
    (hEven :
      ⁅InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod,
        clockAxis H⁆
        ∈ (InfoGeometry.Canonical.PhaseAxisCartanSymmetricLie.phaseAxisSymmetricLieAlgebra
            (E := H)).evenLieSubalgebra) :
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator (E := H)
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      (clockAxis H)
      = 0 := by
  have hScaleZero :
      ⁅InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod,
        InfoGeometry.Krein.clockAxis (E := H)⁆ = 0 :=
    InfoGeometry.Canonical.PhaseAxisCartanSymmetricLie.scaleClock_commutator_eq_zero_of_mem_phaseAxis_even
      (E := H) hMod hEven
  have hScaleTransport :
      InfoGeometry.Canonical.BogoliubovTransport.transportCommutator (E := H)
        (InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod)
        (clockAxis H)
        = 0 := by
    simpa [InfoGeometry.Canonical.BogoliubovTransport.lieBracket_eq_transportCommutator]
      using hScaleZero
  have hFullEqScale :
      InfoGeometry.Canonical.BogoliubovTransport.transportCommutator (E := H)
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        (clockAxis H)
        =
      InfoGeometry.Canonical.BogoliubovTransport.transportCommutator (E := H)
        (InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod)
        (clockAxis H) := by
    have hFull :=
      modularTransportGenerator_clockAxis_commutator_eq_cartanScaleSource (H := H) hMod
    have hScaleSource :
        InfoGeometry.Canonical.BogoliubovTransport.transportCommutator (E := H)
          (InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod)
          (clockAxis H)
          =
        (2 : ℝ) •
          ((InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod).comp
            (clockAxis H)) := by
      simpa [InfoGeometry.Canonical.BogoliubovTransport.phaseAxisForce, clockAxis] using
        InfoGeometry.Canonical.BogoliubovTransport.phaseAxisForce_eq_two_smul_comp_of_IsPhaseAntilinear
          (E := H)
          (InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart (E := H) hMod)
          (InfoGeometry.Canonical.BogoliubovTransport.modularGeneratorScalePart_isPhaseAntilinear
            (E := H) hMod)
    exact hFull.trans hScaleSource.symm
  rw [hFullEqScale, hScaleTransport]

/--
Detailed equilibrium kills the non-equilibrium defect exactly.
-/
theorem nonEquilibriumClockDefect_eq_zero_of_detailedEquilibrium
    (hMod : EndH)
    (hEq : IsDetailedEquilibriumSeed (H := H) hMod) :
    nonEquilibriumClockDefect (H := H) hMod = 0 := by
  exact (nonEquilibriumClockDefect_eq_zero_iff_commute (H := H) hMod).2
    (modularTransportGenerator_commutes_clockAxis_of_detailedEquilibrium
      (H := H) hMod hEq)

/--
Detailed equilibrium implies zero winding obstruction for the transport
generator branch.
-/
theorem windingOrbitObstruction_modularTransportGenerator_eq_zero_of_detailedEquilibrium
    (hMod : EndH) (N : ℤ)
    (hEq : IsDetailedEquilibriumSeed (H := H) hMod) :
    windingOrbitObstruction
      (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N = 0 := by
  exact windingOrbitObstruction_eq_zero_of_commute
    (H := H)
    (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (N := N)
    (modularTransportGenerator_commutes_clockAxis_of_detailedEquilibrium
      (H := H) hMod hEq)

/--
Clock-equilibrium is the exact source condition needed by the winding owner:
zero clock defect gives the commutation witness and therefore zero winding
obstruction.
-/
theorem windingOrbitObstruction_modularTransportGenerator_eq_zero_of_clockEquilibrium
    (hMod : EndH) (N : ℤ)
    (hEq : IsClockEquilibriumLane (H := H) hMod) :
    windingOrbitObstruction
      (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N = 0 := by
  exact windingOrbitObstruction_eq_zero_of_commute
    (H := H)
    (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (N := N)
    ((nonEquilibriumClockDefect_eq_zero_iff_commute (H := H) hMod).1 hEq)

/--
Faithful branch reverse direction:
if the selected exponential branch detects clock commutation, then zero winding
obstruction forces clock equilibrium of the modular transport generator.
-/
theorem clockEquilibrium_of_windingOrbitObstruction_eq_zero_of_clockFaithfulBranch
    (hMod : EndH) (N : ℤ)
    (hFaithful :
      IsClockFaithfulExponentialBranch
        (H := H)
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        N)
    (hObs :
      windingOrbitObstruction
        (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        N = 0) :
    IsClockEquilibriumLane (H := H) hMod := by
  have hExp :
      NormedSpace.exp
        (multiBranchedGenerator
          (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N)
        =
      NormedSpace.exp
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) := by
    exact sub_eq_zero.mp hObs
  exact (nonEquilibriumClockDefect_eq_zero_iff_commute (H := H) hMod).2
    (hFaithful hExp)

/--
With an explicit clock-faithful exponential branch, clock equilibrium is
equivalent to zero winding obstruction. Without this faithfulness hypothesis,
only the forward direction is source-owned.
-/
theorem clockEquilibrium_iff_windingOrbitObstruction_eq_zero_of_clockFaithfulBranch
    (hMod : EndH) (N : ℤ)
    (hFaithful :
      IsClockFaithfulExponentialBranch
        (H := H)
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        N) :
    IsClockEquilibriumLane (H := H) hMod ↔
      windingOrbitObstruction
        (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        N = 0 := by
  constructor
  · intro hEq
    exact windingOrbitObstruction_modularTransportGenerator_eq_zero_of_clockEquilibrium
      (H := H) hMod N hEq
  · intro hObs
    exact clockEquilibrium_of_windingOrbitObstruction_eq_zero_of_clockFaithfulBranch
      (H := H) hMod N hFaithful hObs

/--
Constructive reverse direction for D1: a local clock-gauge symmetry certificate
supplies the faithful branch witness, so zero winding obstruction forces clock
equilibrium without exposing `IsClockFaithfulExponentialBranch` separately.
-/
theorem clockEquilibrium_of_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry
    (hMod : EndH) (N : ℤ)
    (C : LocalClockGaugeSymmetryCertificate
      (H := H)
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      N)
    (hObs :
      windingOrbitObstruction
        (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        N = 0) :
    IsClockEquilibriumLane (H := H) hMod := by
  exact clockEquilibrium_of_windingOrbitObstruction_eq_zero_of_clockFaithfulBranch
    (H := H)
    hMod
    N
    (clockFaithfulExponentialBranch_of_localClockGaugeSymmetry (H := H) C)
    hObs

/--
Constructive faithful-branch package for the reverse D1 equivalence: a local
clock-gauge symmetry certificate is enough to recover the winding-obstruction /
clock-equilibrium iff on the selected branch.
-/
theorem clockEquilibrium_iff_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry
    (hMod : EndH) (N : ℤ)
    (C : LocalClockGaugeSymmetryCertificate
      (H := H)
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      N) :
    IsClockEquilibriumLane (H := H) hMod ↔
      windingOrbitObstruction
        (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        N = 0 := by
  exact clockEquilibrium_iff_windingOrbitObstruction_eq_zero_of_clockFaithfulBranch
    (H := H)
    hMod
    N
    (clockFaithfulExponentialBranch_of_localClockGaugeSymmetry (H := H) C)

/--
Constructive reverse-lane iff: the local clock-gauge certificate upgrades the
winding-obstruction criterion all the way to the raw non-equilibrium defect
surface, not just the packaged clock-equilibrium predicate.
-/
theorem nonEquilibriumClockDefect_eq_zero_iff_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry
    (hMod : EndH) (N : ℤ)
    (C : LocalClockGaugeSymmetryCertificate
      (H := H)
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      N) :
    nonEquilibriumClockDefect (H := H) hMod = 0 ↔
      windingOrbitObstruction
        (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        N = 0 := by
  show IsClockEquilibriumLane (H := H) hMod ↔
      windingOrbitObstruction
        (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        N = 0
  exact clockEquilibrium_iff_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry
    (H := H) hMod N C

/--
Constructive reverse-lane readback: on a certified local clock-gauge branch,
zero winding obstruction already forces vanishing of the non-equilibrium clock
defect, without a separate faithful-branch hypothesis.
-/
theorem nonEquilibriumClockDefect_eq_zero_of_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry
    (hMod : EndH) (N : ℤ)
    (C : LocalClockGaugeSymmetryCertificate
      (H := H)
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      N)
    (hObs :
      windingOrbitObstruction
        (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        N = 0) :
    nonEquilibriumClockDefect (H := H) hMod = 0 := by
  exact
    (nonEquilibriumClockDefect_eq_zero_iff_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry
      (H := H) hMod N C).2 hObs

/--
Clock-equilibrium gives branch periodicity for the modular transport generator.
-/
theorem winding_orbit_periodicity_of_clockEquilibrium
    (hMod : EndH) (N : ℤ)
    (hEq : IsClockEquilibriumLane (H := H) hMod) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) =
      NormedSpace.exp
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) := by
  exact winding_orbit_periodicity
    (H := H)
    (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (N := N)
    ((nonEquilibriumClockDefect_eq_zero_iff_commute (H := H) hMod).1 hEq)

/--
Clock-equilibrium gives successor branch periodicity for the modular transport
generator.
-/
theorem winding_orbit_periodicity_succ_of_clockEquilibrium
    (hMod : EndH) (N : ℤ)
    (hEq : IsClockEquilibriumLane (H := H) hMod) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) (N + 1)) =
      NormedSpace.exp
        (multiBranchedGenerator
          (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) := by
  exact winding_orbit_periodicity_succ
    (H := H)
    (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
    (N := N)
    ((nonEquilibriumClockDefect_eq_zero_iff_commute (H := H) hMod).1 hEq)

/--
Constructive branch periodicity: a local clock-gauge symmetry certificate plus
zero winding obstruction recovers clock equilibrium, so the modular transport
branch is periodic without exposing a separate faithful-branch or equilibrium
hypothesis.
-/
theorem winding_orbit_periodicity_of_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry
    (hMod : EndH) (N : ℤ)
    (C : LocalClockGaugeSymmetryCertificate
      (H := H)
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      N)
    (hObs :
      windingOrbitObstruction
        (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        N = 0) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) =
      NormedSpace.exp
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) := by
  exact winding_orbit_periodicity_of_clockEquilibrium
    (H := H)
    hMod
    N
    (clockEquilibrium_of_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry
      (H := H) hMod N C hObs)

/--
Successor branch periodicity on the same constructive reverse lane.
-/
theorem winding_orbit_periodicity_succ_of_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry
    (hMod : EndH) (N : ℤ)
    (C : LocalClockGaugeSymmetryCertificate
      (H := H)
      (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
      N)
    (hObs :
      windingOrbitObstruction
        (K := InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod)
        N = 0) :
    NormedSpace.exp
      (multiBranchedGenerator
        (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) (N + 1)) =
      NormedSpace.exp
        (multiBranchedGenerator
          (InfoGeometry.Canonical.BogoliubovTransport.modularTransportGenerator (E := H) hMod) N) := by
  exact winding_orbit_periodicity_succ_of_clockEquilibrium
    (H := H)
    hMod
    N
    (clockEquilibrium_of_windingOrbitObstruction_eq_zero_of_localClockGaugeSymmetry
      (H := H) hMod N C hObs)

/--
Any noncommuting scale lane is necessarily outside detailed equilibrium.
-/
theorem not_detailedEquilibrium_of_noncommutingScaleLane
    (hMod : EndH)
    (hNon : IsNoncommutingScaleLane (H := H) hMod) :
    ¬ IsDetailedEquilibriumSeed (H := H) hMod := by
  intro hEq
  exact hNon (nonEquilibriumClockDefect_eq_zero_of_detailedEquilibrium (H := H) hMod hEq)

/--
The noncommuting scale lane is precisely the complement of detailed
equilibrium on the winding clock defect.
-/
theorem noncommutingScaleLane_iff_not_detailedEquilibrium
    (hMod : EndH) :
    IsNoncommutingScaleLane (H := H) hMod ↔
      ¬ IsDetailedEquilibriumSeed (H := H) hMod := by
  unfold IsNoncommutingScaleLane
  constructor
  · exact not_detailedEquilibrium_of_noncommutingScaleLane (H := H) hMod
  · intro hNot hZero
    exact hNot
      ((nonEquilibriumClockDefect_eq_zero_iff_detailedEquilibrium (H := H) hMod).1 hZero)

end Core

end InfoGeometry.Canonical.WindingOrbitClosure
