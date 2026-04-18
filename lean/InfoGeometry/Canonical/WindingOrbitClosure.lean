import InfoGeometry.Canonical.KKTCore
import InfoGeometry.Canonical.Cl11LorentzAction
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.BogoliubovClosedForms
import InfoGeometry.Canonical.BogoliubovTransport
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
Any noncommuting scale lane is necessarily outside detailed equilibrium.
-/
theorem not_detailedEquilibrium_of_noncommutingScaleLane
    (hMod : EndH)
    (hNon : IsNoncommutingScaleLane (H := H) hMod) :
    ¬ IsDetailedEquilibriumSeed (H := H) hMod := by
  intro hEq
  exact hNon (nonEquilibriumClockDefect_eq_zero_of_detailedEquilibrium (H := H) hMod hEq)

end Core

end InfoGeometry.Canonical.WindingOrbitClosure
