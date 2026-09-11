import InfoGeometry.Canonical.RyuTakayanagiEntanglementBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RyuTakayanagiThermalTimeBridge
import InfoGeometry.Canonical.TrialitySpin8Permutations
import InfoGeometry.Canonical.Spin44CharacterShadow
import InfoGeometry.Quantum.SplitTrialityFockBridge

/-!
# Holographic Entanglement Symmetry

This file connects the existing finite Ryu-Takayanagi entropy/area readout to
the repository's real doubled split-triality kernel.

It deliberately does not introduce an abstract von Neumann entropy primitive, a
new `TrialityGroup`, or a full `Spin(4,4)` representation action.  The owner
facts available in the repository are:

* the scalar depth-indexed RT bridge in
  `Canonical.RyuTakayanagiEntanglementBridge`;
* the promoted forward-time thermal/de-Rham/RT bridge in
  `Canonical.RyuTakayanagiThermalTimeBridge`;
* the `Fin 3` triality sector cycle in `Canonical.TrialitySpin8Permutations`;
* the finite D4 character shadow in `Canonical.Spin44CharacterShadow`;
* the canonical real doubled split-triality supercharge in
  `Quantum.SplitTrialityFockBridge`.

The bridge below packages exactly those kernel-checked facts.
-/

set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.HolographicEntanglementSymmetry

open InfoGeometry.Canonical.RyuTakayanagiEntanglementBridge
open InfoGeometry.Canonical.RyuTakayanagiThermalTimeBridge
open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData
open InfoGeometry.Canonical.TrialitySpin8Permutations
open InfoGeometry.Canonical.Spin44CharacterShadow
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy
open InfoGeometry.Quantum
open InfoGeometry.Quantum.SplitTrialityFockBridge

section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => YangMillsContinuum.EndH E

/-- Sector-tagged entropy readout.  The current owner is sector-blind by design:
the depth-indexed boundary entropy depends on the Cantor depth, not on the
triality label. -/
def sectorSubtreeEntropy (_s : TrialitySector) (n : ℕ) : ℝ :=
  subtreeEntropy n

/-- Sector-tagged minimal surface readout.  This mirrors the sector-blind
finite RT owner while allowing triality-equivariance statements to be typed. -/
def sectorMinimalSurfaceArea (_s : TrialitySector) (n : ℕ) : ℝ :=
  minimalSurfaceArea n

@[simp] theorem sectorSubtreeEntropy_def (s : TrialitySector) (n : ℕ) :
    sectorSubtreeEntropy s n = subtreeEntropy n := rfl

@[simp] theorem sectorMinimalSurfaceArea_def (s : TrialitySector) (n : ℕ) :
    sectorMinimalSurfaceArea s n = minimalSurfaceArea n := rfl

/-- The finite entropy readout is invariant under one triality-sector step. -/
theorem sectorSubtreeEntropy_triality_invariant (s : TrialitySector) (n : ℕ) :
    sectorSubtreeEntropy (trialityCycle s) n = sectorSubtreeEntropy s n := rfl

/-- The finite minimal-area readout is invariant under one triality-sector step. -/
theorem sectorMinimalSurfaceArea_triality_invariant (s : TrialitySector) (n : ℕ) :
    sectorMinimalSurfaceArea (trialityCycle s) n = sectorMinimalSurfaceArea s n := rfl

/-- The triality sector action closes after three steps. -/
theorem trialityCycle_cube_apply (s : TrialitySector) :
    (trialityCycle ^ 3) s = s := by
  rw [trialityCycle_pow_three]
  rfl

/-- Sector-tagged RT formula, transported from the finite scalar RT owner. -/
theorem sector_ryu_takayanagi_formula (s : TrialitySector) (n : ℕ) :
    sectorSubtreeEntropy s n =
      sectorMinimalSurfaceArea s n / (4 * effectiveNewtonConstant) := by
  unfold sectorSubtreeEntropy sectorMinimalSurfaceArea
  exact ryu_takayanagi_formula n

/-- The RT readout is equivariant under the finite triality-sector cycle. -/
theorem sector_ryu_takayanagi_triality_equivariant
    (s : TrialitySector) (n : ℕ) :
    sectorSubtreeEntropy (trialityCycle s) n =
        sectorMinimalSurfaceArea (trialityCycle s) n / (4 * effectiveNewtonConstant) ∧
      sectorSubtreeEntropy (trialityCycle s) n = sectorSubtreeEntropy s n ∧
      sectorMinimalSurfaceArea (trialityCycle s) n = sectorMinimalSurfaceArea s n := by
  exact ⟨sector_ryu_takayanagi_formula (trialityCycle s) n,
    sectorSubtreeEntropy_triality_invariant s n,
    sectorMinimalSurfaceArea_triality_invariant s n⟩

/-- Canonical real doubled split-triality square law on the Hestenes/Krein carrier. -/
theorem splitTrialitySupercharge_square_eq_id
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (canonicalSplitTrialityKernel (E := E)).trialitySupercharge.comp
        (canonicalSplitTrialityKernel (E := E)).trialitySupercharge =
      LinearMap.id := by
  exact trialitySupercharge_square_eq_id_via_cliffordConcreteCAR (E := E)

/--
The concrete packet tying together the available holographic and triality
owners.  This is intentionally a finite, proof-carrying interface rather than
a claim of a full analytic RT/von-Neumann/`Spin(4,4)` theorem.
-/
def HolographicEntanglementTrialityPacket
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (s : TrialitySector) (n N : ℕ) : Prop :=
    sectorSubtreeEntropy s n =
      sectorMinimalSurfaceArea s n / (4 * effectiveNewtonConstant) ∧
    sectorSubtreeEntropy (trialityCycle s) n = sectorSubtreeEntropy s n
    ∧ sectorMinimalSurfaceArea (trialityCycle s) n = sectorMinimalSurfaceArea s n
    ∧ (trialityCycle ^ 3) s = s
    ∧
    (canonicalSplitTrialityKernel (E := E)).trialitySupercharge.comp
        (canonicalSplitTrialityKernel (E := E)).trialitySupercharge =
      LinearMap.id ∧
    (Finset.univ.filter fun ε : Fin 4 → Bool => EvenMinus ε).card = 8 ∧
    (Finset.univ.filter fun ε : Fin 4 → Bool => OddMinus ε).card = 8 ∧
    cumulativeBraidEntropy N = (N : ℝ) * braidEntanglementPerStep

/-- Canonical construction of the holographic entanglement/triality packet. -/
theorem canonical_holographic_entanglement_triality_packet
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (s : TrialitySector) (n N : ℕ) :
    HolographicEntanglementTrialityPacket E s n N := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sector_ryu_takayanagi_formula s n
  · exact sectorSubtreeEntropy_triality_invariant s n
  · exact sectorMinimalSurfaceArea_triality_invariant s n
  · exact trialityCycle_cube_apply s
  · exact splitTrialitySupercharge_square_eq_id (E := E)
  · exact evenMinus_card
  · exact oddMinus_card
  · rfl

/--
Capstone forward-time packet: holography/triality consumes the promoted
physical forward-time bridge directly, together with the existing finite RT and
split-triality kernel owners.
-/
def ForwardTimeHolographicTrialityPacket
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E))
    (s : TrialitySector) (n N : ℕ) (A : EndH) : Prop :=
  PositiveBranchClockPacket (E := E)
      (PhysicalForwardTimeBridge (E := E) B) n A ∧
    sectorSubtreeEntropy s n =
      sectorMinimalSurfaceArea s n / (4 * effectiveNewtonConstant) ∧
    sectorSubtreeEntropy (trialityCycle s) n = sectorSubtreeEntropy s n
    ∧ sectorMinimalSurfaceArea (trialityCycle s) n = sectorMinimalSurfaceArea s n
    ∧ (trialityCycle ^ 3) s = s
    ∧
    (canonicalSplitTrialityKernel (E := E)).trialitySupercharge.comp
        (canonicalSplitTrialityKernel (E := E)).trialitySupercharge =
      LinearMap.id ∧
    (Finset.univ.filter fun ε : Fin 4 → Bool => EvenMinus ε).card = 8 ∧
    (Finset.univ.filter fun ε : Fin 4 → Bool => OddMinus ε).card = 8 ∧
    cumulativeBraidEntropy N = (N : ℝ) * braidEntanglementPerStep

/--
Canonical construction of the capstone forward-time/triality/holography packet.
-/
theorem canonical_forward_time_holographic_triality_packet
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E))
    (s : TrialitySector) (n N : ℕ) (A : EndH) :
    ForwardTimeHolographicTrialityPacket (E := E) B s n N A := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact physicalForwardTimeBridge_clockPacket (E := E) (B := B) n A
  · exact sector_ryu_takayanagi_formula s n
  · exact sectorSubtreeEntropy_triality_invariant s n
  · exact sectorMinimalSurfaceArea_triality_invariant s n
  · exact trialityCycle_cube_apply s
  · exact splitTrialitySupercharge_square_eq_id (E := E)
  · exact evenMinus_card
  · exact oddMinus_card
  · rfl

/--
Projection theorem: from the capstone packet, the promoted physical lane yields
an explicit forward-time/winding readout on the positive branch.
-/
theorem forward_time_equals_positive_winding_readout
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E))
    {s : TrialitySector} {n N : ℕ} {A : EndH}
    (P : ForwardTimeHolographicTrialityPacket (E := E) B s n N A) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A =
        B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (n : ℤ)) A ∧
      ((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase (n : ℤ) ∧
      Complex.exp (((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) ∧
      subtreeEntropy n = minimalSurfaceArea n / (4 * effectiveNewtonConstant) := by
  exact ⟨
    P.1.1,
    P.1.2.1,
    P.1.2.2.1,
    by simpa [PhysicalForwardTimeBridge, identityDepthPositiveBranchBridge] using
      P.1.2.2.2
  ⟩

/--
The capstone packet also projects to the sector-tagged RT/triality readout at
the same positive winding step.
-/
theorem sector_forward_time_triality_readout
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E))
    {s : TrialitySector} {n N : ℕ} {A : EndH}
    (P : ForwardTimeHolographicTrialityPacket (E := E) B s n N A) :
    sectorSubtreeEntropy s n =
        sectorMinimalSurfaceArea s n / (4 * effectiveNewtonConstant) ∧
      sectorSubtreeEntropy (trialityCycle s) n = sectorSubtreeEntropy s n ∧
      sectorMinimalSurfaceArea (trialityCycle s) n = sectorMinimalSurfaceArea s n := by
  exact ⟨P.2.1, P.2.2.1, P.2.2.2.1⟩

/--
Positive-branch time clock theorem: on the promoted forward-time lane, the
nonnegative winding label `n` is the clock readout simultaneously governing
modular evolution, de Rham monodromy, unit Wilson holonomy, and the RT law.
-/
theorem positive_branch_time_clock_theorem
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E))
    {s : TrialitySector} {n N : ℕ} {A : EndH}
    (P : ForwardTimeHolographicTrialityPacket (E := E) B s n N A) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A =
        B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (n : ℤ)) A ∧
      ((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase (n : ℤ) ∧
      Complex.exp (((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) ∧
      subtreeEntropy n = minimalSurfaceArea n / (4 * effectiveNewtonConstant) := by
  exact forward_time_equals_positive_winding_readout (B := B) P

/--
Semantic capstone corollary: on the promoted physical lane, thermal time is read
by the positive-branch monodromy clock indexed by the nonnegative winding label.
-/
theorem thermal_time_is_positive_branch_monodromy_clock
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E))
    {s : TrialitySector} {n N : ℕ} {A : EndH}
    (P : ForwardTimeHolographicTrialityPacket (E := E) B s n N A) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A =
        B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (n : ℤ)) A ∧
      ((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase (n : ℤ) ∧
      Complex.exp (((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) := by
  exact ⟨
    (positive_branch_time_clock_theorem (B := B) P).1,
    (positive_branch_time_clock_theorem (B := B) P).2.1,
    (positive_branch_time_clock_theorem (B := B) P).2.2.1
  ⟩

/--
Equivalent semantic readout phrased directly as time being indexed by positive
branch winding, together with the RT law on that same index.
-/
theorem time_is_positive_branch_winding
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E))
    {s : TrialitySector} {n N : ℕ} {A : EndH}
    (P : ForwardTimeHolographicTrialityPacket (E := E) B s n N A) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A =
        B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (n : ℤ)) A ∧
      ((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase (n : ℤ) ∧
      Complex.exp (((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) ∧
      subtreeEntropy n = minimalSurfaceArea n / (4 * effectiveNewtonConstant) := by
  exact positive_branch_time_clock_theorem (B := B) P

end

end InfoGeometry.Canonical.HolographicEntanglementSymmetry
