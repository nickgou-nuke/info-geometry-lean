import InfoGeometry.Canonical.RyuTakayanagiEntanglementBridge
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
open InfoGeometry.Canonical.TrialitySpin8Permutations
open InfoGeometry.Canonical.Spin44CharacterShadow
open InfoGeometry.Quantum
open InfoGeometry.Quantum.SplitTrialityFockBridge

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
structure HolographicEntanglementTrialityPacket
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (s : TrialitySector) (n N : ℕ) : Prop where
  rt_at_sector :
    sectorSubtreeEntropy s n =
      sectorMinimalSurfaceArea s n / (4 * effectiveNewtonConstant)
  entropy_triality_invariant :
    sectorSubtreeEntropy (trialityCycle s) n = sectorSubtreeEntropy s n
  area_triality_invariant :
    sectorMinimalSurfaceArea (trialityCycle s) n = sectorMinimalSurfaceArea s n
  sector_cycle3 :
    (trialityCycle ^ 3) s = s
  supercharge_square :
    (canonicalSplitTrialityKernel (E := E)).trialitySupercharge.comp
        (canonicalSplitTrialityKernel (E := E)).trialitySupercharge =
      LinearMap.id
  even_half_spinor_card :
    (Finset.univ.filter fun ε : Fin 4 → Bool => EvenMinus ε).card = 8
  odd_half_spinor_card :
    (Finset.univ.filter fun ε : Fin 4 → Bool => OddMinus ε).card = 8
  braid_entropy_readout :
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

end InfoGeometry.Canonical.HolographicEntanglementSymmetry
