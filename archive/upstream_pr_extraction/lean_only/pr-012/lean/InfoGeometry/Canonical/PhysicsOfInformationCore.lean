import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Meta.Architecture

open scoped BigOperators

/-!
# InfoGeometry.Canonical.PhysicsOfInformationCore

Canonical owner surface for the next representation-lineage corpus:

1. routing simplex / permutation-mode data,
2. weighted split-Clifford semantic presentation,
3. spectral-inference compatibility hooks.

This module records the first formal targets:

- total-mass invariant preservation across routing and Clifford presentations;
- an explicit bridge object between permutation and Clifford modes;
- preservation readouts for mode entropy and parity entropy across the bridge.
-/

namespace InfoGeometry.Canonical.PhysicsOfInformationCore

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.SpectralInference

section Core

variable {n : Nat}

/-- Permutation routing mode alias inherited from the MoE owner. -/
abbrev RoutingMode (n : Nat) := PermutationMode n

/-- Split-Clifford routing label alias inherited from the MoE owner. -/
abbrev RoutingLabel := CliffordLabel

/-- Raw permutation-mode presentation for routing data. -/
structure PermutationPresentation (n : Nat) where
  weights : RoutingMode n → ℝ
  labels : RoutingMode n → RoutingLabel

/--
Split-Clifford presentation of the same routing data.

This structure is the first bridge object between permutation-mode coordinates
and split-Clifford semantic coordinates.
-/
structure CliffordPresentation (n : Nat) where
  weights : RoutingMode n → ℝ
  labels : RoutingMode n → RoutingLabel
  semanticState : ℝ × ℝ
  h_semanticState :
    semanticState = permutationCliffordSemanticState weights labels

/-- Total routing mass in the permutation presentation. -/
noncomputable def permutationTotalMass (P : PermutationPresentation n) : ℝ :=
  ∑ σ : RoutingMode n, P.weights σ

/-- Canonical split-Clifford state induced by permutation data. -/
noncomputable def canonicalCliffordState (P : PermutationPresentation n) : ℝ × ℝ :=
  permutationCliffordSemanticState P.weights P.labels

/-- Canonical bridge map from permutation data to split-Clifford data. -/
noncomputable def toCliffordPresentation (P : PermutationPresentation n) :
    CliffordPresentation n :=
  { weights := P.weights
    labels := P.labels
    semanticState := canonicalCliffordState P
    h_semanticState := rfl }

/-- Total routing mass viewed from the Clifford presentation side. -/
noncomputable def cliffordTotalMass (C : CliffordPresentation n) : ℝ :=
  ∑ σ : RoutingMode n, C.weights σ

/-- Mode-entropy readout on permutation presentation. -/
noncomputable def permutationModeEntropy (P : PermutationPresentation n) : ℝ :=
  modeWeightEntropy P.weights

/-- Parity-entropy readout on permutation presentation. -/
noncomputable def permutationParityEntropy (P : PermutationPresentation n) : ℝ :=
  parityEntropy P.weights P.labels

/-- Mode-entropy readout on Clifford presentation. -/
noncomputable def cliffordModeEntropy (C : CliffordPresentation n) : ℝ :=
  modeWeightEntropy C.weights

/-- Parity-entropy readout on Clifford presentation. -/
noncomputable def cliffordParityEntropy (C : CliffordPresentation n) : ℝ :=
  parityEntropy C.weights C.labels

/--
Target 1 (mass/invariant bridge):
the weighted split-Clifford coordinates preserve the same total routing mass.
-/
theorem routingClifford_totalMass_invariant (P : PermutationPresentation n) :
    (canonicalCliffordState P).1 + (canonicalCliffordState P).2
      = permutationTotalMass P := by
  simpa [canonicalCliffordState, permutationTotalMass, RoutingMode] using
    (cliffordSemanticState_coord_sum_eq_weight_sum P.weights P.labels)

/--
Unit-mass specialization of the routing/Clifford invariant law.
-/
theorem routingClifford_totalMass_invariant_unit
    (P : PermutationPresentation n)
    (hMass : permutationTotalMass P = 1) :
    (canonicalCliffordState P).1 + (canonicalCliffordState P).2 = 1 := by
  rw [routingClifford_totalMass_invariant (P := P), hMass]

/--
Target 2 (change-of-basis bridge):
the canonical bridge from permutation to Clifford presentation preserves total mass.
-/
theorem bridge_totalMass_preserved (P : PermutationPresentation n) :
    cliffordTotalMass (toCliffordPresentation P) = permutationTotalMass P := by
  rfl

/--
Target 3 (entropy preservation):
mode entropy is unchanged by the permutation-to-Clifford bridge.
-/
theorem bridge_modeEntropy_preserved (P : PermutationPresentation n) :
    cliffordModeEntropy (toCliffordPresentation P) = permutationModeEntropy P := by
  rfl

/--
Target 3 (parity preservation):
parity entropy is unchanged by the permutation-to-Clifford bridge.
-/
theorem bridge_parityEntropy_preserved (P : PermutationPresentation n) :
    cliffordParityEntropy (toCliffordPresentation P) = permutationParityEntropy P := by
  rfl

/--
Semantic-state transport law for the canonical bridge object.
-/
theorem bridge_semanticState_eq_canonical
    (P : PermutationPresentation n) :
    (toCliffordPresentation P).semanticState = canonicalCliffordState P := by
  rfl

/--
Coordinate-sum mass law on the bridged Clifford presentation.
-/
theorem bridge_semanticState_coord_sum_eq_totalMass
    (P : PermutationPresentation n) :
    (toCliffordPresentation P).semanticState.1
      + (toCliffordPresentation P).semanticState.2
      = cliffordTotalMass (toCliffordPresentation P) := by
  simpa [toCliffordPresentation, canonicalCliffordState, cliffordTotalMass, RoutingMode] using
    (cliffordSemanticState_coord_sum_eq_weight_sum P.weights P.labels)

end Core

section SpectralHooks

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Optional spectral hook surface for the corpus:
the bridge can carry an external certified chiral package without altering the
routing-side invariants.
-/
structure SpectralHookDatum where
  chiralPackage : CertifiedChiralSpectralTriple E

/-- Spectral obstruction operator exposed at the hook level. -/
noncomputable def spectralObstruction (S : SpectralHookDatum (E := E)) : E →L[ℝ] E :=
  CertifiedChiralSpectralTriple.chiralAnomalyOperator S.chiralPackage

/-- Scalar anomaly scale exposed at the hook level. -/
noncomputable def anomalyScale (S : SpectralHookDatum (E := E)) : ℝ :=
  CertifiedChiralSpectralTriple.epsilon S.chiralPackage

end SpectralHooks

end InfoGeometry.Canonical.PhysicsOfInformationCore
