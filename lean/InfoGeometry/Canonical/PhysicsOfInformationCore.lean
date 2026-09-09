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
Nonnegative routing weights induce nonnegative Clifford semantic coordinates
on the canonical bridge object.
-/
theorem bridge_semanticState_nonneg_of_nonneg_weights
    (P : PermutationPresentation n)
    (hw : ∀ σ : RoutingMode n, 0 ≤ P.weights σ) :
    0 ≤ (toCliffordPresentation P).semanticState.1 ∧
      0 ≤ (toCliffordPresentation P).semanticState.2 := by
  constructor
  · simpa [toCliffordPresentation, canonicalCliffordState, permutationCliffordSemanticState,
      cliffordSemanticState_fst_eq_plusMass] using
      (plusMass_nonneg (w := P.weights) (label := P.labels) hw)
  · simpa [toCliffordPresentation, canonicalCliffordState, permutationCliffordSemanticState,
      cliffordSemanticState_snd_eq_minusMass] using
      (minusMass_nonneg (w := P.weights) (label := P.labels) hw)

/-- Under simplex routing weights, the first bridged semantic coordinate is bounded by one. -/
theorem bridge_semanticState_fst_le_one_of_simplex
    (P : PermutationPresentation n)
    (hw_nonneg : ∀ σ : RoutingMode n, 0 ≤ P.weights σ)
    (hMass : permutationTotalMass P = 1) :
    (toCliffordPresentation P).semanticState.1 ≤ 1 := by
  simpa [toCliffordPresentation, canonicalCliffordState, permutationCliffordSemanticState,
    permutationTotalMass, RoutingMode] using
    (cliffordSemanticState_fst_le_one_of_simplex (n := n) (w := P.weights)
      (label := P.labels) hw_nonneg hMass)

/-- Under simplex routing weights, the second bridged semantic coordinate is bounded by one. -/
theorem bridge_semanticState_snd_le_one_of_simplex
    (P : PermutationPresentation n)
    (hw_nonneg : ∀ σ : RoutingMode n, 0 ≤ P.weights σ)
    (hMass : permutationTotalMass P = 1) :
    (toCliffordPresentation P).semanticState.2 ≤ 1 := by
  simpa [toCliffordPresentation, canonicalCliffordState, permutationCliffordSemanticState,
    permutationTotalMass, RoutingMode] using
    (cliffordSemanticState_snd_le_one_of_simplex (n := n) (w := P.weights)
      (label := P.labels) hw_nonneg hMass)

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

section BistochasticLift

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (n : Nat) [Nonempty (Fin n)]

/--
Bistochastic routing admits a Clifford presentation whose permutation weights
and permutation-vertex decomposition are simultaneously preserved.

This is the honest bridge statement: the permutation matrices are the
extreme-point vertices of the bistochastic polytope, and the same weights can
be transported into the split-Clifford presentation.
-/
theorem exists_cliffordPresentation_of_bistochastic
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x)
    (label : RoutingMode n → RoutingLabel) :
    ∃ C : CliffordPresentation n,
      ∑ σ : RoutingMode n, C.weights σ • σ.permMatrix ℝ = switchMatrix n β x ∧
      cliffordTotalMass C = 1 ∧
      C.semanticState = permutationCliffordSemanticState C.weights C.labels := by
  rcases exists_clifford_labeled_state_of_bistochastic (n := n) β x hcol label with
    ⟨w, _hw_nonneg, hw_sum, hw_matrix, _hψ⟩
  refine ⟨{ weights := w
            labels := label
            semanticState := permutationCliffordSemanticState w label
            h_semanticState := rfl }, hw_matrix, ?_, rfl⟩
  simpa [cliffordTotalMass] using hw_sum

/--
The bistochastic Clifford bridge can be chosen with nonnegative semantic
coordinates.
-/
theorem exists_cliffordPresentation_of_bistochastic_nonneg
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x)
    (label : RoutingMode n → RoutingLabel) :
    ∃ C : CliffordPresentation n,
      ∑ σ : RoutingMode n, C.weights σ • σ.permMatrix ℝ = switchMatrix n β x ∧
      cliffordTotalMass C = 1 ∧
      C.semanticState = permutationCliffordSemanticState C.weights C.labels ∧
      0 ≤ C.semanticState.1 ∧ 0 ≤ C.semanticState.2 := by
  rcases exists_clifford_labeled_state_of_bistochastic (n := n) β x hcol label with
    ⟨w, hw_nonneg, hw_sum, hw_matrix, hψ⟩
  refine ⟨{ weights := w
            labels := label
            semanticState := permutationCliffordSemanticState w label
            h_semanticState := rfl }, hw_matrix, ?_, rfl, ?_⟩
  · simpa [cliffordTotalMass] using hw_sum
  · simpa [permutationCliffordSemanticState] using ⟨hψ.1, hψ.2.left⟩

end BistochasticLift

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
