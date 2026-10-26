import InfoGeometry.MassSpectrometry.ChemicalGraph
import InfoGeometry.MassSpectrometry.ExperimentalObservation
import InfoGeometry.MassSpectrometry.FiniteExperimentIdentifiability

/-!
# Candidate-indexed molecular experiments

The simulator returns the existing spectrum carrier with a per-scan size.
Chemical equivalence is supplied explicitly. A feature map is also explicit;
no claim that it is injective or chemistry-preserving is hidden in its type.
The general finite-experiment and robustness theorems are connected to these
actual molecular graphs, acquisition conditions and variable spectra.
-/

noncomputable section
namespace InfoGeometry.MassSpectrometry.MolecularExperimentEvidence
open ExperimentalObservation

abbrev AcquisitionForwardModel (atoms : ℕ) :=
  MultiEnergyForwardModel (MolecularGraph atoms) AcquisitionCondition VariableSpectrum

/-- The finite candidate index may contain repeated/isomorphic graphs. -/
def candidateModel {atoms : ℕ} {I O : Type*}
    (F : AcquisitionForwardModel atoms) (candidate : I → MolecularGraph atoms)
    (features : VariableSpectrum → O) : MultiEnergyForwardModel I AcquisitionCondition O where
  observe c i := features (F.observe c (candidate i))

/-- Pull back the chosen chemical relation, without substituting index equality. -/
def candidateSetoid {atoms : ℕ} {I : Type*}
    (chemical : Setoid (MolecularGraph atoms)) (candidate : I → MolecularGraph atoms) : Setoid I where
  r i j := chemical.r (candidate i) (candidate j)
  iseqv := ⟨fun i => chemical.iseqv.refl (candidate i),
    fun {_ _} h => chemical.iseqv.symm h, fun {_ _ _} h₁ h₂ => chemical.iseqv.trans h₁ h₂⟩

/-- Relabeling/chemical invariance must be a property of the simulator itself;
postprocessing preserves an invariance already established at spectrum level. -/
theorem candidate_features_invariant {atoms : ℕ} {I O : Type*}
    (F : AcquisitionForwardModel atoms) (candidate : I → MolecularGraph atoms)
    (features : VariableSpectrum → O) (chemical : Setoid (MolecularGraph atoms))
    (hinvariant : ∀ c G H, chemical.r G H → F.observe c G = F.observe c H)
    {i j : I} (h : (candidateSetoid chemical candidate).r i j) :
    (candidateModel F candidate features).signature i =
      (candidateModel F candidate features).signature j := by
  funext c
  exact congrArg features (hinvariant c (candidate i) (candidate j) h)

theorem finite_candidate_experiment {atoms : ℕ} {I O : Type*} [Fintype I]
    (F : AcquisitionForwardModel atoms) (candidate : I → MolecularGraph atoms)
    (features : VariableSpectrum → O) (chemical : Setoid (MolecularGraph atoms))
    (h : (candidateModel F candidate features).IdentifiableUpTo
      (candidateSetoid chemical candidate)) :
    ∃ S : Finset AcquisitionCondition,
      ((candidateModel F candidate features).restrictConditions S).IdentifiableUpTo
        (candidateSetoid chemical candidate) :=
  (candidateModel F candidate features).exists_finite_identifying_experiment
    (candidateSetoid chemical candidate) h

/-- Concrete molecular specialization of robust finite-experiment uniqueness. -/
theorem robust_molecular_identification {atoms : ℕ} {I O : Type*} [PseudoMetricSpace O]
    (F : AcquisitionForwardModel atoms) (candidate : I → MolecularGraph atoms)
    (features : VariableSpectrum → O) (chemical : Setoid (MolecularGraph atoms))
    (S : Finset AcquisitionCondition) (ε : ℝ)
    (hsep : (candidateModel F candidate features).RobustlySeparatesOn
      (candidateSetoid chemical candidate) Set.univ S ε)
    (observed : AcquisitionCondition → O) {i j : I}
    (hi : (candidateModel F candidate features).FitsOn S observed ε i)
    (hj : (candidateModel F candidate features).FitsOn S observed ε j) :
    chemical.r (candidate i) (candidate j) :=
  (candidateModel F candidate features).robust_identification
    (candidateSetoid chemical candidate) Set.univ S ε hsep observed
    (Set.mem_univ i) (Set.mem_univ j) hi hj

end InfoGeometry.MassSpectrometry.MolecularExperimentEvidence
