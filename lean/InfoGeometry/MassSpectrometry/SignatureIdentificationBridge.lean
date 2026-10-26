import InfoGeometry.MassSpectrometry.FragmentObservabilityGramian
import InfoGeometry.MassSpectrometry.FiniteExperimentIdentifiability

/-!
# Observational equivalence through signature Gram kernels

The linear latent encoding and readout family are supplied. Chemical equivalence
is not replaced by latent-vector equality, nor is physical separation inferred
from the mere existence of a Gram matrix or a pseudoinverse.
-/
noncomputable section
namespace InfoGeometry.MassSpectrometry.SignatureIdentification
open SignatureGeometry

variable {E F Candidate Condition : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]

def signatureModel (O : Condition → E →L[ℝ] F) (state : Candidate → E) :
    MultiEnergyForwardModel Candidate Condition F where
  observe e a := O e (state a)

def correlationModel (O : Condition → E →L[ℝ] F) (state : Candidate → E) :
    MultiEnergyForwardModel Candidate Condition E where
  observe e a := gram (O e) (state a)

/-- Exact state-side Gram kernels retain precisely the linear signature fibers. -/
theorem observational_equivalence_iff_gram_kernel
    (O : Condition → E →L[ℝ] F) (state : Candidate → E) (a b : Candidate) :
    (signatureModel O state).ObservationallyEquivalent a b ↔
      ∀ e, gram (O e) (state a-state b)=0 := by
  constructor <;> intro h e
  · exact (same_signature_iff_gram_difference (O e) (state a) (state b)).mp (h e)
  · exact (same_signature_iff_gram_difference (O e) (state a) (state b)).mpr (h e)

/-- Correlation replacement preserves the modeled equivalence, not arbitrary statistics. -/
theorem signature_correlation_same_equivalence
    (O : Condition → E →L[ℝ] F) (state : Candidate → E) (a b : Candidate) :
    (signatureModel O state).ObservationallyEquivalent a b ↔
      (correlationModel O state).ObservationallyEquivalent a b := by
  rw [observational_equivalence_iff_gram_kernel]
  change (∀ e, gram (O e) (state a-state b)=0) ↔
    (∀ e, gram (O e) (state a)=gram (O e) (state b))
  simp only [map_sub, sub_eq_zero]

/-- Transfer a supplied chemical-class separation statement in either direction. -/
theorem chemical_identifiability_iff
    (O : Condition → E →L[ℝ] F) (state : Candidate → E) (chemical : Setoid Candidate) :
    (∀ a b, (signatureModel O state).ObservationallyEquivalent a b → chemical.r a b) ↔
    (∀ a b, (correlationModel O state).ObservationallyEquivalent a b → chemical.r a b) := by
  constructor <;> intro h a b hab
  · exact h a b ((signature_correlation_same_equivalence O state a b).mpr hab)
  · exact h a b ((signature_correlation_same_equivalence O state a b).mp hab)

/-- A genuinely positive Gram lower bound supplies quantitative separation. -/
theorem gram_coercivity_signature_bound (O : E →L[ℝ] F) (κ : ℝ)
    (hκ : ∀ x, κ*‖x‖^2 ≤ inner ℝ x (gram O x)) (x y : E) :
    κ * dist x y ^ 2 ≤ dist (O x) (O y) ^ 2 := by
  have h := hκ (x-y)
  rw [gram_energy, real_inner_self_eq_norm_sq, map_sub] at h
  simpa [dist_eq_norm] using h

end InfoGeometry.MassSpectrometry.SignatureIdentification
