import InfoGeometry.MassSpectrometry.FragmentationResponseStability
import InfoGeometry.MassSpectrometry.FiniteExperimentIdentifiability

/-!
# From finite fragmentation responses to robust experimental identification

The kernels and their ranked DAGs may vary with both condition and candidate.
Uniform rank-horizon, kernel-error and reward-amplitude bounds construct the
existing numerical certificate. The robust-identification theorem then reuses
that certificate directly. The readout is a finite response vector, not an
implicitly calibrated instrument spectrum or a statistical confidence level.
-/

noncomputable section
namespace InfoGeometry.MassSpectrometry.FragmentationResponseEvidence
open scoped Matrix Matrix.Norms.Operator
open InfoGeometry.Algebra.RankedMatrixPowers

variable {Candidate Condition : Type*} {n : ℕ}

/-- A specified family of transient responses on the existing forward-model carrier. -/
def responseModel (D : Condition × Candidate → FragmentationDAG n)
    (G : ∀ x, StochasticGrammar (D x)) (reward : Condition × Candidate → Fin n → ℝ) :
    MultiEnergyForwardModel Candidate Condition (Fin n → ℝ) where
  observe e c := (G (e, c)).fundamentalMatrix *ᵥ reward (e, c)

/-- Quantitative model error derived from transition error, rather than assumed
as an unexplained simulator bound. Both models retain exact strict support. -/
def responseModelError
    (D E : Condition × Candidate → FragmentationDAG n)
    (G : ∀ x, StochasticGrammar (D x)) (H : ∀ x, StochasticGrammar (E x))
    (reward : Condition × Candidate → Fin n → ℝ)
    (N M : ℕ) (δ C : NNReal)
    (hN : ∀ x, rankHorizon (D x).rank ≤ N)
    (hM : ∀ x, rankHorizon (E x).rank ≤ M)
    (hδ : ∀ x, ‖(G x).transientMatrix - (H x).transientMatrix‖ ≤ (δ : ℝ))
    (hC : ∀ x, ‖reward x‖ ≤ (C : ℝ)) :
    NumericalEvidence.UniformErrorBound
      (fun x : Condition × Candidate => (responseModel D G reward).observe x.1 x.2)
      (fun x : Condition × Candidate => (responseModel E H reward).observe x.1 x.2) where
  error := (N : NNReal) * (M : NNReal) * δ * C
  bound x := by
    change dist ((H x).fundamentalMatrix *ᵥ reward x)
      ((G x).fundamentalMatrix *ᵥ reward x) ≤ _
    rw [dist_comm, dist_eq_norm]
    calc
      ‖(G x).fundamentalMatrix *ᵥ reward x - (H x).fundamentalMatrix *ᵥ reward x‖ ≤
          ((rankHorizon (D x).rank : ℝ) * (rankHorizon (E x).rank : ℝ) *
            ‖(G x).transientMatrix - (H x).transientMatrix‖) * ‖reward x‖ :=
        (G x).response_difference_norm_le (H x) (reward x)
      _ ≤ ((N : ℝ) * (M : ℝ) * (δ : ℝ)) * (C : ℝ) := by
        gcongr <;> first
        | exact_mod_cast hN x
        | exact_mod_cast hM x
        | exact hδ x
        | exact hC x
      _ = _ := by simp

/-- End-to-end class uniqueness using the derived accumulated-response budget. -/
theorem robust_identification_from_transition_error
    (D E : Condition × Candidate → FragmentationDAG n)
    (G : ∀ x, StochasticGrammar (D x)) (H : ∀ x, StochasticGrammar (E x))
    (reward : Condition × Candidate → Fin n → ℝ)
    (N M : ℕ) (δ C : NNReal)
    (hN : ∀ x, rankHorizon (D x).rank ≤ N)
    (hM : ∀ x, rankHorizon (E x).rank ≤ M)
    (hδ : ∀ x, ‖(G x).transientMatrix - (H x).transientMatrix‖ ≤ (δ : ℝ))
    (hC : ∀ x, ‖reward x‖ ≤ (C : ℝ))
    (chemical : Setoid Candidate) (candidates : Set Candidate) (S : Finset Condition)
    (ε : ℝ)
    (hsep : (responseModel D G reward).RobustlySeparatesOn chemical candidates S
      (ε + (N : ℝ) * (M : ℝ) * (δ : ℝ) * (C : ℝ)))
    (observed : Condition → Fin n → ℝ) {a b : Candidate}
    (ha : a ∈ candidates) (hb : b ∈ candidates)
    (hfitA : (responseModel E H reward).FitsOn S observed ε a)
    (hfitB : (responseModel E H reward).FitsOn S observed ε b) : chemical.r a b := by
  let B := responseModelError D E G H reward N M δ C hN hM hδ hC
  apply (responseModel D G reward).robust_identification_of_uniform_refinement
    (responseModel E H reward) B chemical candidates S ε
    (by simpa [B, responseModelError] using hsep) observed ha hb hfitA hfitB

end InfoGeometry.MassSpectrometry.FragmentationResponseEvidence
