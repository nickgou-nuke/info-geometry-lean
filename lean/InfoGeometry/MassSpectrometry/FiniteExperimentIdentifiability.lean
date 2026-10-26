import InfoGeometry.MassSpectrometry.MultiEnergyIdentifiability
import InfoGeometry.MassSpectrometry.NumericalEvidenceBounds

/-!
# Identification from a finite experiment

Uses the existing forward model and its observational quotient. The measured
condition set and candidate class are explicit. Exact finite separation and
robust uniqueness are different results; neither asserts chemical separation
for an unspecified simulator. Strict margins, not tolerance equality, are used.
-/

noncomputable section
namespace InfoGeometry.MassSpectrometry
namespace MultiEnergyForwardModel

variable {M Energy Observation : Type*}

/-- Restrict an existing forward model to exactly the sampled conditions. -/
def restrictConditions (F : MultiEnergyForwardModel M Energy Observation)
    (S : Finset Energy) : MultiEnergyForwardModel M S Observation where
  observe e a := F.observe e.val a

theorem restrict_observationallyEquivalent_iff
    (F : MultiEnergyForwardModel M Energy Observation) (S : Finset Energy) (a b : M) :
    (F.restrictConditions S).ObservationallyEquivalent a b ↔
      ∀ e ∈ S, F.observe e a = F.observe e b := by
  constructor
  · intro h e he
    exact h ⟨e, he⟩
  · intro h e
    exact h e.val e.property

/-- Adding measured conditions can only refine observational equivalence. -/
theorem restricted_equivalence_mono
    (F : MultiEnergyForwardModel M Energy Observation) {S T : Finset Energy}
    (hST : S ⊆ T) {a b : M}
    (h : (F.restrictConditions T).ObservationallyEquivalent a b) :
    (F.restrictConditions S).ObservationallyEquivalent a b := by
  intro e
  exact h ⟨e.val, hST e.property⟩

/-- The native quotient criterion is reused on the sampled carrier. -/
theorem restricted_quotient_identifiability
    (F : MultiEnergyForwardModel M Energy Observation) (S : Finset Energy)
    (chemical : Setoid M)
    (hinvariant : ∀ a b, chemical.r a b →
      (F.restrictConditions S).signature a = (F.restrictConditions S).signature b) :
    (F.restrictConditions S).IdentifiableUpTo chemical ↔
      Function.Injective
        ((F.restrictConditions S).chemicalSignature chemical hinvariant) :=
  (F.restrictConditions S).identifiableUpTo_iff_chemicalSignature_injective
    chemical hinvariant

/-- For a finite candidate type, global separation has a finite witness set.
This is an existence theorem using choice, not an experiment optimizer. -/
theorem exists_finite_identifying_experiment [Fintype M]
    (F : MultiEnergyForwardModel M Energy Observation) (chemical : Setoid M)
    (h : F.IdentifiableUpTo chemical) :
    ∃ S : Finset Energy, (F.restrictConditions S).IdentifiableUpTo chemical := by
  classical
  have hsep : ∀ a b, ¬ chemical.r a b → ∃ e, F.observe e a ≠ F.observe e b := by
    intro a b hab
    by_contra hn
    push_neg at hn
    exact hab (h a b hn)
  let Bad := {p : M × M // ¬ chemical.r p.1 p.2}
  let chooseEnergy : Bad → Energy := fun p => Classical.choose (hsep p.val.1 p.val.2 p.property)
  have chosen : ∀ p : Bad, F.observe (chooseEnergy p) p.val.1 ≠
      F.observe (chooseEnergy p) p.val.2 :=
    fun p => Classical.choose_spec (hsep p.val.1 p.val.2 p.property)
  let S : Finset Energy := Finset.univ.image chooseEnergy
  refine ⟨S, ?_⟩
  intro a b hab
  by_contra hne
  let p : Bad := ⟨(a, b), hne⟩
  have he : chooseEnergy p ∈ S := Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
  exact chosen p (hab ⟨chooseEnergy p, he⟩)

section Metric
variable [PseudoMetricSpace Observation]

/-- Each sampled observation is within ε of the chosen candidate prediction. -/
def FitsOn (F : MultiEnergyForwardModel M Energy Observation)
    (S : Finset Energy) (observed : Energy → Observation) (ε : ℝ) (a : M) : Prop :=
  ∀ e ∈ S, dist (observed e) (F.observe e a) ≤ ε

/-- Every chemically distinct candidate pair is separated by one measured
condition by more than twice the declared total error budget. -/
def RobustlySeparatesOn (F : MultiEnergyForwardModel M Energy Observation)
    (chemical : Setoid M) (candidates : Set M) (S : Finset Energy) (ε : ℝ) : Prop :=
  ∀ a ∈ candidates, ∀ b ∈ candidates, ¬ chemical.r a b →
    ∃ e ∈ S, 2 * ε < dist (F.observe e a) (F.observe e b)

/-- Two simultaneously fitting candidates must be chemically equivalent. -/
theorem robust_identification
    (F : MultiEnergyForwardModel M Energy Observation)
    (chemical : Setoid M) (candidates : Set M) (S : Finset Energy) (ε : ℝ)
    (hsep : F.RobustlySeparatesOn chemical candidates S ε)
    (observed : Energy → Observation) {a b : M}
    (ha : a ∈ candidates) (hb : b ∈ candidates)
    (hfitA : F.FitsOn S observed ε a) (hfitB : F.FitsOn S observed ε b) :
    chemical.r a b := by
  by_contra hne
  obtain ⟨e, he, hfar⟩ := hsep a ha b hb hne
  have hA : dist (F.observe e a) (observed e) ≤ ε := by
    simpa only [dist_comm] using hfitA e he
  have hB := hfitB e he
  have htri := dist_triangle (F.observe e a) (observed e) (F.observe e b)
  linarith

/-- The result is one quotient class, not necessarily one labelled graph. -/
theorem robust_observable_class_unique
    (F : MultiEnergyForwardModel M Energy Observation)
    (chemical : Setoid M) (candidates : Set M) (S : Finset Energy) (ε : ℝ)
    (hsep : F.RobustlySeparatesOn chemical candidates S ε)
    (observed : Energy → Observation) {a b : M}
    (ha : a ∈ candidates) (hb : b ∈ candidates)
    (hfitA : F.FitsOn S observed ε a) (hfitB : F.FitsOn S observed ε b) :
    (Quotient.mk chemical a : Quotient chemical) = Quotient.mk chemical b :=
  Quotient.sound (F.robust_identification chemical candidates S ε hsep observed ha hb hfitA hfitB)

/-- Additional conditions preserve a separation margin. -/
theorem robust_separation_mono
    (F : MultiEnergyForwardModel M Energy Observation)
    (chemical : Setoid M) (candidates : Set M) {S T : Finset Energy} {ε : ℝ}
    (hST : S ⊆ T) (h : F.RobustlySeparatesOn chemical candidates S ε) :
    F.RobustlySeparatesOn chemical candidates T ε := by
  intro a ha b hb hne
  obtain ⟨e, he, hfar⟩ := h a ha b hb hne
  exact ⟨e, hST he, hfar⟩

/-- A quantitative margin also gives exact identifiability on that same
sampled set, assuming ε is nonnegative. -/
theorem exact_identifiability_of_robust
    (F : MultiEnergyForwardModel M Energy Observation)
    (chemical : Setoid M) (S : Finset Energy) {ε : ℝ} (hε : 0 ≤ ε)
    (h : F.RobustlySeparatesOn chemical Set.univ S ε) :
    (F.restrictConditions S).IdentifiableUpTo chemical := by
  intro a b heq
  by_contra hne
  obtain ⟨e, he, hfar⟩ := h a (Set.mem_univ _) b (Set.mem_univ _) hne
  have hab : F.observe e a = F.observe e b := heq ⟨e, he⟩
  rw [hab, dist_self] at hfar
  linarith

/-- A certified simulation deviation increases the fit radius explicitly. -/
theorem fitsOn_transfer
    (F G : MultiEnergyForwardModel M Energy Observation)
    (S : Finset Energy) (observed : Energy → Observation) {ε δ : ℝ} {a : M}
    (hfit : G.FitsOn S observed ε a)
    (hmodel : ∀ e ∈ S, dist (G.observe e a) (F.observe e a) ≤ δ) :
    F.FitsOn S observed (ε + δ) a := by
  intro e he
  exact (dist_triangle _ _ _).trans (add_le_add (hfit e he) (hmodel e he))

/-- Candidate fitting may use an approximate simulator, but the robust margin
must include its certified error. -/
theorem robust_identification_with_model_error
    (F G : MultiEnergyForwardModel M Energy Observation)
    (chemical : Setoid M) (candidates : Set M) (S : Finset Energy)
    (ε δ : ℝ)
    (hsep : F.RobustlySeparatesOn chemical candidates S (ε + δ))
    (hmodel : ∀ a ∈ candidates, ∀ e ∈ S,
      dist (G.observe e a) (F.observe e a) ≤ δ)
    (observed : Energy → Observation) {a b : M}
    (ha : a ∈ candidates) (hb : b ∈ candidates)
    (hfitA : G.FitsOn S observed ε a) (hfitB : G.FitsOn S observed ε b) :
    chemical.r a b :=
  F.robust_identification chemical candidates S (ε + δ) hsep observed ha hb
    (F.fitsOn_transfer G S observed hfitA (hmodel a ha))
    (F.fitsOn_transfer G S observed hfitB (hmodel b hb))

/-- The numerical refinement contract feeds the robust candidate theorem directly. -/
theorem robust_identification_of_uniform_refinement
    (F G : MultiEnergyForwardModel M Energy Observation)
    (B : NumericalEvidence.UniformErrorBound
      (fun p : Energy × M => F.observe p.1 p.2)
      (fun p : Energy × M => G.observe p.1 p.2))
    (chemical : Setoid M) (candidates : Set M) (S : Finset Energy) (ε : ℝ)
    (hsep : F.RobustlySeparatesOn chemical candidates S (ε + (B.error : ℝ)))
    (observed : Energy → Observation) {a b : M}
    (ha : a ∈ candidates) (hb : b ∈ candidates)
    (hfitA : G.FitsOn S observed ε a) (hfitB : G.FitsOn S observed ε b) :
    chemical.r a b := by
  apply F.robust_identification_with_model_error G chemical candidates S ε
    (B.error : ℝ) hsep (fun a _ e _ => B.bound (e, a)) observed ha hb hfitA hfitB

end Metric
end MultiEnergyForwardModel
end InfoGeometry.MassSpectrometry
