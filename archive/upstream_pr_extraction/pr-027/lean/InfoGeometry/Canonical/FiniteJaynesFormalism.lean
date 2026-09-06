import InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge

/-!
# InfoGeometry.Canonical.FiniteJaynesFormalism

Finite theorem-safe Jaynes formalism for the centered LDDS layer.

This module completes the finite side of the Jaynes picture around a reference
background:

* Shannon entropy of a finite observation profile;
* cross entropy against a finite reference profile;
* finite KL/relative entropy against the reference;
* the algebraic identity `cross entropy = entropy + KL` under explicit
  positivity hypotheses;
* LDDS entropy as negative relative entropy to the reference;
* finite observable expectation and Massieu/free-energy-style Jaynes dual
  readout.

No continuous entropy theorem.
No measure-theoretic LDDS limit.
No MaxEnt optimizer theorem beyond explicitly imported finite modules.
No spectral theorem, Tomita theorem, or analytic completion.
-/

namespace InfoGeometry.Canonical.FiniteJaynesFormalism

open Finset
open FiniteJaynesCenteredScoreBridge
open FiniteJaynesCenteredScoreBridge.FiniteReferenceStateOps

variable {ι : Type*} [Fintype ι]

/-- Finite Shannon entropy `-∑ pᵢ log pᵢ`. -/
noncomputable def finiteShannonEntropy (obs : FiniteProfile ι) : ℝ :=
  -∑ i : ι, obs i * Real.log (obs i)

/-- Finite cross entropy of an observation profile against a reference profile. -/
noncomputable def finiteCrossEntropy (R : FiniteReferenceState ι) (obs : FiniteProfile ι) : ℝ :=
  -∑ i : ι, obs i * Real.log (R.weight i)

/-- Finite KL/relative entropy of an observation profile against a reference profile. -/
noncomputable def finiteKLDivergence (R : FiniteReferenceState ι) (obs : FiniteProfile ι) : ℝ :=
  ∑ i : ι, obs i * Real.log (obs i / R.weight i)

/-- Jaynes LDDS entropy: Shannon entropy corrected by the finite reference density. -/
noncomputable def finiteLDDSEntropy (R : FiniteReferenceState ι) (obs : FiniteProfile ι) : ℝ :=
  -finiteKLDivergence R obs

omit [Fintype ι] in
/-- Positive observation/reference profiles give the pointwise KL decomposition. -/
theorem pointwise_kl_eq_cross_sub_entropy
    (R : FiniteReferenceState ι) (obs : FiniteProfile ι)
    {i : ι} (hobs : 0 < obs i) (href : 0 < R.weight i) :
    obs i * Real.log (obs i / R.weight i) =
      -(obs i * Real.log (R.weight i)) - (-(obs i * Real.log (obs i))) := by
  rw [Real.log_div hobs.ne' href.ne']
  ring

/-- Finite Jaynes identity: cross entropy is Shannon entropy plus KL divergence. -/
theorem finiteCrossEntropy_eq_finiteShannonEntropy_add_KL
    (R : FiniteReferenceState ι) (obs : FiniteProfile ι)
    (hobs : ∀ i : ι, 0 < obs i) (href : IsPositive R) :
    finiteCrossEntropy R obs = finiteShannonEntropy obs + finiteKLDivergence R obs := by
  unfold finiteCrossEntropy finiteShannonEntropy finiteKLDivergence IsPositive at *
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  calc
    ∑ i : ι, -(obs i * Real.log (R.weight i)) =
        ∑ i : ι, (-(obs i * Real.log (obs i)) +
          obs i * Real.log (obs i / R.weight i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Real.log_div (hobs i).ne' (href i).ne']
      ring
    _ = (∑ i : ι, -(obs i * Real.log (obs i))) +
        ∑ i : ι, obs i * Real.log (obs i / R.weight i) := by
      rw [Finset.sum_add_distrib]

/-- Equivalent finite Jaynes identity for LDDS entropy. -/
theorem finiteLDDSEntropy_eq_entropy_sub_cross_correction
    (R : FiniteReferenceState ι) (obs : FiniteProfile ι)
    (hobs : ∀ i : ι, 0 < obs i) (href : IsPositive R) :
    finiteLDDSEntropy R obs = finiteShannonEntropy obs - finiteCrossEntropy R obs := by
  have h := finiteCrossEntropy_eq_finiteShannonEntropy_add_KL R obs hobs href
  unfold finiteLDDSEntropy
  linarith

/-- Finite expectation of an observable against an observation profile. -/
def finiteExpectation (obs : FiniteProfile ι) (observable : ι → ℝ) : ℝ :=
  ∑ i : ι, obs i * observable i

/-- Finite partition function with a reference profile and observable. -/
noncomputable def finitePartition
    (R : FiniteReferenceState ι) (observable : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑ i : ι, R.weight i * Real.exp (-lam * observable i)

/-- Finite Jaynes/Massieu dual readout `log Z + lam E`. -/
noncomputable def finiteJaynesDual
    (R : FiniteReferenceState ι) (observable : ι → ℝ) (target : ℝ) (lam : ℝ) : ℝ :=
  Real.log (finitePartition R observable lam) + lam * target

/-- Finite Gibbs profile relative to a reference profile. -/
noncomputable def finiteGibbsProfile
    (R : FiniteReferenceState ι) (observable : ι → ℝ) (lam : ℝ) (i : ι) : ℝ :=
  R.weight i * Real.exp (-lam * observable i) / finitePartition R observable lam

omit [Fintype ι] in
/-- Positive reference weights give nonnegative partition summands. -/
theorem finitePartition_summand_pos
    (R : FiniteReferenceState ι) (observable : ι → ℝ) (lam : ℝ)
    (href : IsPositive R) (i : ι) :
    0 < R.weight i * Real.exp (-lam * observable i) :=
  mul_pos (href i) (Real.exp_pos _)

/-- If a finite atom is supplied, positive reference weights make the partition positive. -/
theorem finitePartition_pos_of_atom
    (R : FiniteReferenceState ι) (observable : ι → ℝ) (lam : ℝ)
    (href : IsPositive R) (i0 : ι) :
    0 < finitePartition R observable lam := by
  unfold finitePartition
  exact Finset.sum_pos' (by
    intro i hi
    exact le_of_lt (finitePartition_summand_pos R observable lam href i))
    ⟨i0, Finset.mem_univ i0, finitePartition_summand_pos R observable lam href i0⟩

/-- The Gibbs profile clears denominators to the weighted Boltzmann factor. -/
theorem finiteGibbsProfile_mul_partition
    (R : FiniteReferenceState ι) (observable : ι → ℝ) (lam : ℝ) {i : ι}
    (hZ : finitePartition R observable lam ≠ 0) :
    finiteGibbsProfile R observable lam i * finitePartition R observable lam =
      R.weight i * Real.exp (-lam * observable i) := by
  unfold finiteGibbsProfile
  field_simp [hZ]

/-- Finite Gibbs profile is positive under positive reference and positive partition. -/
theorem finiteGibbsProfile_pos
    (R : FiniteReferenceState ι) (observable : ι → ℝ) (lam : ℝ) {i : ι}
    (href : IsPositive R) (hZ : 0 < finitePartition R observable lam) :
    0 < finiteGibbsProfile R observable lam i := by
  unfold finiteGibbsProfile
  exact div_pos (finitePartition_summand_pos R observable lam href i) hZ

end InfoGeometry.Canonical.FiniteJaynesFormalism
