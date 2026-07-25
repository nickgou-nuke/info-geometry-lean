import Mathlib.Tactic

noncomputable section

open scoped BigOperators
open Complex
open scoped ComplexConjugate
namespace PrimonSuperThermo

def primeEnergy (p : ℕ) : ℝ := Real.log (p : ℝ)
def modeWeight (β : ℝ) (p : ℕ) : ℝ := Real.exp (-(β * primeEnergy p))
def superLocalFactor (β : ℝ) (p : ℕ) : ℝ := 1 - modeWeight β p
def bosonLocalFactor (β : ℝ) (p : ℕ) : ℝ := (superLocalFactor β p)⁻¹

def superPartition (β : ℝ) (S : Finset ℕ) : ℝ := S.prod (fun p => superLocalFactor β p)
def bosonPartition (β : ℝ) (S : Finset ℕ) : ℝ := S.prod (fun p => bosonLocalFactor β p)
def superModeEnergy (β : ℝ) (p : ℕ) : ℝ := (primeEnergy p) * modeWeight β p / superLocalFactor β p
def bosonModeEnergy (β : ℝ) (p : ℕ) : ℝ := - superModeEnergy β p

def superInternalEnergy (β : ℝ) (S : Finset ℕ) : ℝ := S.sum (fun p => superModeEnergy β p)
def bosonInternalEnergy (β : ℝ) (S : Finset ℕ) : ℝ := S.sum (fun p => bosonModeEnergy β p)
def superFreeEnergy (β : ℝ) (S : Finset ℕ) : ℝ := -(1 / β) * Real.log (superPartition β S)
def bosonFreeEnergy (β : ℝ) (S : Finset ℕ) : ℝ := -(1 / β) * Real.log (bosonPartition β S)
def superEntropy (β : ℝ) (S : Finset ℕ) : ℝ := β * (superInternalEnergy β S - superFreeEnergy β S)
def bosonEntropy (β : ℝ) (S : Finset ℕ) : ℝ := β * (bosonInternalEnergy β S - bosonFreeEnergy β S)

def hasPositiveModes (S : Finset ℕ) (β : ℝ) : Prop := (0 < β) ∧ (∀ p ∈ S, 1 < p)

/--
Microscopic single-mode reading:
`superLocalFactor β p = 1 - p^{-β}` is the supertrace over the two states
`|0⟩` (grade `+1`, energy `0`) and `|p⟩` (grade `-1`, energy `log p`).
-/
lemma super_partition_singleton (β : ℝ) (p : ℕ) :
    superPartition β ({p}) = superLocalFactor β p := by
  simp [superPartition]

lemma boson_partition_singleton (β : ℝ) (p : ℕ) :
    bosonPartition β ({p}) = bosonLocalFactor β p := by
  simp [bosonPartition]

lemma super_internal_singleton (β : ℝ) (p : ℕ) :
    superInternalEnergy β ({p}) = superModeEnergy β p := by
  simp [superInternalEnergy]

lemma boson_internal_singleton (β : ℝ) (p : ℕ) :
    bosonInternalEnergy β ({p}) = bosonModeEnergy β p := by
  simp [bosonInternalEnergy]

lemma super_free_singleton (β : ℝ) (p : ℕ) :
    superFreeEnergy β ({p}) = -(1 / β) * Real.log (superLocalFactor β p) := by
  simp [superFreeEnergy, superPartition]

lemma boson_free_singleton (β : ℝ) (p : ℕ) :
    bosonFreeEnergy β ({p}) = -(1 / β) * Real.log (bosonLocalFactor β p) := by
  simp [bosonFreeEnergy, bosonPartition]

lemma super_entropy_singleton (β : ℝ) (p : ℕ) :
    superEntropy β ({p}) = β * (superModeEnergy β p + (1 / β) * Real.log (superLocalFactor β p)) := by
  simp [superEntropy, superInternalEnergy, superFreeEnergy, superPartition]

lemma boson_entropy_singleton (β : ℝ) (p : ℕ) :
    bosonEntropy β ({p}) = β * (bosonModeEnergy β p + (1 / β) * Real.log (bosonLocalFactor β p)) := by
  simp [bosonEntropy, bosonInternalEnergy, bosonFreeEnergy, bosonPartition]

lemma localfactor_pos (β : ℝ) (p : ℕ) (hβ : 0 < β) (hp : 1 < p) :
    0 < superLocalFactor β p := by
  have hlogp : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (show (1 : ℝ) < p by exact_mod_cast hp)
  have hlt : Real.exp (-(β * Real.log (p : ℝ))) < 1 := by
    have hmul : 0 < β * Real.log (p : ℝ) := mul_pos hβ hlogp
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hxp : modeWeight β p = Real.exp (-(β * Real.log (p : ℝ))) := by rfl
  unfold superLocalFactor
  rw [hxp]
  exact sub_pos.mpr hlt

lemma localfactor_nonzero (β : ℝ) (p : ℕ) (hβ : 0 < β) (hp : 1 < p) :
    superLocalFactor β p ≠ 0 := ne_of_gt (localfactor_pos β p hβ hp)

lemma bosonPartition_eq_inv_superPartition (β : ℝ) (S : Finset ℕ) :
    bosonPartition β S = (superPartition β S)⁻¹ := by
  unfold bosonPartition bosonLocalFactor superPartition
  exact Finset.prod_inv_distrib (fun p => superLocalFactor β p) (s := S)

lemma log_super_eq_sum (β : ℝ) (S : Finset ℕ) (h : hasPositiveModes S β) :
    Real.log (superPartition β S) = S.sum (fun p => Real.log (superLocalFactor β p)) := by
  unfold superPartition
  exact Real.log_prod (fun p hp => localfactor_nonzero β p h.1 (h.2 p hp))

lemma log_boson_eq_neg_log_super (β : ℝ) (S : Finset ℕ) :
    Real.log (bosonPartition β S) = -Real.log (superPartition β S) := by
  rw [bosonPartition_eq_inv_superPartition β S]
  rw [Real.log_inv]

lemma freeEnergy_neg_bosonic (β : ℝ) (S : Finset ℕ) :
    superFreeEnergy β S = -bosonFreeEnergy β S := by
  simp [superFreeEnergy, bosonFreeEnergy, log_boson_eq_neg_log_super β S]

lemma internalEnergy_neg_bosonic (β : ℝ) (S : Finset ℕ) :
    superInternalEnergy β S = -bosonInternalEnergy β S := by
  simp [superInternalEnergy, bosonInternalEnergy, bosonModeEnergy, Finset.sum_neg_distrib]

lemma entropy_neg_bosonic (β : ℝ) (S : Finset ℕ) :
    superEntropy β S = -bosonEntropy β S := by
  rw [superEntropy, bosonEntropy, internalEnergy_neg_bosonic β S, freeEnergy_neg_bosonic β S]
  ring

/-- For fixed prime mode `p>1`, `log(1-p^{-β}) → 0` as `β → +∞`. -/
lemma local_superlog_term_tendsto_zero_atTop (p : ℕ) (hp : 1 < p) :
    Filter.Tendsto (fun β : ℝ => Real.log (superLocalFactor β p)) Filter.atTop (nhds 0) := by
  have hlogp : (1 : ℝ) < p := by exact_mod_cast hp
  have hmul : Filter.Tendsto (fun β : ℝ => β * Real.log (p : ℝ)) Filter.atTop Filter.atTop := by
    have hconst : Filter.Tendsto (fun _ : ℝ => Real.log (p : ℝ)) Filter.atTop (nhds (Real.log (p : ℝ))) :=
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => Real.log (p : ℝ)) Filter.atTop (nhds (Real.log (p : ℝ))))
    simpa [mul_comm] using (Filter.Tendsto.atTop_mul_pos (Real.log_pos hlogp) Filter.tendsto_id hconst)
  have hExp : Filter.Tendsto (fun β : ℝ => Real.exp (-(β * Real.log (p : ℝ)))) Filter.atTop (nhds 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul)
  have hinner :
      Filter.Tendsto (fun β : ℝ => 1 - Real.exp (-(β * Real.log (p : ℝ)))) Filter.atTop (nhds (1 : ℝ)) := by
    simpa using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds (1 : ℝ))).sub hExp)
  have hcont : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log (by norm_num)
  have hlog : Filter.Tendsto (fun β : ℝ => Real.log (1 - Real.exp (-(β * Real.log (p : ℝ)))) )
      Filter.atTop (nhds (Real.log (1 : ℝ))) := hcont.tendsto.comp hinner
  simpa [superLocalFactor, modeWeight, primeEnergy] using hlog

lemma local_supermode_internal_tendsto_zero_atTop (p : ℕ) (hp : 1 < p) :
    Filter.Tendsto (fun β : ℝ => superModeEnergy β p) Filter.atTop (nhds 0) := by
  have hlogp : (1 : ℝ) < p := by exact_mod_cast hp
  have hmul : Filter.Tendsto (fun β : ℝ => β * Real.log (p : ℝ)) Filter.atTop Filter.atTop := by
    have hconst : Filter.Tendsto (fun _ : ℝ => Real.log (p : ℝ)) Filter.atTop (nhds (Real.log (p : ℝ))) :=
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => Real.log (p : ℝ)) Filter.atTop (nhds (Real.log (p : ℝ))))
    simpa [mul_comm] using (Filter.Tendsto.atTop_mul_pos (Real.log_pos hlogp) Filter.tendsto_id hconst)
  have hExp : Filter.Tendsto (fun β : ℝ => Real.exp (-(β * Real.log (p : ℝ)))) Filter.atTop (nhds 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul)
  have hnum :
      Filter.Tendsto (fun β : ℝ => (primeEnergy p) * Real.exp (-(β * Real.log (p : ℝ))))
      Filter.atTop (nhds (primeEnergy p * (0 : ℝ))) :=
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => primeEnergy p) Filter.atTop (nhds (primeEnergy p))).mul hExp
  have hden :
      Filter.Tendsto (fun β : ℝ => 1 - Real.exp (-(β * Real.log (p : ℝ)))) Filter.atTop (nhds (1 : ℝ)) := by
    simpa using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds (1 : ℝ))).sub hExp)
  have hdiv : Filter.Tendsto
      (fun β : ℝ => (primeEnergy p) * Real.exp (-(β * Real.log (p : ℝ))) /
        (1 - Real.exp (-(β * Real.log (p : ℝ)))) )
      Filter.atTop (nhds ((primeEnergy p * 0) / 1)) :=
    Filter.Tendsto.div hnum hden (by norm_num)
  simpa [superModeEnergy, superLocalFactor, modeWeight, primeEnergy] using hdiv

lemma superLog_tendsto_zero_atTop (S : Finset ℕ) (hS : ∀ p ∈ S, 1 < p) :
    Filter.Tendsto (fun β : ℝ => Real.log (superPartition β S)) Filter.atTop (nhds 0) := by
  have hlocal :
      ∀ p ∈ S, Filter.Tendsto (fun β : ℝ => Real.log (superLocalFactor β p)) Filter.atTop (nhds 0) :=
    by
      intro p hp
      exact local_superlog_term_tendsto_zero_atTop p (hS p hp)
  have hsum : Filter.Tendsto
      (fun β : ℝ => S.sum (fun p => Real.log (superLocalFactor β p))) Filter.atTop (nhds 0) := by
    simpa using (tendsto_finset_sum S (fun p hp => hlocal p hp))
  have hEq :
      (fun β : ℝ => S.sum (fun p => Real.log (superLocalFactor β p)) ) =ᶠ[Filter.atTop]
        (fun β : ℝ => Real.log (superPartition β S)) := by
    filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ)] with β hβ
    have hβm : hasPositiveModes S β := ⟨hβ, hS⟩
    exact (log_super_eq_sum β S hβm).symm
  exact Filter.Tendsto.congr' hEq hsum

lemma superInternalEnergy_tendsto_zero_atTop (S : Finset ℕ) (hS : ∀ p ∈ S, 1 < p) :
    Filter.Tendsto (fun β : ℝ => superInternalEnergy β S) Filter.atTop (nhds 0) := by
  have hlocal : ∀ p ∈ S, Filter.Tendsto (fun β : ℝ => superModeEnergy β p) Filter.atTop (nhds 0) := by
    intro p hp
    exact local_supermode_internal_tendsto_zero_atTop p (hS p hp)
  simpa [superInternalEnergy] using (tendsto_finset_sum S hlocal)

lemma superFreeEnergy_tendsto_zero_atTop (S : Finset ℕ) (hS : ∀ p ∈ S, 1 < p) :
    Filter.Tendsto (fun β : ℝ => superFreeEnergy β S) Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun β : ℝ => Real.log (superPartition β S)) Filter.atTop (nhds 0) :=
    superLog_tendsto_zero_atTop S hS
  have hinv : Filter.Tendsto (fun β : ℝ => 1 / β) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero : Filter.Tendsto (fun β : ℝ => β⁻¹) Filter.atTop (nhds (0 : ℝ)))
  have hmul : Filter.Tendsto
      (fun β : ℝ => (1 / β) * Real.log (superPartition β S)) Filter.atTop (nhds 0) := by
    simpa using (Filter.Tendsto.mul hinv hlog)
  simpa [superFreeEnergy] using Filter.Tendsto.neg hmul

/-- Dictionary for the finite cutoff model: bosonic and graded sector thermodynamics are opposite signed. -/
theorem primon_super_thermo_finite_dictionary :
    (∀ β S, bosonPartition β S = (superPartition β S)⁻¹) ∧
    (∀ β S, superFreeEnergy β S = -bosonFreeEnergy β S) ∧
    (∀ β S, superInternalEnergy β S = -bosonInternalEnergy β S) ∧
    (∀ β S, superEntropy β S = -bosonEntropy β S) := by
  constructor
  · intro β S
    exact bosonPartition_eq_inv_superPartition β S
  constructor
  · intro β S
    exact freeEnergy_neg_bosonic β S
  constructor
  · intro β S
    exact internalEnergy_neg_bosonic β S
  · intro β S
    exact entropy_neg_bosonic β S

/-- Finite-cutoff localization of the global `PrimonZetaMobius` dictionary. -/
theorem finite_cutoff_zeta_mobius_local_duality (β : ℝ) (S : Finset ℕ) (hβ : 0 < β)
    (hS : ∀ p ∈ S, 1 < p) :
    bosonPartition β S * superPartition β S = 1 := by
  rw [bosonPartition_eq_inv_superPartition β S]
  have hne : (superPartition β S) ≠ 0 := by
    rw [superPartition]
    exact (Finset.prod_ne_zero_iff).2 (fun p hp => ne_of_gt (localfactor_pos β p hβ (hS p hp)))
  exact inv_mul_cancel₀ hne

/-- Finite Möbius/boolean parity expansion:
    `∏_{p∈S}(1 - p^{-β}) =
      Σ_{T⊆S} (-1)^{|T|} ∏_{p∈T} p^{-β}`,
    i.e. the finite cutoff Dirichlet truncation of `1/ζ`.
-/
theorem finite_cutoff_mobius_expansion (β : ℝ) (S : Finset ℕ) :
    superPartition β S =
      ∑ t ∈ S.powerset, ((-1 : ℝ) ^ t.card) * ∏ p ∈ t, modeWeight β p := by
  unfold superPartition
  simpa [superLocalFactor] using (Finset.prod_sub (fun _ => (1 : ℝ)) (modeWeight β) S)

/-- Geometric language linkage:
A local finite graded index is the reciprocal of the local bosonic factor,
so local vanishing of `bosonPartition β S` marks the corresponding finite geometric
singularity in the style of `GeometricZeta.geometricReciprocalSingularity`.
-/
theorem finite_local_index_as_geometric_reciprocal (β : ℝ) (S : Finset ℕ) :
    (superPartition β S)⁻¹ = bosonPartition β S := by
  exact (bosonPartition_eq_inv_superPartition β S).symm

/-- CPT action on spectral parameter: thermal reflection `s ↦ 1-s` and time reversal `s ↦ s̄`. -/
def thermalReflection (s : ℂ) : ℂ := 1 - s

def timeReversal (s : ℂ) : ℂ := conj s

def cptSpectralMap (s : ℂ) : ℂ := thermalReflection (timeReversal s)

lemma cptSpectralMap_on_axis (β t : ℝ) :
    cptSpectralMap (β + (t : ℂ) * I) = (1 - β) + (t : ℂ) * I := by
  have hconj : conj (β + (t : ℂ) * I) = (β : ℂ) - (t : ℂ) * I := by
    refine (Complex.ext_iff).2 ?_
    constructor <;> simp
  calc
    cptSpectralMap (β + (t : ℂ) * I)
        = 1 - conj (β + (t : ℂ) * I) := by
            simp [cptSpectralMap, thermalReflection, timeReversal]
    _ = 1 - ((β : ℂ) - (t : ℂ) * I) := by rw [hconj]
    _ = (1 - β) + (t : ℂ) * I := by ring

lemma cptSpectralMap_involutive (s : ℂ) :
    cptSpectralMap (cptSpectralMap s) = s := by
  simp [cptSpectralMap, thermalReflection, timeReversal, sub_eq_add_neg, add_comm, add_left_comm]

/-- CPT-graded total observables in finite-prime cutoff: physical × CPT-conjugate.
They vanish as net thermodynamic anomaly:
`F_total = 0`, `U_total = 0`, `S_total = 0`, and `Z_total = 1` (with non-singular finite cutoff).
-/
def totalCPTPartition (β : ℝ) (S : Finset ℕ) : ℝ := bosonPartition β S * superPartition β S

def totalCPTFreeEnergy (β : ℝ) (S : Finset ℕ) : ℝ := bosonFreeEnergy β S + superFreeEnergy β S

def totalCPTInternalEnergy (β : ℝ) (S : Finset ℕ) : ℝ := bosonInternalEnergy β S + superInternalEnergy β S

def totalCPTEntropy (β : ℝ) (S : Finset ℕ) : ℝ := bosonEntropy β S + superEntropy β S

theorem totalCPTPartition_is_one (β : ℝ) (S : Finset ℕ) (hβ : 0 < β) (hS : ∀ p ∈ S, 1 < p) :
    totalCPTPartition β S = 1 := by
  rw [totalCPTPartition]
  exact finite_cutoff_zeta_mobius_local_duality β S hβ hS

theorem totalCPTFreeEnergy_zero (β : ℝ) (S : Finset ℕ) :
    totalCPTFreeEnergy β S = 0 := by
  rw [totalCPTFreeEnergy, freeEnergy_neg_bosonic β S]
  ring

theorem totalCPTInternalEnergy_zero (β : ℝ) (S : Finset ℕ) :
    totalCPTInternalEnergy β S = 0 := by
  rw [totalCPTInternalEnergy, internalEnergy_neg_bosonic β S]
  ring

theorem totalCPTEntropy_zero (β : ℝ) (S : Finset ℕ) :
    totalCPTEntropy β S = 0 := by
  calc
    totalCPTEntropy β S = bosonEntropy β S + superEntropy β S := rfl
    _ = bosonEntropy β S + -bosonEntropy β S := by rw [entropy_neg_bosonic β S]
    _ = 0 := by abel

end PrimonSuperThermo
