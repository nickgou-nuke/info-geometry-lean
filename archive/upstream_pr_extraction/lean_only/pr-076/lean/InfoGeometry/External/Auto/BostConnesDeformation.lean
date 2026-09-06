import Mathlib.Tactic

noncomputable section

open scoped BigOperators
open Complex

namespace BostConnesDeformation

/-- Arithmetic-mode ingredients, reusing the same spectral convention as the finite
prime gas thermodynamics.
-/
def primeEnergy (p : ℕ) : ℝ := Real.log (p : ℝ)
def modeWeight (β : ℝ) (p : ℕ) : ℝ := Real.exp (-(β * primeEnergy p))

/-- Fugacity of the grand-canonical deformation. -/
def chemicalFugacity (β μ : ℝ) : ℝ := Real.exp (β * μ)

/-- Chemical-potential deformed one-mode Boltzmann weight.

`μ` enters as a shift in the single-mode damping exponent:
`exp(-(β(log p - μ))) = exp(β*μ) * exp(-β log p)`.
-/
def deformedModeWeight (β μ : ℝ) (p : ℕ) : ℝ :=
  Real.exp (β * (μ - Real.log (p : ℝ)))

/-- 3D complex deformation parameter `s = β + i t` at chemical potential `μ`. -/
def deformedModeWeightComplex (β t μ : ℝ) (p : ℕ) : ℂ :=
  Complex.exp (((β : ℂ) + t * Complex.I) * ((μ : ℂ) - Real.log (p : ℝ)))

def deformedSuperLocalFactorComplex (β t μ : ℝ) (p : ℕ) : ℂ :=
  1 - deformedModeWeightComplex β t μ p

def deformedBosonLocalFactorComplex (β t μ : ℝ) (p : ℕ) : ℂ :=
  (deformedSuperLocalFactorComplex β t μ p)⁻¹

def deformedSuperPartitionComplex (β t μ : ℝ) (S : Finset ℕ) : ℂ :=
  S.prod (fun p => deformedSuperLocalFactorComplex β t μ p)

def deformedBosonPartitionComplex (β t μ : ℝ) (S : Finset ℕ) : ℂ :=
  S.prod (fun p => deformedBosonLocalFactorComplex β t μ p)

lemma deformedBosonPartitionComplex_eq_inv_superPartitionComplex (β t μ : ℝ) (S : Finset ℕ) :
    deformedBosonPartitionComplex β t μ S = (deformedSuperPartitionComplex β t μ S)⁻¹ := by
  unfold deformedBosonPartitionComplex deformedBosonLocalFactorComplex deformedSuperPartitionComplex
  exact Finset.prod_inv_distrib (fun p => deformedSuperLocalFactorComplex β t μ p) (s := S)

/-- Complex finite-cutoff duality under a non-singular `β+i t` window. -/
theorem deformed_finite_cutoff_duality_complex (β t μ : ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, deformedSuperLocalFactorComplex β t μ p ≠ 0) :
    deformedBosonPartitionComplex β t μ S * deformedSuperPartitionComplex β t μ S = 1 := by
  rw [deformedBosonPartitionComplex_eq_inv_superPartitionComplex β t μ S]
  have hne : deformedSuperPartitionComplex β t μ S ≠ 0 := by
    rw [deformedSuperPartitionComplex]
    exact Finset.prod_ne_zero_iff.2 (fun p hp => hS p hp)
  exact inv_mul_cancel₀ hne

/-- Deformed local Möbius factor (super sector). -/
def deformedSuperLocalFactor (β μ : ℝ) (p : ℕ) : ℝ :=
  1 - deformedModeWeight β μ p

def deformedBosonLocalFactor (β μ : ℝ) (p : ℕ) : ℝ :=
  (deformedSuperLocalFactor β μ p)⁻¹

def deformedSuperPartition (β μ : ℝ) (S : Finset ℕ) : ℝ :=
  S.prod (fun p => deformedSuperLocalFactor β μ p)

def deformedBosonPartition (β μ : ℝ) (S : Finset ℕ) : ℝ :=
  S.prod (fun p => deformedBosonLocalFactor β μ p)

def deformedSuperModeEnergy (β μ : ℝ) (p : ℕ) : ℝ :=
  (primeEnergy p - μ) * deformedModeWeight β μ p / deformedSuperLocalFactor β μ p

def deformedBosonModeEnergy (β μ : ℝ) (p : ℕ) : ℝ :=
  -deformedSuperModeEnergy β μ p

def deformedSuperInternalEnergy (β μ : ℝ) (S : Finset ℕ) : ℝ :=
  S.sum (fun p => deformedSuperModeEnergy β μ p)
def deformedBosonInternalEnergy (β μ : ℝ) (S : Finset ℕ) : ℝ :=
  S.sum (fun p => deformedBosonModeEnergy β μ p)

def deformedSuperFreeEnergy (β μ : ℝ) (S : Finset ℕ) : ℝ :=
  -(1 / β) * Real.log (deformedSuperPartition β μ S)
def deformedBosonFreeEnergy (β μ : ℝ) (S : Finset ℕ) : ℝ :=
  -(1 / β) * Real.log (deformedBosonPartition β μ S)
def deformedSuperEntropy (β μ : ℝ) (S : Finset ℕ) : ℝ :=
  β * (deformedSuperInternalEnergy β μ S - deformedSuperFreeEnergy β μ S)
def deformedBosonEntropy (β μ : ℝ) (S : Finset ℕ) : ℝ :=
  β * (deformedBosonInternalEnergy β μ S - deformedBosonFreeEnergy β μ S)

lemma deformedModeWeight_eq (β μ : ℝ) (p : ℕ) :
    deformedModeWeight β μ p = chemicalFugacity β μ * modeWeight β p := by
  rw [deformedModeWeight, chemicalFugacity, modeWeight, primeEnergy]
  rw [sub_eq_add_neg, mul_add, Real.exp_add]
  ring_nf

lemma deformedSuper_local_singleton (β μ : ℝ) (p : ℕ) :
    deformedSuperPartition β μ ({p}) = deformedSuperLocalFactor β μ p := by
  simp [deformedSuperPartition]

lemma deformedBoson_local_singleton (β μ : ℝ) (p : ℕ) :
    deformedBosonPartition β μ ({p}) = deformedBosonLocalFactor β μ p := by
  simp [deformedBosonPartition]

lemma deformedBosonPartition_eq_inv_superPartition (β μ : ℝ) (S : Finset ℕ) :
    deformedBosonPartition β μ S = (deformedSuperPartition β μ S)⁻¹ := by
  unfold deformedBosonPartition deformedBosonLocalFactor deformedSuperPartition
  exact Finset.prod_inv_distrib (fun p => deformedSuperLocalFactor β μ p) (s := S)

lemma deformed_internalEnergy_neg_bosonic (β μ : ℝ) (S : Finset ℕ) :
    deformedSuperInternalEnergy β μ S = -deformedBosonInternalEnergy β μ S := by
  simp [deformedSuperInternalEnergy, deformedBosonInternalEnergy, deformedBosonModeEnergy,
    Finset.sum_neg_distrib]

lemma deformed_freeEnergy_neg_bosonic (β μ : ℝ) (S : Finset ℕ) :
    deformedSuperFreeEnergy β μ S = -deformedBosonFreeEnergy β μ S := by
  rw [deformedSuperFreeEnergy, deformedBosonFreeEnergy, deformedBosonPartition_eq_inv_superPartition]
  rw [Real.log_inv]
  ring

lemma deformed_entropy_neg_bosonic (β μ : ℝ) (S : Finset ℕ) :
    deformedSuperEntropy β μ S = -deformedBosonEntropy β μ S := by
  rw [deformedSuperEntropy, deformedBosonEntropy,
    deformed_internalEnergy_neg_bosonic β μ S, deformed_freeEnergy_neg_bosonic β μ S]
  ring

/-- Algebraic dictionary for finite prime cutoff (same cancellation shape). -/
theorem deformedDictionary (β μ : ℝ) :
    (∀ S, deformedBosonPartition β μ S = (deformedSuperPartition β μ S)⁻¹) ∧
    (∀ S, deformedSuperInternalEnergy β μ S = -deformedBosonInternalEnergy β μ S) ∧
    (∀ S, deformedSuperFreeEnergy β μ S = -deformedBosonFreeEnergy β μ S) ∧
    (∀ S, deformedSuperEntropy β μ S = -deformedBosonEntropy β μ S) := by
  constructor
  · intro S
    exact deformedBosonPartition_eq_inv_superPartition β μ S
  constructor
  · intro S
    exact deformed_internalEnergy_neg_bosonic β μ S
  constructor
  · intro S
    exact deformed_freeEnergy_neg_bosonic β μ S
  · intro S
    exact deformed_entropy_neg_bosonic β μ S

/-- Finite Möbius expansion with deformed chemical weights:
`∏_{p∈S}(1 - z_β,μ(p)) = Σ_{T⊆S} (-1)^{|T|} ∏_{p∈T} z_β,μ(p)`.
-/
theorem deformed_finite_cutoff_mobius_expansion (β μ : ℝ) (S : Finset ℕ) :
    deformedSuperPartition β μ S =
      ∑ t ∈ S.powerset, ((-1 : ℝ) ^ t.card) * ∏ p ∈ t,
        deformedModeWeight β μ p := by
  unfold deformedSuperPartition
  simpa [deformedSuperLocalFactor] using
    (Finset.prod_sub (fun _ => (1 : ℝ)) (deformedModeWeight β μ) S)

lemma deformed_localfactor_pos (β μ : ℝ) (p : ℕ) (hβ : 0 < β) (hμ : μ < Real.log (p : ℝ)) :
    0 < deformedSuperLocalFactor β μ p := by
  have hexp : deformedModeWeight β μ p < 1 := by
    have hlt : β * (μ - Real.log (p : ℝ)) < 0 := by
      have hsub : μ - Real.log (p : ℝ) < 0 := sub_lt_zero.mpr hμ
      exact mul_neg_of_pos_of_neg hβ hsub
    exact (Real.exp_lt_one_iff).2 hlt
  have hnonneg : 0 < deformedModeWeight β μ p := by exact Real.exp_pos _
  have hne : deformedModeWeight β μ p ≠ 1 := ne_of_lt hexp
  rw [deformedSuperLocalFactor, sub_eq_add_neg]
  nlinarith

lemma deformed_localfactor_nonzero (β μ : ℝ) (p : ℕ) (hβ : 0 < β)
    (hμ : μ < Real.log (p : ℝ)) : deformedSuperLocalFactor β μ p ≠ 0 := by
  have hpos : 0 < deformedSuperLocalFactor β μ p := deformed_localfactor_pos β μ p hβ hμ
  exact ne_of_gt hpos

/-- Finite-partition duality identity in a non-singular β-μ window. -/
theorem deformed_finite_cutoff_duality (β μ : ℝ) (S : Finset ℕ)
    (hβ : 0 < β) (hμ : ∀ p ∈ S, μ < Real.log (p : ℝ)) :
    deformedBosonPartition β μ S * deformedSuperPartition β μ S = 1 := by
  rw [deformedBosonPartition_eq_inv_superPartition β μ S]
  have hne : (deformedSuperPartition β μ S) ≠ 0 := by
    rw [deformedSuperPartition]
    exact Finset.prod_ne_zero_iff.2 (fun p hp =>
      deformed_localfactor_nonzero β μ p hβ (hμ p hp))
  exact inv_mul_cancel₀ hne

/-- Critical-line characterization for real `β`:
for `p>1` and `β≠0`, local deformed factor vanishes iff `μ = log p`.
-/
theorem deformed_localCritical_iff (β μ : ℝ) (p : ℕ) (hβ : β ≠ 0) :
    deformedSuperLocalFactor β μ p = 0 ↔ μ = Real.log (p : ℝ) := by
  constructor
  · intro hzero
    have htmp : 1 - deformedModeWeight β μ p = 0 := by simpa [deformedSuperLocalFactor] using hzero
    have hone : deformedModeWeight β μ p = 1 := by
      have h' : 1 = deformedModeWeight β μ p := sub_eq_zero.mp htmp
      exact h'.symm
    have hexp : Real.exp (β * (μ - Real.log (p : ℝ))) = 1 := by
      simpa [deformedModeWeight] using hone
    have hexp0 : β * (μ - Real.log (p : ℝ)) = 0 := (Real.exp_eq_one_iff (β * (μ - Real.log (p : ℝ)))).1 hexp
    have hmul : μ - Real.log (p : ℝ) = 0 := (mul_eq_zero.mp hexp0).resolve_left hβ
    exact sub_eq_zero.mp hmul
  · intro hmu
    rw [hmu, deformedSuperLocalFactor, deformedModeWeight]
    simp [sub_self]


/-- Algebraic local critical equation in fugacity form. -/
def local_deformed_partition (p : ℕ) (beta z : ℝ) : ℝ :=
  1 - z * (p : ℝ) ^ (-beta)

lemma localDeformedPartition_zero_iff (p : ℝ) (beta z : ℝ) (hp : 0 < p) :
    (1 - z * p ^ (-beta) = 0 ↔ z = p ^ beta) := by
  constructor
  · intro h
    have h1 : z * p ^ (-beta) = 1 := by
      have h' : 1 = z * p ^ (-beta) := by
        simpa using (sub_eq_zero.mp h)
      linarith
    have hpow : z / p ^ beta = 1 := by
      calc
        z / p ^ beta = z * (p ^ beta)⁻¹ := by simp [div_eq_mul_inv]
        _ = z * p ^ (-beta) := by rw [Real.rpow_neg (le_of_lt hp) beta]
        _ = 1 := h1
    have hne : p ^ beta ≠ 0 := (Real.rpow_pos_of_pos hp beta).ne'
    have h' : z = 1 * p ^ beta := (div_eq_iff hne).1 hpow
    simpa using h'
  · intro hz
    rw [hz]
    rw [Real.rpow_neg (le_of_lt hp)]
    have hne : p ^ beta ≠ 0 := (Real.rpow_pos_of_pos hp beta).ne'
    have hmul : p ^ beta * (p ^ beta)⁻¹ = (1 : ℝ) := by
      exact mul_inv_cancel₀ hne
    nlinarith


theorem local_deformed_partition_zero_iff (p : ℕ) (beta z : ℝ) (hp : 0 < p) :
    local_deformed_partition p beta z = 0 ↔ z = (p : ℝ) ^ beta := by
  unfold local_deformed_partition
  exact localDeformedPartition_zero_iff (p := (p : ℝ)) beta z (by exact_mod_cast hp)

/-- `exp(β*μ)` fugacity form: critical equation is μ = log p. -/
theorem local_deformed_partition_fugacity_zero_iff_log (p : ℕ) (β μ : ℝ) (hp : 0 < p) (hβ : β ≠ 0) :
    local_deformed_partition p β (Real.exp (β * μ)) = 0 ↔ μ = Real.log (p : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  constructor
  · intro h
    have h1 : Real.exp (β * μ) = (p : ℝ) ^ β :=
      (local_deformed_partition_zero_iff p β (Real.exp (β * μ)) hp).mp h
    have h2 : Real.exp (β * μ) = Real.exp (β * Real.log (p : ℝ)) := by
      calc
        Real.exp (β * μ) = (p : ℝ) ^ β := h1
        _ = Real.exp (Real.log (p : ℝ) * β) := by
          rw [Real.rpow_def_of_pos hpR β]
        _ = Real.exp (β * Real.log (p : ℝ)) := by ring_nf
    have h3 : β * μ = β * Real.log (p : ℝ) := Real.exp_injective h2
    exact mul_left_cancel₀ hβ h3
  · intro hμ
    rw [hμ]
    exact (local_deformed_partition_zero_iff p β (Real.exp (β * Real.log (p : ℝ))) hp).2 <|
      by
        rw [Real.rpow_def_of_pos hpR β]
        ring_nf

/-- Complex CPT partition at finite cutoff. -/
def totalDeformedCPTPartitionComplex (β t μ : ℝ) (S : Finset ℕ) : ℂ :=
  deformedBosonPartitionComplex β t μ S * deformedSuperPartitionComplex β t μ S

/-- CPT-paired finite totals remain balanced for the deformed model under a
non-singular window. -/
def totalDeformedCPTPartition (β μ : ℝ) (S : Finset ℕ) : ℝ :=
  deformedBosonPartition β μ S * deformedSuperPartition β μ S

def totalDeformedCPTFreeEnergy (β μ : ℝ) (S : Finset ℕ) : ℝ :=
  deformedBosonFreeEnergy β μ S + deformedSuperFreeEnergy β μ S

def totalDeformedCPTInternalEnergy (β μ : ℝ) (S : Finset ℕ) : ℝ :=
  deformedBosonInternalEnergy β μ S + deformedSuperInternalEnergy β μ S

def totalDeformedCPTEntropy (β μ : ℝ) (S : Finset ℕ) : ℝ :=
  deformedBosonEntropy β μ S + deformedSuperEntropy β μ S

theorem totalDeformedCPTPartitionComplex_is_one (β t μ : ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, deformedSuperLocalFactorComplex β t μ p ≠ 0) :
    totalDeformedCPTPartitionComplex β t μ S = 1 := by
  rw [totalDeformedCPTPartitionComplex, deformed_finite_cutoff_duality_complex β t μ S hS]


theorem totalDeformedCPTPartition_is_one (β μ : ℝ) (S : Finset ℕ)
    (hβ : 0 < β)
    (hμ : ∀ p ∈ S, μ < Real.log (p : ℝ)) :
    totalDeformedCPTPartition β μ S = 1 := by
  rw [totalDeformedCPTPartition, deformed_finite_cutoff_duality β μ S hβ hμ]


theorem totalDeformedCPTZero (β μ : ℝ) (S : Finset ℕ) :
    totalDeformedCPTFreeEnergy β μ S = 0 := by
  rw [totalDeformedCPTFreeEnergy, deformed_freeEnergy_neg_bosonic β μ S]
  ring

theorem totalDeformedCPTZero_internal (β μ : ℝ) (S : Finset ℕ) :
    totalDeformedCPTInternalEnergy β μ S = 0 := by
  rw [totalDeformedCPTInternalEnergy, deformed_internalEnergy_neg_bosonic β μ S]
  ring

theorem totalDeformedCPTZero_entropy (β μ : ℝ) (S : Finset ℕ) :
    totalDeformedCPTEntropy β μ S = 0 := by
  rw [totalDeformedCPTEntropy, deformed_entropy_neg_bosonic β μ S]
  ring

end BostConnesDeformation
