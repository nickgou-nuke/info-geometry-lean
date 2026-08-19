import InfoGeometry.Canonical.PrimeLeeYangBooleanIsingCoherenceBridge

/-!
# Prime Lee--Yang coherence interface

This file isolates the exact adapter between the multivariate local-fugacity
partition function and the coarse one-variable polynomial projection.

The multivariate Lee--Yang witness in `PrimePartitionPolynomials` is not, by
itself, a theorem about `partitionPolynomial`: the two readouts use different
weights.  We therefore make the missing equality an explicit hypothesis and
prove only the consequence that follows from it.  No general Lee--Yang
stability theorem is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimeLeeYangCoherence

open InfoGeometry.Canonical.PrimeHurwitzLimit
open InfoGeometry.Canonical.PrimeLeeYangFerromagnet
open InfoGeometry.Canonical.PrimeLeeYangBooleanIsingCoherenceBridge
open InfoGeometry.Canonical.PrimePartitionPolynomials

/-! ## The finite normalized readout equality -/

/--
Coherence of the uniform global fugacity with the multivariate local readout,
including the exact coupling rescaling and scalar self-energy correction.
The structure remains a reusable interface; the concrete finite witness is
constructed below from the configuration-sum identities.
-/
structure NormalizedGlobalFugacityCoherence : Prop where
  eval_eq_multi :
    ∀ {N : ℕ} (D : FinitePrimeChainData N) (lam : ℝ) (z : ℂ),
      multiPartition D (2 * lam) (fun _ : Fin N => z) =
        (Real.exp ((lam / 2 : ℝ) * ∑ i : Fin N, (D.ell i) ^ 2) : ℂ) *
          partitionFunction D lam z

/-! ## The normalization correction for the concrete owners -/

theorem prod_bool_fugacity_eq_pow_occupiedCount
    {α : Type*} (s : Finset α) (σ : α → Bool) (z : ℂ) :
    (∏ i ∈ s, (if σ i then z else 1)) =
      z ^ (∑ i ∈ s, (if σ i then 1 else 0)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      cases h : σ a with
      | false => simp [h, ih]
      | true =>
          simp only [h, ite_true, mul_one]
          rw [ih, Nat.one_add, pow_succ, mul_comm]

theorem prod_uniform_fugacity_eq_pow_occupiedCount
    {N : ℕ} (σ : SpinConfig N) (z : ℂ) :
    (∏ i : Fin N, (if σ i then z else 1)) = z ^ occupiedCount σ := by
  simpa [occupiedCount] using
    (prod_bool_fugacity_eq_pow_occupiedCount (Finset.univ : Finset (Fin N)) σ z)

@[simp]
theorem centeredBit_eq_half_spinSign (b : Bool) :
    centeredBit b = (1 / 2 : ℝ) * spinSign b := by
  cases b <;> simp [centeredBit, spinSign]

theorem centeredLogMagnetization_eq_half_sum
    (D : FinitePrimeChainData N) (σ : SpinConfig N) :
    centeredLogMagnetization D σ =
      (1 / 2 : ℝ) * ∑ i : Fin N, D.ell i * spinSign (σ i) := by
  unfold centeredLogMagnetization
  simp_rw [centeredBit_eq_half_spinSign]
  rw [Finset.mul_sum]
  congr 1
  funext i
  ring

theorem hopfieldWeight_eq_selfEnergy_mul_configurationWeight_half
    (D : FinitePrimeChainData N) (lam : ℝ) (σ : SpinConfig N) :
    hopfieldInteractionWeight D lam σ =
      Real.exp ((lam / 4 : ℝ) * ∑ i : Fin N, (D.ell i) ^ 2) *
        configurationWeight D (lam / 2) σ := by
  unfold hopfieldInteractionWeight configurationWeight
  rw [centeredLogMagnetization_eq_half_sum]
  rw [← Real.exp_add]
  congr 1
  rw [PrimeLeeYangBooleanIsingCoherenceBridge.interactionEnergy_eq_collective_square_sub_diagonal]
  simp [boolIsingSpin]
  ring

theorem partitionFunction_eq_configuration_sum
    (D : FinitePrimeChainData N) (lam : ℝ) (z : ℂ) :
    partitionFunction D lam z =
      ∑ σ : SpinConfig N,
        ((configurationWeight D lam σ : ℝ) : ℂ) * z ^ occupiedCount σ := by
  classical
  dsimp [partitionFunction, partitionPolynomial]
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- A finite Lee--Yang partition polynomial cannot vanish at a positive real
fugacity, because every configuration contribution is strictly positive. -/
theorem partitionFunction_ne_zero_of_pos
    (D : FinitePrimeChainData N) (lam : ℝ)
    {z : ℝ} (hz : 0 < z) :
    partitionFunction D lam (z : ℂ) ≠ 0 := by
  rw [partitionFunction_eq_configuration_sum]
  have hterm : ∀ σ : SpinConfig N,
      0 < configurationWeight D lam σ * z ^ occupiedCount σ := by
    intro σ
    exact mul_pos (configurationWeight_pos D lam σ) (pow_pos hz _)
  have hsum : 0 < ∑ σ : SpinConfig N,
      configurationWeight D lam σ * z ^ occupiedCount σ := by
    exact Finset.sum_pos (fun σ _ => hterm σ)
      ⟨fun _ => false, Finset.mem_univ _⟩
  intro hzero
  have hreal := congrArg Complex.re hzero
  simp at hreal
  have hpow (n : ℕ) : ((z : ℂ) ^ n).re = z ^ n := by
    calc
      ((z : ℂ) ^ n).re = ((z ^ n : ℝ) : ℂ).re := by
        rw [Complex.ofReal_pow]
      _ = z ^ n := Complex.ofReal_re _
  simp_rw [hpow] at hreal
  have hreal' :
      ∑ σ : SpinConfig N,
        configurationWeight D lam σ * z ^ occupiedCount σ = 0 := by
    exact hreal
  exact (ne_of_gt hsum) hreal'

theorem multiPartition_uniform_eq_hopfield_sum
    (D : FinitePrimeChainData N) (lam : ℝ) (z : ℂ) :
    multiPartition D lam (fun _ : Fin N => z) =
      ∑ σ : SpinConfig N,
        ((hopfieldInteractionWeight D lam σ : ℝ) : ℂ) * z ^ occupiedCount σ := by
  classical
  unfold multiPartition
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [prod_uniform_fugacity_eq_pow_occupiedCount]

theorem multiPartition_uniform_eq_normalized_partitionFunction
    (D : FinitePrimeChainData N) (lam : ℝ) (z : ℂ) :
    multiPartition D (2 * lam) (fun _ : Fin N => z) =
      (Real.exp ((lam / 2 : ℝ) * ∑ i : Fin N, (D.ell i) ^ 2) : ℂ) *
        partitionFunction D lam z := by
  rw [multiPartition_uniform_eq_hopfield_sum,
    partitionFunction_eq_configuration_sum]
  have h_scale : 2 * lam / 4 = lam / 2 := by ring
  have h_half : 2 * lam / 2 = lam := by ring
  have h_weight (σ : SpinConfig N) :
      (hopfieldInteractionWeight D (2 * lam) σ : ℂ) =
        (Real.exp ((lam / 2 : ℝ) * ∑ i : Fin N, (D.ell i) ^ 2) : ℂ) *
          (configurationWeight D lam σ : ℂ) := by
    have hw := hopfieldWeight_eq_selfEnergy_mul_configurationWeight_half D (2 * lam) σ
    rw [h_scale, h_half] at hw
    push_cast
    rw [hw]
    push_cast
    rfl
  simp_rw [h_weight, mul_assoc]
  have hsum :
      (∑ i : Fin N, lam / 2 * (D.ell i) ^ 2) =
        lam / 2 * ∑ i : Fin N, (D.ell i) ^ 2 := by
    rw [Finset.mul_sum]
  rw [← hsum]
  calc
    (∑ σ : SpinConfig N,
        (Real.exp (∑ i : Fin N, lam / 2 * (D.ell i) ^ 2) : ℂ) *
          ((configurationWeight D lam σ : ℂ) * z ^ occupiedCount σ)) =
        (Real.exp (∑ i : Fin N, lam / 2 * (D.ell i) ^ 2) : ℂ) *
          ∑ σ : SpinConfig N, (configurationWeight D lam σ : ℂ) * z ^ occupiedCount σ := by
          rw [Finset.mul_sum]

/-- The normalized multivariate partition is also nonzero at a positive real
uniform fugacity. -/
theorem multiPartition_uniform_ne_zero_of_pos
    (D : FinitePrimeChainData N) (lam : ℝ)
    {z : ℝ} (hz : 0 < z) :
    multiPartition D (2 * lam) (fun _ : Fin N => (z : ℂ)) ≠ 0 := by
  rw [multiPartition_uniform_eq_normalized_partitionFunction]
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
    (partitionFunction_ne_zero_of_pos D lam hz)

/-- Concrete coherence witness supplied by the finite configuration identities above. -/
def concreteNormalizedGlobalFugacityCoherence :
    NormalizedGlobalFugacityCoherence where
  eval_eq_multi := by
    intro N D lam z
    exact multiPartition_uniform_eq_normalized_partitionFunction D lam z

/-! ## The honest positive-coupling polynomial consequence -/

/- Circle law for the coarse polynomial, at strictly positive coupling. -/
/--
The multivariate inside/outside zero-free property implies the one-variable
circle law once the two finite readouts are coherently identified.
-/
theorem positivePolynomialWitness_of_polydisc
    (LY : LeeYangPolydiscWitness)
    (coh : NormalizedGlobalFugacityCoherence) :
    ∀ {N : ℕ} (D : FinitePrimeChainData N) {lam : ℝ},
      0 < lam →
        ∀ z : ℂ, (partitionPolynomial D lam).IsRoot z → OnUnitCircle z := by
  intro N D lam hlam z hz
  unfold OnUnitCircle
  by_contra hnot
  have hsplit : Complex.normSq z < 1 ∨ 1 < Complex.normSq z := by
    exact lt_or_gt_of_ne hnot
  have hpoly_zero : partitionFunction D lam z = 0 := by
    simpa [partitionFunction, Polynomial.IsRoot] using hz
  have hmulti_zero : multiPartition D (2 * lam) (fun _ : Fin N => z) = 0 := by
    rw [coh.eval_eq_multi D lam z, hpoly_zero, mul_zero]
  rcases hsplit with hinside | houtside
  · have hlocal : ∀ i : Fin N, InUnitDisk z := by
      intro i
      exact hinside
    exact (LY.1 D (2 * lam) (by linarith) (fun _ : Fin N => z) hlocal) hmulti_zero
  · have hlocal : ∀ i : Fin N, OutsideUnitDisk z := by
      intro i
      exact houtside
    exact (LY.2 D (2 * lam) (by linarith) (fun _ : Fin N => z) hlocal) hmulti_zero

theorem positivePolynomialWitness_of_polydisc_concrete
    (LY : LeeYangPolydiscWitness) :
    ∀ {N : ℕ} (D : FinitePrimeChainData N) {lam : ℝ},
      0 < lam →
        ∀ z : ℂ, (partitionPolynomial D lam).IsRoot z → OnUnitCircle z := by
  exact positivePolynomialWitness_of_polydisc LY concreteNormalizedGlobalFugacityCoherence

end InfoGeometry.Canonical.PrimeLeeYangCoherence
