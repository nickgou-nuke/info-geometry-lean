/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/

import InfoGeometry.Inference.FiniteGibbsInference
import InfoGeometry.Inference.FiniteRelativeEntropy
import InfoGeometry.Inference.FiniteRelativeEntropyEquality
import InfoGeometry.Inference.GibbsVariational

/-!
# Finite Gibbs thermodynamic identity

This module makes the entropy/energy/free-energy relation explicit for the
finite Gibbs inference core.  It is an algebraic finite-state identity and
does not assert a thermodynamic limit.
-/

open scoped BigOperators

namespace InfoGeometry.Inference.FiniteGibbs

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]

/-- Gibbs mean energy at a parameter and temperature. -/
noncomputable def meanEnergy
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) : ℝ :=
  ∑ i : Data, weight M θ ε i * M.energy i θ

/-- Shannon entropy of the finite Gibbs weight vector. -/
noncomputable def entropy
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) : ℝ :=
  -∑ i : Data, weight M θ ε i * Real.log (weight M θ ε i)

/-- Shannon entropy functional on an arbitrary finite trial weight vector. -/
noncomputable def entropyOf (q : Data → ℝ) : ℝ :=
  -∑ i : Data, q i * Real.log (q i)

/-- The entropy-regularized variational objective in energy-minus-entropy form. -/
theorem entropyRegularizedObjective_eq_meanEnergy_sub_temperature_mul_entropyOf
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ)
    (q : Data → ℝ) :
    entropyRegularizedObjective M θ ε q =
      (∑ i : Data, q i * M.energy i θ) - ε * entropyOf q := by
  unfold entropyRegularizedObjective entropyOf
  ring

/-- The generic entropy functional specializes to Gibbs entropy at Gibbs weights. -/
theorem entropyOf_weight_eq_entropy
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) :
    entropyOf (weight M θ ε) = entropy M θ ε := by
  rfl

/-- Relative entropy to the uniform finite state is the entropy deficit of `q`. -/
theorem finiteRelativeEntropy_to_uniform_eq_log_card_sub_entropyOf
    (q : Data → ℝ) (hq_pos : ∀ i, 0 < q i)
    (hq_sum : ∑ i : Data, q i = 1) :
    finiteRelativeEntropy q (fun _ : Data => 1 / (Fintype.card Data : ℝ)) =
      Real.log (Fintype.card Data) - entropyOf q := by
  let n : ℝ := Fintype.card Data
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  let u : Data → ℝ := fun _ => 1 / n
  have hlog : ∀ i : Data,
      Real.log (q i / u i) = Real.log (q i) + Real.log n := by
    intro i
    change Real.log (q i / (1 / n)) = Real.log (q i) + Real.log n
    rw [Real.log_div (ne_of_gt (hq_pos i)) (by dsimp [u]; positivity)]
    rw [one_div, Real.log_inv]
    ring
  have hlogz : ∑ i : Data, q i * Real.log n = Real.log n := by
    calc
      _ = (∑ i : Data, q i) * Real.log n := by
        exact (Finset.sum_mul (Finset.univ : Finset Data)
          (fun i : Data => q i) (Real.log n)).symm
      _ = Real.log n := by rw [hq_sum]; ring
  change finiteRelativeEntropy q u = Real.log n - entropyOf q
  unfold finiteRelativeEntropy entropyOf
  simp_rw [hlog, mul_add]
  rw [Finset.sum_add_distrib, hlogz]
  ring

/-- Entropy of any positive normalized finite trial distribution is bounded by volume. -/
theorem entropyOf_le_log_card
    (q : Data → ℝ) (hq_pos : ∀ i, 0 < q i)
    (hq_sum : ∑ i : Data, q i = 1) :
    entropyOf q ≤ Real.log (Fintype.card Data) := by
  let n : ℝ := Fintype.card Data
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  let u : Data → ℝ := fun _ => 1 / n
  have hu_pos : ∀ i, 0 < u i := by
    intro i
    dsimp [u]
    positivity
  have hu_sum : ∑ i : Data, u i = 1 := by
    dsimp [u]
    rw [Finset.sum_const, Finset.card_univ]
    norm_num [n]
  have hkl : 0 ≤ finiteRelativeEntropy q u :=
    finiteRelativeEntropy_nonneg q u hq_pos hu_pos hq_sum hu_sum
  rw [finiteRelativeEntropy_to_uniform_eq_log_card_sub_entropyOf q hq_pos hq_sum] at hkl
  linarith

/-- Maximum entropy among positive normalized finite trial distributions is uniformity. -/
theorem entropyOf_eq_log_card_iff_uniform
    (q : Data → ℝ) (hq_pos : ∀ i, 0 < q i)
    (hq_sum : ∑ i : Data, q i = 1) :
    entropyOf q = Real.log (Fintype.card Data) ↔
      ∀ i : Data, q i = 1 / (Fintype.card Data : ℝ) := by
  let n : ℝ := Fintype.card Data
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  let u : Data → ℝ := fun _ => 1 / n
  have hu_pos : ∀ i, 0 < u i := by
    intro i
    dsimp [u]
    positivity
  have hu_sum : ∑ i : Data, u i = 1 := by
    dsimp [u]
    rw [Finset.sum_const, Finset.card_univ]
    norm_num [n]
  constructor
  · intro h
    have hkl : finiteRelativeEntropy q u = 0 := by
      rw [finiteRelativeEntropy_to_uniform_eq_log_card_sub_entropyOf q hq_pos hq_sum]
      have hzero : Real.log n - entropyOf q = 0 := by
        rw [show Real.log n = Real.log (Fintype.card Data) by rfl, h]
        ring
      exact hzero
    have hweights := (finiteRelativeEntropy_eq_zero_iff q u hq_pos hu_pos hq_sum hu_sum).mp hkl
    intro i
    simpa [u, n] using congrFun hweights i
  · intro huniform
    have hweights : q = u := by
      funext i
      exact huniform i
    have hkl : finiteRelativeEntropy q u = 0 := by
      rw [hweights]
      simp [finiteRelativeEntropy]
    rw [finiteRelativeEntropy_to_uniform_eq_log_card_sub_entropyOf q hq_pos hq_sum] at hkl
    linarith

/-- Entropy of any positive normalized finite trial distribution is nonnegative. -/
theorem entropyOf_nonneg
    (q : Data → ℝ) (hq_pos : ∀ i, 0 < q i)
    (hq_sum : ∑ i : Data, q i = 1) :
    0 ≤ entropyOf q := by
  have hq_nonneg : ∀ i : Data, 0 ≤ q i := fun i => (hq_pos i).le
  have hq_leone : ∀ i : Data, q i ≤ 1 := by
    intro i
    have hsingle : q i ≤ ∑ j : Data, q j := by
      exact Finset.single_le_sum (fun j hj => hq_nonneg j)
        (Finset.mem_univ i)
    simpa [hq_sum] using hsingle
  unfold entropyOf
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_nonneg
  intro i hi
  have hlog := Real.log_le_sub_one_of_pos (hq_pos i)
  have hmul := mul_le_mul_of_nonneg_left hlog (hq_pos i).le
  have hquad : q i * (q i - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hq_pos i).le (sub_nonpos.mpr (hq_leone i))
  linarith

/--
Canonical finite Gibbs free energy decomposes as mean energy minus
temperature times entropy.
-/
theorem freeEnergy_eq_meanEnergy_sub_temperature_mul_entropy
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ)
    (hε : 0 < ε) :
    freeEnergy M θ ε =
      meanEnergy M θ ε - ε * entropy M θ ε := by
  have hZne : partitionFunction M θ ε ≠ 0 := partitionFunction_ne_zero M θ ε
  have hlog : ∀ i : Data,
      Real.log (weight M θ ε i) =
        -M.energy i θ / ε - Real.log (partitionFunction M θ ε) := by
    intro i
    unfold weight
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) hZne]
    rw [Real.log_exp]
  have hsum : ∑ i : Data, weight M θ ε i = 1 := weights_sum_one M θ ε
  have henergy :
      ∑ i : Data, weight M θ ε i * (-M.energy i θ / ε) =
        -(∑ i : Data, weight M θ ε i * M.energy i θ) / ε := by
    calc
      _ = ∑ i : Data, -(weight M θ ε i * M.energy i θ / ε) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = -(∑ i : Data, weight M θ ε i * M.energy i θ / ε) := by
        rw [Finset.sum_neg_distrib]
      _ = -(∑ i : Data, weight M θ ε i * M.energy i θ) / ε := by
        rw [show (∑ i : Data, weight M θ ε i * M.energy i θ / ε) =
            (∑ i : Data, weight M θ ε i * M.energy i θ) * ε⁻¹ by
          simp_rw [div_eq_mul_inv]
          exact (Finset.sum_mul (Finset.univ : Finset Data)
            (fun i : Data => weight M θ ε i * M.energy i θ) ε⁻¹).symm]
        simp [div_eq_mul_inv]
  have hlogz :
      ∑ i : Data, weight M θ ε i * Real.log (partitionFunction M θ ε) =
        Real.log (partitionFunction M θ ε) := by
    calc
      _ = (∑ i : Data, weight M θ ε i) * Real.log (partitionFunction M θ ε) := by
        exact (Finset.sum_mul (Finset.univ : Finset Data)
          (fun i : Data => weight M θ ε i)
          (Real.log (partitionFunction M θ ε))).symm
      _ = Real.log (partitionFunction M θ ε) := by rw [hsum]; ring
  unfold freeEnergy meanEnergy entropy
  simp_rw [hlog]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, henergy, hlogz]
  field_simp [ne_of_gt hε]
  ring

/-- Finite Gibbs entropy is nonnegative. -/
theorem entropy_nonneg
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) :
    0 ≤ entropy M θ ε := by
  have hsum : ∑ i : Data, weight M θ ε i = 1 := weights_sum_one M θ ε
  have hnonneg : ∀ i : Data, 0 ≤ weight M θ ε i :=
    fun i => (weight_pos M θ ε i).le
  have hleone : ∀ i : Data, weight M θ ε i ≤ 1 := by
    intro i
    have hsingle : weight M θ ε i ≤ ∑ j : Data, weight M θ ε j := by
      exact Finset.single_le_sum (fun j hj => hnonneg j) (Finset.mem_univ i)
    simpa [hsum] using hsingle
  unfold entropy
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_nonneg
  intro i hi
  have hp : 0 < weight M θ ε i := weight_pos M θ ε i
  have hlog := Real.log_le_sub_one_of_pos hp
  have hmul := mul_le_mul_of_nonneg_left hlog hp.le
  have hquad : weight M θ ε i * (weight M θ ε i - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hp.le (sub_nonpos.mpr (hleone i))
  linarith

/-- Finite Gibbs entropy is bounded by the logarithm of the state-space size. -/
theorem entropy_le_log_card
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) :
    entropy M θ ε ≤ Real.log (Fintype.card Data) := by
  let n : ℝ := Fintype.card Data
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  let u : Data → ℝ := fun _ => 1 / n
  have hu_pos : ∀ i, 0 < u i := by
    intro i
    dsimp [u]
    positivity
  have hu_sum : ∑ i : Data, u i = 1 := by
    dsimp [u]
    rw [Finset.sum_const, Finset.card_univ]
    norm_num [n]
  have hw_pos : ∀ i, 0 < weight M θ ε i := fun i => weight_pos M θ ε i
  have hw_sum : ∑ i : Data, weight M θ ε i = 1 := weights_sum_one M θ ε
  have hkl : 0 ≤ finiteRelativeEntropy (weight M θ ε) u :=
    finiteRelativeEntropy_nonneg (weight M θ ε) u hw_pos hu_pos hw_sum hu_sum
  have hlog : ∀ i : Data,
      Real.log (weight M θ ε i / u i) =
        Real.log (weight M θ ε i) + Real.log n := by
    intro i
    change Real.log (weight M θ ε i / (1 / n)) =
      Real.log (weight M θ ε i) + Real.log n
    rw [Real.log_div (ne_of_gt (hw_pos i)) (ne_of_gt (hu_pos i))]
    change Real.log (weight M θ ε i) - Real.log (1 / n) =
      Real.log (weight M θ ε i) + Real.log n
    rw [one_div, Real.log_inv]
    ring
  unfold entropy at *
  unfold finiteRelativeEntropy at hkl
  simp_rw [hlog] at hkl
  have hsumlog : ∑ i : Data, weight M θ ε i * Real.log n = Real.log n := by
    calc
      _ = (∑ i : Data, weight M θ ε i) * Real.log n := by
        exact (Finset.sum_mul (Finset.univ : Finset Data)
          (fun i : Data => weight M θ ε i) (Real.log n)).symm
      _ = Real.log n := by rw [hw_sum]; ring
  simp only [mul_add] at hkl
  rw [Finset.sum_add_distrib, hsumlog] at hkl
  linarith

/-- Relative entropy to the uniform finite state is the entropy deficit. -/
theorem finiteRelativeEntropy_to_uniform_eq_log_card_sub_entropy
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) :
    finiteRelativeEntropy (weight M θ ε)
        (fun _ : Data => 1 / (Fintype.card Data : ℝ)) =
      Real.log (Fintype.card Data) - entropy M θ ε := by
  let n : ℝ := Fintype.card Data
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  let u : Data → ℝ := fun _ => 1 / n
  have hlog : ∀ i : Data,
      Real.log (weight M θ ε i / u i) =
        Real.log (weight M θ ε i) + Real.log n := by
    intro i
    change Real.log (weight M θ ε i / (1 / n)) =
      Real.log (weight M θ ε i) + Real.log n
    rw [Real.log_div (ne_of_gt (weight_pos M θ ε i))
      (by dsimp [u]; positivity)]
    rw [one_div, Real.log_inv]
    ring
  have hsum : ∑ i : Data, weight M θ ε i = 1 := weights_sum_one M θ ε
  have hlogz : ∑ i : Data, weight M θ ε i * Real.log n = Real.log n := by
    calc
      _ = (∑ i : Data, weight M θ ε i) * Real.log n := by
        exact (Finset.sum_mul (Finset.univ : Finset Data)
          (fun i : Data => weight M θ ε i) (Real.log n)).symm
      _ = Real.log n := by rw [hsum]; ring
  change finiteRelativeEntropy (weight M θ ε) u =
    Real.log n - entropy M θ ε
  unfold finiteRelativeEntropy entropy
  simp_rw [hlog, mul_add]
  rw [Finset.sum_add_distrib, hlogz]
  ring

/-- Maximum finite Gibbs entropy occurs exactly at the uniform weight vector. -/
theorem entropy_eq_log_card_iff_uniform
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) :
    entropy M θ ε = Real.log (Fintype.card Data) ↔
      ∀ i : Data, weight M θ ε i = 1 / (Fintype.card Data : ℝ) := by
  let n : ℝ := Fintype.card Data
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  let u : Data → ℝ := fun _ => 1 / n
  have hu_pos : ∀ i, 0 < u i := by
    intro i
    dsimp [u]
    positivity
  have hu_sum : ∑ i : Data, u i = 1 := by
    dsimp [u]
    rw [Finset.sum_const, Finset.card_univ]
    norm_num [n]
  have hw_pos : ∀ i, 0 < weight M θ ε i := fun i => weight_pos M θ ε i
  have hw_sum : ∑ i : Data, weight M θ ε i = 1 := weights_sum_one M θ ε
  have hdef := finiteRelativeEntropy_to_uniform_eq_log_card_sub_entropy M θ ε
  constructor
  · intro h
    have hkl : finiteRelativeEntropy (weight M θ ε) u = 0 := by
      rw [hdef]
      have hzero : Real.log n - entropy M θ ε = 0 := by
        rw [show Real.log n = Real.log (Fintype.card Data) by rfl, h]
        ring
      exact hzero
    have hweights := (finiteRelativeEntropy_eq_zero_iff
      (weight M θ ε) u hw_pos hu_pos hw_sum hu_sum).mp hkl
    intro i
    simpa [u, n] using congrFun hweights i
  · intro huniform
    have hweights : weight M θ ε = u := by
      funext i
      exact huniform i
    have hkl : finiteRelativeEntropy (weight M θ ε) u = 0 := by
      rw [hweights]
      simp [finiteRelativeEntropy]
    rw [hdef] at hkl
    linarith

/-- Entropy volume bounds the finite Gibbs free energy from below. -/
theorem freeEnergy_ge_meanEnergy_sub_temperature_log_card
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ)
    (hε : 0 < ε) :
    meanEnergy M θ ε - ε * Real.log (Fintype.card Data) ≤
      freeEnergy M θ ε := by
  rw [freeEnergy_eq_meanEnergy_sub_temperature_mul_entropy M θ ε hε]
  have hS := entropy_le_log_card M θ ε
  have hscaled := mul_le_mul_of_nonneg_left hS hε.le
  linarith

/-- Equality in the free-energy volume bound is equivalent to uniformity. -/
theorem freeEnergy_eq_meanEnergy_sub_temperature_log_card_iff_uniform
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ)
    (hε : 0 < ε) :
    freeEnergy M θ ε =
        meanEnergy M θ ε - ε * Real.log (Fintype.card Data) ↔
      ∀ i : Data, weight M θ ε i = 1 / (Fintype.card Data : ℝ) := by
  rw [freeEnergy_eq_meanEnergy_sub_temperature_mul_entropy M θ ε hε]
  constructor
  · intro h
    apply (entropy_eq_log_card_iff_uniform M θ ε).mp
    nlinarith
  · intro h
    have hS := (entropy_eq_log_card_iff_uniform M θ ε).mpr h
    rw [hS]


end InfoGeometry.Inference.FiniteGibbs
