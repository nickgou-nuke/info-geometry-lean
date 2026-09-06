import InfoGeometry.Clifford.Cl55WittReflectionAlignment

namespace InfoGeometry.Clifford.Clifford55

/-!
# The orthogonal anisotropic Witt basis for `Q55`

The basis is kept indexed by `Fin 5 ⊕ Fin 5`, so the two isotropic Witt
halves remain visible instead of being folded into a second carrier.
-/

abbrev WittIndex := Fin 5 ⊕ Fin 5

def wittBasis : WittIndex → V55
  | Sum.inl i => e_pos i
  | Sum.inr i => f_neg i

@[simp] theorem wittBasis_left (i : Fin 5) :
    wittBasis (Sum.inl i) = e_pos i := rfl

@[simp] theorem wittBasis_right (i : Fin 5) :
    wittBasis (Sum.inr i) = f_neg i := rfl

theorem fin5_delta_pair_sum
    (i j : Fin 5) (hij : i ≠ j) :
    ∑ k : Fin 5,
        ((if k = i then (1 : ℝ) else 0) +
          if k = j then 1 else 0) ^ 2 = 2 := by
  have hcross :
      ∑ k : Fin 5,
          (if k = i then (1 : ℝ) else 0) *
            (if k = j then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hki : k = i
    · subst k
      simp [hij]
    · simp [hki]
  calc
    ∑ k : Fin 5,
        ((if k = i then (1 : ℝ) else 0) +
          if k = j then 1 else 0) ^ 2 =
        ∑ k : Fin 5,
          ((if k = i then (1 : ℝ) else 0) ^ 2 +
            (if k = j then (1 : ℝ) else 0) ^ 2 +
            2 * (if k = i then (1 : ℝ) else 0) *
              (if k = j then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (∑ k : Fin 5, (if k = i then (1 : ℝ) else 0) ^ 2) +
          (∑ k : Fin 5, (if k = j then (1 : ℝ) else 0) ^ 2) +
          2 * ∑ k : Fin 5,
            (if k = i then (1 : ℝ) else 0) *
              (if k = j then 1 else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      simp only [mul_assoc]
    _ = 2 := by
      have hji : j ≠ i := Ne.symm hij
      rw [hcross]
      norm_num [hji]

theorem wittBasis_Q_ne_zero (i : WittIndex) :
    Q55 (wittBasis i) ≠ 0 := by
  cases i with
  | inl i => rw [wittBasis_left, Q55_e_pos i]; norm_num
  | inr i => rw [wittBasis_right, Q55_f_neg i]; norm_num

theorem wittBasis_pairwise_orthogonal
    {i j : WittIndex} (hij : i ≠ j) :
    QuadraticMap.polar (⇑Q55) (wittBasis i) (wittBasis j) = 0 := by
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have h : i ≠ j := by
            intro h'
            exact hij (congrArg Sum.inl h')
          simp only [wittBasis]
          rw [QuadraticMap.polar]
          simp only [Q55_apply, e_pos, Prod.fst_add, Prod.snd_add,
            zero_add, add_zero, Pi.add_apply, Pi.zero_apply]
          rw [fin5_delta_pair_sum i j h]
          norm_num
      | inr j =>
          exact (e_pos_ortho_f_neg i j).polar_eq_zero
  | inr i =>
      cases j with
      | inl j =>
          exact (e_pos_ortho_f_neg j i).symm.polar_eq_zero
      | inr j =>
          have h : i ≠ j := by
            intro h'
            exact hij (congrArg Sum.inr h')
          simp only [wittBasis]
          rw [QuadraticMap.polar]
          simp only [Q55_apply, f_neg, Prod.fst_add, Prod.snd_add,
            zero_add, add_zero, Pi.add_apply, Pi.zero_apply]
          rw [fin5_delta_pair_sum i j h]
          norm_num

theorem wittBasis_span_eq_top :
    Submodule.span ℝ (Set.range wittBasis) = ⊤ := by
  apply top_unique
  rintro ⟨x, y⟩ -
  have hx : (x, (0 : Fin 5 → ℝ)) =
      ∑ i : Fin 5, x i • wittBasis (Sum.inl i) := by
    apply Prod.ext
    · funext j
      change x j =
        (LinearMap.fst ℝ (Fin 5 → ℝ) (Fin 5 → ℝ)
          (∑ i : Fin 5, x i • wittBasis (Sum.inl i))) j
      rw [map_sum]
      simp [wittBasis, e_pos]
    · change (0 : Fin 5 → ℝ) =
        LinearMap.snd ℝ (Fin 5 → ℝ) (Fin 5 → ℝ)
          (∑ i : Fin 5, x i • wittBasis (Sum.inl i))
      rw [map_sum]
      simp [wittBasis, e_pos]
  have hy : ((0 : Fin 5 → ℝ), y) =
      ∑ i : Fin 5, y i • wittBasis (Sum.inr i) := by
    apply Prod.ext
    · change (0 : Fin 5 → ℝ) =
        LinearMap.fst ℝ (Fin 5 → ℝ) (Fin 5 → ℝ)
          (∑ i : Fin 5, y i • wittBasis (Sum.inr i))
      rw [map_sum]
      simp [wittBasis, f_neg]
    · funext j
      change y j =
        (LinearMap.snd ℝ (Fin 5 → ℝ) (Fin 5 → ℝ)
          (∑ i : Fin 5, y i • wittBasis (Sum.inr i))) j
      rw [map_sum]
      simp [wittBasis, f_neg]
  have hx_mem : (x, (0 : Fin 5 → ℝ)) ∈
      Submodule.span ℝ (Set.range wittBasis) := by
    rw [hx]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self (Sum.inl i)))
  have hy_mem : ((0 : Fin 5 → ℝ), y) ∈
      Submodule.span ℝ (Set.range wittBasis) := by
    rw [hy]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self (Sum.inr i)))
  rw [show (x, y) = (x, (0 : Fin 5 → ℝ)) + ((0 : Fin 5 → ℝ), y) by
    ext j <;> simp]
  exact Submodule.add_mem _ hx_mem hy_mem

end InfoGeometry.Clifford.Clifford55
