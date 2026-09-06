def cuntzSdag (n : ℕ) (i : Fin n) : CuntzAlg n := cuntzMk n (Sdag n i)

/-- The Cuntz--Toeplitz quotient satisfies `Sᵢ† Sⱼ = δᵢⱼ`. -/
theorem toeplitz_orthogonality (n : ℕ) (i j : Fin n) :
    toeplitzSdag n i * toeplitzS n j = if i = j then 1 else 0 := by
  change toeplitzMk n (Sdag n i) * toeplitzMk n (S n j) = _
  rw [← map_mul]
  simpa using RingQuot.mkAlgHom_rel ℂ (CuntzToeplitzRel.orth i j)

/-- The Cuntz quotient satisfies `Sᵢ† Sⱼ = δᵢⱼ`. -/
theorem cuntz_orthogonality (n : ℕ) (i j : Fin n) :
    cuntzSdag n i * cuntzS n j = if i = j then 1 else 0 := by
  change cuntzMk n (Sdag n i) * cuntzMk n (S n j) = _
  rw [← map_mul]
  simpa using RingQuot.mkAlgHom_rel ℂ (CuntzRel.orth i j)

/-- The finite Cuntz quotient satisfies `Σᵢ Sᵢ Sᵢ† = 1`. -/
theorem cuntz_ranges_sum_one (n : ℕ) :
    (∑ i : Fin n, cuntzS n i * cuntzSdag n i) = 1 := by
  change (∑ i : Fin n, cuntzMk n (S n i) * cuntzMk n (Sdag n i)) = 1
  simp_rw [← map_mul]
  rw [← map_sum]
  simpa using RingQuot.mkAlgHom_rel ℂ (CuntzRel.ranges_sum_one (n := n))

/-- Each Cuntz generator is an algebraic isometry in the quotient. -/
theorem cuntz_isometry (n : ℕ) (i : Fin n) :
    cuntzSdag n i * cuntzS n i = 1 := by
  simpa using cuntz_orthogonality n i i

/-- Distinct Cuntz generators have orthogonal initial spaces. -/
theorem cuntz_distinct_orthogonal (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    cuntzSdag n i * cuntzS n j = 0 := by
  simpa [hij] using cuntz_orthogonality n i j

/-- The quotient construction packages exactly the finite algebraic Cuntz relations. -/
theorem finite_cuntz_tensor_quotient_packet (n : ℕ) :
    (∀ i j : Fin n, cuntzSdag n i * cuntzS n j = if i = j then 1 else 0) ∧
    (∑ i : Fin n, cuntzS n i * cuntzSdag n i) = 1 := by
  exact ⟨cuntz_orthogonality n, cuntz_ranges_sum_one n⟩

/-! ## Dagger descends through the Cuntz relations -/

theorem dagger_CuntzRel {n : ℕ} : ∀ {x y : CuntzTensor n},
    CuntzRel n x y → CuntzRel n (star x) (star y) := by
  intro x y h
  rcases h with (⟨i, j⟩ | _)
  · change CuntzRel n (dagger n (Sdag n i * S n j)) (dagger n (if i = j then 1 else 0))
    by_cases hij : i = j
    · subst j
      simpa using CuntzRel.orth (n := n) i i
    · have hji : j ≠ i := fun h => hij h.symm