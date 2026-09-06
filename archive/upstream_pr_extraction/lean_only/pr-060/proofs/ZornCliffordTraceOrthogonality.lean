import proofs.ZornCliffordPBWFinrank

/-!
# Trace orthogonality of the canonical Clifford monomials

This module separates distinct ordered gamma words by their finite parity
characters and derives vanishing of their mixed trace pairing.
-/

noncomputable section

namespace ZornCliffordTraceOrthogonality

open CanonicalZornCliffordRepresentation
open ZornCliffordBasisMonomials
open ZornCliffordIsomorphismClosure

/-- Number of sign-changing crossings when `basisGamma j` passes through the
ordered word indexed by `I`. -/
def swapExponent (j : Fin 8) (I : Finset (Fin 8)) : ℕ :=
  I.card - if j ∈ I then 1 else 0

theorem basisGamma_mul_cliffordMonomial (j : Fin 8) (I : Finset (Fin 8)) :
    basisGamma j * cliffordMonomial I =
      ((-1 : ℂ) ^ swapExponent j I) •
        (cliffordMonomial I * basisGamma j) := by
  by_cases hjI : j ∈ I
  · simpa [cliffordMonomial, swapExponent, hjI] using
      basisGamma_list_prod_comm j (I.sort (· ≤ ·))
        (Finset.sort_nodup I (· ≤ ·))
  · simpa [cliffordMonomial, swapExponent, hjI] using
      basisGamma_list_prod_comm j (I.sort (· ≤ ·))
        (Finset.sort_nodup I (· ≤ ·))

/-- A crossing exponent is odd exactly when membership agrees with evenness
of the word length. -/
theorem odd_swapExponent_iff (j : Fin 8) (I : Finset (Fin 8)) :
    Odd (swapExponent j I) ↔
      (j ∈ I ∧ Even I.card) ∨ (j ∉ I ∧ Odd I.card) := by
  by_cases hj : j ∈ I
  · simp only [swapExponent, hj, if_true]
    simp only [true_and, not_true_eq_false, false_and]
    rcases Nat.even_or_odd I.card with he | ho
    · constructor
      · intro _
        exact Or.inl he
      · intro _
        rcases he with ⟨m, hm⟩
        have hp : 0 < I.card := Finset.card_pos.mpr ⟨j, hj⟩
        use m - 1
        omega
    · constructor
      · intro h
        rcases h with ⟨m, hm⟩
        rcases ho with ⟨n, hn⟩
        omega
      · intro h
        rcases h with he | hfalse
        · exact False.elim (Nat.not_even_iff_odd.mpr ho he)
        · exact False.elim hfalse
  · simp [swapExponent, hj]

/-- Complementation in the even eight-element universe preserves cardinal
parity. -/
private theorem even_card_compl_iff (I : Finset (Fin 8)) :
    Even Iᶜ.card ↔ Even I.card := by
  have hcard : Iᶜ.card = 8 - I.card := by
    simpa using Finset.card_compl I
  have hle : I.card ≤ 8 := by
    simpa using Finset.card_le_univ I
  rw [hcard]
  constructor
  · rintro ⟨m, hm⟩
    use 4 - m
    omega
  · rintro ⟨m, hm⟩
    use 4 - m
    omega

/-- The eight parity characters distinguish all subsets. -/
theorem exists_swapExponent_opposite_parity :
    ∀ I J : Finset (Fin 8), I ≠ J →
      ∃ j : Fin 8,
        (Even (swapExponent j I) ∧ Odd (swapExponent j J)) ∨
        (Odd (swapExponent j I) ∧ Even (swapExponent j J)) := by
  intro I J hIJ
  by_contra hsep
  push_neg at hsep
  have hodd (j : Fin 8) :
      Odd (swapExponent j I) ↔ Odd (swapExponent j J) := by
    rcases Nat.even_or_odd (swapExponent j I) with hIe | hIo <;>
      rcases Nat.even_or_odd (swapExponent j J) with hJe | hJo
    · exact ⟨fun h => False.elim (Nat.not_even_iff_odd.mpr h hIe),
        fun h => False.elim (Nat.not_even_iff_odd.mpr h hJe)⟩
    · exact False.elim ((hsep j).1 hIe hJo)
    · exact False.elim ((hsep j).2 hIo hJe)
    · exact ⟨fun _ => hJo, fun _ => hIo⟩
  rcases Nat.even_or_odd I.card with hIe | hIo <;>
    rcases Nat.even_or_odd J.card with hJe | hJo
  · apply hIJ
    ext j
    have := hodd j
    have hnIo : ¬ Odd I.card := Nat.not_odd_iff_even.mpr hIe
    have hnJo : ¬ Odd J.card := Nat.not_odd_iff_even.mpr hJe
    simp [odd_swapExponent_iff, hIe, hJe, hnIo, hnJo] at this
    exact this
  · have hcomp : J = Iᶜ := by
      ext j
      have := hodd j
      have hnIo : ¬ Odd I.card := Nat.not_odd_iff_even.mpr hIe
      have hnJe : ¬ Even J.card := Nat.not_even_iff_odd.mpr hJo
      simp [odd_swapExponent_iff, hIe, hJo, hnIo, hnJe] at this ⊢
      tauto
    have : Even J.card := by rw [hcomp, even_card_compl_iff]; exact hIe
    exact False.elim (Nat.not_even_iff_odd.mpr hJo this)
  · have hcomp : I = Jᶜ := by
      ext j
      have := hodd j
      have hnIe : ¬ Even I.card := Nat.not_even_iff_odd.mpr hIo
      have hnJo : ¬ Odd J.card := Nat.not_odd_iff_even.mpr hJe
      simp [odd_swapExponent_iff, hIo, hJe, hnIe, hnJo] at this ⊢
      tauto
    have : Even I.card := by rw [hcomp, even_card_compl_iff]; exact hJe
    exact False.elim (Nat.not_even_iff_odd.mpr hIo this)
  · apply hIJ
    ext j
    have := hodd j
    have hnIe : ¬ Even I.card := Nat.not_even_iff_odd.mpr hIo
    have hnJe : ¬ Even J.card := Nat.not_even_iff_odd.mpr hJo
    simp [odd_swapExponent_iff, hIo, hJo, hnIe, hnJe] at this
    tauto

/-- Distinct monomials have a product which anticommutes with at least one
basis gamma. -/
theorem exists_basisGamma_anticommutes_monomial_mul
    (I J : Finset (Fin 8)) (hIJ : I ≠ J) :
    ∃ j : Fin 8,
      basisGamma j * (cliffordMonomial I * cliffordMonomial J) =
        -((cliffordMonomial I * cliffordMonomial J) * basisGamma j) := by
  obtain ⟨j, hpar | hpar⟩ := exists_swapExponent_opposite_parity I J hIJ
  · refine ⟨j, ?_⟩
    have hI := basisGamma_mul_cliffordMonomial j I
    have hJ := basisGamma_mul_cliffordMonomial j J
    rw [hpar.1.neg_one_pow, one_smul] at hI
    rw [hpar.2.neg_one_pow] at hJ
    have hJneg : basisGamma j * cliffordMonomial J =
        -(cliffordMonomial J * basisGamma j) :=
      hJ.trans (neg_one_smul ℂ (cliffordMonomial J * basisGamma j))
    calc
      basisGamma j * (cliffordMonomial I * cliffordMonomial J) =
          (basisGamma j * cliffordMonomial I) * cliffordMonomial J := by
            rw [mul_assoc]
      _ = (cliffordMonomial I * basisGamma j) * cliffordMonomial J := by rw [hI]
      _ = cliffordMonomial I * (basisGamma j * cliffordMonomial J) := by
            rw [mul_assoc]
      _ = cliffordMonomial I * (-(cliffordMonomial J * basisGamma j)) := by rw [hJneg]
      _ = -(cliffordMonomial I * (cliffordMonomial J * basisGamma j)) := by
            apply LinearMap.ext
            intro x
            change cliffordMonomial I ((-(cliffordMonomial J * basisGamma j)) x) =
              -(cliffordMonomial I ((cliffordMonomial J * basisGamma j) x))
            rw [LinearMap.neg_apply, map_neg]
      _ = -((cliffordMonomial I * cliffordMonomial J) * basisGamma j) :=
            congrArg Neg.neg (mul_assoc _ _ _).symm
  · refine ⟨j, ?_⟩
    have hI := basisGamma_mul_cliffordMonomial j I
    have hJ := basisGamma_mul_cliffordMonomial j J
    rw [hpar.1.neg_one_pow] at hI
    rw [hpar.2.neg_one_pow, one_smul] at hJ
    have hIneg : basisGamma j * cliffordMonomial I =
        -(cliffordMonomial I * basisGamma j) :=
      hI.trans (neg_one_smul ℂ (cliffordMonomial I * basisGamma j))
    calc
      basisGamma j * (cliffordMonomial I * cliffordMonomial J) =
          (basisGamma j * cliffordMonomial I) * cliffordMonomial J := by
            rw [mul_assoc]
      _ = (-(cliffordMonomial I * basisGamma j)) * cliffordMonomial J := by rw [hIneg]
      _ = -(cliffordMonomial I * (basisGamma j * cliffordMonomial J)) := by
            apply LinearMap.ext
            intro x
            rfl
      _ = -(cliffordMonomial I * (cliffordMonomial J * basisGamma j)) := by rw [hJ]
      _ = -((cliffordMonomial I * cliffordMonomial J) * basisGamma j) := by
            rw [mul_assoc]

/-- Mixed trace pairing of two distinct Clifford monomials vanishes. -/
theorem cliffordMonomial_trace_orthogonality
    (I J : Finset (Fin 8)) (hIJ : I ≠ J) :
    LinearMap.trace ℂ _ (cliffordMonomial I * cliffordMonomial J) = 0 := by
  obtain ⟨j, hanti⟩ := exists_basisGamma_anticommutes_monomial_mul I J hIJ
  exact trace_zero_of_basisGamma_anticommutes j _ hanti

end ZornCliffordTraceOrthogonality

end noncomputable section
