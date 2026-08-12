import InfoGeometry.Canonical.CanonicalZornSpinChirality
import proofs.ZornCliffordBasisMonomials

/-!
# Parity API for canonical Zorn Clifford monomials

This file records the operator-level `ℤ/2ℤ` grading of the canonical gamma
words.  Even words preserve the two typed semispinor summands, while odd words
exchange them.
-/

noncomputable section

namespace ZornCliffordParityAPI

open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open CanonicalZornSpinChirality
open ZornCliffordBasisMonomials

/-- Chirality viewed as an endomorphism of the Dirac carrier. -/
def chiralityOperator : Module.End ℂ DiracSpinor16 :=
  diracChirality.toLinearMap

@[simp] theorem chiralityOperator_apply (S : SpinorPlus8) (C : SpinorMinus8) :
    chiralityOperator (S, C) = (S, -C) := rfl

theorem chiralityOperator_sq : chiralityOperator * chiralityOperator = 1 := by
  apply LinearMap.ext
  intro Ψ
  exact diracChirality_sq Ψ

/-- An endomorphism is even when it commutes with chirality. -/
def IsEvenOperator (A : Module.End ℂ DiracSpinor16) : Prop :=
  chiralityOperator * A = A * chiralityOperator

/-- An endomorphism is odd when it anticommutes with chirality. -/
def IsOddOperator (A : Module.End ℂ DiracSpinor16) : Prop :=
  chiralityOperator * A = -(A * chiralityOperator)

/-- Intrinsic block-diagonal condition relative to the typed chiral splitting. -/
def IsBlockDiagonal (A : Module.End ℂ DiracSpinor16) : Prop :=
  (∀ S : SpinorPlus8, (A (S, 0)).2 = 0) ∧
    (∀ C : SpinorMinus8, (A (0, C)).1 = 0)

/-- Intrinsic off-diagonal condition relative to the typed chiral splitting. -/
def IsOffDiagonal (A : Module.End ℂ DiracSpinor16) : Prop :=
  (∀ S : SpinorPlus8, (A (S, 0)).1 = 0) ∧
    (∀ C : SpinorMinus8, (A (0, C)).2 = 0)

/-- Every vector gamma is odd. -/
theorem diracGamma_odd (V : Vector8) : IsOddOperator (diracGamma V) := by
  apply LinearMap.ext
  intro Ψ
  exact diracChirality_gamma V Ψ

theorem basisGamma_odd (i : Fin 8) : IsOddOperator (basisGamma i) := by
  exact diracGamma_odd (sageZornBasis i)

/-- Moving chirality through a gamma word contributes its length parity. -/
private theorem chirality_mul_gammaList (L : List (Fin 8)) :
    chiralityOperator * (L.map basisGamma).prod =
      ((-1 : ℂ) ^ L.length) •
        ((L.map basisGamma).prod * chiralityOperator) := by
  induction L with
  | nil => simp
  | cons i L ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [← mul_assoc, basisGamma_odd i]
      change -((basisGamma i * chiralityOperator) *
        (L.map basisGamma).prod) = _
      rw [mul_assoc, ih]
      rw [mul_smul_comm, ← neg_one_smul ℂ, smul_smul]
      rw [pow_succ']
      congr 1

/-- Canonical monomial parity formula. -/
theorem chirality_mul_cliffordMonomial (I : Finset (Fin 8)) :
    chiralityOperator * cliffordMonomial I =
      ((-1 : ℂ) ^ I.card) •
        (cliffordMonomial I * chiralityOperator) := by
  simpa [cliffordMonomial] using chirality_mul_gammaList (I.sort (· ≤ ·))

theorem cliffordMonomial_even (I : Finset (Fin 8)) (hI : Even I.card) :
    IsEvenOperator (cliffordMonomial I) := by
  rw [IsEvenOperator, chirality_mul_cliffordMonomial, hI.neg_one_pow, one_smul]

theorem cliffordMonomial_odd (I : Finset (Fin 8)) (hI : Odd I.card) :
    IsOddOperator (cliffordMonomial I) := by
  rw [IsOddOperator, chirality_mul_cliffordMonomial, hI.neg_one_pow]
  exact neg_one_smul ℂ (cliffordMonomial I * chiralityOperator)

/-- Commutation with chirality forces preservation of the positive summand. -/
theorem evenOperator_preserves_plus {A : Module.End ℂ DiracSpinor16}
    (hA : IsEvenOperator A) (S : SpinorPlus8) :
    (A (S, 0)).2 = 0 := by
  have h := LinearMap.congr_fun hA (S, 0)
  have h2 := congrArg Prod.snd h
  have h2' : -(A (S, 0)).2 = (A (S, 0)).2 := by
    simpa [chiralityOperator] using h2
  have htwo : (2 : ℂ) • (A (S, 0)).2 = 0 := by
    simpa [two_smul] using (neg_eq_iff_add_eq_zero.mp h2')
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Commutation with chirality forces preservation of the negative summand. -/
theorem evenOperator_preserves_minus {A : Module.End ℂ DiracSpinor16}
    (hA : IsEvenOperator A) (C : SpinorMinus8) :
    (A (0, C)).1 = 0 := by
  have h := LinearMap.congr_fun hA (0, C)
  have h1 := congrArg Prod.fst h
  have hneg : A (0, -C) = -(A (0, C)) := by
    simpa using map_neg A (0, C)
  have h1' : (A (0, C)).1 = -(A (0, C)).1 := by
    change (diracChirality (A (0, C))).1 = (A (0, -C)).1 at h1
    rw [hneg] at h1
    simpa [chiralityOperator] using h1
  have htwo : (2 : ℂ) • (A (0, C)).1 = 0 := by
    simpa [two_smul] using (eq_neg_iff_add_eq_zero.mp h1')
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Anticommutation with chirality sends the positive summand to the negative one. -/
theorem oddOperator_reverses_plus {A : Module.End ℂ DiracSpinor16}
    (hA : IsOddOperator A) (S : SpinorPlus8) :
    (A (S, 0)).1 = 0 := by
  have h := LinearMap.congr_fun hA (S, 0)
  have h1 := congrArg Prod.fst h
  have h1' : (A (S, 0)).1 = -(A (S, 0)).1 := by
    simpa [chiralityOperator] using h1
  have htwo : (2 : ℂ) • (A (S, 0)).1 = 0 := by
    simpa [two_smul] using (eq_neg_iff_add_eq_zero.mp h1')
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Anticommutation with chirality sends the negative summand to the positive one. -/
theorem oddOperator_reverses_minus {A : Module.End ℂ DiracSpinor16}
    (hA : IsOddOperator A) (C : SpinorMinus8) :
    (A (0, C)).2 = 0 := by
  have h := LinearMap.congr_fun hA (0, C)
  have h2 := congrArg Prod.snd h
  have hneg : A (0, -C) = -(A (0, C)) := by
    simpa using map_neg A (0, C)
  have h2' : -(A (0, C)).2 = (A (0, C)).2 := by
    change (diracChirality (A (0, C))).2 = (-A (0, -C)).2 at h2
    rw [hneg] at h2
    simpa [chiralityOperator] using h2
  have htwo : (2 : ℂ) • (A (0, C)).2 = 0 := by
    simpa [two_smul] using (neg_eq_iff_add_eq_zero.mp h2')
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem evenOperator_blockDiagonal {A : Module.End ℂ DiracSpinor16}
    (hA : IsEvenOperator A) : IsBlockDiagonal A :=
  ⟨evenOperator_preserves_plus hA, evenOperator_preserves_minus hA⟩

theorem oddOperator_offDiagonal {A : Module.End ℂ DiracSpinor16}
    (hA : IsOddOperator A) : IsOffDiagonal A :=
  ⟨oddOperator_reverses_plus hA, oddOperator_reverses_minus hA⟩

theorem cliffordMonomial_even_preserves_chirality
    (I : Finset (Fin 8)) (hI : Even I.card) :
    (∀ S : SpinorPlus8, (cliffordMonomial I (S, 0)).2 = 0) ∧
      (∀ C : SpinorMinus8, (cliffordMonomial I (0, C)).1 = 0) := by
  exact ⟨evenOperator_preserves_plus (cliffordMonomial_even I hI),
    evenOperator_preserves_minus (cliffordMonomial_even I hI)⟩

theorem evenClifford_blockDiagonal
    (I : Finset (Fin 8)) (hI : Even I.card) :
    IsBlockDiagonal (cliffordMonomial I) :=
  evenOperator_blockDiagonal (cliffordMonomial_even I hI)

theorem cliffordMonomial_odd_reverses_chirality
    (I : Finset (Fin 8)) (hI : Odd I.card) :
    (∀ S : SpinorPlus8, (cliffordMonomial I (S, 0)).1 = 0) ∧
      (∀ C : SpinorMinus8, (cliffordMonomial I (0, C)).2 = 0) := by
  exact ⟨oddOperator_reverses_plus (cliffordMonomial_odd I hI),
    oddOperator_reverses_minus (cliffordMonomial_odd I hI)⟩

theorem oddClifford_offDiagonal
    (I : Finset (Fin 8)) (hI : Odd I.card) :
    IsOffDiagonal (cliffordMonomial I) :=
  oddOperator_offDiagonal (cliffordMonomial_odd I hI)

end ZornCliffordParityAPI

end noncomputable section
