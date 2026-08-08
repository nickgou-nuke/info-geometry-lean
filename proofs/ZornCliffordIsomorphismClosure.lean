import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import proofs.CanonicalZornCliffordRepresentation
import proofs.CanonicalZornCliffordIsomorphism
import proofs.ZornCliffordBasisMonomials

noncomputable section

namespace ZornCliffordIsomorphismClosure

open CliffordAlgebra LinearMap Finset
open CanonicalZornCliffordRepresentation
open CanonicalZornCliffordIsomorphism
open ZornCliffordBasisMonomials

def frobeniusInnerProduct (A B : Module.End ℂ DiracSpinor16) : ℂ :=
  LinearMap.trace ℂ _ (A * B)

/-- Основна структурна лема за комутация на $\Gamma_j$ със списък от базисни индекси.
Комутира със себе си (без знак) и антикомутира с всички останали (знак -1). -/
lemma basisGamma_list_prod_comm (j : Fin 8) (L : List (Fin 8)) (h_nodup : L.Nodup) :
    basisGamma j * (L.map basisGamma).prod =
      (if j ∈ L then (-1 : ℂ) ^ (L.length - 1) else (-1 : ℂ) ^ L.length) •
        ((L.map basisGamma).prod * basisGamma j) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have haL : a ∉ L := (List.nodup_cons.mp h_nodup).1
      have hLn : L.Nodup := (List.nodup_cons.mp h_nodup).2
      have ih' := ih hLn
      by_cases haj : j = a
      · subst a
        simp only [List.map_cons, List.prod_cons, List.length_cons,
          List.mem_cons, true_or, if_true]
        rw [Nat.add_sub_cancel]
        have hjL : j ∉ L := haL
        rw [if_neg hjL] at ih'
        rw [← mul_assoc, basisGamma_sq]
        rw [ih']
        rw [smul_mul_assoc]
        rw [mul_assoc (L.map basisGamma).prod, basisGamma_sq]
        rw [smul_smul]
        have hs : ((-1 : ℂ) ^ L.length) * ((-1 : ℂ) ^ L.length) = 1 := by
          rw [← pow_add]
          exact (show Even (L.length + L.length) by simp).neg_one_pow
        rw [hs, one_smul]
        exact Algebra.commutes _ _
      · have haj' : a ≠ j := Ne.symm haj
        simp only [List.map_cons, List.prod_cons, List.length_cons,
          List.mem_cons, haj, false_or]
        rw [← mul_assoc]
        rw [basisGamma_anticommute haj]
        change -((basisGamma a * basisGamma j) * (L.map basisGamma).prod) = _
        rw [mul_assoc, ih', mul_smul_comm]
        by_cases hjL : j ∈ L
        · rw [if_pos hjL, if_pos hjL]
          have hpos : 0 < L.length :=
            List.length_pos_of_ne_nil (List.ne_nil_of_mem hjL)
          rw [Nat.add_sub_cancel]
          rw [← neg_smul ((-1 : ℂ) ^ (L.length - 1))
            (basisGamma a * ((L.map basisGamma).prod * basisGamma j))]
          congr 1
          calc
            -((-1 : ℂ) ^ (L.length - 1)) =
                (-1 : ℂ) ^ ((L.length - 1) + 1) := by
                  rw [pow_succ]
                  ring
            _ = (-1 : ℂ) ^ L.length := by
                  rw [Nat.sub_add_cancel hpos]
        · rw [if_neg hjL, if_neg hjL]
          rw [← neg_smul ((-1 : ℂ) ^ L.length)
            (basisGamma a * ((L.map basisGamma).prod * basisGamma j))]
          rw [pow_succ']
          congr 1
          ring

/-- Доказателство, че за всеки непразен I съществува антикомутиращ индекс j. -/
lemma exists_anticommuting_basisGamma (I : Finset (Fin 8)) (h_nonempty : I.Nonempty) :
    ∃ j : Fin 8, basisGamma j * cliffordMonomial I = - (cliffordMonomial I * basisGamma j) := by
  rcases Nat.even_or_odd I.card with heven | hodd
  · obtain ⟨j, hjI⟩ := h_nonempty
    refine ⟨j, ?_⟩
    have hword := basisGamma_list_prod_comm j (I.sort (· ≤ ·))
      (Finset.sort_nodup I (· ≤ ·))
    have hjL : j ∈ I.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).2 hjI
    rw [if_pos hjL, Finset.length_sort] at hword
    have hcardpos : 0 < I.card := Finset.card_pos.mpr ⟨j, hjI⟩
    have hoddPred : Odd (I.card - 1) := by
      rcases heven with ⟨m, hm⟩
      use m - 1
      omega
    rw [hoddPred.neg_one_pow] at hword
    change basisGamma j * ((I.sort (· ≤ ·)).map basisGamma).prod =
      -(((I.sort (· ≤ ·)).map basisGamma).prod * basisGamma j)
    exact hword.trans
      (neg_one_smul ℂ (((I.sort (· ≤ ·)).map basisGamma).prod * basisGamma j))
  · have hout : ∃ j : Fin 8, j ∉ I := by
      by_contra h
      push_neg at h
      have h_univ : I = Finset.univ := Finset.eq_univ_of_forall h
      subst I
      norm_num at hodd
    obtain ⟨j, hjI⟩ := hout
    refine ⟨j, ?_⟩
    have hword := basisGamma_list_prod_comm j (I.sort (· ≤ ·))
      (Finset.sort_nodup I (· ≤ ·))
    have hjL : j ∉ I.sort (· ≤ ·) := by simpa using hjI
    rw [if_neg hjL, Finset.length_sort, hodd.neg_one_pow] at hword
    change basisGamma j * ((I.sort (· ≤ ·)).map basisGamma).prod =
      -(((I.sort (· ≤ ·)).map basisGamma).prod * basisGamma j)
    exact hword.trans
      (neg_one_smul ℂ (((I.sort (· ≤ ·)).map basisGamma).prod * basisGamma j))

/-- Any endomorphism anticommuting with a basis gamma has zero trace. -/
theorem trace_zero_of_basisGamma_anticommutes
    (j : Fin 8) (M : Module.End ℂ DiracSpinor16)
    (hanti : basisGamma j * M = -(M * basisGamma j)) :
    LinearMap.trace ℂ _ M = 0 := by
  have hcyc := LinearMap.trace_mul_comm ℂ (basisGamma j) (basisGamma j * M)
  rw [← mul_assoc, basisGamma_sq] at hcyc
  rw [hanti] at hcyc
  have hright : (-(M * basisGamma j)) * basisGamma j =
      -(M * (basisGamma j * basisGamma j)) := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hright, basisGamma_sq] at hcyc
  have hs : cayleySign j ≠ 0 := by
    unfold cayleySign
    split <;> norm_num
  rw [← Algebra.commutes (cayleySign j) M] at hcyc
  rw [← Algebra.smul_def] at hcyc
  have hscalar :
      cayleySign j * LinearMap.trace ℂ _ M =
        -(cayleySign j * LinearMap.trace ℂ _ M) := by
    simpa only [map_smul, map_neg] using hcyc
  have hzero : cayleySign j * LinearMap.trace ℂ _ M = 0 := by
    have htwo : (2 : ℂ) *
        (cayleySign j * LinearMap.trace ℂ _ M) = 0 := by
      let x := cayleySign j * LinearMap.trace ℂ _ M
      change (2 : ℂ) * x = 0
      calc
        (2 : ℂ) * x = x + x := two_mul x
        _ = x + (-x) := congrArg (fun y => x + y) hscalar
        _ = 0 := add_neg_cancel x
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have : LinearMap.trace ℂ _ M = 0 := (mul_eq_zero.mp hzero).resolve_left hs
  exact this

theorem cliffordMonomial_trace_zero (I : Finset (Fin 8)) (h_nonempty : I.Nonempty) :
    LinearMap.trace ℂ _ (cliffordMonomial I) = 0 := by
  rcases exists_anticommuting_basisGamma I h_nonempty with ⟨j, hanti⟩
  exact trace_zero_of_basisGamma_anticommutes j (cliffordMonomial I) hanti

end ZornCliffordIsomorphismClosure
