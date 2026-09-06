import proofs.Clifford55PBWTraceBasis

/-! # Center and vector-anticenter of the real split Clifford algebra -/

noncomputable section
namespace Clifford55CenterAnticenter

open Clifford55
open V55Fin10Coordinates
open Clifford55PBWMonomials
open Clifford55PBWTraceBasis

def rightGamma55 (j : Fin 10) : Cl55 →ₗ[ℝ] Cl55 :=
  LinearMap.mulRight ℝ (gamma55 j)

theorem rightGamma55_injective (j : Fin 10) : Function.Injective (rightGamma55 j) := by
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change x * gamma55 j = 0 at hx
  have h : (x * gamma55 j) * gamma55 j = 0 := by
    simpa using congrArg (fun z : Cl55 => z * gamma55 j) hx
  rw [mul_assoc, gamma55_sq] at h
  rw [← Algebra.commutes (gammaSign55 j) x, ← Algebra.smul_def] at h
  exact (smul_eq_zero.mp h).resolve_left (gammaSign55_ne_zero j)

theorem rightGamma55_family_linearIndependent (j : Fin 10) :
    LinearIndependent ℝ (fun I : Finset (Fin 10) => cliffordMonomial55 I * gamma55 j) := by
  have hli := cliffordMonomials55_linearIndependent
  have hm := hli.map' (rightGamma55 j)
    (LinearMap.ker_eq_bot.mpr (rightGamma55_injective j))
  simpa [rightGamma55, Function.comp_def] using hm

/-- A commuting element has no coefficient in a PBW character on which the
chosen generator acts by `-1`. -/
theorem basisCoefficient_eq_zero_of_commutes_of_odd
    (x : Cl55) (j : Fin 10)
    (hcomm : gamma55 j * x = x * gamma55 j)
    (I : Finset (Fin 10)) (hodd : Odd (swapExponent55 j I)) :
    (cliffordMonomial55Basis.repr x) I = 0 := by
  let c : Finset (Fin 10) → ℝ := fun K => (cliffordMonomial55Basis.repr x) K
  have hx := cliffordMonomial55Basis.sum_repr x
  have heq := hcomm
  rw [← hx] at heq
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    cliffordMonomial55Basis_apply] at heq
  simp_rw [gamma55_mul_cliffordMonomial55] at heq
  have hsum :
      ∑ K : Finset (Fin 10),
        (((-1 : ℝ) ^ swapExponent55 j K - 1) * c K) •
          (cliffordMonomial55 K * gamma55 j) = 0 := by
    calc
      ∑ K : Finset (Fin 10),
          (((-1 : ℝ) ^ swapExponent55 j K - 1) * c K) •
            (cliffordMonomial55 K * gamma55 j) =
          (∑ K : Finset (Fin 10),
              c K • ((-1 : ℝ) ^ swapExponent55 j K) •
                (cliffordMonomial55 K * gamma55 j)) -
            ∑ K : Finset (Fin 10),
              c K • (cliffordMonomial55 K * gamma55 j) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro K hK
                simp [c, smul_smul]
                module
      _ = 0 := sub_eq_zero.mpr heq
  have hall := (Fintype.linearIndependent_iff.mp
    (rightGamma55_family_linearIndependent j))
      (fun K => (((-1 : ℝ) ^ swapExponent55 j K - 1) * c K)) hsum I
  rw [hodd.neg_one_pow] at hall
  norm_num at hall
  exact hall

/-- The centralizer of the vector generators consists only of scalars. -/
theorem eq_algebraMap_of_commutes_all_gamma (x : Cl55)
    (hcomm : ∀ j : Fin 10, gamma55 j * x = x * gamma55 j) :
    ∃ c : ℝ, x = algebraMap ℝ Cl55 c := by
  let c : ℝ := (cliffordMonomial55Basis.repr x) ∅
  refine ⟨c, ?_⟩
  rw [← cliffordMonomial55Basis.sum_repr x]
  classical
  rw [Finset.sum_eq_single ∅]
  · simp [c, cliffordMonomial55Basis_apply, cliffordMonomial55_empty,
      Algebra.smul_def]
  · intro I _ hI
    have hne : I ≠ ∅ := hI
    have hnall : ¬ ∀ j : Fin 10, Even (swapExponent55 j I) := by
      intro hall
      exact hne ((all_swapExponent55_even_iff I).1 hall)
    push_neg at hnall
    obtain ⟨j, hj⟩ := hnall
    have hodd : Odd (swapExponent55 j I) :=
      Nat.not_even_iff_odd.mp hj
    rw [basisCoefficient_eq_zero_of_commutes_of_odd x j (hcomm j) I hodd,
      zero_smul]
  · simp

/-- An anticommuting element has no coefficient in a PBW character on which
the chosen generator acts by `+1`. -/
theorem basisCoefficient_eq_zero_of_anticommutes_of_even
    (x : Cl55) (j : Fin 10)
    (hanti : gamma55 j * x = -(x * gamma55 j))
    (I : Finset (Fin 10)) (heven : Even (swapExponent55 j I)) :
    (cliffordMonomial55Basis.repr x) I = 0 := by
  let c : Finset (Fin 10) → ℝ := fun K => (cliffordMonomial55Basis.repr x) K
  have hx := cliffordMonomial55Basis.sum_repr x
  have heq := hanti
  rw [← hx] at heq
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    cliffordMonomial55Basis_apply] at heq
  simp_rw [gamma55_mul_cliffordMonomial55] at heq
  have hsum :
      ∑ K : Finset (Fin 10),
        (((-1 : ℝ) ^ swapExponent55 j K + 1) * c K) •
          (cliffordMonomial55 K * gamma55 j) = 0 := by
    calc
      ∑ K : Finset (Fin 10),
          (((-1 : ℝ) ^ swapExponent55 j K + 1) * c K) •
            (cliffordMonomial55 K * gamma55 j) =
          (∑ K : Finset (Fin 10),
              c K • ((-1 : ℝ) ^ swapExponent55 j K) •
                (cliffordMonomial55 K * gamma55 j)) +
            ∑ K : Finset (Fin 10),
              c K • (cliffordMonomial55 K * gamma55 j) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro K hK
                simp [c, smul_smul]
                module
      _ = 0 := add_eq_zero_iff_eq_neg.mpr heq
  have hall := (Fintype.linearIndependent_iff.mp
    (rightGamma55_family_linearIndependent j))
      (fun K => (((-1 : ℝ) ^ swapExponent55 j K + 1) * c K)) hsum I
  rw [heven.neg_one_pow] at hall
  norm_num at hall
  exact hall

/-- The vector-anticenter is the one-dimensional volume line. -/
theorem eq_smul_volume_of_anticommutes_all_gamma (x : Cl55)
    (hanti : ∀ j : Fin 10, gamma55 j * x = -(x * gamma55 j)) :
    ∃ c : ℝ, x = c • cliffordMonomial55 Finset.univ := by
  let c : ℝ := (cliffordMonomial55Basis.repr x) Finset.univ
  refine ⟨c, ?_⟩
  rw [← cliffordMonomial55Basis.sum_repr x]
  classical
  rw [Finset.sum_eq_single Finset.univ]
  · simp [c, cliffordMonomial55Basis_apply]
  · intro I _ hI
    have hne : I ≠ Finset.univ := hI
    have hnall : ¬ ∀ j : Fin 10, Odd (swapExponent55 j I) := by
      intro hall
      exact hne ((all_swapExponent55_odd_iff I).1 hall)
    push_neg at hnall
    obtain ⟨j, hj⟩ := hnall
    have heven : Even (swapExponent55 j I) :=
      Nat.not_odd_iff_even.mp hj
    rw [basisCoefficient_eq_zero_of_anticommutes_of_even x j (hanti j) I heven,
      zero_smul]
  · simp

theorem involute_cliffordMonomial55 (I : Finset (Fin 10)) :
    CliffordAlgebra.involute (cliffordMonomial55 I) =
      ((-1 : ℝ) ^ I.card) • cliffordMonomial55 I := by
  simpa [cliffordMonomial55, gamma55, Finset.length_sort, List.map_map,
    Function.comp_def] using
    (CliffordAlgebra.involute_prod_map_ι (Q := Q55)
      ((I.sort (· ≤ ·)).map fin10Basis55))

@[simp] theorem involute_volume55 :
    CliffordAlgebra.involute (cliffordMonomial55 (Finset.univ : Finset (Fin 10))) =
      cliffordMonomial55 Finset.univ := by
  rw [involute_cliffordMonomial55]
  norm_num

end Clifford55CenterAnticenter
end noncomputable section
