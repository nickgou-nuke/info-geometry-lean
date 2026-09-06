import proofs.Clifford55PBWFinrank
import proofs.Q55OrthogonalGeometry

/-! # Ordered PBW monomials for the real split Clifford algebra `Cl(5,5)` -/

noncomputable section
namespace Clifford55PBWMonomials

open Clifford55
open V55Fin10Coordinates
open SplitOctonionTKK55

/-- The ten fixed orthogonal Clifford generators. -/
def gamma55 (i : Fin 10) : Cl55 := ι55 (fin10Basis55 i)

/-- Their diagonal Clifford signs. -/
def gammaSign55 (i : Fin 10) : ℝ := if i.1 < 5 then 1 else -1

theorem Q55_fin10Basis55 (i : Fin 10) :
    Q55 (fin10Basis55 i) = gammaSign55 i := by
  rw [Q55_eq_eta55]
  simp [v55Fin10Equiv, fin10Basis55.equivFun_self, eta55,
    gammaSign55, dotProduct, Matrix.mulVec]

@[simp] theorem gamma55_sq (i : Fin 10) :
    gamma55 i * gamma55 i = algebraMap ℝ Cl55 (gammaSign55 i) := by
  rw [gamma55, CliffordAlgebra.ι_sq_scalar, Q55_fin10Basis55]

theorem gammaSign55_ne_zero (i : Fin 10) : gammaSign55 i ≠ 0 := by
  unfold gammaSign55
  split_ifs <;> norm_num

theorem gamma55_anticommute {i j : Fin 10} (hij : i ≠ j) :
    gamma55 i * gamma55 j = -(gamma55 j * gamma55 i) := by
  have hortho := Q55OrthogonalGeometry.fin10Basis55_orthogonal hij
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q55)
    (fin10Basis55 i) (fin10Basis55 j)
  have hp : QuadraticMap.polar Q55 (fin10Basis55 i) (fin10Basis55 j) =
      2 • Q55OrthogonalGeometry.B55 (fin10Basis55 i) (fin10Basis55 j) := by
    have hpolar := congrArg
      (fun F : LinearMap.BilinMap ℝ V55 ℝ =>
        F (fin10Basis55 i) (fin10Basis55 j))
      (QuadraticMap.two_nsmul_associated ℝ Q55)
    exact hpolar.symm
  rw [hp, hortho, smul_zero, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Ordered native Clifford word indexed by a subset of the ten generators. -/
def cliffordMonomial55 (I : Finset (Fin 10)) : Cl55 :=
  ((I.sort (· ≤ ·)).map gamma55).prod

@[simp] theorem cliffordMonomial55_empty : cliffordMonomial55 ∅ = 1 := by
  simp [cliffordMonomial55]

/-- Number of sign-changing crossings when `gamma55 j` passes through `I`. -/
def swapExponent55 (j : Fin 10) (I : Finset (Fin 10)) : ℕ :=
  I.card - if j ∈ I then 1 else 0

lemma gamma55_list_prod_comm (j : Fin 10) (L : List (Fin 10))
    (hL : L.Nodup) :
    gamma55 j * (L.map gamma55).prod =
      (if j ∈ L then (-1 : ℝ) ^ (L.length - 1) else (-1 : ℝ) ^ L.length) •
        ((L.map gamma55).prod * gamma55 j) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have haL : a ∉ L := (List.nodup_cons.mp hL).1
      have hLn : L.Nodup := (List.nodup_cons.mp hL).2
      have ih' := ih hLn
      by_cases haj : j = a
      · subst a
        simp only [List.map_cons, List.prod_cons, List.length_cons,
          List.mem_cons, true_or, if_true]
        rw [Nat.add_sub_cancel]
        have hjL : j ∉ L := haL
        rw [if_neg hjL] at ih'
        rw [← mul_assoc, gamma55_sq, ih', smul_mul_assoc]
        rw [mul_assoc (L.map gamma55).prod, gamma55_sq, smul_smul]
        have hs : ((-1 : ℝ) ^ L.length) * ((-1 : ℝ) ^ L.length) = 1 := by
          rw [← pow_add]
          exact (show Even (L.length + L.length) by simp).neg_one_pow
        rw [hs, one_smul]
        exact Algebra.commutes _ _
      · simp only [List.map_cons, List.prod_cons, List.length_cons,
          List.mem_cons, haj, false_or]
        rw [← mul_assoc, gamma55_anticommute haj]
        rw [neg_mul, mul_assoc, ih', mul_smul_comm]
        by_cases hjL : j ∈ L
        · rw [if_pos hjL, if_pos hjL]
          have hp : 0 < L.length := List.length_pos_of_ne_nil (List.ne_nil_of_mem hjL)
          rw [Nat.add_sub_cancel]
          rw [← neg_smul ((-1 : ℝ) ^ (L.length - 1))
            (gamma55 a * ((L.map gamma55).prod * gamma55 j))]
          congr 1
          · calc
              -((-1 : ℝ) ^ (L.length - 1)) =
                  (-1 : ℝ) ^ ((L.length - 1) + 1) := by rw [pow_succ]; ring
              _ = (-1 : ℝ) ^ L.length := by rw [Nat.sub_add_cancel hp]
          · rw [mul_assoc]
        · rw [if_neg hjL, if_neg hjL]
          rw [← neg_smul ((-1 : ℝ) ^ L.length)
            (gamma55 a * ((L.map gamma55).prod * gamma55 j))]
          rw [pow_succ']
          congr 1
          · ring
          · rw [mul_assoc]

/-- The diagonal sign character of the ten PBW monomials. -/
theorem gamma55_mul_cliffordMonomial55 (j : Fin 10) (I : Finset (Fin 10)) :
    gamma55 j * cliffordMonomial55 I =
      ((-1 : ℝ) ^ swapExponent55 j I) •
        (cliffordMonomial55 I * gamma55 j) := by
  by_cases hj : j ∈ I
  · simpa [cliffordMonomial55, swapExponent55, hj] using
      gamma55_list_prod_comm j (I.sort (· ≤ ·))
        (Finset.sort_nodup I (· ≤ ·))
  · simpa [cliffordMonomial55, swapExponent55, hj] using
      gamma55_list_prod_comm j (I.sort (· ≤ ·))
        (Finset.sort_nodup I (· ≤ ·))

theorem odd_swapExponent55_iff (j : Fin 10) (I : Finset (Fin 10)) :
    Odd (swapExponent55 j I) ↔
      (j ∈ I ∧ Even I.card) ∨ (j ∉ I ∧ Odd I.card) := by
  by_cases hj : j ∈ I
  · simp only [swapExponent55, hj, if_true, true_and, not_true_eq_false,
      false_and, or_false]
    rcases Nat.even_or_odd I.card with he | ho
    · constructor
      · intro _; exact he
      · intro _
        rcases he with ⟨m, hm⟩
        have hp : 0 < I.card := Finset.card_pos.mpr ⟨j, hj⟩
        use m - 1
        omega
    · constructor <;> intro h
      · rcases h with ⟨m, hm⟩
        rcases ho with ⟨n, hn⟩
        omega
      · exact False.elim (Nat.not_even_iff_odd.mpr ho h)
  · simp [swapExponent55, hj]

/-- Only the scalar PBW character commutes with every vector generator. -/
theorem all_swapExponent55_even_iff (I : Finset (Fin 10)) :
    (∀ j : Fin 10, Even (swapExponent55 j I)) ↔ I = ∅ := by
  constructor
  · intro h
    rcases Nat.even_or_odd I.card with he | ho
    · apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨j, hj⟩
      have hs : Odd (swapExponent55 j I) :=
        (odd_swapExponent55_iff j I).2 (Or.inl ⟨hj, he⟩)
      exact (Nat.not_even_iff_odd.mpr hs) (h j)
    · exfalso
      have hne : I ≠ Finset.univ := by
        intro hI
        subst I
        norm_num at ho
      obtain ⟨j, hj⟩ : ∃ j : Fin 10, j ∉ I := by
        by_contra hn
        push_neg at hn
        exact hne (Finset.eq_univ_of_forall hn)
      have hs : Odd (swapExponent55 j I) :=
        (odd_swapExponent55_iff j I).2 (Or.inr ⟨hj, ho⟩)
      exact (Nat.not_even_iff_odd.mpr hs) (h j)
  · rintro rfl j
    simp [swapExponent55]

/-- Only the full volume PBW character anticommutes with every generator. -/
theorem all_swapExponent55_odd_iff (I : Finset (Fin 10)) :
    (∀ j : Fin 10, Odd (swapExponent55 j I)) ↔ I = Finset.univ := by
  constructor
  · intro h
    rcases Nat.even_or_odd I.card with he | ho
    · apply Finset.eq_univ_of_forall
      intro j
      by_contra hj
      have hs := h j
      rw [odd_swapExponent55_iff] at hs
      simp [hj, he, Nat.not_odd_iff_even.mpr he] at hs
    · have hnonempty : I.Nonempty := by
        by_contra hI
        rw [Finset.not_nonempty_iff_eq_empty] at hI
        subst I
        simp at ho
      obtain ⟨j, hj⟩ := hnonempty
      have hs := h j
      rw [odd_swapExponent55_iff] at hs
      simp [hj, ho, Nat.not_even_iff_odd.mpr ho] at hs
  · rintro rfl j
    rw [odd_swapExponent55_iff]
    norm_num

/-- Square formula for a duplicate-free ordered word. -/
theorem gamma55_list_prod_sq (L : List (Fin 10)) (hL : L.Nodup) :
    (L.map gamma55).prod * (L.map gamma55).prod =
      algebraMap ℝ Cl55
        (((-1 : ℝ) ^ (L.length * (L.length - 1) / 2)) *
          (L.map gammaSign55).prod) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have haL : a ∉ L := (List.nodup_cons.mp hL).1
      have hLn : L.Nodup := (List.nodup_cons.mp hL).2
      have hcomm := gamma55_list_prod_comm a L hLn
      rw [if_neg haL] at hcomm
      let T : Cl55 := (L.map gamma55).prod
      let s : ℝ := (-1 : ℝ) ^ L.length
      have hcomm' : gamma55 a * T = s • (T * gamma55 a) := by
        simpa [T, s] using hcomm
      have hs : s * s = 1 := by
        dsimp [s]
        rw [← pow_add]
        exact (show Even (L.length + L.length) by simp).neg_one_pow
      have hrev : T * gamma55 a = s • (gamma55 a * T) := by
        calc
          T * gamma55 a = 1 • (T * gamma55 a) := (one_smul ℝ _).symm
          _ = (s * s) • (T * gamma55 a) := by rw [hs]
          _ = s • (s • (T * gamma55 a)) := by rw [smul_smul]
          _ = s • (gamma55 a * T) := congrArg (fun X => s • X) hcomm'.symm
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      change (gamma55 a * T) * (gamma55 a * T) = _
      rw [mul_assoc (gamma55 a), ← mul_assoc T, hrev]
      rw [smul_mul_assoc, mul_smul_comm, mul_assoc (gamma55 a) T T,
        ← mul_assoc (gamma55 a) (gamma55 a) (T * T), gamma55_sq]
      rw [ih hLn]
      have hscalar :
          s * (gammaSign55 a *
            (((-1 : ℝ) ^ (L.length * (L.length - 1) / 2)) *
              (L.map gammaSign55).prod)) =
            ((-1 : ℝ) ^ ((L.length + 1) * (L.length + 1 - 1) / 2)) *
              (gammaSign55 a * (L.map gammaSign55).prod) := by
        dsimp [s]
        have htriangle : (L.length + 1) * L.length / 2 =
            L.length * (L.length - 1) / 2 + L.length := by
          simpa using Nat.triangle_succ L.length
        rw [htriangle, pow_add]
        ring
      simpa only [Algebra.smul_def, map_mul] using
        congrArg (algebraMap ℝ Cl55) hscalar

theorem cliffordMonomial55_sq (I : Finset (Fin 10)) :
    cliffordMonomial55 I * cliffordMonomial55 I =
      algebraMap ℝ Cl55
        (((-1 : ℝ) ^ (I.card * (I.card - 1) / 2)) * I.prod gammaSign55) := by
  have hsq := gamma55_list_prod_sq (I.sort (· ≤ ·))
    (Finset.sort_nodup I (· ≤ ·))
  have hprod : ((I.sort (· ≤ ·)).map gammaSign55).prod =
      I.prod gammaSign55 := by
    rw [← List.prod_toFinset gammaSign55 (Finset.sort_nodup I (· ≤ ·))]
    simp
  simpa only [cliffordMonomial55, Finset.length_sort, hprod] using hsq

theorem cliffordMonomial55_sq_scalar_ne_zero (I : Finset (Fin 10)) :
    ((-1 : ℝ) ^ (I.card * (I.card - 1) / 2)) * I.prod gammaSign55 ≠ 0 := by
  apply mul_ne_zero
  · exact pow_ne_zero _ (by norm_num)
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => gammaSign55_ne_zero i)

end Clifford55PBWMonomials
end noncomputable section
