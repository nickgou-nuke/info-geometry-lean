import Mathlib.Tactic
import InfoGeometry.Algebraic.SplitQuadraticForm

/-!
# Cl(n,n) CAR algebra — n fermionic modes (PROVED)

Algebraic proof using the split quadratic form decomposition
into positive and negative sectors.

All CAR identities are proved for arbitrary n via sum computations
on the diagonal split quadratic form `Q(v) = ∑(v_inl)² - ∑(v_inr)²`.
-/

open CliffordAlgebra
open InfoGeometry.Algebraic.SplitSignature

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CliffordCAR

/-! ### Split quadratic form decomposition

The key lemma: `splitQuadraticForm n` decomposes as the difference
of positive and negative sector sum-of-squares.
-/

lemma splitQuadraticForm_decomposed (n : ℕ) (v : SplitModule n) :
    splitQuadraticForm n v = (∑ x : Fin n, (v (Sum.inl x)) ^ 2) - (∑ x : Fin n, (v (Sum.inr x)) ^ 2) := by
  rw [splitQuadraticForm_apply, Fintype.sum_sum_type]
  simp [splitWeight, ← pow_two, sub_eq_add_neg]

/-! ### Clifford generators for the split basis -/

abbrev Clnn (n : ℕ) := CliffordAlgebra (splitQuadraticForm n)

def pVec (n : ℕ) (i : Fin n) : SplitModule n := splitBasisVector (Sum.inl i)
def nVec (n : ℕ) (i : Fin n) : SplitModule n := splitBasisVector (Sum.inr i)
def posG (n : ℕ) (i : Fin n) : Clnn n := ι (splitQuadraticForm n) (pVec n i)
def negG (n : ℕ) (i : Fin n) : Clnn n := ι (splitQuadraticForm n) (nVec n i)

@[simp] theorem p_sq (n : ℕ) (i : Fin n) : posG n i * posG n i = 1 := by
  calc
    posG n i * posG n i = algebraMap ℝ (Clnn n) ((splitQuadraticForm n) (pVec n i)) := ι_sq_scalar _ _
    _ = algebraMap ℝ (Clnn n) 1 := by rw [pVec, splitQuadraticForm_posBasisVector]
    _ = 1 := by simp

@[simp] theorem n_sq (n : ℕ) (i : Fin n) : negG n i * negG n i = -1 := by
  calc
    negG n i * negG n i = algebraMap ℝ (Clnn n) ((splitQuadraticForm n) (nVec n i)) := ι_sq_scalar _ _
    _ = algebraMap ℝ (Clnn n) (-1) := by rw [nVec, splitQuadraticForm_negBasisVector]
    _ = -1 := by simp

theorem pos_neg_anticomm (n : ℕ) (i j : Fin n) : posG n i * negG n j + negG n j * posG n i = 0 := by
  have h : QuadraticMap.polar (splitQuadraticForm n) (pVec n i) (nVec n j) = 0 := by
    dsimp [pVec, nVec]
    rw [QuadraticMap.polar]
    simp [splitQuadraticForm, splitBasisVector]
  rw [posG, negG, ι_mul_ι_add_swap, h]; simp

/-! ### CAR annihilation and creation operators -/

def aVec (n : ℕ) (i : Fin n) : SplitModule n := (1/2 : ℝ) • (pVec n i + nVec n i)
def aDagVec (n : ℕ) (i : Fin n) : SplitModule n := (1/2 : ℝ) • (pVec n i - nVec n i)
def ann (n : ℕ) (i : Fin n) : Clnn n := ι (splitQuadraticForm n) (aVec n i)
def cre (n : ℕ) (i : Fin n) : Clnn n := ι (splitQuadraticForm n) (aDagVec n i)

/-! ### Quadratic form vanishes on a and a† vectors -/

lemma Q_aVec (n : ℕ) (i : Fin n) : (splitQuadraticForm n) (aVec n i) = 0 := by
  dsimp [aVec, pVec, nVec]
  have hsmul := (splitQuadraticForm n).map_smul (1/2 : ℝ)
    (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i))
  have hsq : ((1/2 : ℝ) * (1/2 : ℝ)) = (1/4 : ℝ) := by norm_num
  have hQadd : splitQuadraticForm n (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i)) = 0 := by
    rw [splitQuadraticForm_decomposed]
    simp [splitBasisVector, Pi.add_apply]
  calc
    (splitQuadraticForm n) ((1/2 : ℝ) • (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i)))
        = ((1/2 : ℝ) * (1/2 : ℝ)) • splitQuadraticForm n (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i)) := by
      simpa using hsmul
    _ = (1/4 : ℝ) • 0 := by rw [hsq, hQadd]
    _ = 0 := by simp

lemma Q_aDagVec (n : ℕ) (i : Fin n) : (splitQuadraticForm n) (aDagVec n i) = 0 := by
  dsimp [aDagVec, pVec, nVec]
  have hsmul := (splitQuadraticForm n).map_smul (1/2 : ℝ)
    (splitBasisVector (Sum.inl i) - splitBasisVector (Sum.inr i))
  have hsq : ((1/2 : ℝ) * (1/2 : ℝ)) = (1/4 : ℝ) := by norm_num
  have hQsub : splitQuadraticForm n (splitBasisVector (Sum.inl i) - splitBasisVector (Sum.inr i)) = 0 := by
    rw [splitQuadraticForm_decomposed]
    simp [splitBasisVector, Pi.sub_apply]
  calc
    (splitQuadraticForm n) ((1/2 : ℝ) • (splitBasisVector (Sum.inl i) - splitBasisVector (Sum.inr i)))
        = ((1/2 : ℝ) * (1/2 : ℝ)) • splitQuadraticForm n (splitBasisVector (Sum.inl i) - splitBasisVector (Sum.inr i)) := by
      simpa using hsmul
    _ = (1/4 : ℝ) • 0 := by rw [hsq, hQsub]
    _ = 0 := by simp

@[simp] theorem ann_sq_zero (n : ℕ) (i : Fin n) : ann n i * ann n i = 0 := by
  rw [ann, ι_sq_scalar, Q_aVec]; simp

@[simp] theorem cre_sq_zero (n : ℕ) (i : Fin n) : cre n i * cre n i = 0 := by
  rw [cre, ι_sq_scalar, Q_aDagVec]; simp

/-! ### Polar form on the split basis

The four cases of the polar form on positive/negative basis vectors.
These are the atomic building blocks for all CAR identities.
-/

lemma polar_inl_inl (n : ℕ) (k l : Fin n) :
    QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl k)) (splitBasisVector (Sum.inl l)) =
    if k = l then (2 : ℝ) else 0 := by
  dsimp [QuadraticMap.polar]
  by_cases hkl : k = l
  · subst l
    rw [(splitQuadraticForm n).map_add_self (splitBasisVector (Sum.inl k)), splitQuadraticForm_posBasisVector]
    norm_num
  · rw [splitQuadraticForm_decomposed, splitQuadraticForm_decomposed, splitQuadraticForm_decomposed]
    simp [splitBasisVector, Pi.add_apply, add_sq, Finset.sum_add_distrib, hkl, eq_comm]

lemma polar_inr_inr (n : ℕ) (k l : Fin n) :
    QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inr k)) (splitBasisVector (Sum.inr l)) =
    if k = l then (-2 : ℝ) else 0 := by
  dsimp [QuadraticMap.polar]
  by_cases hkl : k = l
  · subst l
    rw [(splitQuadraticForm n).map_add_self (splitBasisVector (Sum.inr k)), splitQuadraticForm_negBasisVector]
    norm_num
  · rw [splitQuadraticForm_decomposed, splitQuadraticForm_decomposed, splitQuadraticForm_decomposed]
    simp [splitBasisVector, Pi.add_apply, add_sq, Finset.sum_add_distrib, hkl, eq_comm]

lemma polar_inl_inr (n : ℕ) (k l : Fin n) :
    QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl k)) (splitBasisVector (Sum.inr l)) = (0 : ℝ) := by
  dsimp [QuadraticMap.polar]
  rw [splitQuadraticForm_decomposed, splitQuadraticForm_decomposed, splitQuadraticForm_decomposed]
  simp [splitBasisVector, Pi.add_apply]

lemma polar_inr_inl (n : ℕ) (k l : Fin n) :
    QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inr k)) (splitBasisVector (Sum.inl l)) = (0 : ℝ) := by
  dsimp [QuadraticMap.polar]
  rw [splitQuadraticForm_decomposed, splitQuadraticForm_decomposed, splitQuadraticForm_decomposed]
  simp [splitBasisVector, Pi.add_apply]

/-! ### Polar computations for a and a† vectors -/

private lemma polar_pp_nn_zero (n : ℕ) (i j : Fin n) :
    QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i))
      (splitBasisVector (Sum.inl j) + splitBasisVector (Sum.inr j)) = 0 := by
  calc
    _ = QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl i))
            (splitBasisVector (Sum.inl j) + splitBasisVector (Sum.inr j)) +
        QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inr i))
            (splitBasisVector (Sum.inl j) + splitBasisVector (Sum.inr j)) := by
      rw [QuadraticMap.polar_add_left]
    _ = (QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl i)) (splitBasisVector (Sum.inl j)) +
         QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl i)) (splitBasisVector (Sum.inr j))) +
        (QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inr i)) (splitBasisVector (Sum.inl j)) +
         QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inr i)) (splitBasisVector (Sum.inr j))) := by
      rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right]
    _ = ((if i = j then 2 else 0) + 0) + (0 + (if i = j then -2 else 0)) := by
      rw [polar_inl_inl n i j, polar_inl_inr n i j, polar_inr_inl n i j, polar_inr_inr n i j]
    _ = 0 := by
      split_ifs <;> ring

private lemma polar_pm_pm_zero (n : ℕ) (i j : Fin n) :
    QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl i) - splitBasisVector (Sum.inr i))
      (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j)) = 0 := by
  calc
    _ = QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl i))
            (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j)) -
        QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inr i))
            (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j)) := by
      rw [QuadraticMap.polar_sub_left]
    _ = (QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl i)) (splitBasisVector (Sum.inl j)) -
         QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl i)) (splitBasisVector (Sum.inr j))) -
        (QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inr i)) (splitBasisVector (Sum.inl j)) -
         QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inr i)) (splitBasisVector (Sum.inr j))) := by
      rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right]
    _ = ((if i = j then 2 else 0) - 0) - (0 - (if i = j then -2 else 0)) := by
      rw [polar_inl_inl n i j, polar_inl_inr n i j, polar_inr_inl n i j, polar_inr_inr n i j]
    _ = 0 := by
      split_ifs <;> ring

private lemma polar_pp_pm_delta (n : ℕ) (i j : Fin n) :
    QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i))
      (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j)) =
    if i = j then (4 : ℝ) else 0 := by
  calc
    _ = QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl i))
            (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j)) +
        QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inr i))
            (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j)) := by
      rw [QuadraticMap.polar_add_left]
    _ = (QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl i)) (splitBasisVector (Sum.inl j)) -
         QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inl i)) (splitBasisVector (Sum.inr j))) +
        (QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inr i)) (splitBasisVector (Sum.inl j)) -
         QuadraticMap.polar (splitQuadraticForm n) (splitBasisVector (Sum.inr i)) (splitBasisVector (Sum.inr j))) := by
      rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right]
    _ = ((if i = j then 2 else 0) - 0) + (0 - (if i = j then -2 else 0)) := by
      rw [polar_inl_inl n i j, polar_inl_inr n i j, polar_inr_inl n i j, polar_inr_inr n i j]
    _ = (if i = j then 4 else 0) := by
      split_ifs <;> ring

theorem polar_ann_ann (n : ℕ) (i j : Fin n) :
    QuadraticMap.polar (splitQuadraticForm n) (aVec n i) (aVec n j) = 0 := by
  dsimp [aVec, pVec, nVec]
  calc
    QuadraticMap.polar (splitQuadraticForm n)
        ((1/2 : ℝ) • (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i)))
        ((1/2 : ℝ) • (splitBasisVector (Sum.inl j) + splitBasisVector (Sum.inr j)))
        = (1/2 : ℝ) • QuadraticMap.polar (splitQuadraticForm n)
            (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i))
            ((1/2 : ℝ) • (splitBasisVector (Sum.inl j) + splitBasisVector (Sum.inr j))) := by
      rw [QuadraticMap.polar_smul_left]
    _ = (1/2 : ℝ) • (1/2 : ℝ) • QuadraticMap.polar (splitQuadraticForm n)
            (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i))
            (splitBasisVector (Sum.inl j) + splitBasisVector (Sum.inr j)) := by
      rw [QuadraticMap.polar_smul_right]
    _ = ((1/2 : ℝ) * (1/2 : ℝ)) • QuadraticMap.polar (splitQuadraticForm n)
            (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i))
            (splitBasisVector (Sum.inl j) + splitBasisVector (Sum.inr j)) := by
      rw [smul_smul]
    _ = (1/4 : ℝ) • 0 := by
      rw [show ((1/2 : ℝ) * (1/2 : ℝ)) = (1/4 : ℝ) by norm_num, polar_pp_nn_zero n i j]
    _ = 0 := by simp

theorem polar_cre_cre (n : ℕ) (i j : Fin n) :
    QuadraticMap.polar (splitQuadraticForm n) (aDagVec n i) (aDagVec n j) = 0 := by
  dsimp [aDagVec, pVec, nVec]
  calc
    QuadraticMap.polar (splitQuadraticForm n)
        ((1/2 : ℝ) • (splitBasisVector (Sum.inl i) - splitBasisVector (Sum.inr i)))
        ((1/2 : ℝ) • (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j)))
        = (1/2 : ℝ) • QuadraticMap.polar (splitQuadraticForm n)
            (splitBasisVector (Sum.inl i) - splitBasisVector (Sum.inr i))
            ((1/2 : ℝ) • (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j))) := by
      rw [QuadraticMap.polar_smul_left]
    _ = (1/2 : ℝ) • (1/2 : ℝ) • QuadraticMap.polar (splitQuadraticForm n)
            (splitBasisVector (Sum.inl i) - splitBasisVector (Sum.inr i))
            (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j)) := by
      rw [QuadraticMap.polar_smul_right]
    _ = ((1/2 : ℝ) * (1/2 : ℝ)) • QuadraticMap.polar (splitQuadraticForm n)
            (splitBasisVector (Sum.inl i) - splitBasisVector (Sum.inr i))
            (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j)) := by
      rw [smul_smul]
    _ = (1/4 : ℝ) • 0 := by
      rw [show ((1/2 : ℝ) * (1/2 : ℝ)) = (1/4 : ℝ) by norm_num, polar_pm_pm_zero n i j]
    _ = 0 := by simp

theorem polar_ann_cre (n : ℕ) (i j : Fin n) :
    QuadraticMap.polar (splitQuadraticForm n) (aVec n i) (aDagVec n j) =
    if i = j then (1 : ℝ) else 0 := by
  dsimp [aVec, aDagVec, pVec, nVec]
  calc
    QuadraticMap.polar (splitQuadraticForm n)
        ((1/2 : ℝ) • (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i)))
        ((1/2 : ℝ) • (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j)))
        = (1/2 : ℝ) • QuadraticMap.polar (splitQuadraticForm n)
            (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i))
            ((1/2 : ℝ) • (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j))) := by
      rw [QuadraticMap.polar_smul_left]
    _ = (1/2 : ℝ) • (1/2 : ℝ) • QuadraticMap.polar (splitQuadraticForm n)
            (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i))
            (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j)) := by
      rw [QuadraticMap.polar_smul_right]
    _ = ((1/2 : ℝ) * (1/2 : ℝ)) • QuadraticMap.polar (splitQuadraticForm n)
            (splitBasisVector (Sum.inl i) + splitBasisVector (Sum.inr i))
            (splitBasisVector (Sum.inl j) - splitBasisVector (Sum.inr j)) := by
      rw [smul_smul]
    _ = (1/4 : ℝ) • (if i = j then (4 : ℝ) else 0) := by
      rw [show ((1/2 : ℝ) * (1/2 : ℝ)) = (1/4 : ℝ) by norm_num, polar_pp_pm_delta n i j]
    _ = (if i = j then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num

/-! ### CAR algebra identities -/

theorem car_identity (n : ℕ) (i j : Fin n) :
    ann n i * cre n j + cre n j * ann n i = (if i = j then (1 : Clnn n) else 0) := by
  rw [ann, cre, ι_mul_ι_add_swap, polar_ann_cre n i j]; split_ifs <;> simp

theorem ann_ann_anticomm (n : ℕ) (i j : Fin n) : ann n i * ann n j + ann n j * ann n i = 0 := by
  by_cases h : i = j; · subst j; simp [ann_sq_zero]
  · rw [ann, ann, ι_mul_ι_add_swap, polar_ann_ann n i j]; simp

theorem cre_cre_anticomm (n : ℕ) (i j : Fin n) : cre n i * cre n j + cre n j * cre n i = 0 := by
  by_cases h : i = j; · subst j; simp [cre_sq_zero]
  · rw [cre, cre, ι_mul_ι_add_swap, polar_cre_cre n i j]; simp

/-- Complete CAR packet for n fermionic modes from Cl(n,n). -/
theorem car_packet (n : ℕ) :
    (∀ i : Fin n, ann n i * ann n i = 0) ∧
    (∀ i : Fin n, cre n i * cre n i = 0) ∧
    (∀ i j : Fin n, ann n i * ann n j + ann n j * ann n i = 0) ∧
    (∀ i j : Fin n, cre n i * cre n j + cre n j * cre n i = 0) ∧
    (∀ i j, ann n i * cre n j + cre n j * ann n i = if i = j then (1 : Clnn n) else 0) := by
  exact ⟨ann_sq_zero n, cre_sq_zero n, ann_ann_anticomm n, cre_cre_anticomm n, car_identity n⟩

end InfoGeometry.OperatorAlgebra.CliffordCAR
