import Mathlib.Tactic
import InfoGeometry.Algebraic.SplitQuadraticForm
import InfoGeometry.OperatorAlgebra.ChiralRetainedWordFiveGradeClosure

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

def mixedGenerator (n : ℕ) (i j : Fin n) : Clnn n :=
  cre n i * ann n j - (if i = j then (1 / 2 : ℝ) • (1 : Clnn n) else 0)

theorem cre_cre_commutator (n : ℕ) (i j : Fin n) :
    cre n i * cre n j - cre n j * cre n i =
      (2 : ℝ) • (cre n i * cre n j) := by
  have hcc := cre_cre_anticomm n i j
  have hswap : cre n j * cre n i = -(cre n i * cre n j) :=
    eq_neg_of_add_eq_zero_right hcc
  rw [hswap, two_smul]
  simp [sub_eq_add_neg]

theorem ann_ann_commutator (n : ℕ) (i j : Fin n) :
    ann n i * ann n j - ann n j * ann n i =
      (2 : ℝ) • (ann n i * ann n j) := by
  have haa := ann_ann_anticomm n i j
  have hswap : ann n j * ann n i = -(ann n i * ann n j) :=
    eq_neg_of_add_eq_zero_right haa
  rw [hswap, two_smul]
  simp [sub_eq_add_neg]

theorem cre_ann_commutator (n : ℕ) (i j : Fin n) :
    cre n i * ann n j - ann n j * cre n i =
      (2 : ℝ) • mixedGenerator n i j := by
  by_cases hij : i = j
  · subst j
    have hcar : ann n i * cre n i + cre n i * ann n i = 1 := by
      simpa using car_identity n i i
    simp [mixedGenerator]
    have hac : ann n i * cre n i = 1 - cre n i * ann n i :=
      eq_sub_of_add_eq hcar
    rw [hac]
    simp [two_smul, sub_eq_add_neg]
    abel
  · have hcar : ann n j * cre n i + cre n i * ann n j = 0 := by
      simpa [if_neg (Ne.symm hij)] using car_identity n j i
    have hswap : ann n j * cre n i = -(cre n i * ann n j) :=
      eq_neg_of_add_eq_zero_left hcar
    simp only [mixedGenerator, if_neg hij]
    rw [hswap, two_smul]
    simp [sub_eq_add_neg]

private theorem cre_ann_raw_commutator_cre
    (n : ℕ) (i j k : Fin n) :
    cre n i * ann n j * cre n k - cre n k * (cre n i * ann n j) =
      if j = k then cre n i else 0 := by
  by_cases hjk : j = k
  · subst k
    have hcar : ann n j * cre n j + cre n j * ann n j = 1 := by
      simpa using car_identity n j j
    have hcc : cre n j * cre n i = -(cre n i * cre n j) :=
      eq_neg_of_add_eq_zero_right (cre_cre_anticomm n i j)
    have hac : ann n j * cre n j = 1 - cre n j * ann n j :=
      eq_sub_of_add_eq hcar
    simp only [if_pos rfl]
    calc
      cre n i * ann n j * cre n j - cre n j * (cre n i * ann n j) =
          cre n i * (ann n j * cre n j) -
            (cre n j * cre n i) * ann n j := by noncomm_ring
      _ = cre n i * (1 - cre n j * ann n j) -
            (-(cre n i * cre n j)) * ann n j := by rw [hac, hcc]
      _ = cre n i := by noncomm_ring
  · have hcar : ann n j * cre n k + cre n k * ann n j = 0 := by
      simpa [if_neg hjk] using car_identity n j k
    have hcc : cre n k * cre n i = -(cre n i * cre n k) :=
      eq_neg_of_add_eq_zero_right (cre_cre_anticomm n i k)
    have hac : ann n j * cre n k = -(cre n k * ann n j) :=
      eq_neg_of_add_eq_zero_left hcar
    simp only [if_neg hjk]
    calc
      cre n i * ann n j * cre n k - cre n k * (cre n i * ann n j) =
          cre n i * (ann n j * cre n k) -
            (cre n k * cre n i) * ann n j := by noncomm_ring
      _ = cre n i * (-(cre n k * ann n j)) -
            (-(cre n i * cre n k)) * ann n j := by rw [hac, hcc]
      _ = 0 := by noncomm_ring

theorem mixedGenerator_commutator_cre
    (n : ℕ) (i j k : Fin n) :
    mixedGenerator n i j * cre n k - cre n k * mixedGenerator n i j =
      if j = k then cre n i else 0 := by
  simpa [mixedGenerator, sub_mul, mul_sub] using
    cre_ann_raw_commutator_cre n i j k

private theorem cre_ann_raw_commutator_ann
    (n : ℕ) (i j k : Fin n) :
    cre n i * ann n j * ann n k - ann n k * (cre n i * ann n j) =
      if i = k then -(ann n j) else 0 := by
  by_cases hik : i = k
  · subst k
    have hcar : ann n i * cre n i + cre n i * ann n i = 1 := by
      simpa using car_identity n i i
    have haa : ann n j * ann n i = -(ann n i * ann n j) :=
      eq_neg_of_add_eq_zero_left (ann_ann_anticomm n j i)
    have hac : ann n i * cre n i = 1 - cre n i * ann n i :=
      eq_sub_of_add_eq hcar
    simp only [if_pos rfl]
    calc
      cre n i * ann n j * ann n i - ann n i * (cre n i * ann n j) =
          cre n i * (ann n j * ann n i) -
            (ann n i * cre n i) * ann n j := by noncomm_ring
      _ = cre n i * (ann n j * ann n i) -
            (1 - cre n i * ann n i) * ann n j := by rw [hac]
      _ = -(ann n j) := by rw [haa]; noncomm_ring
  · have hcar : ann n k * cre n i + cre n i * ann n k = 0 := by
      simpa [if_neg (Ne.symm hik)] using car_identity n k i
    have haa : ann n j * ann n k = -(ann n k * ann n j) :=
      eq_neg_of_add_eq_zero_left (ann_ann_anticomm n j k)
    have hac : ann n k * cre n i = -(cre n i * ann n k) :=
      eq_neg_of_add_eq_zero_left hcar
    simp only [if_neg hik]
    calc
      cre n i * ann n j * ann n k - ann n k * (cre n i * ann n j) =
          cre n i * (ann n j * ann n k) -
            (ann n k * cre n i) * ann n j := by noncomm_ring
      _ = cre n i * (ann n j * ann n k) -
            (-(cre n i * ann n k)) * ann n j := by rw [hac]
      _ = 0 := by
        rw [haa]
        noncomm_ring

theorem mixedGenerator_commutator_ann
    (n : ℕ) (i j k : Fin n) :
    mixedGenerator n i j * ann n k - ann n k * mixedGenerator n i j =
      if i = k then -(ann n j) else 0 := by
  simpa [mixedGenerator, sub_mul, mul_sub] using
    cre_ann_raw_commutator_ann n i j k

/-! ### The centered number operator

The CAR relations already present above determine the integer charge
derivation.  We keep this in the native Clifford algebra: no matrix model or
second operator carrier is introduced.
-/

def numberOperator (n : ℕ) : Clnn n :=
  ∑ i : Fin n, cre n i * ann n i

def centeredNumberOperator (n : ℕ) : Clnn n :=
  numberOperator n - ((n : ℝ) / 2) • (1 : Clnn n)

private theorem numberSummand_commutator_cre
    (n : ℕ) (i j : Fin n) :
    cre n i * ann n i * cre n j - cre n j * (cre n i * ann n i) =
      if i = j then cre n j else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl]
    have hcar : ann n i * cre n i + cre n i * ann n i = 1 := by
      simpa using car_identity n i i
    have hac : ann n i * cre n i = 1 - cre n i * ann n i :=
      eq_sub_of_add_eq hcar
    calc
      cre n i * ann n i * cre n i - cre n i * (cre n i * ann n i) =
          cre n i * (ann n i * cre n i) -
            (cre n i * cre n i) * ann n i := by noncomm_ring
      _ = cre n i * (1 - cre n i * ann n i) -
            0 * ann n i := by rw [hac, cre_sq_zero]
      _ = cre n i := by
        simp [mul_sub, ← mul_assoc, cre_sq_zero]
  · have hcar := car_identity n i j
    simp only [if_neg hij] at hcar
    have hcc := cre_cre_anticomm n i j
    have hac : ann n i * cre n j = -(cre n j * ann n i) := by
      have hcar' : cre n j * ann n i + ann n i * cre n j = 0 := by
        simpa [add_comm] using hcar
      exact eq_neg_of_add_eq_zero_right hcar'
    have hci : cre n j * cre n i = -(cre n i * cre n j) := by
      exact eq_neg_of_add_eq_zero_right hcc
    rw [if_neg hij]
    calc
      cre n i * ann n i * cre n j - cre n j * (cre n i * ann n i) =
          cre n i * (ann n i * cre n j) -
            (cre n j * cre n i) * ann n i := by noncomm_ring
      _ = cre n i * (-(cre n j * ann n i)) -
            (-(cre n i * cre n j)) * ann n i := by rw [hac, hci]
      _ = 0 := by noncomm_ring

private theorem numberSummand_commutator_ann
    (n : ℕ) (i j : Fin n) :
    cre n i * ann n i * ann n j - ann n j * (cre n i * ann n i) =
      if i = j then -(ann n j) else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl]
    have hcar : ann n i * cre n i + cre n i * ann n i = 1 := by
      simpa using car_identity n i i
    have hca : ann n i * cre n i = 1 - cre n i * ann n i :=
      eq_sub_of_add_eq hcar
    calc
      cre n i * ann n i * ann n i - ann n i * (cre n i * ann n i) =
          cre n i * (ann n i * ann n i) -
            (ann n i * cre n i) * ann n i := by noncomm_ring
      _ = cre n i * 0 - (1 - cre n i * ann n i) * ann n i := by
        have hzero : cre n i * ann n i * ann n i = 0 := by
          calc
            cre n i * ann n i * ann n i =
                cre n i * (ann n i * ann n i) := by noncomm_ring
            _ = 0 := by rw [ann_sq_zero, mul_zero]
        rw [ann_sq_zero, mul_zero, hca]
      _ = -(ann n i) := by
        rw [sub_mul, mul_zero, one_mul]
        have hzero : cre n i * ann n i * ann n i = 0 := by
          calc
            cre n i * ann n i * ann n i =
                cre n i * (ann n i * ann n i) := by noncomm_ring
            _ = 0 := by rw [ann_sq_zero, mul_zero]
        rw [hzero]
        simp
  · have hcar : ann n j * cre n i + cre n i * ann n j = 0 := by
      simpa [if_neg (Ne.symm hij)] using car_identity n j i
    have haa := ann_ann_anticomm n i j
    have hac : ann n j * cre n i = -(cre n i * ann n j) := by
      exact eq_neg_of_add_eq_zero_left hcar
    have hai : ann n i * ann n j = -(ann n j * ann n i) := by
      exact eq_neg_of_add_eq_zero_left haa
    rw [if_neg hij]
    calc
      cre n i * ann n i * ann n j - ann n j * (cre n i * ann n i) =
          cre n i * (ann n i * ann n j) -
            (ann n j * cre n i) * ann n i := by noncomm_ring
      _ = cre n i * (-(ann n j * ann n i)) -
            (-(cre n i * ann n j)) * ann n i := by rw [hai, hac]
      _ = 0 := by noncomm_ring

theorem numberOperator_commutator_cre (n : ℕ) (j : Fin n) :
    numberOperator n * cre n j - cre n j * numberOperator n = cre n j := by
  calc
    numberOperator n * cre n j - cre n j * numberOperator n =
        ∑ i : Fin n, (cre n i * ann n i * cre n j -
          cre n j * (cre n i * ann n i)) := by
            simp only [numberOperator, Finset.sum_mul, Finset.mul_sum,
              Finset.sum_sub_distrib]
    _ =
        ∑ i : Fin n, if i = j then cre n j else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact numberSummand_commutator_cre n i j
    _ = cre n j := by simp

theorem numberOperator_commutator_ann (n : ℕ) (j : Fin n) :
    numberOperator n * ann n j - ann n j * numberOperator n = -(ann n j) := by
  calc
    numberOperator n * ann n j - ann n j * numberOperator n =
        ∑ i : Fin n, (cre n i * ann n i * ann n j -
          ann n j * (cre n i * ann n i)) := by
            simp only [numberOperator, Finset.sum_mul, Finset.mul_sum,
              Finset.sum_sub_distrib]
    _ =
        ∑ i : Fin n, if i = j then -(ann n j) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact numberSummand_commutator_ann n i j
    _ = -(ann n j) := by simp

theorem centeredNumberOperator_commutator_cre (n : ℕ) (j : Fin n) :
    centeredNumberOperator n * cre n j -
        cre n j * centeredNumberOperator n = cre n j := by
  rw [centeredNumberOperator]
  calc
    (numberOperator n - ((n : ℝ) / 2) • (1 : Clnn n)) * cre n j -
        cre n j * (numberOperator n - ((n : ℝ) / 2) • (1 : Clnn n)) =
        (numberOperator n * cre n j - cre n j * numberOperator n) -
          (((n : ℝ) / 2) • (1 : Clnn n) * cre n j -
            cre n j * ((n : ℝ) / 2) • (1 : Clnn n)) := by noncomm_ring
    _ = cre n j - (((n : ℝ) / 2) • (1 : Clnn n) * cre n j -
          cre n j * ((n : ℝ) / 2) • (1 : Clnn n)) := by
      rw [numberOperator_commutator_cre]
    _ = cre n j := by simp

theorem centeredNumberOperator_commutator_ann (n : ℕ) (j : Fin n) :
    centeredNumberOperator n * ann n j -
        ann n j * centeredNumberOperator n = -(ann n j) := by
  rw [centeredNumberOperator]
  calc
    (numberOperator n - ((n : ℝ) / 2) • (1 : Clnn n)) * ann n j -
        ann n j * (numberOperator n - ((n : ℝ) / 2) • (1 : Clnn n)) =
        (numberOperator n * ann n j - ann n j * numberOperator n) -
          (((n : ℝ) / 2) • (1 : Clnn n) * ann n j -
            ann n j * ((n : ℝ) / 2) • (1 : Clnn n)) := by noncomm_ring
    _ = -(ann n j) - (((n : ℝ) / 2) • (1 : Clnn n) * ann n j -
          ann n j * ((n : ℝ) / 2) • (1 : Clnn n)) := by
      rw [numberOperator_commutator_ann]
    _ = -(ann n j) := by simp

theorem commutator_mul (n : ℕ) (X Y : Clnn n) :
    centeredNumberOperator n * (X * Y) -
        (X * Y) * centeredNumberOperator n =
      (centeredNumberOperator n * X - X * centeredNumberOperator n) * Y +
        X * (centeredNumberOperator n * Y - Y * centeredNumberOperator n) := by
  noncomm_ring

theorem centeredNumberOperator_commutator_cre_cre (n : ℕ) (i j : Fin n) :
    centeredNumberOperator n * (cre n i * cre n j) -
        (cre n i * cre n j) * centeredNumberOperator n =
      (2 : ℝ) • (cre n i * cre n j) := by
  calc
    centeredNumberOperator n * (cre n i * cre n j) -
        (cre n i * cre n j) * centeredNumberOperator n =
        (centeredNumberOperator n * cre n i - cre n i * centeredNumberOperator n) *
            cre n j +
          cre n i * (centeredNumberOperator n * cre n j -
            cre n j * centeredNumberOperator n) := by
              exact commutator_mul n (cre n i) (cre n j)
    _ = cre n i * cre n j + cre n i * cre n j := by
      rw [centeredNumberOperator_commutator_cre,
        centeredNumberOperator_commutator_cre]
    _ = (2 : ℝ) • (cre n i * cre n j) := by
      rw [two_smul]

theorem centeredNumberOperator_commutator_ann_ann (n : ℕ) (i j : Fin n) :
    centeredNumberOperator n * (ann n i * ann n j) -
        (ann n i * ann n j) * centeredNumberOperator n =
      (-2 : ℝ) • (ann n i * ann n j) := by
  calc
    centeredNumberOperator n * (ann n i * ann n j) -
        (ann n i * ann n j) * centeredNumberOperator n =
        (centeredNumberOperator n * ann n i - ann n i * centeredNumberOperator n) *
            ann n j +
          ann n i * (centeredNumberOperator n * ann n j -
            ann n j * centeredNumberOperator n) := by
              exact commutator_mul n (ann n i) (ann n j)
    _ = -(ann n i * ann n j) - (ann n i * ann n j) := by
      rw [centeredNumberOperator_commutator_ann,
        centeredNumberOperator_commutator_ann]
      noncomm_ring
    _ = (-2 : ℝ) • (ann n i * ann n j) := by
      calc
        -(ann n i * ann n j) - (ann n i * ann n j) =
            -(ann n i * ann n j + ann n i * ann n j) := by noncomm_ring
        _ = -(2 • (ann n i * ann n j)) := by rw [two_smul]
        _ = (-2 : ℝ) • (ann n i * ann n j) := by
          rw [neg_smul]
          rfl

theorem centeredNumberOperator_commutator_cre_ann (n : ℕ) (i j : Fin n) :
    centeredNumberOperator n * (cre n i * ann n j) -
        (cre n i * ann n j) * centeredNumberOperator n = 0 := by
  calc
    centeredNumberOperator n * (cre n i * ann n j) -
        (cre n i * ann n j) * centeredNumberOperator n =
        (centeredNumberOperator n * cre n i - cre n i * centeredNumberOperator n) *
            ann n j +
          cre n i * (centeredNumberOperator n * ann n j -
            ann n j * centeredNumberOperator n) := by
              exact commutator_mul n (cre n i) (ann n j)
    _ = 0 := by
      rw [centeredNumberOperator_commutator_cre,
        centeredNumberOperator_commutator_ann]
      simp

theorem centeredNumberOperator_commutator_ann_cre (n : ℕ) (i j : Fin n) :
    centeredNumberOperator n * (ann n i * cre n j) -
        (ann n i * cre n j) * centeredNumberOperator n = 0 := by
  calc
    centeredNumberOperator n * (ann n i * cre n j) -
        (ann n i * cre n j) * centeredNumberOperator n =
        (centeredNumberOperator n * ann n i - ann n i * centeredNumberOperator n) *
            cre n j +
          ann n i * (centeredNumberOperator n * cre n j -
            cre n j * centeredNumberOperator n) := by
              exact commutator_mul n (ann n i) (cre n j)
    _ = 0 := by
      rw [centeredNumberOperator_commutator_ann,
        centeredNumberOperator_commutator_cre]
      simp

theorem centeredNumberOperator_commutator_mixedGenerator
    (n : ℕ) (i j : Fin n) :
    centeredNumberOperator n * mixedGenerator n i j -
        mixedGenerator n i j * centeredNumberOperator n = 0 := by
  unfold mixedGenerator
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl]
    calc
      centeredNumberOperator n *
          (cre n i * ann n i - (1 / 2 : ℝ) • (1 : Clnn n)) -
          (cre n i * ann n i - (1 / 2 : ℝ) • (1 : Clnn n)) *
            centeredNumberOperator n =
          (centeredNumberOperator n * (cre n i * ann n i) -
              (cre n i * ann n i) * centeredNumberOperator n) -
            (centeredNumberOperator n * ((1 / 2 : ℝ) • (1 : Clnn n)) -
              ((1 / 2 : ℝ) • (1 : Clnn n)) * centeredNumberOperator n) := by
                noncomm_ring
      _ = 0 := by
        rw [centeredNumberOperator_commutator_cre_ann]
        simp
  · simpa [hij] using centeredNumberOperator_commutator_cre_ann n i j

/-! ### Quadratic-to-linear Witt routing

The ordinary commutator Lie closure of the creation/annihilation generators
has a finite quadratic-to-linear routing law inside the native Clifford
algebra.  This is distinct from arbitrary associative cubic words.
-/

theorem cre_cre_commutator_ann
    (n : ℕ) (i j k : Fin n) :
    cre n i * cre n j * ann n k - ann n k * (cre n i * cre n j) =
      (if j = k then cre n i else 0) -
        (if i = k then cre n j else 0) := by
  by_cases hik : i = k
  · subst k
    by_cases hij : i = j
    · subst j
      simp only [if_pos rfl]
      rw [cre_sq_zero]
      simp
    · have hcar : ann n i * cre n j + cre n j * ann n i = 0 := by
        have h := car_identity n i j
        rw [if_neg hij] at h
        exact h
      have hac : cre n j * ann n i = -(ann n i * cre n j) :=
        eq_neg_of_add_eq_zero_right hcar
      have hself : ann n i * cre n i =
          1 - cre n i * ann n i := by
        simpa using eq_sub_of_add_eq (car_identity n i i)
      have hji : j ≠ i := Ne.symm hij
      simp [hij, hji]
      calc
        cre n i * cre n j * ann n i - ann n i * (cre n i * cre n j) =
            cre n i * (cre n j * ann n i) -
              (ann n i * cre n i) * cre n j := by noncomm_ring
        _ = cre n i * (-(ann n i * cre n j)) -
              (1 - cre n i * ann n i) * cre n j := by rw [hac, hself]
        _ = -(cre n j) := by noncomm_ring
  · by_cases hjk : j = k
    · subst k
      have hcar : ann n j * cre n i + cre n i * ann n j = 0 := by
        have h := car_identity n j i
        rw [if_neg (Ne.symm hik)] at h
        exact h
      have hac : ann n j * cre n i = -(cre n i * ann n j) :=
        eq_neg_of_add_eq_zero_left hcar
      have hdiag : ann n j * cre n j + cre n j * ann n j = 1 := by
        simpa using car_identity n j j
      have hdiag' : cre n j * ann n j + ann n j * cre n j = 1 := by
        simpa [add_comm] using hdiag
      simp [hik, Ne.symm hik]
      calc
        cre n i * cre n j * ann n j - ann n j * (cre n i * cre n j) =
            cre n i * (cre n j * ann n j) -
              (ann n j * cre n i) * cre n j := by noncomm_ring
        _ = cre n i * (cre n j * ann n j) -
              (-(cre n i * ann n j)) * cre n j := by rw [hac]
        _ = cre n i := by
          calc
            cre n i * (cre n j * ann n j) -
                (-(cre n i * ann n j)) * cre n j =
                cre n i * (cre n j * ann n j + ann n j * cre n j) := by
                  noncomm_ring
            _ = cre n i := by rw [hdiag']; simp
    · have hki : ann n k * cre n i = -(cre n i * ann n k) := by
        have hcar : ann n k * cre n i + cre n i * ann n k = 0 := by
          have h := car_identity n k i
          rw [if_neg (Ne.symm hik)] at h
          exact h
        exact eq_neg_of_add_eq_zero_left hcar
      have hkj : ann n k * cre n j = -(cre n j * ann n k) := by
        have hcar : ann n k * cre n j + cre n j * ann n k = 0 := by
          have h := car_identity n k j
          rw [if_neg (Ne.symm hjk)] at h
          exact h
        exact eq_neg_of_add_eq_zero_left hcar
      have hkj' : cre n j * ann n k = -(ann n k * cre n j) := by
        have hcar : ann n k * cre n j + cre n j * ann n k = 0 := by
          have h := car_identity n k j
          rw [if_neg (Ne.symm hjk)] at h
          exact h
        exact eq_neg_of_add_eq_zero_right hcar
      simp [hik, hjk]
      calc
        cre n i * cre n j * ann n k - ann n k * (cre n i * cre n j) =
            cre n i * (cre n j * ann n k) -
              (ann n k * cre n i) * cre n j := by noncomm_ring
        _ = cre n i * (-(ann n k * cre n j)) -
              (-(cre n i * ann n k)) * cre n j := by rw [hkj', hki]
        _ = 0 := by noncomm_ring

theorem ann_ann_commutator_cre
    (n : ℕ) (i j k : Fin n) :
    ann n i * ann n j * cre n k - cre n k * (ann n i * ann n j) =
      (if j = k then ann n i else 0) -
        (if i = k then ann n j else 0) := by
  by_cases hik : i = k
  · subst k
    by_cases hij : i = j
    · subst j
      simp only [if_pos rfl]
      rw [ann_sq_zero]
      simp
    · have hcar : ann n j * cre n i + cre n i * ann n j = 0 := by
        have h := car_identity n j i
        rw [if_neg (Ne.symm hij)] at h
        exact h
      have hac : ann n j * cre n i = -(cre n i * ann n j) :=
        eq_neg_of_add_eq_zero_left hcar
      have hself : cre n i * ann n i =
          1 - ann n i * cre n i := by
        have hdiag : cre n i * ann n i + ann n i * cre n i = 1 := by
          simpa [add_comm] using car_identity n i i
        exact eq_sub_of_add_eq hdiag
      have hji : j ≠ i := Ne.symm hij
      simp [hij, hji]
      calc
        ann n i * ann n j * cre n i - cre n i * (ann n i * ann n j) =
            ann n i * (ann n j * cre n i) -
              (cre n i * ann n i) * ann n j := by noncomm_ring
        _ = ann n i * (-(cre n i * ann n j)) -
              (1 - ann n i * cre n i) * ann n j := by rw [hac, hself]
        _ = -(ann n j) := by noncomm_ring
  · by_cases hjk : j = k
    · subst k
      have hcar : ann n i * cre n j + cre n j * ann n i = 0 := by
        have h := car_identity n i j
        rw [if_neg hik] at h
        exact h
      have hac : cre n j * ann n i = -(ann n i * cre n j) :=
        eq_neg_of_add_eq_zero_right hcar
      have hdiag : ann n j * cre n j + cre n j * ann n j = 1 := by
        simpa using car_identity n j j
      have hdiag' : cre n j * ann n j + ann n j * cre n j = 1 := by
        simpa [add_comm] using hdiag
      simp [hik, Ne.symm hik]
      calc
        ann n i * ann n j * cre n j - cre n j * (ann n i * ann n j) =
            ann n i * (ann n j * cre n j) -
              (cre n j * ann n i) * ann n j := by noncomm_ring
        _ = ann n i * (ann n j * cre n j) -
              (-(ann n i * cre n j)) * ann n j := by rw [hac]
        _ = ann n i := by
          calc
            ann n i * (ann n j * cre n j) -
                (-(ann n i * cre n j)) * ann n j =
                ann n i * (ann n j * cre n j + cre n j * ann n j) := by
                  noncomm_ring
            _ = ann n i := by rw [hdiag]; simp
    · have hki : cre n k * ann n i = -(ann n i * cre n k) := by
        have hcar : cre n k * ann n i + ann n i * cre n k = 0 := by
          have h := car_identity n i k
          rw [if_neg hik] at h
          simpa [add_comm] using h
        exact eq_neg_of_add_eq_zero_left hcar
      have hkj : cre n k * ann n j = -(ann n j * cre n k) := by
        have hcar : cre n k * ann n j + ann n j * cre n k = 0 := by
          have h := car_identity n j k
          rw [if_neg hjk] at h
          simpa [add_comm] using h
        exact eq_neg_of_add_eq_zero_left hcar
      have hkj' : ann n j * cre n k = -(cre n k * ann n j) := by
        have hcar : cre n k * ann n j + ann n j * cre n k = 0 := by
          have h := car_identity n j k
          rw [if_neg hjk] at h
          simpa [add_comm] using h
        exact eq_neg_of_add_eq_zero_right hcar
      simp [hik, hjk]
      calc
        ann n i * ann n j * cre n k - cre n k * (ann n i * ann n j) =
            ann n i * (ann n j * cre n k) -
              (cre n k * ann n i) * ann n j := by noncomm_ring
        _ = ann n i * (-(cre n k * ann n j)) -
              (-(ann n i * cre n k)) * ann n j := by rw [hkj', hki]
        _ = 0 := by noncomm_ring

theorem commutator_mul_right (X Y Z : Clnn n) :
    X * (Y * Z) - (Y * Z) * X =
      (X * Y - Y * X) * Z + Y * (X * Z - Z * X) := by
  noncomm_ring

theorem mixedGenerator_commutator_mixedGenerator
    (n : ℕ) (i j k l : Fin n) :
    mixedGenerator n i j * mixedGenerator n k l -
        mixedGenerator n k l * mixedGenerator n i j =
      (if j = k then mixedGenerator n i l else 0) -
        (if i = l then mixedGenerator n k j else 0) := by
  have hcentral : ∀ (r : ℝ) (x : Clnn n),
      (r • (1 : Clnn n)) * x = x * (r • (1 : Clnn n)) := by
    intro r x
    simpa [Algebra.smul_def] using (Algebra.commutes r x)
  unfold mixedGenerator
  calc
    (cre n i * ann n j - (if i = j then (1 / 2 : ℝ) • (1 : Clnn n) else 0)) *
          (cre n k * ann n l -
            (if k = l then (1 / 2 : ℝ) • (1 : Clnn n) else 0)) -
        (cre n k * ann n l -
            (if k = l then (1 / 2 : ℝ) • (1 : Clnn n) else 0)) *
          (cre n i * ann n j -
            (if i = j then (1 / 2 : ℝ) • (1 : Clnn n) else 0)) =
        (cre n i * ann n j) * (cre n k * ann n l) -
          (cre n k * ann n l) * (cre n i * ann n j) := by
            by_cases hij : i = j <;> by_cases hkl : k = l <;>
              simp [hij, hkl, mul_sub, sub_mul, Algebra.smul_def,
                Algebra.commutes]
              <;> noncomm_ring
    _ = ((cre n i * ann n j) * cre n k -
          cre n k * (cre n i * ann n j)) * ann n l +
        cre n k * ((cre n i * ann n j) * ann n l -
          ann n l * (cre n i * ann n j)) := by
            exact commutator_mul_right (cre n i * ann n j) (cre n k) (ann n l)
    _ = (if j = k then cre n i else 0) * ann n l +
        cre n k * (if i = l then -(ann n j) else 0) := by
          rw [cre_ann_raw_commutator_cre, cre_ann_raw_commutator_ann]
    _ = (if j = k then
          (cre n i * ann n l -
            (if i = l then (1 / 2 : ℝ) • (1 : Clnn n) else 0)) else 0) -
        (if i = l then
          (cre n k * ann n j -
            (if k = j then (1 / 2 : ℝ) • (1 : Clnn n) else 0)) else 0) := by
          by_cases hjk : j = k <;> by_cases hil : i = l <;>
            simp_all [eq_comm]
            <;> noncomm_ring

theorem mixedGenerator_commutator_cre_cre
    (n : ℕ) (i j k l : Fin n) :
    mixedGenerator n i j * (cre n k * cre n l) -
        (cre n k * cre n l) * mixedGenerator n i j =
      (if j = k then cre n i * cre n l else 0) +
        (if j = l then cre n k * cre n i else 0) := by
  calc
    mixedGenerator n i j * (cre n k * cre n l) -
        (cre n k * cre n l) * mixedGenerator n i j =
        (mixedGenerator n i j * cre n k - cre n k * mixedGenerator n i j) *
            cre n l +
          cre n k * (mixedGenerator n i j * cre n l -
            cre n l * mixedGenerator n i j) := by
              exact commutator_mul_right (mixedGenerator n i j) (cre n k) (cre n l)
    _ = (if j = k then cre n i else 0) * cre n l +
          cre n k * (if j = l then cre n i else 0) := by
            rw [mixedGenerator_commutator_cre, mixedGenerator_commutator_cre]
    _ = (if j = k then cre n i * cre n l else 0) +
          (if j = l then cre n k * cre n i else 0) := by
            by_cases hjk : j = k <;> by_cases hjl : j = l <;>
              simp [hjk, hjl]

theorem mixedGenerator_commutator_ann_ann
    (n : ℕ) (i j k l : Fin n) :
    mixedGenerator n i j * (ann n k * ann n l) -
        (ann n k * ann n l) * mixedGenerator n i j =
      (if i = k then -(ann n j) * ann n l else 0) +
        (if i = l then ann n k * (-(ann n j)) else 0) := by
  calc
    mixedGenerator n i j * (ann n k * ann n l) -
        (ann n k * ann n l) * mixedGenerator n i j =
        (mixedGenerator n i j * ann n k - ann n k * mixedGenerator n i j) *
            ann n l +
          ann n k * (mixedGenerator n i j * ann n l -
            ann n l * mixedGenerator n i j) := by
              exact commutator_mul_right (mixedGenerator n i j) (ann n k) (ann n l)
    _ = (if i = k then -(ann n j) else 0) * ann n l +
          ann n k * (if i = l then -(ann n j) else 0) := by
            rw [mixedGenerator_commutator_ann, mixedGenerator_commutator_ann]
    _ = (if i = k then -(ann n j) * ann n l else 0) +
          (if i = l then ann n k * (-(ann n j)) else 0) := by
            by_cases hik : i = k <;> by_cases hil : i = l <;>
              simp [hik, hil]

theorem cre_cre_commutator_ann_ann
    (n : ℕ) (i j k l : Fin n) :
    (cre n i * cre n j) * (ann n k * ann n l) -
        (ann n k * ann n l) * (cre n i * cre n j) =
      ((if j = k then cre n i else 0) -
          (if i = k then cre n j else 0)) * ann n l +
        ann n k * ((if j = l then cre n i else 0) -
          (if i = l then cre n j else 0)) := by
  calc
    (cre n i * cre n j) * (ann n k * ann n l) -
        (ann n k * ann n l) * (cre n i * cre n j) =
        ((cre n i * cre n j) * ann n k -
            ann n k * (cre n i * cre n j)) * ann n l +
          ann n k * ((cre n i * cre n j) * ann n l -
            ann n l * (cre n i * cre n j)) := by
              exact commutator_mul_right (cre n i * cre n j) (ann n k) (ann n l)
    _ = ((if j = k then cre n i else 0) -
          (if i = k then cre n j else 0)) * ann n l +
        ann n k * ((if j = l then cre n i else 0) -
          (if i = l then cre n j else 0)) := by
            rw [cre_cre_commutator_ann, cre_cre_commutator_ann]

theorem ann_ann_commutator_cre_cre
    (n : ℕ) (i j k l : Fin n) :
    (ann n i * ann n j) * (cre n k * cre n l) -
        (cre n k * cre n l) * (ann n i * ann n j) =
      ((if j = k then ann n i else 0) -
          (if i = k then ann n j else 0)) * cre n l +
        cre n k * ((if j = l then ann n i else 0) -
          (if i = l then ann n j else 0)) := by
  calc
    (ann n i * ann n j) * (cre n k * cre n l) -
        (cre n k * cre n l) * (ann n i * ann n j) =
        ((ann n i * ann n j) * cre n k -
            cre n k * (ann n i * ann n j)) * cre n l +
          cre n k * ((ann n i * ann n j) * cre n l -
            cre n l * (ann n i * ann n j)) := by
              exact commutator_mul_right (ann n i * ann n j) (cre n k) (cre n l)
    _ = ((if j = k then ann n i else 0) -
          (if i = k then ann n j else 0)) * cre n l +
        cre n k * ((if j = l then ann n i else 0) -
          (if i = l then ann n j else 0)) := by
            rw [ann_ann_commutator_cre, ann_ann_commutator_cre]

theorem cre_cre_commutator_cre
    (n : ℕ) (i j k : Fin n) :
    (cre n i * cre n j) * cre n k -
        cre n k * (cre n i * cre n j) = 0 := by
  have hjk : cre n j * cre n k = -(cre n k * cre n j) :=
    eq_neg_of_add_eq_zero_left (cre_cre_anticomm n j k)
  have hik : cre n i * cre n k = -(cre n k * cre n i) :=
    eq_neg_of_add_eq_zero_left (cre_cre_anticomm n i k)
  calc
    (cre n i * cre n j) * cre n k -
        cre n k * (cre n i * cre n j) =
        cre n i * (cre n j * cre n k) -
          cre n k * (cre n i * cre n j) := by noncomm_ring
    _ = cre n i * (-(cre n k * cre n j)) -
          cre n k * (cre n i * cre n j) := by rw [hjk]
    _ = -((cre n i * cre n k) * cre n j) -
          cre n k * (cre n i * cre n j) := by noncomm_ring
    _ = -((-(cre n k * cre n i)) * cre n j) -
          cre n k * (cre n i * cre n j) := by rw [hik]
    _ = 0 := by noncomm_ring

theorem ann_ann_commutator_ann
    (n : ℕ) (i j k : Fin n) :
    (ann n i * ann n j) * ann n k -
        ann n k * (ann n i * ann n j) = 0 := by
  have hjk : ann n j * ann n k = -(ann n k * ann n j) :=
    eq_neg_of_add_eq_zero_left (ann_ann_anticomm n j k)
  have hik : ann n i * ann n k = -(ann n k * ann n i) :=
    eq_neg_of_add_eq_zero_left (ann_ann_anticomm n i k)
  calc
    (ann n i * ann n j) * ann n k -
        ann n k * (ann n i * ann n j) =
        ann n i * (ann n j * ann n k) -
          ann n k * (ann n i * ann n j) := by noncomm_ring
    _ = ann n i * (-(ann n k * ann n j)) -
          ann n k * (ann n i * ann n j) := by rw [hjk]
    _ = -((ann n i * ann n k) * ann n j) -
          ann n k * (ann n i * ann n j) := by noncomm_ring
    _ = -((-(ann n k * ann n i)) * ann n j) -
          ann n k * (ann n i * ann n j) := by rw [hik]
    _ = 0 := by noncomm_ring

theorem cre_cre_commutator_cre_cre
    (n : ℕ) (i j k l : Fin n) :
    (cre n i * cre n j) * (cre n k * cre n l) -
        (cre n k * cre n l) * (cre n i * cre n j) = 0 := by
  calc
    (cre n i * cre n j) * (cre n k * cre n l) -
        (cre n k * cre n l) * (cre n i * cre n j) =
        ((cre n i * cre n j) * cre n k -
            cre n k * (cre n i * cre n j)) * cre n l +
          cre n k * ((cre n i * cre n j) * cre n l -
            cre n l * (cre n i * cre n j)) := by
              exact commutator_mul_right (cre n i * cre n j) (cre n k) (cre n l)
    _ = 0 := by rw [cre_cre_commutator_cre, cre_cre_commutator_cre]; simp

theorem ann_ann_commutator_ann_ann
    (n : ℕ) (i j k l : Fin n) :
    (ann n i * ann n j) * (ann n k * ann n l) -
        (ann n k * ann n l) * (ann n i * ann n j) = 0 := by
  calc
    (ann n i * ann n j) * (ann n k * ann n l) -
        (ann n k * ann n l) * (ann n i * ann n j) =
        ((ann n i * ann n j) * ann n k -
            ann n k * (ann n i * ann n j)) * ann n l +
          ann n k * ((ann n i * ann n j) * ann n l -
            ann n l * (ann n i * ann n j)) := by
              exact commutator_mul_right (ann n i * ann n j) (ann n k) (ann n l)
    _ = 0 := by rw [ann_ann_commutator_ann, ann_ann_commutator_ann]; simp

/-! ### Bridge to the existing generic grade interface

The generic `HasOperatorGrade` predicate and its product-routing theorem live
in `ChiralRetainedWordFiveGradeClosure`.  These lemmas only instantiate that
interface with the native centered Clifford number operator.
-/

theorem hasOperatorGrade_cre (n : ℕ) (i : Fin n) :
    HasOperatorGrade (centeredNumberOperator n) (cre n i) 1 := by
  simpa [HasOperatorGrade] using centeredNumberOperator_commutator_cre n i

theorem hasOperatorGrade_ann (n : ℕ) (i : Fin n) :
    HasOperatorGrade (centeredNumberOperator n) (ann n i) (-1) := by
  simpa [HasOperatorGrade] using centeredNumberOperator_commutator_ann n i

theorem hasOperatorGrade_cre_cre (n : ℕ) (i j : Fin n) :
    HasOperatorGrade (centeredNumberOperator n) (cre n i * cre n j) 2 := by
  simpa [HasOperatorGrade] using centeredNumberOperator_commutator_cre_cre n i j

theorem hasOperatorGrade_ann_ann (n : ℕ) (i j : Fin n) :
    HasOperatorGrade (centeredNumberOperator n) (ann n i * ann n j) (-2) := by
  simpa [HasOperatorGrade] using centeredNumberOperator_commutator_ann_ann n i j

theorem hasOperatorGrade_cre_ann (n : ℕ) (i j : Fin n) :
    HasOperatorGrade (centeredNumberOperator n) (cre n i * ann n j) 0 := by
  simpa [HasOperatorGrade] using centeredNumberOperator_commutator_cre_ann n i j

theorem hasOperatorGrade_ann_cre (n : ℕ) (i j : Fin n) :
    HasOperatorGrade (centeredNumberOperator n) (ann n i * cre n j) 0 := by
  simpa [HasOperatorGrade] using centeredNumberOperator_commutator_ann_cre n i j

theorem hasOperatorGrade_mixedGenerator (n : ℕ) (i j : Fin n) :
    HasOperatorGrade (centeredNumberOperator n) (mixedGenerator n i j) 0 := by
  simpa [HasOperatorGrade] using centeredNumberOperator_commutator_mixedGenerator n i j

/-! ### Native Witt sectors

These are the actual real submodules generated by the native Witt words.  They
are deliberately defined here, from the Clifford operators themselves, rather
than by introducing another carrier or another copy of the generic grading
interface.  The following inclusions record the grade content of the five
native sectors; closure under the ordinary commutator is supplied by the
generator identities above together with `grade_commutator`.
-/

def wittNegTwo (n : ℕ) : Submodule ℝ (Clnn n) :=
  Submodule.span ℝ (Set.range (fun ij : Fin n × Fin n =>
    ann n ij.1 * ann n ij.2))

def wittNegOne (n : ℕ) : Submodule ℝ (Clnn n) :=
  Submodule.span ℝ (Set.range (ann n))

def wittZero (n : ℕ) : Submodule ℝ (Clnn n) :=
  Submodule.span ℝ (Set.range (fun ij : Fin n × Fin n =>
    mixedGenerator n ij.1 ij.2))

def wittPosOne (n : ℕ) : Submodule ℝ (Clnn n) :=
  Submodule.span ℝ (Set.range (cre n))

def wittPosTwo (n : ℕ) : Submodule ℝ (Clnn n) :=
  Submodule.span ℝ (Set.range (fun ij : Fin n × Fin n =>
    cre n ij.1 * cre n ij.2))

theorem wittNegTwo_le_gradeSubmodule (n : ℕ) :
    wittNegTwo n ≤ gradeSubmodule (centeredNumberOperator n) (-2) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact hasOperatorGrade_ann_ann n i j

theorem wittNegOne_le_gradeSubmodule (n : ℕ) :
    wittNegOne n ≤ gradeSubmodule (centeredNumberOperator n) (-1) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact hasOperatorGrade_ann n i

theorem wittZero_le_gradeSubmodule (n : ℕ) :
    wittZero n ≤ gradeSubmodule (centeredNumberOperator n) 0 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact hasOperatorGrade_mixedGenerator n i j

theorem wittPosOne_le_gradeSubmodule (n : ℕ) :
    wittPosOne n ≤ gradeSubmodule (centeredNumberOperator n) 1 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact hasOperatorGrade_cre n i

theorem wittPosTwo_le_gradeSubmodule (n : ℕ) :
    wittPosTwo n ≤ gradeSubmodule (centeredNumberOperator n) 2 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact hasOperatorGrade_cre_cre n i j

theorem wittPosOne_commutator_mem_wittPosTwo
    (n : ℕ) {X Y : Clnn n}
    (hX : X ∈ wittPosOne n) (hY : Y ∈ wittPosOne n) :
    X * Y - Y * X ∈ wittPosTwo n := by
  have hsmul_right : ∀ (c : ℝ) (x y : Clnn n),
      x * (c • y) - (c • y) * x = c • (x * y - y * x) := by
    intro c x y
    simp only [Algebra.smul_def]
    calc
      x * ((algebraMap ℝ (Clnn n)) c * y) -
          ((algebraMap ℝ (Clnn n)) c * y) * x =
          ((algebraMap ℝ (Clnn n)) c * x) * y -
            ((algebraMap ℝ (Clnn n)) c * y) * x := by
              rw [← mul_assoc x (algebraMap ℝ (Clnn n) c) y,
                ← Algebra.commutes c x]
      _ = (algebraMap ℝ (Clnn n)) c * (x * y) -
            (algebraMap ℝ (Clnn n)) c * (y * x) := by
              rw [mul_assoc, mul_assoc]
      _ = (algebraMap ℝ (Clnn n)) c * (x * y - y * x) := by
            noncomm_ring
  have hsmul_left : ∀ (c : ℝ) (x y : Clnn n),
      (c • x) * y - y * (c • x) = c • (x * y - y * x) := by
    intro c x y
    simp only [Algebra.smul_def]
    calc
      ((algebraMap ℝ (Clnn n)) c * x) * y -
          y * ((algebraMap ℝ (Clnn n)) c * x) =
          (algebraMap ℝ (Clnn n)) c * (x * y) -
            ((algebraMap ℝ (Clnn n)) c * y) * x := by
              rw [← mul_assoc y (algebraMap ℝ (Clnn n) c) x,
                ← Algebra.commutes c y]
              noncomm_ring
      _ = (algebraMap ℝ (Clnn n)) c * (x * y - y * x) := by
            noncomm_ring
  refine Submodule.span_induction
    (p := fun X _ => X * Y - Y * X ∈ wittPosTwo n)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => cre n i * Y - Y * cre n i ∈ wittPosTwo n)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨j, rfl⟩
      rw [cre_cre_commutator]
      exact (wittPosTwo n).smul_mem 2
        (Submodule.subset_span (Set.mem_range_self (i, j)))
    · simpa using (Submodule.zero_mem (wittPosTwo n))
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [show cre n i * (y₁ + y₂) - (y₁ + y₂) * cre n i =
          (cre n i * y₁ - y₁ * cre n i) +
            (cre n i * y₂ - y₂ * cre n i) by noncomm_ring]
      exact (wittPosTwo n).add_mem hy₁ hy₂
    · intro c y _ hy
      rw [hsmul_right c (cre n i) y]
      exact (wittPosTwo n).smul_mem c hy
  · simpa using (Submodule.zero_mem (wittPosTwo n))
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [show (x₁ + x₂) * Y - Y * (x₁ + x₂) =
        (x₁ * Y - Y * x₁) + (x₂ * Y - Y * x₂) by noncomm_ring]
    exact (wittPosTwo n).add_mem hx₁ hx₂
  · intro c x _ hx
    rw [hsmul_left c x Y]
    exact (wittPosTwo n).smul_mem c hx

theorem wittZero_commutator_mem_wittZero
    (n : ℕ) {X Y : Clnn n}
    (hX : X ∈ wittZero n) (hY : Y ∈ wittZero n) :
    X * Y - Y * X ∈ wittZero n := by
  have hsmul_right : ∀ (c : ℝ) (x y : Clnn n),
      x * (c • y) - (c • y) * x = c • (x * y - y * x) := by
    intro c x y
    simp only [Algebra.smul_def]
    calc
      x * ((algebraMap ℝ (Clnn n)) c * y) -
          ((algebraMap ℝ (Clnn n)) c * y) * x =
          ((algebraMap ℝ (Clnn n)) c * x) * y -
            ((algebraMap ℝ (Clnn n)) c * y) * x := by
              rw [← mul_assoc x (algebraMap ℝ (Clnn n) c) y,
                ← Algebra.commutes c x]
      _ = (algebraMap ℝ (Clnn n)) c * (x * y) -
            (algebraMap ℝ (Clnn n)) c * (y * x) := by
              rw [mul_assoc, mul_assoc]
      _ = (algebraMap ℝ (Clnn n)) c * (x * y - y * x) := by
            noncomm_ring
  have hsmul_left : ∀ (c : ℝ) (x y : Clnn n),
      (c • x) * y - y * (c • x) = c • (x * y - y * x) := by
    intro c x y
    simp only [Algebra.smul_def]
    calc
      ((algebraMap ℝ (Clnn n)) c * x) * y -
          y * ((algebraMap ℝ (Clnn n)) c * x) =
          (algebraMap ℝ (Clnn n)) c * (x * y) -
            ((algebraMap ℝ (Clnn n)) c * y) * x := by
              rw [Algebra.commutes c y]
              noncomm_ring
      _ = (algebraMap ℝ (Clnn n)) c * (x * y - y * x) := by
            noncomm_ring
  refine Submodule.span_induction
    (p := fun X _ => X * Y - Y * X ∈ wittZero n)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨⟨i, j⟩, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => mixedGenerator n i j * Y -
        Y * mixedGenerator n i j ∈ wittZero n)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨⟨k, l⟩, rfl⟩
      rw [mixedGenerator_commutator_mixedGenerator]
      by_cases hjk : j = k
      · by_cases hil : i = l
        · simp only [if_pos hjk, if_pos hil]
          exact (wittZero n).sub_mem
            (Submodule.subset_span (Set.mem_range_self (i, l)))
            (Submodule.subset_span (Set.mem_range_self (k, j)))
        · simp only [if_pos hjk, if_neg hil]
          exact (wittZero n).sub_mem
            (Submodule.subset_span (Set.mem_range_self (i, l)))
            (Submodule.zero_mem _)
      · by_cases hil : i = l
        · simp only [if_neg hjk, if_pos hil]
          exact (wittZero n).sub_mem
            (Submodule.zero_mem _)
            (Submodule.subset_span (Set.mem_range_self (k, j)))
        · simp only [if_neg hjk, if_neg hil]
          simpa using (Submodule.zero_mem (wittZero n))
    · simpa using (Submodule.zero_mem (wittZero n))
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [show mixedGenerator n i j * (y₁ + y₂) -
          (y₁ + y₂) * mixedGenerator n i j =
          (mixedGenerator n i j * y₁ - y₁ * mixedGenerator n i j) +
            (mixedGenerator n i j * y₂ - y₂ * mixedGenerator n i j) by
              noncomm_ring]
      exact (wittZero n).add_mem hy₁ hy₂
    · intro c y _ hy
      rw [hsmul_right c (mixedGenerator n i j) y]
      exact (wittZero n).smul_mem c hy
  · simpa using (Submodule.zero_mem (wittZero n))
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [show (x₁ + x₂) * Y - Y * (x₁ + x₂) =
        (x₁ * Y - Y * x₁) + (x₂ * Y - Y * x₂) by noncomm_ring]
    exact (wittZero n).add_mem hx₁ hx₂
  · intro c x _ hx
    rw [hsmul_left c x Y]
    exact (wittZero n).smul_mem c hx

end InfoGeometry.OperatorAlgebra.CliffordCAR
