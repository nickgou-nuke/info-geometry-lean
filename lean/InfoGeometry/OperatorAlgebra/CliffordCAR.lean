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

/-! Native quadratic sectors used by the CAR Lie-closure owner. -/

def mixedGenerator (n : ℕ) (i j : Fin n) : Clnn n :=
  cre n i * ann n j - (if i = j then (1 / 2 : ℝ) • (1 : Clnn n) else 0)

def wittNegTwo (n : ℕ) : Submodule ℝ (Clnn n) :=
  Submodule.span ℝ (Set.range (fun ij : Fin n × Fin n =>
    ann n ij.1 * ann n ij.2))

def wittZero (n : ℕ) : Submodule ℝ (Clnn n) :=
  Submodule.span ℝ (Set.range (fun ij : Fin n × Fin n =>
    mixedGenerator n ij.1 ij.2))

def wittPosTwo (n : ℕ) : Submodule ℝ (Clnn n) :=
  Submodule.span ℝ (Set.range (fun ij : Fin n × Fin n =>
    cre n ij.1 * cre n ij.2))

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

theorem cre_cre_commutator (n : ℕ) (i j : Fin n) :
    cre n i * cre n j - cre n j * cre n i =
      (2 : ℝ) • (cre n i * cre n j) := by
  have h := cre_cre_anticomm n i j
  have hswap : cre n j * cre n i = -(cre n i * cre n j) :=
    eq_neg_of_add_eq_zero_right h
  rw [hswap, two_smul]
  simp [sub_eq_add_neg]

theorem ann_ann_commutator (n : ℕ) (i j : Fin n) :
    ann n i * ann n j - ann n j * ann n i =
      (2 : ℝ) • (ann n i * ann n j) := by
  have h := ann_ann_anticomm n i j
  have hswap : ann n j * ann n i = -(ann n i * ann n j) :=
    eq_neg_of_add_eq_zero_right h
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

private theorem cre_ann_raw_commutator_cre (n : ℕ) (i j k : Fin n) :
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

private theorem cre_ann_raw_commutator_ann (n : ℕ) (i j k : Fin n) :
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
      _ = 0 := by rw [haa]; noncomm_ring

theorem mixedGenerator_commutator_cre (n : ℕ) (i j k : Fin n) :
    mixedGenerator n i j * cre n k - cre n k * mixedGenerator n i j =
      if j = k then cre n i else 0 := by
  simpa [mixedGenerator, sub_mul, mul_sub] using
    cre_ann_raw_commutator_cre n i j k

theorem mixedGenerator_commutator_ann (n : ℕ) (i j k : Fin n) :
    mixedGenerator n i j * ann n k - ann n k * mixedGenerator n i j =
      if i = k then -(ann n j) else 0 := by
  simpa [mixedGenerator, sub_mul, mul_sub] using
    cre_ann_raw_commutator_ann n i j k

theorem commutator_mul_right {n : ℕ} (X Y Z : Clnn n) :
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
    _ = (cre n i * ann n j) * (cre n k * ann n l) -
          (cre n k * ann n l) * (cre n i * ann n j) := by
      by_cases hij : i = j <;> by_cases hkl : k = l <;>
        simp [hij, hkl, mul_sub, sub_mul, Algebra.smul_def, Algebra.commutes]
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

theorem cre_cre_commutator_cre (n : ℕ) (i j k : Fin n) :
    (cre n i * cre n j) * cre n k - cre n k * (cre n i * cre n j) = 0 := by
  have hjk := eq_neg_of_add_eq_zero_left (cre_cre_anticomm n j k)
  have hik := eq_neg_of_add_eq_zero_left (cre_cre_anticomm n i k)
  calc
    _ = cre n i * (cre n j * cre n k) - cre n k * (cre n i * cre n j) := by
      noncomm_ring
    _ = cre n i * (-(cre n k * cre n j)) -
        cre n k * (cre n i * cre n j) := by rw [hjk]
    _ = -((cre n i * cre n k) * cre n j) -
        cre n k * (cre n i * cre n j) := by noncomm_ring
    _ = -((-(cre n k * cre n i)) * cre n j) -
        cre n k * (cre n i * cre n j) := by rw [hik]
    _ = 0 := by noncomm_ring

theorem ann_ann_commutator_ann (n : ℕ) (i j k : Fin n) :
    (ann n i * ann n j) * ann n k - ann n k * (ann n i * ann n j) = 0 := by
  have hjk := eq_neg_of_add_eq_zero_left (ann_ann_anticomm n j k)
  have hik := eq_neg_of_add_eq_zero_left (ann_ann_anticomm n i k)
  calc
    _ = ann n i * (ann n j * ann n k) - ann n k * (ann n i * ann n j) := by
      noncomm_ring
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
    _ = ((cre n i * cre n j) * cre n k -
        cre n k * (cre n i * cre n j)) * cre n l +
        cre n k * ((cre n i * cre n j) * cre n l -
          cre n l * (cre n i * cre n j)) := by
      exact commutator_mul_right (cre n i * cre n j) (cre n k) (cre n l)
    _ = 0 := by
      rw [show (cre n i * cre n j) * cre n k -
          cre n k * (cre n i * cre n j) = 0 by
            exact cre_cre_commutator_cre n i j k,
        show (cre n i * cre n j) * cre n l -
          cre n l * (cre n i * cre n j) = 0 by
            exact cre_cre_commutator_cre n i j l]
      simp

theorem ann_ann_commutator_ann_ann
    (n : ℕ) (i j k l : Fin n) :
    (ann n i * ann n j) * (ann n k * ann n l) -
        (ann n k * ann n l) * (ann n i * ann n j) = 0 := by
  calc
    _ = ((ann n i * ann n j) * ann n k -
        ann n k * (ann n i * ann n j)) * ann n l +
        ann n k * ((ann n i * ann n j) * ann n l -
          ann n l * (ann n i * ann n j)) := by
      exact commutator_mul_right (ann n i * ann n j) (ann n k) (ann n l)
    _ = 0 := by
      rw [show (ann n i * ann n j) * ann n k -
          ann n k * (ann n i * ann n j) = 0 by
            exact ann_ann_commutator_ann n i j k,
        show (ann n i * ann n j) * ann n l -
          ann n l * (ann n i * ann n j) = 0 by
            exact ann_ann_commutator_ann n i j l]
      simp

end InfoGeometry.OperatorAlgebra.CliffordCAR
