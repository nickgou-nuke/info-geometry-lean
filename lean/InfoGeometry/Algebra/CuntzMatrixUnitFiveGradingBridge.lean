/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzMatrixUnits
import InfoGeometry.Algebra.CuntzSuperalgebra
import InfoGeometry.Physics.TripotentAdjointDerivation
import InfoGeometry.Algebra.FiveGradedIwasawaNilpotency
import InfoGeometry.Core.TripotentAdjoint

/-!
# Five-grade weights on the finite Cuntz matrix-unit sector

For `E i j = S i S j†`, the native matrix-unit law gives
`E i j * E k l = δ(j,k) E i l`.  The grading below is only the finite
matrix-unit sector of `CuntzAlg 3`; it is not a decomposition theorem for the
whole Cuntz algebra and it is not a TKK property.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzMatrixUnits
open InfoGeometry.Algebra.CuntzSuperalgebra

abbrev Cuntz3 := CuntzAlg 3

def hop (i j : Fin 3) : Cuntz3 := E 3 i j

def commutator (x y : Cuntz3) : Cuntz3 := x * y - y * x

def colourWeight (i : Fin 3) : ℤ :=
  if i = 0 then 1 else if i = 1 then -1 else 0

def gradingOp : Cuntz3 := hop 0 0 - hop 1 1

def IsGradedComponent (h : Cuntz3) (k : ℂ) (x : Cuntz3) : Prop :=
  commutator h x = k • x

theorem commutator_mem_grade_add
    {p q : ℂ} {x y : Cuntz3}
    (hx : IsGradedComponent gradingOp p x)
    (hy : IsGradedComponent gradingOp q y) :
    IsGradedComponent gradingOp (p + q) (commutator x y) := by
  change InfoGeometry.Physics.Algebra.adOp gradingOp (x * y - y * x) =
    (p + q) • (x * y - y * x)
  change InfoGeometry.Physics.Algebra.adOp gradingOp x = p • x at hx
  change InfoGeometry.Physics.Algebra.adOp gradingOp y = q • y at hy
  have hxy :
      InfoGeometry.Physics.Algebra.adOp gradingOp (x * y) =
        (p + q) • (x * y) := by
    rw [InfoGeometry.Physics.Algebra.adOp_mul, hx, hy]
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← add_smul]
  have hyx :
      InfoGeometry.Physics.Algebra.adOp gradingOp (y * x) =
        (p + q) • (y * x) := by
    rw [InfoGeometry.Physics.Algebra.adOp_mul, hy, hx]
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← add_smul]
    rw [add_comm]
  change InfoGeometry.Physics.Algebra.commutatorAction gradingOp
      (x * y - y * x) = (p + q) • (x * y - y * x)
  change InfoGeometry.Physics.Algebra.commutatorAction gradingOp (x * y) =
      (p + q) • (x * y) at hxy
  change InfoGeometry.Physics.Algebra.commutatorAction gradingOp (y * x) =
      (p + q) • (y * x) at hyx
  rw [InfoGeometry.Physics.Algebra.commutatorAction_sub, hxy, hyx,
    smul_sub]
theorem hop_mul_hop (i j k l : Fin 3) :
    hop i j * hop k l = if j = k then hop i l else 0 := by
  exact matrix_unit_mul 3 i j k l

/-- The matrix-unit hopping sector is even for the native Cuntz parity. -/
theorem parity_hop (i j : Fin 3) :
    parity 3 (hop i j) = hop i j := by
  calc
    parity 3 (hop i j) =
        parity 3 (cuntzS 3 i) * parity 3 (cuntzSdag 3 j) := by
      rw [hop, E, map_mul]
    _ = (-cuntzS 3 i) * (-cuntzSdag 3 j) := by
      rw [parity_S, parity_Sdag]
    _ = hop i j := by
      change
        (- (cuntzS 3 i) : CuntzAlg 3) *
            (- (cuntzSdag 3 j) : CuntzAlg 3) =
          cuntzS 3 i * cuntzSdag 3 j
      exact neg_mul_neg (cuntzS 3 i) (cuntzSdag 3 j)

/-- The Cartan grading operator belongs to the even Cuntz sector. -/
theorem parity_gradingOp :
    parity 3 gradingOp = gradingOp := by
  rw [gradingOp, map_sub, parity_hop, parity_hop]

theorem gradingOp_comm_hop (i j : Fin 3) :
    commutator (gradingOp) (hop i j) =
      ((colourWeight i - colourWeight j : ℤ) : ℂ) • hop i j := by
  fin_cases i <;> fin_cases j <;>
    simp [commutator, gradingOp, hop, colourWeight,
      sub_mul, mul_sub, matrix_unit_mul, one_smul, two_smul] <;>
    module

theorem hop_mem_grade (i j : Fin 3) :
    IsGradedComponent gradingOp
      ((colourWeight i - colourWeight j : ℤ) : ℂ) (hop i j) := by
  exact gradingOp_comm_hop i j

theorem hop_zero_one_mem_grade_two :
    IsGradedComponent gradingOp 2 (hop 0 1) := by
  unfold IsGradedComponent
  simpa [colourWeight] using gradingOp_comm_hop 0 1

theorem hop_one_zero_mem_grade_neg_two :
    IsGradedComponent gradingOp (-2) (hop 1 0) := by
  unfold IsGradedComponent
  simpa [colourWeight] using gradingOp_comm_hop 1 0

theorem hop_zero_two_mem_grade_one :
    IsGradedComponent gradingOp 1 (hop 0 2) := by
  change commutator gradingOp (hop 0 2) = (1 : ℂ) • hop 0 2
  simpa [colourWeight] using gradingOp_comm_hop 0 2

theorem hop_two_zero_mem_grade_neg_one :
    IsGradedComponent gradingOp (-1) (hop 2 0) := by
  unfold IsGradedComponent
  simpa [colourWeight] using gradingOp_comm_hop 2 0

theorem hop_two_two_mem_grade_zero :
    IsGradedComponent gradingOp 0 (hop 2 2) := by
  change commutator gradingOp (hop 2 2) = (0 : ℂ) • hop 2 2
  simpa [colourWeight] using gradingOp_comm_hop 2 2

theorem gradingOp_sq :
    gradingOp * gradingOp = hop 0 0 + hop 1 1 := by
  unfold gradingOp
  simp only [sub_mul, mul_sub, hop_mul_hop]
  norm_num

theorem gradingOp_cube :
    gradingOp * gradingOp * gradingOp = gradingOp := by
  calc
    gradingOp * gradingOp * gradingOp =
        (gradingOp * gradingOp) * gradingOp := rfl
    _ = (hop 0 0 + hop 1 1) * gradingOp := by rw [gradingOp_sq]
    _ = gradingOp := by
      simp [gradingOp, hop, add_mul, mul_sub, matrix_unit_mul]

section GeneralTripotentIwasawa

open InfoGeometry.Algebra.FiveGradedIwasawa
open InfoGeometry.Core.TripotentAdjoint

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private theorem ad_pow_of_inGrade {A : Type*} [Ring A] [Algebra ℝ A]
    {t x : A} {j : ℝ} (hx : InGrade t j x) (m : ℕ) :
    (LieAlgebra.ad ℝ A t ^ m) x = j ^ m • x := by
  induction m with
  | zero =>
      simp only [pow_zero, Module.End.one_apply, one_smul]
  | succ m ihm =>
      rw [pow_succ', Module.End.mul_apply, ihm, map_smul]
      have h1 : LieAlgebra.ad ℝ A t x = j • x := hx
      rw [h1, smul_smul, pow_succ']
      congr 1
      ring

theorem isFiveGraded_of_tripotent {A : Type*} [Ring A] [Algebra ℝ A]
    {t : A} (ht : t * t * t = t) : IsFiveGraded t where
  grade_bound j x hjx hnot := by
    have hq := congrArg (fun f : Module.End ℝ A => f x) (ad_quintic (A := A) ht)
    simp only [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, ad_pow_of_inGrade hjx 5, ad_pow_of_inGrade hjx 3] at hq
    have h1 : LieAlgebra.ad ℝ A t x = j • x := hjx
    rw [h1, smul_smul, smul_smul] at hq
    have hcomb : (j ^ 5 - 5 * j ^ 3 + 4 * j) • x = 0 := by
      calc
        (j ^ 5 - 5 * j ^ 3 + 4 * j) • x =
            (j ^ 5 - 5 * j ^ 3) • x + (4 * j) • x := add_smul _ _ _
        _ = (j ^ 5 • x - (5 * j ^ 3) • x) + (4 * j) • x := by rw [sub_smul]
        _ = 0 := hq
    have hpoly_ne : j ^ 5 - 5 * j ^ 3 + 4 * j ≠ 0 := by
      have hfac : j ^ 5 - 5 * j ^ 3 + 4 * j =
          j * (j - 1) * (j + 1) * (j - 2) * (j + 2) := by ring
      rw [hfac]
      rcases hnot with ⟨hn2, hn1, h0, hp1, hp2⟩
      intro hzero
      simp only [mul_eq_zero] at hzero
      rcases hzero with (((h0' | hm1) | hp1') | hm2) | hp2'
      · exact h0 h0'
      · exact hp1 (sub_eq_zero.mp hm1)
      · exact hn1 (add_eq_zero_iff_eq_neg.mp hp1')
      · exact hp2 (sub_eq_zero.mp hm2)
      · exact hn2 (add_eq_zero_iff_eq_neg.mp hp2')
    have hcancel := congrArg ((j ^ 5 - 5 * j ^ 3 + 4 * j)⁻¹ • ·) hcomb
    rw [smul_smul, inv_mul_cancel₀ hpoly_ne, one_smul, smul_zero] at hcancel
    exact hcancel

/-- Any Lie subalgebra `S` of an associative `ℝ`-algebra containing a tripotent `t`
inherits `IsFiveGraded ⟨t, htS⟩`. -/
theorem isFiveGraded_of_lieSubalgebra_tripotent {A : Type*} [Ring A] [Algebra ℝ A]
    (S : LieSubalgebra ℝ A) {t : A} (htS : t ∈ S) (ht : t * t * t = t) :
    IsFiveGraded (⟨t, htS⟩ : S) where
  grade_bound j x hjx hnot := by
    have hco : InGrade t j (x : A) := by
      have := congrArg (fun u : S => (u : A)) hjx
      exact this
    have hzero : (x : A) = 0 :=
      (isFiveGraded_of_tripotent (A := A) ht).grade_bound j (x : A) hco hnot
    exact Subtype.ext hzero

end GeneralTripotentIwasawa

section GeneralCuntzGrading

open InfoGeometry.Algebra.FiveGradedIwasawa

namespace ScopedCuntzInstances

/-- Scoped Lie ring structure on `CuntzAlg n` (kept inside a sub-namespace to avoid downstream diamonds). -/
scoped instance cuntzLieRing (n : ℕ) : LieRing (CuntzAlg n) :=
  LieRing.ofAssociativeRing

/-- Scoped real algebra structure on `CuntzAlg n` induced by `ℝ →+* ℂ`. -/
scoped instance cuntzRealAlgebra (n : ℕ) : Algebra ℝ (CuntzAlg n) :=
  Algebra.compHom (CuntzAlg n) (algebraMap ℝ ℂ)

/-- Scoped real Lie algebra structure on `CuntzAlg n`. -/
scoped instance cuntzRealLieAlgebra (n : ℕ) : LieAlgebra ℝ (CuntzAlg n) :=
  LieAlgebra.ofAssociativeAlgebra

end ScopedCuntzInstances

open scoped ScopedCuntzInstances

private theorem cuntz_real_smul_eq (n : ℕ) (r : ℝ) (x : CuntzAlg n) :
    r • x = ((r : ℂ) • x) := by
  change (algebraMap ℝ (CuntzAlg n) r) * x = (algebraMap ℂ (CuntzAlg n) (r : ℂ)) * x
  rfl

/-- Generalized diagonal color weight `+1` on `Splus`, `-1` on `Sminus`, `0` elsewhere
for disjoint subsets `Splus, Sminus : Finset (Fin n)`. -/
def genColourWeight (n : ℕ) (Splus Sminus : Finset (Fin n)) (i : Fin n) : ℤ :=
  (if i ∈ Splus then 1 else 0) - (if i ∈ Sminus then 1 else 0)

/-- Generalized Cartan grading operator `(∑ i ∈ Splus, E n i i) - (∑ j ∈ Sminus, E n j j)`
in `CuntzAlg n`. -/
def genGradingOp (n : ℕ) (Splus Sminus : Finset (Fin n)) : CuntzAlg n :=
  (∑ i ∈ Splus, E n i i) - (∑ j ∈ Sminus, E n j j)

private theorem sum_diag_E_mul_sum_diag_E (n : ℕ) (A B : Finset (Fin n)) :
    (∑ i ∈ A, E n i i) * (∑ j ∈ B, E n j j) = ∑ i ∈ A ∩ B, E n i i := by
  rw [Finset.sum_mul]
  have hterm : ∀ i ∈ A, E n i i * (∑ j ∈ B, E n j j) =
      if i ∈ B then E n i i else 0 := by
    intro i _
    rw [Finset.mul_sum]
    simp_rw [matrix_unit_mul]
    calc
      (∑ x ∈ B, if i = x then E n i x else 0) =
          ∑ x ∈ B, if i = x then E n i i else 0 := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        split_ifs with h
        · subst x; rfl
        · rfl
      _ = if i ∈ B then E n i i else 0 := Finset.sum_ite_eq B i (fun _ => E n i i)
  calc
    ∑ i ∈ A, E n i i * (∑ j ∈ B, E n j j) =
        ∑ i ∈ A, (if i ∈ B then E n i i else 0) := Finset.sum_congr rfl hterm
    _ = ∑ i ∈ A ∩ B, E n i i := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]

theorem genGradingOp_sq {n : ℕ} {Splus Sminus : Finset (Fin n)}
    (hdisj : Disjoint Splus Sminus) :
    genGradingOp n Splus Sminus * genGradingOp n Splus Sminus =
      (∑ i ∈ Splus, E n i i) + (∑ j ∈ Sminus, E n j j) := by
  unfold genGradingOp
  rw [sub_mul, mul_sub, mul_sub,
    sum_diag_E_mul_sum_diag_E, sum_diag_E_mul_sum_diag_E,
    sum_diag_E_mul_sum_diag_E, sum_diag_E_mul_sum_diag_E]
  rw [Finset.inter_self, Finset.inter_self,
    Finset.disjoint_iff_inter_eq_empty.mp hdisj,
    Finset.disjoint_iff_inter_eq_empty.mp hdisj.symm]
  simp only [Finset.sum_empty, sub_zero, zero_sub, sub_neg_eq_add]

theorem genGradingOp_cube {n : ℕ} {Splus Sminus : Finset (Fin n)}
    (hdisj : Disjoint Splus Sminus) :
    genGradingOp n Splus Sminus * genGradingOp n Splus Sminus *
        genGradingOp n Splus Sminus =
      genGradingOp n Splus Sminus := by
  rw [genGradingOp_sq hdisj]
  unfold genGradingOp
  rw [add_mul, mul_sub, mul_sub,
    sum_diag_E_mul_sum_diag_E, sum_diag_E_mul_sum_diag_E,
    sum_diag_E_mul_sum_diag_E, sum_diag_E_mul_sum_diag_E]
  rw [Finset.inter_self, Finset.inter_self,
    Finset.disjoint_iff_inter_eq_empty.mp hdisj,
    Finset.disjoint_iff_inter_eq_empty.mp hdisj.symm]
  simp only [Finset.sum_empty, sub_zero, zero_sub]
  abel

private theorem sum_diag_E_mul_E (n : ℕ) (S : Finset (Fin n)) (i j : Fin n) :
    (∑ k ∈ S, E n k k) * E n i j = if i ∈ S then E n i j else 0 := by
  rw [Finset.sum_mul]
  simp_rw [matrix_unit_mul]
  exact Finset.sum_ite_eq' S i (fun k => E n k j)

private theorem E_mul_sum_diag_E (n : ℕ) (S : Finset (Fin n)) (i j : Fin n) :
    E n i j * (∑ k ∈ S, E n k k) = if j ∈ S then E n i j else 0 := by
  rw [Finset.mul_sum]
  simp_rw [matrix_unit_mul]
  exact Finset.sum_ite_eq S j (fun k => E n i k)

/-- Generalized matrix-unit Lie bracket `[genGradingOp, E n i j]` for any `n : ℕ`
and any disjoint subsets `Splus, Sminus : Finset (Fin n)`. -/
theorem genGradingOp_lie_E (n : ℕ) (Splus Sminus : Finset (Fin n)) (i j : Fin n) :
    ⁅genGradingOp n Splus Sminus, E n i j⁆ =
      ((genColourWeight n Splus Sminus i - genColourWeight n Splus Sminus j : ℤ) : ℝ) •
        E n i j := by
  change genGradingOp n Splus Sminus * E n i j - E n i j * genGradingOp n Splus Sminus = _
  unfold genGradingOp
  rw [sub_mul, mul_sub, sum_diag_E_mul_E, sum_diag_E_mul_E,
    E_mul_sum_diag_E, E_mul_sum_diag_E, cuntz_real_smul_eq]
  unfold genColourWeight
  by_cases hi1 : i ∈ Splus <;> by_cases hi2 : i ∈ Sminus <;>
    by_cases hj1 : j ∈ Splus <;> by_cases hj2 : j ∈ Sminus <;>
    simp [hi1, hi2, hj1, hj2] <;> module

/-- Generalized `IsFiveGraded` theorem for any disjoint partition `(Splus, Sminus)` on
`CuntzAlg n`. -/
theorem genGradingOp_isFiveGraded {n : ℕ} {Splus Sminus : Finset (Fin n)}
    (hdisj : Disjoint Splus Sminus) :
    IsFiveGraded (genGradingOp n Splus Sminus) := by
  apply isFiveGraded_of_tripotent (A := CuntzAlg n)
  exact genGradingOp_cube hdisj

/-- Concrete `Cuntz3` `gradingOp` is a specialization of `genGradingOp 3 {0} {1}`. -/
theorem gradingOp_eq_genGradingOp :
    gradingOp = genGradingOp 3 ({0} : Finset (Fin 3)) ({1} : Finset (Fin 3)) := by
  unfold gradingOp genGradingOp hop
  simp only [Finset.sum_singleton]

namespace ScopedCuntzInstances

/-- Scoped `IsFiveGraded gradingOp` instance on `Cuntz3`. -/
scoped instance gradingOp_isFiveGraded : IsFiveGraded gradingOp := by
  rw [gradingOp_eq_genGradingOp]
  exact genGradingOp_isFiveGraded (by decide)

end ScopedCuntzInstances

end GeneralCuntzGrading

section GlobalCuntzLieSubalgebra

open scoped InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge.ScopedCuntzInstances
open InfoGeometry.Algebra.FiveGradedIwasawa

/-- Global real Lie subalgebra spanned by the `3 × 3` Cuntz matrix units `hop i j`.
Using a dedicated `LieSubalgebra ℝ Cuntz3` keeps `LieRing (CuntzAlg n)` instances `scoped`
and avoids downstream typeclass diamonds while exposing global `IsFiveGraded` structure. -/
def matrixUnitLieSubalgebra : LieSubalgebra ℝ Cuntz3 :=
  { (Submodule.span ℝ (Set.range fun p : Fin 3 × Fin 3 => hop p.1 p.2) :
        Submodule ℝ Cuntz3) with
    lie_mem' := by
      intro x y hx hy
      change ⁅x, y⁆ ∈
        Submodule.span ℝ (Set.range fun p : Fin 3 × Fin 3 => hop p.1 p.2)
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨⟨i, j⟩, rfl⟩
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨⟨k, l⟩, rfl⟩
          change commutator (hop i j) (hop k l) ∈
            Submodule.span ℝ (Set.range fun p : Fin 3 × Fin 3 => hop p.1 p.2)
          unfold commutator
          rw [hop_mul_hop, hop_mul_hop]
          refine Submodule.sub_mem _ ?_ ?_
          · split_ifs
            · exact Submodule.subset_span ⟨(i, l), rfl⟩
            · exact Submodule.zero_mem _
          · split_ifs
            · exact Submodule.subset_span ⟨(k, j), rfl⟩
            · exact Submodule.zero_mem _
        · simp only [lie_zero, Submodule.zero_mem]
        · intro a b _ _ ha hb
          rw [lie_add]
          exact Submodule.add_mem _ ha hb
        · intro r a _ ha
          rw [lie_smul]
          exact Submodule.smul_mem _ r ha
      · simp only [zero_lie, Submodule.zero_mem]
      · intro a b _ _ ha hb
        rw [add_lie]
        exact Submodule.add_mem _ ha hb
      · intro r a _ ha
        rw [smul_lie]
        exact Submodule.smul_mem _ r ha }

theorem hop_mem_matrixUnitLieSubalgebra (i j : Fin 3) :
    hop i j ∈ matrixUnitLieSubalgebra := by
  change hop i j ∈ Submodule.span ℝ (Set.range fun p : Fin 3 × Fin 3 => hop p.1 p.2)
  exact Submodule.subset_span ⟨(i, j), rfl⟩

theorem gradingOp_mem_matrixUnitLieSubalgebra :
    gradingOp ∈ matrixUnitLieSubalgebra := by
  unfold gradingOp
  exact Submodule.sub_mem _
    (hop_mem_matrixUnitLieSubalgebra 0 0)
    (hop_mem_matrixUnitLieSubalgebra 1 1)

/-- The Cartan grading element inside `matrixUnitLieSubalgebra`. -/
def gradingOpSub : matrixUnitLieSubalgebra :=
  ⟨gradingOp, gradingOp_mem_matrixUnitLieSubalgebra⟩

/-- Matrix unit `hop i j` inside `matrixUnitLieSubalgebra`. -/
def hopSub (i j : Fin 3) : matrixUnitLieSubalgebra :=
  ⟨hop i j, hop_mem_matrixUnitLieSubalgebra i j⟩

/-- Global `FiveGradedIwasawa.IsFiveGraded` instance on `gradingOpSub` inside
`matrixUnitLieSubalgebra` (no global diamond on `CuntzAlg n`). -/
instance instIsFiveGradedGradingOpSub : IsFiveGraded gradingOpSub :=
  isFiveGraded_of_lieSubalgebra_tripotent matrixUnitLieSubalgebra
    gradingOp_mem_matrixUnitLieSubalgebra gradingOp_cube

theorem hopSub_inGrade (i j : Fin 3) :
    InGrade gradingOpSub ((colourWeight i - colourWeight j : ℤ) : ℝ) (hopSub i j) := by
  apply Subtype.ext
  change commutator gradingOp (hop i j) =
    ((colourWeight i - colourWeight j : ℤ) : ℝ) • hop i j
  rw [gradingOp_comm_hop i j]
  change _ = (((colourWeight i - colourWeight j : ℤ) : ℝ) : ℂ) • hop i j
  simp

/-- Five-grade Iwasawa 2-step nilpotency applied to the concrete Cuntz `N`-sector
spanned by grade-`+1` (`hopSub 0 2`, `hopSub 2 1`) and grade-`+2` (`hopSub 0 1`). -/
theorem cuntz_iwasawa_n_sector_nilpotent (r₁ r₂ s₁ s₂ t₁ t₂ : ℝ) :
    ⁅⁅r₁ • hopSub 0 2 + s₁ • hopSub 0 1,
        r₂ • hopSub 2 1 + s₂ • hopSub 0 1⁆,
      t₁ • hopSub 0 2 + t₂ • hopSub 0 1⁆ = 0 := by
  have h02 : InGrade gradingOpSub 1 (hopSub 0 2) := by
    simpa [colourWeight] using hopSub_inGrade 0 2
  have h21 : InGrade gradingOpSub 1 (hopSub 2 1) := by
    simpa [colourWeight] using hopSub_inGrade 2 1
  have h01 : InGrade gradingOpSub 2 (hopSub 0 1) := by
    simpa [colourWeight] using hopSub_inGrade 0 1
  have hx1 : InGrade gradingOpSub 1 (r₁ • hopSub 0 2) := by
    unfold InGrade at h02 ⊢; rw [lie_smul, h02, smul_comm]
  have hy1 : InGrade gradingOpSub 1 (r₂ • hopSub 2 1) := by
    unfold InGrade at h21 ⊢; rw [lie_smul, h21, smul_comm]
  have hz1 : InGrade gradingOpSub 1 (t₁ • hopSub 0 2) := by
    unfold InGrade at h02 ⊢; rw [lie_smul, h02, smul_comm]
  have hx2 : InGrade gradingOpSub 2 (s₁ • hopSub 0 1) := by
    unfold InGrade at h01 ⊢; rw [lie_smul, h01, smul_comm]
  have hy2 : InGrade gradingOpSub 2 (s₂ • hopSub 0 1) := by
    unfold InGrade at h01 ⊢; rw [lie_smul, h01, smul_comm]
  have hz2 : InGrade gradingOpSub 2 (t₂ • hopSub 0 1) := by
    unfold InGrade at h01 ⊢; rw [lie_smul, h01, smul_comm]
  exact iwasawa_n_sector_nilpotent gradingOpSub
    (r₁ • hopSub 0 2) (s₁ • hopSub 0 1)
    (r₂ • hopSub 2 1) (s₂ • hopSub 0 1)
    (t₁ • hopSub 0 2) (t₂ • hopSub 0 1)
    hx1 hx2 hy1 hy2 hz1 hz2

end GlobalCuntzLieSubalgebra

end InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge
