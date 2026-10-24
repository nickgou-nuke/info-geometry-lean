/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Majorana coefficient kernels and finite-chain boundary commutators

The coefficient matrix and operator algebra are different carriers, connected
by `field`. Hypotheses are the exact defining equations of the existing
IsMajoranaBasis predicate, generalized to an arbitrary finite index type.
No replacement CAR predicate is introduced. The quadratic operator is skew,
not a self-adjoint Hamiltonian; the latter uses an extra central imaginary
factor. The general Pfaffian result consumes the existing square-law witness.
-/
namespace InfoGeometry.Canonical.MajoranaLinearKernel

open scoped BigOperators
open ProjectivePfaffianDeterminantCounts

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real coefficient field in the operator algebra. -/
def field (g : ι → A) (v : ι → ℝ) : A := ∑ i, v i • g i

/-- Skew quadratic generator, with an explicit normalization. -/
def quadratic (g : ι → A) (w : Matrix ι ι ℝ) : A :=
  (1 / 4 : ℝ) • ∑ i, ∑ j, w i j • (g i * g j)

@[simp] theorem field_zero (g : ι → A) : field g 0 = 0 := by
  simp [field]

@[simp] theorem field_single (g : ι → A) (i : ι) :
    field g (Pi.single i 1) = g i := by
  simp [field, Pi.single_apply]

/-- CAR extracts each real coefficient without assuming independence. -/
theorem field_anticommutator {g : ι → A}
    (hg : ∀ i j, g i * g j + g j * g i = if i = j then 2 else 0)
    (i : ι) (v : ι → ℝ) :
    g i * field g v + field g v * g i = (2 * v i) • (1 : A) := by
  calc
    _ = ∑ j, v j • (g i * g j + g j * g i) := by
      simp [field, Finset.mul_sum, Finset.sum_mul, smul_add,
        Finset.sum_add_distrib, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    _ = v i • (2 : A) := by
      simp_rw [hg]
      simp
    _ = (2 * v i) • (1 : A) := by
      rw [show (2 : A) = 1 + 1 by norm_num, smul_add, two_mul, add_smul]

/-- Faithfulness is derived from CAR and nontriviality. -/
theorem field_injective [Nontrivial A] {g : ι → A}
    (hg : ∀ i j, g i * g j + g j * g i = if i = j then 2 else 0) :
    Function.Injective (field g) := by
  intro v w h
  funext i
  have he := congrArg (fun x : A => g i * x + x * g i) h
  rw [field_anticommutator hg, field_anticommutator hg] at he
  have hz : (2 * (v i - w i)) • (1 : A) = 0 := by
    calc
      _ = (2 * v i) • (1 : A) - (2 * w i) • (1 : A) := by
        rw [← sub_smul]
        congr 1
        ring
      _ = 0 := sub_eq_zero.mpr he
  have hs := (smul_eq_zero.mp hz).resolve_right one_ne_zero
  linarith

theorem field_eq_zero_iff [Nontrivial A] {g : ι → A}
    (hg : ∀ i j, g i * g j + g j * g i = if i = j then 2 else 0)
    (v : ι → ℝ) : field g v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    apply field_injective hg
    simpa using hv
  · rintro rfl
    exact field_zero g

/-- Clifford bilinear commutator derived from normalized CAR. -/
theorem bilinear_commutator {g : ι → A}
    (hg : ∀ i j, g i * g j + g j * g i = if i = j then 2 else 0)
    (i j k : ι) :
    (g i * g j) * g k - g k * (g i * g j) =
      (2 : ℝ) • (if j = k then g i else 0) -
      (2 : ℝ) • (if i = k then g j else 0) := by
  calc
    _ = g i * (g j * g k + g k * g j) -
        (g i * g k + g k * g i) * g j := by noncomm_ring
    _ = _ := by
      rw [hg j k, hg i k]
      split_ifs <;> simp [two_smul, mul_two, two_mul]

/-- The quadratic adjoint action is the skew coefficient action. -/
theorem quadratic_comm_generator {g : ι → A}
    (hg : ∀ i j, g i * g j + g j * g i = if i = j then 2 else 0)
    (w : Matrix ι ι ℝ) (hw : ∀ i j, w i j = -w j i) (k : ι) :
    quadratic g w * g k - g k * quadratic g w = field g (fun i => w i k) := by
  have hrow : field g (fun j => w k j) = -field g (fun i => w i k) := by
    unfold field
    calc
      (∑ j, w k j • g j) = ∑ j, -(w j k • g j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hw k j, neg_smul]
      _ = -(∑ j, w j k • g j) := by rw [Finset.sum_neg_distrib]
  calc
    _ = (1 / 4 : ℝ) • ∑ i, ∑ j, w i j •
        ((g i * g j) * g k - g k * (g i * g j)) := by
      simp [quadratic, Finset.mul_sum, Finset.sum_mul,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
        smul_sub, Finset.sum_sub_distrib]
    _ = (1 / 4 : ℝ) • ((2 : ℝ) • field g (fun i => w i k) -
        (2 : ℝ) • field g (fun j => w k j)) := by
      simp_rw [bilinear_commutator hg]
      simp [field, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum,
        smul_smul, mul_comm]
    _ = field g (fun i => w i k) := by
      rw [hrow]
      module

/-- The carrier map connects coefficient-kernel vectors to conserved operators. -/
theorem quadratic_comm_field {g : ι → A}
    (hg : ∀ i j, g i * g j + g j * g i = if i = j then 2 else 0)
    (w : Matrix ι ι ℝ) (hw : ∀ i j, w i j = -w j i) (v : ι → ℝ) :
    quadratic g w * field g v - field g v * quadratic g w =
      field g (w.mulVec v) := by
  calc
    _ = ∑ j, v j • (quadratic g w * g j - g j * quadratic g w) := by
      simp [field, Finset.mul_sum, Finset.sum_mul,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
        smul_sub, Finset.sum_sub_distrib]
    _ = ∑ j, v j • field g (fun i => w i j) := by
      simp_rw [quadratic_comm_generator hg w hw]
    _ = field g (w.mulVec v) := by
      simp only [field, Finset.smul_sum, smul_smul,
        Matrix.mulVec, dotProduct, Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm]

theorem comm_field_zero_iff [Nontrivial A] {g : ι → A}
    (hg : ∀ i j, g i * g j + g j * g i = if i = j then 2 else 0)
    (w : Matrix ι ι ℝ) (hw : ∀ i j, w i j = -w j i) (v : ι → ℝ) :
    quadratic g w * field g v - field g v * quadratic g w = 0 ↔
      w.mulVec v = 0 := by
  rw [quadratic_comm_field hg w hw, field_eq_zero_iff hg]

/-- The existing square-law witness gives the actual coefficient-kernel criterion. -/
theorem pfaffian_zero_iff_nonzero_kernel (P : PfaffianKernel ι) :
    P.pfaffian = 0 ↔ ∃ v : ι → ℝ, v ≠ 0 ∧ P.omega.mulVec v = 0 := by
  rw [Matrix.exists_mulVec_eq_zero_iff, ← P.pf_sq_eq_det]
  simp

/-- The square law comes from P; faithfulness and the operator action are proved. -/
theorem pfaffian_zero_iff_conserved_majorana [Nontrivial A]
    {g : ι → A} (hg : ∀ i j, g i * g j + g j * g i = if i = j then 2 else 0)
    (P : PfaffianKernel ι) :
    P.pfaffian = 0 ↔ ∃ v : ι → ℝ,
      field g v ≠ 0 ∧
      quadratic g P.omega * field g v - field g v * quadratic g P.omega = 0 := by
  rw [pfaffian_zero_iff_nonzero_kernel]
  constructor
  · rintro ⟨v, hv, hk⟩
    exact ⟨v, fun h => hv ((field_eq_zero_iff hg v).mp h),
      (comm_field_zero_iff hg P.omega P.skew v).mpr hk⟩
  · rintro ⟨v, hv, hc⟩
    exact ⟨v, fun h => hv ((field_eq_zero_iff hg v).mpr h),
      (comm_field_zero_iff hg P.omega P.skew v).mp hc⟩

/-- Endpoint conservation for a complete finite sum of bilinears. -/
theorem finite_bilinear_boundary_commutes {J : Type*} [Fintype J]
    {g : ι → A}
    (hg : ∀ i j, g i * g j + g j * g i = if i = j then 2 else 0)
    (a b : J → ι) (q : ι)
    (ha : ∀ j, q ≠ a j) (hb : ∀ j, q ≠ b j)
    (t : A) (ht : Commute (g q) t) :
    g q * (∑ j, t * (g (a j) * g (b j))) -
      (∑ j, t * (g (a j) * g (b j))) * g q = 0 := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro j _
  have hprod : (g (a j) * g (b j)) * g q - g q * (g (a j) * g (b j)) = 0 := by
    rw [bilinear_commutator hg]
    simp [Ne.symm (ha j), Ne.symm (hb j)]
  have hcomm : g q * (g (a j) * g (b j)) = (g (a j) * g (b j)) * g q :=
    (sub_eq_zero.mp hprod).symm
  calc
    _ = t * (g q * (g (a j) * g (b j)) -
      (g (a j) * g (b j)) * g q) := by
        rw [← mul_assoc (g q) t, ht.eq]
        noncomm_ring
    _ = 0 := by rw [hcomm, sub_self, mul_zero]

end
end InfoGeometry.Canonical.MajoranaLinearKernel
