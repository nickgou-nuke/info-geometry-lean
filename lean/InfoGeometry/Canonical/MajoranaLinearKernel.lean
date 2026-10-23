/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Canonical.KitaevChainMajoranaZeroModes
import InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Majorana coefficient kernels and finite-chain boundary commutators

The coefficient matrix and the operator algebra are different carriers.
The map `field` connects them. The quadratic generator is real-skew rather
than a self-adjoint Hamiltonian; a physical Hamiltonian uses an additional
central imaginary factor. The Pfaffian criterion explicitly consumes the
existing PfaffianKernel square-law witness.
-/
namespace InfoGeometry.Canonical.MajoranaLinearKernel

open scoped BigOperators
open KitaevChainMajoranaZeroModes ProjectivePfaffianDeterminantCounts

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable {N : ℕ}

/-- The real linear combination of the supplied Majorana operators. -/
def field (g : Fin (2 * N) → A) (v : Fin (2 * N) → ℝ) : A :=
  ∑ i, v i • g i

/-- Real skew quadratic generator. For Hermitian Majoranas, multiply by i
for the corresponding self-adjoint Hamiltonian. -/
def quadratic (g : Fin (2 * N) → A)
    (w : Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ) : A :=
  (1 / 4 : ℝ) • ∑ i, ∑ j, w i j • (g i * g j)

@[simp] theorem field_zero (g : Fin (2 * N) → A) : field g 0 = 0 := by
  simp [field]

@[simp] theorem field_single (g : Fin (2 * N) → A) (i : Fin (2 * N)) :
    field g (Pi.single i 1) = g i := by
  simp [field, Pi.single_apply]

/-- CAR extracts each real coefficient without an independence assumption. -/
theorem field_anticommutator {g : Fin (2 * N) → A}
    (hg : IsMajoranaBasis N g) (i : Fin (2 * N)) (v : Fin (2 * N) → ℝ) :
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

/-- A nontrivial real operator algebra makes the Majorana field faithful. -/
theorem field_injective [Nontrivial A] {g : Fin (2 * N) → A}
    (hg : IsMajoranaBasis N g) : Function.Injective (field g) := by
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

theorem field_eq_zero_iff [Nontrivial A] {g : Fin (2 * N) → A}
    (hg : IsMajoranaBasis N g) (v : Fin (2 * N) → ℝ) :
    field g v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    apply field_injective hg
    simpa using hv
  · rintro rfl
    exact field_zero g

/-- The Clifford bilinear commutator, derived from the owner's CAR predicate. -/
theorem bilinear_commutator {g : Fin (2 * N) → A}
    (hg : IsMajoranaBasis N g) (i j k : Fin (2 * N)) :
    (g i * g j) * g k - g k * (g i * g j) =
      (2 : ℝ) • (if j = k then g i else 0) -
      (2 : ℝ) • (if i = k then g j else 0) := by
  calc
    _ = g i * (g j * g k + g k * g j) -
        (g i * g k + g k * g i) * g j := by noncomm_ring
    _ = _ := by
      rw [hg j k, hg i k]
      split_ifs <;> simp [two_smul, mul_two, two_mul]

/-- The quadratic adjoint action is exactly the skew coefficient action. -/
theorem quadratic_comm_generator {g : Fin (2 * N) → A}
    (hg : IsMajoranaBasis N g)
    (w : Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ)
    (hw : ∀ i j, w i j = -w j i) (k : Fin (2 * N)) :
    quadratic g w * g k - g k * quadratic g w = field g (fun i => w i k) := by
  have hrow : field g (fun j => w k j) = -field g (fun i => w i k) := by
    simp only [field]
    simp_rw [hw k, neg_smul]
    exact Finset.sum_neg_distrib
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

/-- This is the carrier map required to turn a coefficient kernel vector
into a conserved linear Majorana operator. -/
theorem quadratic_comm_field {g : Fin (2 * N) → A}
    (hg : IsMajoranaBasis N g)
    (w : Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ)
    (hw : ∀ i j, w i j = -w j i) (v : Fin (2 * N) → ℝ) :
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

theorem comm_field_zero_iff [Nontrivial A] {g : Fin (2 * N) → A}
    (hg : IsMajoranaBasis N g)
    (w : Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ)
    (hw : ∀ i j, w i j = -w j i) (v : Fin (2 * N) → ℝ) :
    quadratic g w * field g v - field g v * quadratic g w = 0 ↔
      w.mulVec v = 0 := by
  rw [quadratic_comm_field hg w hw, field_eq_zero_iff hg]

/-- The existing Pfaffian square-law witness gives a genuine kernel criterion. -/
theorem pfaffian_zero_iff_nonzero_kernel
    (P : PfaffianKernel (Fin (2 * N))) :
    P.pfaffian = 0 ↔ ∃ v : Fin (2 * N) → ℝ, v ≠ 0 ∧ P.omega.mulVec v = 0 := by
  rw [Matrix.exists_mulVec_eq_zero_iff, ← P.pf_sq_eq_det]
  simp

/-- Pfaffian zero is equivalent to a nonzero conserved LINEAR Majorana field.
The square law comes from P; faithfulness and the operator action are proved. -/
theorem pfaffian_zero_iff_conserved_majorana [Nontrivial A]
    {g : Fin (2 * N) → A} (hg : IsMajoranaBasis N g)
    (P : PfaffianKernel (Fin (2 * N))) :
    P.pfaffian = 0 ↔ ∃ v : Fin (2 * N) → ℝ,
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

/-- Extend the owner's one-bond lemma to the COMPLETE finite open chain.
The coefficient must commute with the boundary generator. -/
theorem sweetSpot_boundary_commutes {g : Fin (2 * N) → A}
    (hg : IsMajoranaBasis N g) (t : A) (q : Fin (2 * N))
    (hq : q.val = 0 ∨ q.val + 1 = 2 * N) (ht : Commute (g q) t) :
    g q * kitaevSweetSpotHamiltonian N t g -
      kitaevSweetSpotHamiltonian N t g * g q = 0 := by
  unfold kitaevSweetSpotHamiltonian
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro j _
  have h1 : q ≠ (⟨2 * j.val + 1, by omega⟩ : Fin (2 * N)) := by
    intro he
    have he' := congrArg Fin.val he
    rcases hq with hq | hq <;> simp only [Fin.val_mk] at he' <;> omega
  have h2 : q ≠ (⟨2 * j.val + 2, by omega⟩ : Fin (2 * N)) := by
    intro he
    have he' := congrArg Fin.val he
    rcases hq with hq | hq <;> simp only [Fin.val_mk] at he' <;> omega
  have h01 := hg q ⟨2 * j.val + 1, by omega⟩
  have h02 := hg q ⟨2 * j.val + 2, by omega⟩
  rw [if_neg h1] at h01
  rw [if_neg h2] at h02
  have hb := left_boundary_majorana_zero_mode _ _ _ h01 h02
  calc
    _ = t * (g q * (g ⟨2 * j.val + 1, by omega⟩ * g ⟨2 * j.val + 2, by omega⟩) -
      (g ⟨2 * j.val + 1, by omega⟩ * g ⟨2 * j.val + 2, by omega⟩) * g q) := by
      rw [← mul_assoc (g q) t, ht.eq]
      noncomm_ring
    _ = 0 := by rw [hb, mul_zero]

end
end InfoGeometry.Canonical.MajoranaLinearKernel
