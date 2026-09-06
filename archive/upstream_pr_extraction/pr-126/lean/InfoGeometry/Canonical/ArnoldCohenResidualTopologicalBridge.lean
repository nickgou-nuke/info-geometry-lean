import Mathlib

/-!
# Finite Arnold--Cohen residual readout

This owner formalizes only the finite matrix loss associated with a supplied
basis matrix.  It does not assert that arbitrary bases satisfy the
Arnold--Cohen relation: vanishing is an additional condition on the basis.
-/

noncomputable section

namespace InfoGeometry.Canonical

open scoped BigOperators

def acOuter (u v : Fin dE → ℝ) : Matrix (Fin dE) (Fin dE) ℝ :=
  fun a b => u a * v b

def acBivector (Γ : Fin din → Fin dE → ℝ) (i j : Fin din) :
    Matrix (Fin dE) (Fin dE) ℝ :=
  acOuter (Γ i) (Γ j) - acOuter (Γ j) (Γ i)

def acResidual (Γ : Fin din → Fin dE → ℝ)
    (i j k : Fin din) : Matrix (Fin dE) (Fin dE) ℝ :=
  acBivector Γ i j * acBivector Γ j k
    + acBivector Γ j k * acBivector Γ k i
    + acBivector Γ k i * acBivector Γ i j

def acFrobeniusSq (M : Matrix (Fin dE) (Fin dE) ℝ) : ℝ :=
  ∑ a : Fin dE, ∑ b : Fin dE, (M a b) ^ 2

def acResidualLoss (Γ : Fin din → Fin dE → ℝ) : ℝ :=
  ∑ i : Fin din, ∑ j : Fin din, ∑ k : Fin din,
    acFrobeniusSq (acResidual Γ i j k)

theorem continuous_acOuter (i j : Fin din) :
    Continuous (fun Γ : Fin din → Fin dE → ℝ => acOuter (Γ i) (Γ j)) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  have hia : Continuous (fun Γ : Fin din → Fin dE → ℝ => Γ i a) :=
    (continuous_apply a).comp (continuous_apply i)
  have hjb : Continuous (fun Γ : Fin din → Fin dE → ℝ => Γ j b) :=
    (continuous_apply b).comp (continuous_apply j)
  exact hia.mul hjb

theorem continuous_acBivector (i j : Fin din) :
    Continuous (fun Γ : Fin din → Fin dE → ℝ => acBivector Γ i j) := by
  simpa [acBivector] using
    (continuous_acOuter (din := din) (dE := dE) i j).sub
      (continuous_acOuter (din := din) (dE := dE) j i)

theorem continuous_acResidual (i j k : Fin din) :
    Continuous (fun Γ : Fin din → Fin dE → ℝ => acResidual Γ i j k) := by
  have h₁ := (continuous_acBivector (din := din) (dE := dE) i j).matrix_mul
    (continuous_acBivector (din := din) (dE := dE) j k)
  have h₂ := (continuous_acBivector (din := din) (dE := dE) j k).matrix_mul
    (continuous_acBivector (din := din) (dE := dE) k i)
  have h₃ := (continuous_acBivector (din := din) (dE := dE) k i).matrix_mul
    (continuous_acBivector (din := din) (dE := dE) i j)
  simpa [acResidual] using (h₁.add h₂).add h₃

theorem continuous_acFrobeniusSq :
    Continuous (fun M : Matrix (Fin dE) (Fin dE) ℝ => acFrobeniusSq M) := by
  unfold acFrobeniusSq
  apply continuous_finset_sum Finset.univ
  intro a ha
  apply continuous_finset_sum Finset.univ
  intro b hb
  exact ((continuous_apply b).comp (continuous_apply a)).pow 2

theorem continuous_acResidualLoss :
    Continuous (fun Γ : Fin din → Fin dE → ℝ => acResidualLoss Γ) := by
  unfold acResidualLoss
  apply continuous_finset_sum Finset.univ
  intro i hi
  apply continuous_finset_sum Finset.univ
  intro j hj
  apply continuous_finset_sum Finset.univ
  intro k hk
  exact continuous_acFrobeniusSq.comp (continuous_acResidual i j k)

theorem acFrobeniusSq_nonneg (M : Matrix (Fin dE) (Fin dE) ℝ) :
    0 ≤ acFrobeniusSq M := by
  unfold acFrobeniusSq
  exact Finset.sum_nonneg (fun a ha =>
    Finset.sum_nonneg (fun b hb => sq_nonneg _))

theorem acFrobeniusSq_eq_zero_iff (M : Matrix (Fin dE) (Fin dE) ℝ) :
    acFrobeniusSq M = 0 ↔ ∀ a b, M a b = 0 := by
  constructor
  · intro h a b
    have ha : ∑ b : Fin dE, (M a b) ^ 2 = 0 := by
      have hrows := (Finset.sum_eq_zero_iff_of_nonneg
        (fun a ha => Finset.sum_nonneg (fun b hb => sq_nonneg _))).mp h
      exact hrows a (Finset.mem_univ a)
    have hentries := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b hb => sq_nonneg _)).mp ha
    exact (sq_eq_zero_iff.mp (hentries b (Finset.mem_univ b)))
  · intro h
    simp [acFrobeniusSq, h]

theorem acResidualLoss_nonneg (Γ : Fin din → Fin dE → ℝ) :
    0 ≤ acResidualLoss Γ := by
  unfold acResidualLoss
  refine Finset.sum_nonneg ?_
  intro i hi
  refine Finset.sum_nonneg ?_
  intro j hj
  refine Finset.sum_nonneg ?_
  intro k hk
  exact acFrobeniusSq_nonneg _

theorem acResidualLoss_eq_zero_of_residual_eq_zero
    (Γ : Fin din → Fin dE → ℝ)
    (hzero : ∀ i j k, acResidual Γ i j k = 0) :
    acResidualLoss Γ = 0 := by
  unfold acResidualLoss
  simp [hzero, acFrobeniusSq]

theorem acResidualLoss_eq_zero_iff
    (Γ : Fin din → Fin dE → ℝ) :
    acResidualLoss Γ = 0 ↔
      ∀ i j k, acResidual Γ i j k = 0 := by
  constructor
  · intro h i j k
    have hi :
        ∑ j : Fin din, ∑ k : Fin din,
          acFrobeniusSq (acResidual Γ i j k) = 0 := by
      have hrows := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i hi => by
          refine Finset.sum_nonneg ?_
          intro j hj
          refine Finset.sum_nonneg ?_
          intro k hk
          exact acFrobeniusSq_nonneg _)).mp h
      exact hrows i (Finset.mem_univ i)
    have hj :
        ∑ k : Fin din, acFrobeniusSq (acResidual Γ i j k) = 0 := by
      have hrows := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => by
          refine Finset.sum_nonneg ?_
          intro k hk
          exact acFrobeniusSq_nonneg _)).mp hi
      exact hrows j (Finset.mem_univ j)
    have hijk := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k hk => acFrobeniusSq_nonneg _)).mp hj
    have hentries := (acFrobeniusSq_eq_zero_iff _).mp
      (hijk k (Finset.mem_univ k))
    apply funext
    intro a
    apply funext
    intro b
    exact hentries a b
  · intro h
    exact acResidualLoss_eq_zero_of_residual_eq_zero Γ h

theorem acResidualLoss_levelSet_isClosed (c : ℝ) :
    IsClosed {Γ : Fin din → Fin dE → ℝ | acResidualLoss Γ = c} := by
  simpa only [Set.preimage, Set.mem_setOf_eq] using
    (isClosed_singleton : IsClosed ({c} : Set ℝ)).preimage
      (continuous_acResidualLoss (din := din) (dE := dE))

theorem acResidualZeroLocus_isClosed :
    IsClosed {Γ : Fin din → Fin dE → ℝ | acResidualLoss Γ = 0} :=
  acResidualLoss_levelSet_isClosed (din := din) (dE := dE) 0

end InfoGeometry.Canonical
