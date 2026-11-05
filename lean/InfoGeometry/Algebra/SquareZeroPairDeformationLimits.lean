/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SquareZeroPairDeformation
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# The singular limit of square-zero-pair spectral projectors

The deformed operator has a limit, but either projector has a nonzero residue
when the first generator is nonzero. These are topological statements for
arbitrary real algebras, with no finite-dimensional or commutativity assumption.
-/

open Filter Topology

namespace InfoGeometry.Algebra.SquareZeroPairDeformation

section IdempotentLimits

variable {A ι : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  [T2Space A] {l : Filter ι} [l.NeBot] {f : ι → A} {a : A}

/-- Idempotents form a closed locus: an actual limit remains idempotent. -/
theorem isIdempotentElem_of_tendsto
    (hf : Tendsto f l (𝓝 a)) (hi : ∀ᶠ i in l, IsIdempotentElem (f i)) :
    IsIdempotentElem a := by
  exact tendsto_nhds_unique_of_eventuallyEq (hf.mul hf) hf hi

/-- A limit of idempotents cannot be a nonzero nilpotent. -/
theorem nilpotent_eq_zero_of_tendsto_idempotents
    (hf : Tendsto f l (𝓝 a)) (hi : ∀ᶠ i in l, IsIdempotentElem (f i))
    (ha : IsNilpotent a) : a = 0 :=
  (isIdempotentElem_of_tendsto hf hi).eq_zero_of_isNilpotent ha

end IdempotentLimits

section Residues

variable {A ι : Type*} [Ring A] [Algebra ℝ A] [TopologicalSpace A]
  [IsTopologicalRing A] [ContinuousSMul ℝ A]
  {l : Filter ι} {t : ι → ℝ}

/-- The signed deformation itself tends to its first square-zero generator. -/
theorem tendsto_deformation (u v : A) (ht : Tendsto t l (𝓝 0)) :
    Tendsto (fun i => deformation u v (t i)) l (𝓝 u) := by
  simpa only [deformation, zero_smul, add_zero] using
    (tendsto_const_nhds (x := u)).add (ht.smul (tendsto_const_nhds (x := v)))

/-- The exact residue survives even though the normalization is singular. -/
theorem tendsto_projectorPlus_residue (u v : A)
    (ht : Tendsto t l (𝓝 0)) (hne : ∀ᶠ i in l, t i ≠ 0) :
    Tendsto (fun i => t i • projectorPlus u v (t i)) l (𝓝 ((1 / 2 : ℝ) • u)) := by
  have hpoly := (tendsto_const_nhds (x := (1 / 2 : ℝ))).smul
    (((ht.smul (tendsto_const_nhds (x := (1 : A)))).add
      (tendsto_const_nhds (x := u))).add
      ((ht.pow 2).smul (tendsto_const_nhds (x := v))))
  simp only [zero_pow (by decide : 2 ≠ 0), zero_smul, zero_add, add_zero] at hpoly
  apply hpoly.congr'
  filter_upwards [hne] with i hi
  exact (projectorPlus_residue u v hi).symm

theorem tendsto_projectorMinus_residue (u v : A)
    (ht : Tendsto t l (𝓝 0)) (hne : ∀ᶠ i in l, t i ≠ 0) :
    Tendsto (fun i => t i • projectorMinus u v (t i)) l (𝓝 ((1 / 2 : ℝ) • (-u))) := by
  have hpoly := (tendsto_const_nhds (x := (1 / 2 : ℝ))).smul
    (((ht.smul (tendsto_const_nhds (x := (1 : A)))).sub
      (tendsto_const_nhds (x := u))).sub
      ((ht.pow 2).smul (tendsto_const_nhds (x := v))))
  simp only [zero_pow (by decide : 2 ≠ 0), zero_smul, zero_sub, sub_zero] at hpoly
  apply hpoly.congr'
  filter_upwards [hne] with i hi
  exact (projectorMinus_residue u v hi).symm

variable [T2Space A]

/-- A nonzero residue rules out every finite limit of the positive projector. -/
theorem not_tendsto_projectorPlus [l.NeBot] (u v a : A) (hu : u ≠ 0)
    (ht : Tendsto t l (𝓝 0)) (hne : ∀ᶠ i in l, t i ≠ 0) :
    ¬ Tendsto (fun i => projectorPlus u v (t i)) l (𝓝 a) := by
  intro hP
  have hz : Tendsto (fun i => t i • projectorPlus u v (t i)) l (𝓝 (0 : A)) := by
    simpa only [zero_smul] using ht.smul hP
  have heq := tendsto_nhds_unique (tendsto_projectorPlus_residue u v ht hne) hz
  exact hu ((smul_eq_zero.mp heq).resolve_left (by norm_num))

theorem not_tendsto_projectorMinus [l.NeBot] (u v a : A) (hu : u ≠ 0)
    (ht : Tendsto t l (𝓝 0)) (hne : ∀ᶠ i in l, t i ≠ 0) :
    ¬ Tendsto (fun i => projectorMinus u v (t i)) l (𝓝 a) := by
  intro hP
  have hz : Tendsto (fun i => t i • projectorMinus u v (t i)) l (𝓝 (0 : A)) := by
    simpa only [zero_smul] using ht.smul hP
  have heq := tendsto_nhds_unique (tendsto_projectorMinus_residue u v ht hne) hz
  exact hu (neg_eq_zero.mp ((smul_eq_zero.mp heq).resolve_left (by norm_num)))

end Residues

end InfoGeometry.Algebra.SquareZeroPairDeformation
