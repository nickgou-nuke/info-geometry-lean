/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzComplexificationAlgEquiv
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Integer grading embedding of the complexified Cuntz algebra

This owner supplies the genuine noncommutative integer grading embedding.
The map `delta` has values in the additive monoid algebra with the actual
complexified Cuntz algebra as its noncommutative coefficient algebra.
It sends S to degree 1 and T to degree -1. The augmentation `epsilon` sums
coefficients, and its composite with `delta` is the identity on the whole
carrier. This file proves an embedding with a left inverse, not coassociativity
of a coaction. No target star instance or coassociativity assertion is introduced.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzIntegerGrading

open InfoGeometry.Topology.AlgebraicCuntzQuotient
open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzComplexification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem degree_ortho (i j : ι) :
    (AddMonoidAlgebra.single (-1 : ℤ) (Tℂ i) :
        AddMonoidAlgebra (ComplexStarCuntzAlg ι) ℤ) *
      AddMonoidAlgebra.single (1 : ℤ) (Sℂ j) = if i = j then 1 else 0 := by
  rw [AddMonoidAlgebra.single_mul_single]
  rw [neg_add_cancel]
  by_cases h : i = j
  · subst j
    rw [complexified_ortho]
    simp only [ite_true, AddMonoidAlgebra.one_def]
  · rw [complexified_ortho]
    rw [if_neg h, if_neg h, AddMonoidAlgebra.single_zero]

theorem degree_partition :
    (∑ i : ι,
      (AddMonoidAlgebra.single (1 : ℤ) (Sℂ i) :
          AddMonoidAlgebra (ComplexStarCuntzAlg ι) ℤ) *
        AddMonoidAlgebra.single (-1 : ℤ) (Tℂ i)) = 1 := by
  simp only [AddMonoidAlgebra.single_mul_single, add_neg_cancel]
  have h := congrArg
    (AddMonoidAlgebra.singleZeroAlgHom : ComplexStarCuntzAlg ι →ₐ[ℂ]
      AddMonoidAlgebra (ComplexStarCuntzAlg ι) ℤ)
    (complexified_partition (ι := ι))
  simpa only [map_sum, map_one, AddMonoidAlgebra.singleZeroAlgHom_apply] using h

def letterDegree : CuntzAlg ℂ ι →ₐ[ℂ]
    AddMonoidAlgebra (ComplexStarCuntzAlg ι) ℤ :=
  lift (R := ℂ)
    (fun i => AddMonoidAlgebra.single (1 : ℤ) (Sℂ i))
    (fun i => AddMonoidAlgebra.single (-1 : ℤ) (Tℂ i))
    degree_ortho degree_partition

@[simp] theorem letterDegree_S (i : ι) :
    letterDegree (S (R := ℂ) i) = AddMonoidAlgebra.single (1 : ℤ) (Sℂ i) := by
  exact lift_S _ _ degree_ortho degree_partition i

@[simp] theorem letterDegree_T (i : ι) :
    letterDegree (T (R := ℂ) i) = AddMonoidAlgebra.single (-1 : ℤ) (Tℂ i) := by
  exact lift_T _ _ degree_ortho degree_partition i

def delta : ComplexStarCuntzAlg ι →ₐ[ℂ]
    AddMonoidAlgebra (ComplexStarCuntzAlg ι) ℤ :=
  letterDegree.comp complexificationAlgEquiv.toAlgHom

@[simp] theorem delta_S (i : ι) :
    delta (Sℂ i) = AddMonoidAlgebra.single (1 : ℤ) (Sℂ i) := by
  simp [delta]

@[simp] theorem delta_T (i : ι) :
    delta (Tℂ i) = AddMonoidAlgebra.single (-1 : ℤ) (Tℂ i) := by
  simp [delta]

def epsilon : AddMonoidAlgebra (ComplexStarCuntzAlg ι) ℤ →ₐ[ℂ]
    ComplexStarCuntzAlg ι :=
  AddMonoidAlgebra.liftNCAlgHom (AlgHom.id ℂ (ComplexStarCuntzAlg ι))
    (1 : Multiplicative ℤ →* ComplexStarCuntzAlg ι)
    (fun a _ => Commute.one_right a)

@[simp] theorem epsilon_single (n : ℤ) (a : ComplexStarCuntzAlg ι) :
    epsilon (AddMonoidAlgebra.single n a) = a := by
  change AddMonoidAlgebra.liftNC
    (AlgHom.id ℂ (ComplexStarCuntzAlg ι))
    (1 : Multiplicative ℤ →* ComplexStarCuntzAlg ι)
    (AddMonoidAlgebra.single n a) = a
  rw [AddMonoidAlgebra.liftNC_single]
  simp

theorem epsilon_eq_sum (p : AddMonoidAlgebra (ComplexStarCuntzAlg ι) ℤ) :
    epsilon p = p.coeff.sum (fun _ a => a) := by
  calc
    epsilon p = epsilon (p.coeff.sum AddMonoidAlgebra.single) :=
      congrArg epsilon (AddMonoidAlgebra.sum_coeff_single p).symm
    _ = p.coeff.sum (fun _ a => a) := by
      simp only [map_finsuppSum, epsilon_single]

theorem epsilon_comp_delta :
    (epsilon (ι := ι)).comp delta = AlgHom.id ℂ (ComplexStarCuntzAlg ι) := by
  apply Algebra.TensorProduct.ext_ring
  apply quotientHom_ext
  · intro i
    change epsilon (delta (Sℂ i)) = Sℂ i
    rw [delta_S, epsilon_single]
  · intro i
    change epsilon (delta (Tℂ i)) = Tℂ i
    rw [delta_T, epsilon_single]

@[simp] theorem epsilon_delta (a : ComplexStarCuntzAlg ι) :
    epsilon (delta a) = a :=
  DFunLike.congr_fun (epsilon_comp_delta (ι := ι)) a

theorem delta_injective : Function.Injective (delta (ι := ι)) := by
  intro a b h
  have h' := congrArg (epsilon (ι := ι)) h
  simpa only [epsilon_delta] using h'

end InfoGeometry.Algebra.CuntzIntegerGrading
