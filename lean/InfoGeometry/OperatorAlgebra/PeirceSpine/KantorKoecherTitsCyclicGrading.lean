/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTitsFiveGradedLieAlgebra
import Mathlib.Algebra.Lie.Graded
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Cyclic reindexing of the five Peirce grades

The five Peirce sectors are internally direct over `ℤ`. This file reindexes
them by their residues modulo five, giving an additive indexing interface for
Mathlib's `GradedLieAlgebra` class.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTits

open TKKJordanPairData
open OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset

attribute [local instance 100] LieRing.ofAssociativeRing

variable {B : Type*} [Ring B] [StarRing B]

/-- Reindex the order `+2,+1,0,-1,-2` by residues `2,1,0,4,3` in `Fin 5`. -/
def cyclicPeirceReindex : Fin 5 ≃ Fin 5 :=
  (Equiv.swap 0 2).trans (Equiv.swap 3 4)

/-- The Peirce family in cyclic degree order `0,+1,+2,-2,-1`. -/
def cyclicPeirceGrade (N_plus : B) (i : Fin 5) : Submodule ℤ B :=
  peirceFiveGradeSubmodule N_plus (cyclicPeirceReindex.symm i)

/-- The cyclic index corresponding to an integer TKK grade. -/
def cyclicIndexOfTKKGrade : TKKGrade → Fin 5
  | .z0 => 0
  | .p1 => 1
  | .p2 => 2
  | .m2 => 3
  | .m1 => 4

/-- Convert a cyclic index to its concrete Peirce corner label. -/
def tkkGradeOfCyclicIndex (i : Fin 5) : TKKGrade :=
  match i.val with
  | 0 => .z0
  | 1 => .p1
  | 2 => .p2
  | 3 => .m2
  | _ => .m1

/-- The two finite grade-label maps are inverse on TKK grades. -/
theorem tkkGradeOfCyclicIndex_cyclicIndexOfTKKGrade (i : TKKGrade) :
    tkkGradeOfCyclicIndex (cyclicIndexOfTKKGrade i) = i := by
  cases i <;> rfl

/-- Cyclic Peirce components are the same concrete corners as the TKK family. -/
theorem cyclicPeirceGrade_eq_tkk (N_plus : B) (i : Fin 5) :
    cyclicPeirceGrade N_plus i = tkkPeirceGrade N_plus (tkkGradeOfCyclicIndex i) := by
  fin_cases i <;> rfl

/-- Reindexing preserves the internal direct-sum decomposition of the five
Peirce sectors. -/
theorem cyclicPeirceGrade_isInternal (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    DirectSum.IsInternal (cyclicPeirceGrade N_plus) := by
  classical
  let reindex :
      DirectSum (Fin 5) (fun i => peirceFiveGradeSubmodule N_plus i) ≃+
        DirectSum (Fin 5) (fun i => cyclicPeirceGrade N_plus i) :=
    DirectSum.equivCongrLeft cyclicPeirceReindex
  have hcoeHom :
      (DirectSum.coeAddMonoidHom (fun i => cyclicPeirceGrade N_plus i)).comp
          reindex.toAddMonoidHom =
        DirectSum.coeAddMonoidHom (peirceFiveGradeSubmodule N_plus) := by
    apply DirectSum.addHom_ext
    intro i a
    let idx := i
    change DirectSum.coeAddMonoidHom (fun j => cyclicPeirceGrade N_plus j)
        (DirectSum.equivCongrLeft cyclicPeirceReindex
          (DirectSum.of (fun j => peirceFiveGradeSubmodule N_plus j) i a)) =
      DirectSum.coeAddMonoidHom (peirceFiveGradeSubmodule N_plus)
        (DirectSum.of (fun j => peirceFiveGradeSubmodule N_plus j) i a)
    fin_cases i
    all_goals
      have hi : cyclicPeirceReindex.symm (cyclicPeirceReindex idx) = idx := by
        simp [cyclicPeirceReindex]
      let a0 : peirceFiveGradeSubmodule N_plus
          (cyclicPeirceReindex.symm (cyclicPeirceReindex idx)) := hi.symm ▸ a
      have hsource : DirectSum.of (fun j => peirceFiveGradeSubmodule N_plus j) idx a =
          DirectSum.of (fun j => peirceFiveGradeSubmodule N_plus j)
            (cyclicPeirceReindex.symm (cyclicPeirceReindex idx)) a0 := by
        cases hi
        rfl
      rw [hsource, DirectSum.equivCongrLeft_of]
      change DirectSum.coeAddMonoidHom
          (fun j => peirceFiveGradeSubmodule N_plus (cyclicPeirceReindex.symm j))
          (DirectSum.of
            (fun j => peirceFiveGradeSubmodule N_plus (cyclicPeirceReindex.symm j))
            (cyclicPeirceReindex idx) a0) =
        DirectSum.coeAddMonoidHom (peirceFiveGradeSubmodule N_plus)
          (DirectSum.of (fun j => peirceFiveGradeSubmodule N_plus j)
            (cyclicPeirceReindex.symm (cyclicPeirceReindex idx)) a0)
      rw [DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
  have hcoe (x : DirectSum (Fin 5) (fun i => peirceFiveGradeSubmodule N_plus i)) :
      DirectSum.coeAddMonoidHom (fun i => cyclicPeirceGrade N_plus i) (reindex x) =
        DirectSum.coeAddMonoidHom (peirceFiveGradeSubmodule N_plus) x :=
    DFunLike.congr_fun hcoeHom x
  have hold := peirce_five_grade_directSum_isInternal N_plus h_nil h_reg
  constructor
  · intro x y hxy
    have hOld :
        DirectSum.coeAddMonoidHom (peirceFiveGradeSubmodule N_plus) (reindex.symm x) =
          DirectSum.coeAddMonoidHom (peirceFiveGradeSubmodule N_plus) (reindex.symm y) := by
      calc
        DirectSum.coeAddMonoidHom (peirceFiveGradeSubmodule N_plus) (reindex.symm x) =
          DirectSum.coeAddMonoidHom (fun i => cyclicPeirceGrade N_plus i)
            (reindex (reindex.symm x)) := (hcoe _).symm
        _ = DirectSum.coeAddMonoidHom (fun i => cyclicPeirceGrade N_plus i)
            (reindex (reindex.symm y)) := by simpa using hxy
        _ = DirectSum.coeAddMonoidHom (peirceFiveGradeSubmodule N_plus) (reindex.symm y) :=
            hcoe _
    simpa using congrArg reindex (hold.1 hOld)
  · intro z
    obtain ⟨x, hx⟩ := hold.2 z
    exact ⟨reindex x, by simpa [hcoe x] using hx⟩

/-- The cyclic Peirce sectors satisfy Mathlib's native homogeneous-bracket
interface. Brackets that wrap outside the integer five-grade window vanish by
the direct Peirce-corner theorem, so no additive-torsion hypothesis is needed. -/
theorem cyclicPeirceGrade_bracket_mem (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (i j : Fin 5) (x y : B)
    (hx : x ∈ cyclicPeirceGrade N_plus i)
    (hy : y ∈ cyclicPeirceGrade N_plus j) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y ∈
      cyclicPeirceGrade N_plus (i + j) := by
  let gi := tkkGradeOfCyclicIndex i
  let gj := tkkGradeOfCyclicIndex j
  let gk := tkkGradeOfCyclicIndex (i + j)
  have hxi : x ∈ tkkPeirceGrade N_plus gi := by
    simpa [gi, cyclicPeirceGrade_eq_tkk] using hx
  have hyi : y ∈ tkkPeirceGrade N_plus gj := by
    simpa [gj, cyclicPeirceGrade_eq_tkk] using hy
  rw [cyclicPeirceGrade_eq_tkk]
  cases hsum : TKKJordanPairData.gradeAdd gi gj with
  | none =>
      have hzero := peirce_tkk_bracket_eq_zero_direct N_plus h_nil h_reg
        gi gj hsum x y hxi hyi
      rw [hzero]
      exact (tkkPeirceGrade N_plus gk).zero_mem
  | some k =>
      have hbr := peirce_tkk_bracket_mem_direct N_plus h_nil h_reg
        gi gj k hsum x y hxi hyi
      have hk : k = gk := by
        fin_cases i <;> fin_cases j <;>
          simp_all [gi, gj, gk, tkkGradeOfCyclicIndex,
            TKKJordanPairData.gradeAdd, TKKJordanPairData.ofWeight,
            TKKJordanPairData.weight]
      simpa [hk] using hbr

/-- The nilpotent-generated Peirce decomposition is a native Mathlib
`GradedLieAlgebra` indexed by the additive monoid `Fin 5`. -/
@[instance_reducible]
noncomputable def nilpotentPairCyclicGradedLieAlgebra
    (N_plus : B) (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    GradedLieAlgebra (cyclicPeirceGrade N_plus) where
  bracket_mem := by
    intro i j x y hx hy
    exact cyclicPeirceGrade_bracket_mem N_plus h_nil h_reg i j x y hx hy
  decompose' := (cyclicPeirceGrade_isInternal N_plus h_nil h_reg).chooseDecomposition.decompose'
  left_inv := (cyclicPeirceGrade_isInternal N_plus h_nil h_reg).chooseDecomposition.left_inv
  right_inv := (cyclicPeirceGrade_isInternal N_plus h_nil h_reg).chooseDecomposition.right_inv

end InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTits
