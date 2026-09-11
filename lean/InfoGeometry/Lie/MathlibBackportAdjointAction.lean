module

import Mathlib.Algebra.Field.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.LinearAlgebra.JordanChevalley
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RingTheory.Adjoin.Polynomial
public import InfoGeometry.Lie.MathlibBackportJordanChevalley

/-! Project-owned adjoint Jordan--Chevalley compatibility lemmas. -/

public section

open Algebra
open scoped Polynomial
attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

namespace LieAlgebra

theorem commute_ad_of_commute {a b : A} (h : Commute a b) :
    Commute (ad R A a) (ad R A b) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero, ← Ring.lie_def,
    ← (ad R A).map_lie, Ring.lie_def, sub_eq_zero.mpr h, map_zero]

variable {K V : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem ad_isSemisimple_of_isSemisimple {a : Module.End K V}
    (ha : a.IsSemisimple) :
    (ad K (Module.End K V) a).IsSemisimple := by
  rw [ad_eq_lmul_left_sub_lmul_right]
  have hl : Module.End.IsSemisimple (LinearMap.mulLeft K a) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
    have h : Polynomial.aeval (Algebra.lmul K (Module.End K V) a) (minpoly K a) = 0 := by
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    simpa using h
  have hr : Module.End.IsSemisimple (LinearMap.mulRight K a) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
    have h : LinearMap.mulRight K a =
        (Algebra.lsmul (A := (Module.End K V)ᵐᵒᵖ) K K (Module.End K V)) (.op a) := by
      ext
      simp [Algebra.lsmul]
    rw [h]
    rw [Polynomial.aeval_algHom_apply]
    have hmin : Polynomial.aeval a (minpoly K a) = 0 := minpoly.aeval K a
    have hpoly (p : K[X]) :
        Polynomial.aeval (MulOpposite.op a) p =
          MulOpposite.op (Polynomial.aeval a p) := by
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp [hp, hq]
      | monomial n c =>
          rw [Polynomial.aeval_def, Polynomial.eval₂_monomial,
            Polynomial.aeval_def, Polynomial.eval₂_monomial]
          change MulOpposite.op ((algebraMap K (Module.End K V)) c) *
            MulOpposite.op (a ^ n) = _
          rw [← MulOpposite.op_mul]
          exact congrArg MulOpposite.op (Algebra.commutes c (a ^ n)).symm
    ext x
    rw [hpoly, hmin]
    simp
  exact hl.sub_of_commute (LinearMap.commute_mulLeft_right a a) hr

variable {n s : Module.End K V}

theorem ad_mem_adjoin_of_isSemisimple
    (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple) :
    ad K (Module.End K V) s ∈
      Algebra.adjoin K {ad K (Module.End K V) (n + s)} := by
  obtain ⟨n', hn'_adj, s', hs'_adj, hn'_nil, hs'_ss, h_jc⟩ :=
    (ad K (Module.End K V) (n + s)).exists_isNilpotent_isSemisimple
  have hc' : Commute n' s' :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs'_adj
      (Algebra.commute_of_mem_adjoin_self hn'_adj).symm
  obtain ⟨-, hs_eq⟩ := Module.End.isNilpotent_isSemisimple_unique hn'_nil hs'_ss
    (LieAlgebra.ad_nilpotent_of_nilpotent (R := K) hn)
    (LieAlgebra.ad_isSemisimple_of_isSemisimple hs) hc'
    (LieAlgebra.commute_ad_of_commute hc)
    (h_jc.symm.trans (map_add (ad K (Module.End K V)) n s))
  rwa [hs_eq] at hs'_adj

theorem ad_mem_adjoin_of_isNilpotent
    (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple) :
    ad K (Module.End K V) n ∈
      Algebra.adjoin K {ad K (Module.End K V) (n + s)} := by
  have h : ad K (Module.End K V) n =
      ad K (Module.End K V) (n + s) - ad K (Module.End K V) s := by
    simp [map_add]
  rw [h]
  exact sub_mem (Algebra.self_mem_adjoin_singleton K _)
    (ad_mem_adjoin_of_isSemisimple hc hn hs)

end LieAlgebra
