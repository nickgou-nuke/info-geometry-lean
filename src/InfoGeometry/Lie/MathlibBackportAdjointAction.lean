import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.AdjointAction.Basic
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import InfoGeometry.Lie.MathlibBackportJordanChevalley

/-! Project-owned adjoint Jordan--Chevalley compatibility lemmas. -/

section

open Algebra
open scoped Polynomial
attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieAlgebra

variable {K V : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

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
