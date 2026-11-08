import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
import InfoGeometry.Algebra.Zorn.G2TwoPCGroup
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

/-!
# Canonical PC collector for integer factorization words

The six PC generators are not all involutions.  A support-set encoding of a
factorization therefore loses information.  This owner collects the actual
integer powers in the finite `PCExponent` group before mapping to the concrete
automorphism subgroup.
-/

namespace InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector

open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

abbrev FactorToken := Fin 6 × Int
abbrev FactorWord := List FactorToken

def tokenAutomorphism (t : FactorToken) :
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut :=
  (pcGenerator t.1) ^ t.2

noncomputable def collect : FactorWord →
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut
  | [] => 1
  | t :: w => tokenAutomorphism t * collect w

theorem collect_token (t : FactorToken) :
    tokenAutomorphism t = (pcGenerator t.1) ^ t.2 := by
  rfl

theorem collect_eq_factor_product (w : FactorWord) :
    collect w =
      (w.map (fun t =>
        (pcGenerator t.1) ^ t.2)).prod := by
  induction w with
  | nil => simp [collect]
  | cons t w ih =>
      simp only [collect, List.map_cons, List.prod_cons]
      rw [ih]
      rw [collect_token]

theorem collect_append (u v : FactorWord) :
    collect (u ++ v) = collect u * collect v := by
  induction u with
  | nil => simp [collect]
  | cons t u ih =>
      simp only [List.cons_append, collect]
      rw [ih]
      simp [mul_assoc]

theorem tokenAutomorphism_mem_unipotentSubgroup (t : FactorToken) :
    tokenAutomorphism t ∈ unipotentSubgroup := by
  exact Subgroup.zpow_mem unipotentSubgroup
    (show pcGenerator t.1 ∈ unipotentSubgroup from
      ⟨oneAt t.1, pcWord_oneAt_eq_generator t.1⟩) t.2

theorem collect_mem_unipotentSubgroup (w : FactorWord) :
    collect w ∈ unipotentSubgroup := by
  induction w with
  | nil => exact unipotentSubgroup.one_mem
  | cons t w ih =>
      exact unipotentSubgroup.mul_mem
        (tokenAutomorphism_mem_unipotentSubgroup t) ih

noncomputable def collectSubtype (w : FactorWord) : unipotentSubgroup :=
  ⟨collect w, collect_mem_unipotentSubgroup w⟩

@[simp] theorem collectSubtype_val (w : FactorWord) :
    (collectSubtype w).1 = collect w := rfl

theorem collectSubtype_append (u v : FactorWord) :
    (collectSubtype (u ++ v)).1 =
      (collectSubtype u).1 * (collectSubtype v).1 := by
  simp [collect_append]

end InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
