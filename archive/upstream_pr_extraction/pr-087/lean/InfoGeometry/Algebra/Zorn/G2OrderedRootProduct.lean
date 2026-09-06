import InfoGeometry.Algebra.Zorn.G2BruhatResidualEquiv
import InfoGeometry.Algebra.Zorn.G2RootResidualGenerators
import InfoGeometry.Algebra.Zorn.G2CanonicalTopInversionOrder
import InfoGeometry.Algebra.Zorn.G2BruhatResidual

namespace InfoGeometry.Algebra.Zorn.G2OrderedRootProduct

open InfoGeometry.Algebra.Zorn.G2BruhatResidualEquiv
open InfoGeometry.Algebra.Zorn.G2RootResidualGenerators
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.GroupTheory.G2BruhatInversions
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2CanonicalTopInversionOrder
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def orderedRootProduct (p : WeylG2)
    (e : BruhatResidualExponent p) : SplitOctF2Aut :=
  (List.ofFn (fun i : Fin (dihedralLength p) =>
    if e (orderedInversionRoots p i) then
      rootResidualGenerator (orderedInversionRoots p i).1
    else 1)).prod

theorem orderedRootProduct_mem_unipotentSubgroup (p : WeylG2)
    (e : BruhatResidualExponent p) :
    orderedRootProduct p e ∈ unipotentSubgroup := by
  classical
  apply unipotentSubgroup.list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  by_cases h : e (orderedInversionRoots p i)
  · simp only [h]
    exact rootResidualGenerator_mem_unipotentSubgroup
      (orderedInversionRoots p i).1
  · simp only [h]
    exact unipotentSubgroup.one_mem

theorem orderedRootProduct_mem_topResidualSubgroup
    (e : BruhatResidualExponent (3, false)) :
    orderedRootProduct (3, false) e ∈ residualSubgroup (3, false) := by
  rw [residualSubgroup_top_parameter]
  exact orderedRootProduct_mem_unipotentSubgroup (3, false) e

noncomputable def topPCExponent
    (e : BruhatResidualExponent (3, false)) : Fin 6 → Bool :=
  fun i => e (topOrderedInversionRoots i)

noncomputable def topOrderedRootProduct
    (e : BruhatResidualExponent (3, false)) : SplitOctF2Aut :=
  (List.ofFn (fun i : Fin 6 =>
    if e (topOrderedInversionRoots i) then
      rootResidualGenerator (topOrderedInversionRoots i).1
    else 1)).prod

theorem topOrderedRootProduct_eq_pcWord
    (e : BruhatResidualExponent (3, false)) :
    topOrderedRootProduct e = G2TwoSylowSubgroup.pcWord (topPCExponent e) := by
  unfold topOrderedRootProduct G2TwoSylowSubgroup.pcWord
  have hfun :
      (fun i : Fin 6 =>
        if e (topOrderedInversionRoots i) then
          rootResidualGenerator (topOrderedInversionRoots i).1
        else 1) =
      (fun i : Fin 6 => if topPCExponent e i then pcGenerator i else 1) := by
    funext i
    simp [topPCExponent, rootResidualGenerator_eq_pcGenerator,
      topOrderedInversionRoots_apply]
  exact congrArg List.prod (congrArg List.ofFn hfun)

end InfoGeometry.Algebra.Zorn.G2OrderedRootProduct
