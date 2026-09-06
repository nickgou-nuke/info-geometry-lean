import InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup

namespace InfoGeometry.Algebra.Zorn.G2RelativeWeylIntersection

open InfoGeometry.Algebra.Zorn.G2BNBruhatFramework
open InfoGeometry.Algebra.Zorn.G2BNPair
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-!
Structural relative-Weyl boundary for the quotient separation argument.

This file does not enumerate PC words.  It only uses that the concrete Weyl
representatives lie in `concreteN` and that `unipotentSubgroup ∩ concreteN`
is trivial.
-/

theorem orbitWeylRepresentative_mem_concreteN (k : Fin 12) :
    orbitWeylRepresentative k ∈ concreteN := by
  let j : Fin 12 := concreteWeylIndexInv (orbitWeyl k)
  have hj : concreteWeylElement j = orbitWeylRepresentative k := by
    rw [concreteWeylElement_eq_weylNF_index]
    rw [concreteWeylIndexInv_right]
    rfl
  rw [← hj]
  exact concreteWeylElement_mem j

theorem relative_orbitWeyl_not_mem_unipotent
    {k l : Fin 12} (hkl : k ≠ l) :
    orbitWeylRepresentative l *
        (orbitWeylRepresentative k)⁻¹ ∉ unipotentSubgroup := by
  intro hU
  have hN : orbitWeylRepresentative l *
        (orbitWeylRepresentative k)⁻¹ ∈ concreteN := by
    exact concreteN.mul_mem
      (orbitWeylRepresentative_mem_concreteN l)
      (concreteN.inv_mem (orbitWeylRepresentative_mem_concreteN k))
  have hInf : orbitWeylRepresentative l *
        (orbitWeylRepresentative k)⁻¹ ∈
      unipotentSubgroup ⊓ concreteN :=
    ⟨hU, hN⟩
  rw [unipotent_inter_concreteN_eq_bot] at hInf
  have hOne : orbitWeylRepresentative l *
        (orbitWeylRepresentative k)⁻¹ = 1 :=
    Subgroup.mem_bot.mp hInf
  have hRep : orbitWeylRepresentative l = orbitWeylRepresentative k := by
    calc
      orbitWeylRepresentative l =
          (orbitWeylRepresentative l *
            (orbitWeylRepresentative k)⁻¹) *
            orbitWeylRepresentative k := by simp [mul_assoc]
      _ = 1 * orbitWeylRepresentative k := by rw [hOne]
      _ = orbitWeylRepresentative k := one_mul _
  have hParam : orbitWeyl l = orbitWeyl k := by
    apply weylNF_injective
    exact hRep
  have horbit : Function.Injective orbitWeyl := by
    decide
  exact hkl (horbit hParam.symm)

theorem orbitWeylRepresentative_quotient_mk_injective :
    Function.Injective (fun k : Fin 12 =>
      (QuotientGroup.mk (orbitWeylRepresentative k) : CarrierQuotient)) := by
  intro k l hq
  rw [QuotientGroup.eq] at hq
  rcases hq with ⟨e, he⟩
  have hU : (orbitWeylRepresentative k)⁻¹ *
        orbitWeylRepresentative l ∈ unipotentSubgroup := by
    rw [← he]
    exact ⟨e, rfl⟩
  have hN : (orbitWeylRepresentative k)⁻¹ *
        orbitWeylRepresentative l ∈ concreteN := by
    exact concreteN.mul_mem
      (concreteN.inv_mem (orbitWeylRepresentative_mem_concreteN k))
      (orbitWeylRepresentative_mem_concreteN l)
  have hInf : (orbitWeylRepresentative k)⁻¹ *
        orbitWeylRepresentative l ∈ unipotentSubgroup ⊓ concreteN :=
    ⟨hU, hN⟩
  rw [unipotent_inter_concreteN_eq_bot] at hInf
  have hOne : (orbitWeylRepresentative k)⁻¹ *
        orbitWeylRepresentative l = 1 :=
    Subgroup.mem_bot.mp hInf
  have hRep : orbitWeylRepresentative k = orbitWeylRepresentative l := by
    have h' := congrArg
      (fun x : SplitOctF2Aut => orbitWeylRepresentative k * x) hOne
    simpa [mul_assoc] using h'.symm
  have hParam : orbitWeyl k = orbitWeyl l := by
    apply weylNF_injective
    exact hRep
  have horbit : Function.Injective orbitWeyl := by
    decide
  exact horbit hParam

theorem quotientOrbit_disjoint_of_invariant_readout
    {ι : Type*}
    (readout : CarrierQuotient → ι)
    (hinv : ∀ (b : SplitOctF2Aut), b ∈ unipotentSubgroup →
      ∀ q : CarrierQuotient, readout (b • q) = readout q)
    {k l : Fin 12}
    (hread : readout
        (QuotientGroup.mk (orbitWeylRepresentative k)) ≠
      readout
        (QuotientGroup.mk (orbitWeylRepresentative l))) :
    Disjoint
      (quotientOrbit unipotentSubgroup (orbitWeylRepresentative k))
      (quotientOrbit unipotentSubgroup (orbitWeylRepresentative l)) := by
  rw [Set.disjoint_left]
  intro q hqk hql
  rcases hqk with ⟨b, hb, hbk⟩
  rcases hql with ⟨c, hc, hcl⟩
  apply hread
  calc
    readout (QuotientGroup.mk (orbitWeylRepresentative k)) =
        readout (b • QuotientGroup.mk (orbitWeylRepresentative k)) := by
          symm
          exact hinv b hb _
    _ = readout q := by rw [hbk]
    _ = readout (c • QuotientGroup.mk (orbitWeylRepresentative l)) := by
          rw [hcl]
    _ = readout (QuotientGroup.mk (orbitWeylRepresentative l)) := hinv c hc _

end InfoGeometry.Algebra.Zorn.G2RelativeWeylIntersection
