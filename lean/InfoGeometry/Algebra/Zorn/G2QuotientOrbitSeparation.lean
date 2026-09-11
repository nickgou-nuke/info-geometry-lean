import InfoGeometry.Algebra.Zorn.G2BNPair
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2BNBruhatFramework
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

namespace InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation

open InfoGeometry.Algebra.Zorn.G2BNPair
open InfoGeometry.Algebra.Zorn.G2BNBruhatFramework
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev CarrierQuotient :=
  SplitOctF2Aut ⧸ unipotentSubgroup

noncomputable def orbitWeylRepresentative (k : Fin 12) : SplitOctF2Aut :=
  weylNF (orbitWeyl k).1 (orbitWeyl k).2

/-- A finite PC-coordinate separation certificate implies disjointness of the
left `U`-orbits in the quotient.  The certificate is deliberately phrased in
the concrete group and has no quotient or ambient-carrier enumeration. -/
theorem quotientOrbit_disjoint_of_pc_separation
    (hsep : ∀ {k l : Fin 12}, k ≠ l →
      ∀ a c d : G2TwoSylowSubgroup.PCWordExp,
        G2TwoSylowSubgroup.pcWord c * orbitWeylRepresentative l =
          G2TwoSylowSubgroup.pcWord a * orbitWeylRepresentative k *
            G2TwoSylowSubgroup.pcWord d → False) :
    ∀ {k l : Fin 12}, k ≠ l →
      Disjoint
        (quotientOrbit unipotentSubgroup (orbitWeylRepresentative k))
        (quotientOrbit unipotentSubgroup (orbitWeylRepresentative l)) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro q hqk hql
  rcases hqk with ⟨b, hb, hbk⟩
  rcases hql with ⟨c, hc, hcl⟩
  rcases hb with ⟨a, rfl⟩
  rcases hc with ⟨d, rfl⟩
  have hq :
      (QuotientGroup.mk
          (G2TwoSylowSubgroup.pcWord a * orbitWeylRepresentative k) :
        CarrierQuotient) =
        QuotientGroup.mk
          (G2TwoSylowSubgroup.pcWord d * orbitWeylRepresentative l) :=
    hbk.trans hcl.symm
  rw [QuotientGroup.eq] at hq
  rcases hq with ⟨e, he⟩
  exact hsep hkl a d e (by
    calc
      G2TwoSylowSubgroup.pcWord d * orbitWeylRepresentative l =
        (G2TwoSylowSubgroup.pcWord a * orbitWeylRepresentative k) *
          ((G2TwoSylowSubgroup.pcWord a * orbitWeylRepresentative k)⁻¹ *
            (G2TwoSylowSubgroup.pcWord d * orbitWeylRepresentative l)) := by
        group
      _ = (G2TwoSylowSubgroup.pcWord a * orbitWeylRepresentative k) *
          G2TwoSylowSubgroup.pcWord e := by
        rw [← he])

/-! The identity cell is already separated concretely in the older BN
    framework.  Transporting that theorem through the exact double-coset
    equality closes the eleven identity-versus-nonidentity quotient pairs
    without enumerating PC triples. -/

theorem quotientOrbit_zero_disjoint
    {l : Fin 12} (hl : l ≠ 0) :
    Disjoint
      (quotientOrbit unipotentSubgroup (orbitWeylRepresentative 0))
      (quotientOrbit unipotentSubgroup (orbitWeylRepresentative l)) := by
  let j : Fin 12 := concreteWeylIndexInv (orbitWeyl l)
  have hj : j ≠ 0 := by
    intro hj0
    have hidx : concreteWeylIndex j = orbitWeyl l :=
      concreteWeylIndexInv_right (orbitWeyl l)
    rw [hj0] at hidx
    fin_cases l
    · exact hl rfl
    all_goals
      norm_num [orbitWeyl, G2FlagWordCertificate.flagWeyl,
        concreteWeylIndex] at hidx
    all_goals cases hidx
  have hcell :
      Disjoint
        (G2BNBruhatFramework.concreteBruhatCell 0)
        (G2BNBruhatFramework.concreteBruhatCell j) :=
    concreteBruhatCell_zero_disjoint j hj
  change Disjoint
    (doubleCoset unipotentSubgroup (concreteWeylElement 0))
    (doubleCoset unipotentSubgroup (concreteWeylElement j)) at hcell
  have hrep :
      concreteWeylElement j = orbitWeylRepresentative l := by
    rw [concreteWeylElement_eq_weylNF_index]
    change weylNF (concreteWeylIndex j).1 (concreteWeylIndex j).2 = _
    rw [concreteWeylIndexInv_right]
    rfl
  rw [hrep] at hcell
  have hzero : concreteWeylElement 0 = orbitWeylRepresentative 0 := by
    rw [concreteWeylElement_zero_eq_weylNF_zero_false,
      weylNF_zero_false]
    rfl
  rw [hzero] at hcell
  exact disjoint_quotientOrbit_of_disjoint_doubleCoset
    unipotentSubgroup (orbitWeylRepresentative 0)
      (orbitWeylRepresentative l) hcell

end InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation
