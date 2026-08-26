import InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
import InfoGeometry.Algebra.Zorn.G2OneCellQuotientTransport
import InfoGeometry.Algebra.Zorn.G2ConcreteBruhatOrbitCertificate
import InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation

/-!
# Injectivity of the reduced 189-word quotient table

This owner records the exact reduced alignment boundary needed for quotient
injectivity.  The quotient equality is transported through the PC-word factor
interface; it is not an enumeration of the full automorphism carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeInjectivity

open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2OneCellQuotientTransport
open InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation

/-! The following theorem is the exact assembly boundary for distinct Weyl
    representatives.  The separation premise is intentionally explicit:
    this file does not manufacture it by enumeration. -/

theorem pc_weyl_representative_eq_implies_index_eq
    (hsep : ∀ {k l : Fin 12}, k ≠ l →
      ∀ a c d : G2TwoSylowSubgroup.PCWordExp,
        G2TwoSylowSubgroup.pcWord c * orbitWeylRepresentative l =
          G2TwoSylowSubgroup.pcWord a * orbitWeylRepresentative k *
            G2TwoSylowSubgroup.pcWord d → False)
    {k l : Fin 12}
    {a c d : G2TwoSylowSubgroup.PCWordExp}
    (heq : G2TwoSylowSubgroup.pcWord c * orbitWeylRepresentative l =
      G2TwoSylowSubgroup.pcWord a * orbitWeylRepresentative k *
        G2TwoSylowSubgroup.pcWord d) :
    k = l := by
  by_contra hkl
  exact hsep hkl a c d heq

/-! The following lemma isolates the geometric part of residual alignment.
It uses only right Borel invariance of a concrete cell and pairwise
disjointness of distinct cells; no enumeration of the ambient automorphism
carrier is involved. -/

theorem quotient_common_cell_of_cell_separation
    (hcell : ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
      flagRepresentative i ∈
        concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
    (hdisj : ∀ (k l : Fin 12), k ≠ l →
      Disjoint
        (concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
        (concreteBruhatCell (weylNF (orbitWeyl l).1 (orbitWeyl l).2))) :
    ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12, i ∈ orbitCells k ∧ j ∈ orbitCells k := by
  intro i j hij
  have hi : i ∈ Finset.univ.biUnion orbitCells := by
    rw [orbitCells_partition]
    exact Finset.mem_univ i
  have hj : j ∈ Finset.univ.biUnion orbitCells := by
    rw [orbitCells_partition]
    exact Finset.mem_univ j
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hi hj
  obtain ⟨k, hik⟩ := hi
  obtain ⟨l, hjl⟩ := hj
  have hu : (flagRepresentative i)⁻¹ * flagRepresentative j ∈
      unipotentSubgroup :=
    (quotientRepresentative_eq_iff i j).mp hij
  have hus : (flagRepresentative i)⁻¹ * flagRepresentative j ∈
      sylowTwoSubgroup := by
    rw [sylowTwoSubgroup_eq_unipotentSubgroup]
    exact hu
  have hij_factor : flagRepresentative j =
      flagRepresentative i *
        ((flagRepresentative i)⁻¹ * flagRepresentative j) := by
    group
  have hi_cell := hcell k i hik
  have hj_in_k : flagRepresentative j ∈
      concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2) := by
    rw [hij_factor]
    exact concreteBruhatCell_right_mul _ _ _ hus hi_cell
  have hj_cell := hcell l j hjl
  have hkl : k = l := by
    by_contra hkl
    exact (Set.disjoint_left.mp (hdisj k l hkl)) hj_in_k hj_cell
  subst l
  exact ⟨k, hik, hjl⟩

theorem quotient_alignment_of_cell_separation
    (hcell : ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
      flagRepresentative i ∈
        concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
    (hdisj : ∀ (k l : Fin 12), k ≠ l →
      Disjoint
        (concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
        (concreteBruhatCell (weylNF (orbitWeyl l).1 (orbitWeyl l).2)))
    (hresidual_align : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      quotientRepresentative i = quotientRepresentative j →
      residualWord k i = residualWord k j) :
    ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            residualWord k i = residualWord k j := by
  intro i j hij
  obtain ⟨k, hik, hjk⟩ :=
    quotient_common_cell_of_cell_separation hcell hdisj i j hij
  exact ⟨k, hik, hjk, hresidual_align k i j hik hjk hij⟩

/-! The concrete representative-membership obligation is already certified by
`G2OneCellQuotientTransport.all_cells_representative_mem`.  This specialization
therefore exposes the remaining separation boundary without duplicating the
quotient-to-double-coset transport proof. -/

theorem quotient_alignment_of_concrete_cell_separation
    (hdisj : ∀ (k l : Fin 12), k ≠ l →
      Disjoint
        (concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
        (concreteBruhatCell (weylNF (orbitWeyl l).1 (orbitWeyl l).2)))
    (hresidual_align : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      quotientRepresentative i = quotientRepresentative j →
      residualWord k i = residualWord k j) :
    ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            residualWord k i = residualWord k j := by
  apply quotient_alignment_of_cell_separation
  · exact all_cells_representative_mem
  · exact hdisj
  · exact hresidual_align

/-! Quotient-orbit separation is the preferred concrete boundary: the finite
flag certificate proves disjointness on the quotient, while the existing BN
transport theorem converts it to disjointness of the concrete cells. -/

theorem quotient_alignment_of_quotientOrbit_separation
    (hsep : ∀ (k l : Fin 12), k ≠ l →
      Disjoint
        (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
          unipotentSubgroup
          (weylNF (orbitWeyl k).1 (orbitWeyl k).2))
        (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
          unipotentSubgroup
          (weylNF (orbitWeyl l).1 (orbitWeyl l).2)))
    (hresidual_align : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      quotientRepresentative i = quotientRepresentative j →
      residualWord k i = residualWord k j) :
    ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            residualWord k i = residualWord k j := by
  apply quotient_alignment_of_concrete_cell_separation
  · intro k l hkl
    exact concreteBruhatCell_disjoint_of_quotientOrbit_separation
      (weylNF (orbitWeyl k).1 (orbitWeyl k).2)
      (weylNF (orbitWeyl l).1 (orbitWeyl l).2)
      (hsep k l hkl)
  · exact hresidual_align

theorem quotient_alignment_of_pc_separation
    (hsep : ∀ {k l : Fin 12}, k ≠ l →
      ∀ a c d : G2TwoSylowSubgroup.PCWordExp,
        G2TwoSylowSubgroup.pcWord c * orbitWeylRepresentative l =
            G2TwoSylowSubgroup.pcWord a * orbitWeylRepresentative k *
              G2TwoSylowSubgroup.pcWord d → False)
    (hresidual_align : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      quotientRepresentative i = quotientRepresentative j →
      residualWord k i = residualWord k j) :
    ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            residualWord k i = residualWord k j := by
  apply quotient_alignment_of_quotientOrbit_separation
    (quotientOrbit_disjoint_of_pc_separation hsep)
  exact hresidual_align

theorem quotientRepresentative_injective_of_residual_alignment
    (halign : ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            residualWord k i = residualWord k j) :
    Function.Injective quotientRepresentative := by
  intro i j h
  obtain ⟨k, hik, hjk, hres⟩ := halign i j h
  exact residualWord_injective_on_cell k i j hik hjk hres

/-- Once the residual alignment and quotient coverage are supplied, the
189-entry representative table is the required quotient equivalence.  This
is the canonical assembly point: no enumeration of `SplitOctF2Aut` is used.
-/
noncomputable def quotientRepresentativeEquiv
    (halign : ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            residualWord k i = residualWord k j)
    (hsurj : Function.Surjective quotientRepresentative) :
    Fin 189 ≃
      InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative.CarrierQuotient :=
  Equiv.ofBijective quotientRepresentative
    ⟨quotientRepresentative_injective_of_residual_alignment halign, hsurj⟩

/-! The quotient equivalence is the exact final reduction interface for the
ambient order.  No enumeration of the full automorphism carrier is performed
here; the order reduction uses the certified subgroup cardinality. -/

theorem nat_card_splitOctF2Aut_eq_12096_of_quotientRepresentativeEquiv
    (e : Fin 189 ≃
      InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative.CarrierQuotient) :
    Nat.card SplitOctF2Aut = 12096 := by
  exact InfoGeometry.Algebra.Zorn.G2ConcreteBruhatOrbitCertificate.ambient_order e

end InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeInjectivity
