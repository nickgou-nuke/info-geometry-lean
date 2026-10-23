/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2CorrectedCosetSignature
import InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation

/-! Separate native Weyl double cosets using finite point-line signatures. -/
namespace InfoGeometry.Algebra.Zorn.G2SignatureCellSeparation

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2CorrectedCosetSignature G2QuotientOrbitSeparation
open G2TwoSylowSubgroup G2TwoPCSubgroupClosure

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem signature_anchor_separation :
    ∀ (k l : Fin 12) (a : PCWordExp),
      cosetSignature (pcWord a * orbitWeylRepresentative k) =
        cosetSignature (orbitWeylRepresentative l) → k = l := by
  decide

theorem quotient_orbits_disjoint {k l : Fin 12} (hkl : k ≠ l) :
    Disjoint
      (G2BNPair.quotientOrbit unipotentSubgroup (orbitWeylRepresentative k))
      (G2BNPair.quotientOrbit unipotentSubgroup (orbitWeylRepresentative l)) := by
  apply quotientOrbit_disjoint_of_pc_separation ?_ hkl
  intro k l hkl a c d h
  have ha : pcWord a ∈ unipotentSubgroup := ⟨a, rfl⟩
  have hc : pcWord c ∈ unipotentSubgroup := ⟨c, rfl⟩
  obtain ⟨e, he⟩ := unipotentSubgroup.mul_mem
    (unipotentSubgroup.inv_mem hc) ha
  have heq : orbitWeylRepresentative l =
      (pcWord e * orbitWeylRepresentative k) * pcWord d := by
    rw [he]
    calc orbitWeylRepresentative l =
        (pcWord c)⁻¹ * (pcWord c * orbitWeylRepresentative l) := by group
      _ = _ := by rw [h]; group
  have hs := congrArg cosetSignature heq
  rw [cosetSignature_mul_right _ (show pcWord d ∈ unipotentSubgroup from ⟨d, rfl⟩)] at hs
  exact hkl (signature_anchor_separation k l e hs.symm)

theorem cells_disjoint {k l : Fin 12} (hkl : k ≠ l) :
    Disjoint
      (G2TwoBruhatClassification.concreteBruhatCell (orbitWeylRepresentative k))
      (G2TwoBruhatClassification.concreteBruhatCell (orbitWeylRepresentative l)) :=
  G2TwoBruhatClassification.concreteBruhatCell_disjoint_of_quotientOrbit_separation
    _ _ (quotient_orbits_disjoint hkl)

end InfoGeometry.Algebra.Zorn.G2SignatureCellSeparation
