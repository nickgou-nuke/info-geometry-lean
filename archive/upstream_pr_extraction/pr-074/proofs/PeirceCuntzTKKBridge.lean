import proofs.CubicJordanPeirceDecomposition
import proofs.ChiralCuntzInductive
import proofs.PrimonCuntzTower

/-!
# Peirce / Cuntz bridge

This file packages the direct finite witness chain that is already present in
the repository:

* the Peirce tripotent identities;
* the parity-preserving chiral Cuntz induction;
* the finite Cuntz colimit compatibility on `PrimonCuntzTower`.

It does not claim any new analytic or exceptional-algebra embedding.
-/

noncomputable section

namespace PeirceCuntzTKKBridge

/-- Direct bridge theorem from the Peirce tripotent data to the finite Cuntz
tower compatibilities. -/
theorem peirce_cuntz_bridge_synthesis
    {A : Type*} [Ring A]
    (E1 E2 E3 : A)
    (h : CubicJordanPeirceDecomposition.PeirceIdempotents E1 E2 E3) :
    (CubicJordanPeirceDecomposition.Pcanonical E1 E2 *
        CubicJordanPeirceDecomposition.Pcanonical E1 E2 *
          CubicJordanPeirceDecomposition.Pcanonical E1 E2 =
      CubicJordanPeirceDecomposition.Pcanonical E1 E2) ∧
    (CubicJordanPeirceDecomposition.Pcanonical E1 E2 * E1 = E1) ∧
    (CubicJordanPeirceDecomposition.Pcanonical E1 E2 * E2 = -E2) ∧
    (CubicJordanPeirceDecomposition.Pcanonical E1 E2 * E3 = 0) ∧
    (∀ n (i : Fin (2 * n)),
      ChiralCuntzInductive.chiralParity
        (ChiralCuntzInductive.chiralStep n i) =
      ChiralCuntzInductive.chiralParity i) ∧
    (∀ n k (f : InfoGeometry.Quantum.PrimonCuntzTower.Stage n),
      InfoGeometry.Quantum.PrimonCuntzTower.stageToSequence
        (n + k) (InfoGeometry.Quantum.PrimonCuntzTower.embIter n k f) =
      InfoGeometry.Quantum.PrimonCuntzTower.stageToSequence n f) ∧
    (∀ n k (f : InfoGeometry.Quantum.PrimonCuntzTower.Stage n),
      InfoGeometry.Quantum.PrimonCuntzTower.stageToSequence
        (n + k)
        (InfoGeometry.Quantum.PrimonCuntzTower.diracHodgeCuntz (n + k)
          (InfoGeometry.Quantum.PrimonCuntzTower.embIter n k f)) =
      InfoGeometry.Quantum.PrimonCuntzTower.stageToSequence n
        (InfoGeometry.Quantum.PrimonCuntzTower.diracHodgeCuntz n f)) := by
  constructor
  · exact CubicJordanPeirceDecomposition.Pcanonical_is_tripotent
      (E1 := E1) (E2 := E2) (E3 := E3) h
  constructor
  · exact CubicJordanPeirceDecomposition.L_P_E1_eigen
      (E1 := E1) (E2 := E2) (E3 := E3) h
  constructor
  · exact CubicJordanPeirceDecomposition.L_P_E2_eigen
      (E1 := E1) (E2 := E2) (E3 := E3) h
  constructor
  · exact CubicJordanPeirceDecomposition.L_P_E3_zero
      (E1 := E1) (E2 := E2) (E3 := E3) h
  constructor
  · intro n i
    exact ChiralCuntzInductive.chiralStep_parity_preserving n i
  constructor
  · intro n k f
    exact InfoGeometry.Quantum.PrimonCuntzTower.stageToSequence_embIter n k f
  · intro n k f
    exact InfoGeometry.Quantum.PrimonCuntzTower.diracHodgeCuntz_embIter_compatible n k f

end PeirceCuntzTKKBridge
