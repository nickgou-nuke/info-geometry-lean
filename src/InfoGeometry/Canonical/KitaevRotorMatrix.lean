/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import InfoGeometry.Canonical.KitaevBoundaryAlgebra
import InfoGeometry.Canonical.PeirceRotorAction

/-! Polynomial rotor action in the native conserved boundary matrix algebra.
No metric-unitarity or circle normalization is assumed. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevRotorMatrix
open InfoGeometry.Quantum.KitaevChain
open KitaevBoundaryDiracPair KitaevBoundaryAlgebra ReflexiveNilpotentFlows
open PeirceRotorAction
variable {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ}

theorem boundary_rotor_eq_matrix (hN : 0 < N)
    (ops : MajoranaCliffordOperators N A) (c s : ℂ) :
    ReflexiveNilpotentFlows.rotor c s (boundaryAnnihilation hN ops) (boundaryCreation hN ops) =
      boundaryMatrixHom hN ops !![c, s; -s, c] := by
  have hF : boundaryMatrixHom hN ops !![c, s; -s, c] =
      c • support (boundaryAnnihilation hN ops) (boundaryCreation hN ops) +
      s • (boundaryAnnihilation hN ops - boundaryCreation hN ops) := by
    change pairMatrixLinear _ _ _ = _
    simp [pairMatrixLinear_apply, pairMatrixUnit, support, smul_add, smul_sub]
    abel
  rw [hF]
  unfold ReflexiveNilpotentFlows.rotor complement
  rw [boundary_support]
  simp

theorem boundary_movingPlus_eq_matrix (hN : 0 < N)
    (ops : MajoranaCliffordOperators N A) (c s : ℂ) :
    movingPlus c s (boundaryAnnihilation hN ops) (boundaryCreation hN ops) =
      boundaryMatrixHom hN ops !![c*c, -(c*s); -(c*s), s*s] := by
  rw [movingPlus_expansion (boundaryAnnihilation_sq hN ops)
    (boundaryCreation_sq hN ops) (boundary_reflexive hN ops).1
    (boundary_reflexive hN ops).2]
  change _ = pairMatrixLinear _ _ _
  simp [pairMatrixLinear_apply, pairMatrixUnit, smul_add]
  abel

theorem boundary_movingPlus_commutes (hN : 0 < N)
    (ops : MajoranaCliffordOperators N A) (c s t : ℂ) :
    Commute (movingPlus c s (boundaryAnnihilation hN ops) (boundaryCreation hN ops))
      (sweetSpotHamiltonian ops.toMajoranaOperators (algebraMap ℂ A t)) := by
  rw [boundary_movingPlus_eq_matrix]
  exact boundaryMatrixHom_commutes hN ops t _

end InfoGeometry.Canonical.KitaevRotorMatrix
