/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevBoundaryDiracConservation
import InfoGeometry.Canonical.ReflexiveMatrixCorner

/-! The boundary CAR pair represents a unital matrix algebra whose entire
image commutes with the native chain. This is not a classification of the commutant. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevBoundaryAlgebra
open InfoGeometry.Quantum.KitaevChain
open KitaevBoundaryDiracPair KitaevBoundaryDiracConservation ReflexiveNilpotentFlows
variable {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ}

/-- Native unital representation supplied by the full-support boundary pair. -/
def boundaryMatrixHom (hN : 0 < N) (ops : MajoranaCliffordOperators N A) :
    Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] A :=
  pairMatrixAlgHom (boundaryAnnihilation_sq hN ops) (boundaryCreation_sq hN ops)
    (boundary_reflexive hN ops).1 (boundary_reflexive hN ops).2
    (boundary_support hN ops)

theorem boundaryMatrixHom_commutes (hN : 0 < N)
    (ops : MajoranaCliffordOperators N A) (t : ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Commute (boundaryMatrixHom hN ops M)
      (sweetSpotHamiltonian ops.toMajoranaOperators (algebraMap ℂ A t)) := by
  have hd := boundaryAnnihilation_commutes hN ops t
  have hB := boundaryCreation_commutes hN ops t
  have hs (c : ℂ) (x : A)
      (hx : Commute x (sweetSpotHamiltonian ops.toMajoranaOperators (algebraMap ℂ A t))) :
      Commute (c • x) (sweetSpotHamiltonian ops.toMajoranaOperators (algebraMap ℂ A t)) := by
    rw [Algebra.smul_def]
    exact Commute.mul_left (Algebra.commutes c _) hx
  change Commute (pairMatrixLinear _ _ M) _
  simp only [pairMatrixLinear_apply, pairMatrixUnit]
  exact ((hs _ _ (hd.mul_left hB)).add_left (hs _ _ hd)).add_left
    (hs _ _ hB) |>.add_left (hs _ _ (hB.mul_left hd))

end InfoGeometry.Canonical.KitaevBoundaryAlgebra
