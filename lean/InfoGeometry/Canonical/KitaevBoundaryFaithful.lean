/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevBoundaryAlgebra
import InfoGeometry.Canonical.KitaevBoundaryKrein
import InfoGeometry.Canonical.KitaevBoundaryConstructedMetric
import Mathlib.RingTheory.SimpleRing.Matrix

/-! Faithful matrix-algebra representation and reflection of exact boundary
operator equations. The target metric is constructed from the endpoints. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevBoundaryFaithful

open InfoGeometry.Quantum.KitaevChain
open KitaevBoundaryDiracPair KitaevBoundaryAlgebra KitaevBoundaryKrein
open KitaevBoundaryConstructedMetric ReflexiveNilpotentFlows

variable {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ}
variable (hN : 0 < N) (ops : MajoranaCliffordOperators N A)

theorem boundaryMatrixHom_injective [Nontrivial A] :
    Function.Injective (boundaryMatrixHom hN ops) :=
  (boundaryMatrixHom hN ops).toRingHom.injective

theorem boundaryMatrixHom_square_zero_iff [Nontrivial A]
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    boundaryMatrixHom hN ops M * boundaryMatrixHom hN ops M = 0 ↔ M * M = 0 := by
  rw [← map_mul, ← map_zero (boundaryMatrixHom hN ops)]
  exact (boundaryMatrixHom_injective hN ops).eq_iff

variable [StarRing A] [StarModule ℂ A]

theorem boundaryMatrixHom_dirac
    (hL : star (leftEndpoint hN ops) = leftEndpoint hN ops)
    (hR : star (rightEndpoint hN ops) = rightEndpoint hN ops)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (endpointKreinData hN ops hL hR).diracAdjoint (boundaryMatrixHom hN ops M) =
      boundaryMatrixHom hN ops (pairDiracMetric * M.conjTranspose * pairDiracMetric) := by
  change (endpointKreinData hN ops hL hR).diracAdjoint
      (pairMatrixLinear (boundaryAnnihilation hN ops) (boundaryCreation hN ops) M) = _
  exact boundary_pairMatrix_dirac hN ops _
    (endpointKreinData_left_negative hN ops hL hR)
    (endpointKreinData_right_negative hN ops hL hR) M

theorem boundaryMatrixHom_dirac_fixed_iff [Nontrivial A]
    (hL : star (leftEndpoint hN ops) = leftEndpoint hN ops)
    (hR : star (rightEndpoint hN ops) = rightEndpoint hN ops)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (endpointKreinData hN ops hL hR).diracAdjoint (boundaryMatrixHom hN ops M) =
        boundaryMatrixHom hN ops M ↔
      pairDiracMetric * M.conjTranspose * pairDiracMetric = M := by
  rw [boundaryMatrixHom_dirac hN ops hL hR]
  exact (boundaryMatrixHom_injective hN ops).eq_iff

end InfoGeometry.Canonical.KitaevBoundaryFaithful
