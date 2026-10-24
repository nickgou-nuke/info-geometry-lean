/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevBoundaryTraceNormalization
import InfoGeometry.Canonical.PeirceWeightedTrace

/-! Existing Peirce weights as conserved elements of the native boundary
matrix algebra, with their exact concrete trace scale. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevBoundaryWeights

open InfoGeometry.Quantum.KitaevChain InfoGeometry.NCG
open InfoGeometry.OperatorAlgebra.TracialCARDensity
open KitaevBoundaryDiracPair KitaevBoundaryAlgebra PeirceWeightedTrace
open ReflexiveNilpotentFlows KitaevConcreteBoundary KitaevBoundaryTraceNormalization

variable {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ}
variable (hN : 0 < N) (ops : MajoranaCliffordOperators N A)

theorem boundaryMatrixHom_diagonal_weight (a b : ℂ) :
    boundaryMatrixHom hN ops !![b, 0; 0, a] =
      supportWeight a b (boundaryAnnihilation hN ops) (boundaryCreation hN ops) := by
  change pairMatrixLinear _ _ !![b, 0; 0, a] = _
  simp [pairMatrixLinear_apply, pairMatrixUnit, supportWeight, add_comm]

theorem boundary_weight_commutes (a b t : ℂ) :
    Commute (supportWeight a b (boundaryAnnihilation hN ops) (boundaryCreation hN ops))
      (sweetSpotHamiltonian ops.toMajoranaOperators (algebraMap ℂ A t)) := by
  rw [← boundaryMatrixHom_diagonal_weight]
  exact boundaryMatrixHom_commutes hN ops t _

theorem boundary_weighted_trace (τ : TracialFunctional ℂ A) (a b : ℂ) (x : A) :
    a * weighted τ (supportWeight a b (boundaryAnnihilation hN ops) (boundaryCreation hN ops))
        (boundaryAnnihilation hN ops * x) =
      b * weighted τ (supportWeight a b (boundaryAnnihilation hN ops) (boundaryCreation hN ops))
        (x * boundaryAnnihilation hN ops) ∧
    b * weighted τ (supportWeight a b (boundaryAnnihilation hN ops) (boundaryCreation hN ops))
        (boundaryCreation hN ops * x) =
      a * weighted τ (supportWeight a b (boundaryAnnihilation hN ops) (boundaryCreation hN ops))
        (x * boundaryCreation hN ops) :=
  weighted_trace_boundary τ (boundaryAnnihilation_sq hN ops) (boundaryCreation_sq hN ops)
    (boundary_reflexive hN ops).1 (boundary_reflexive hN ops).2 a b x

theorem twoSite_weighted_matrix_trace (a b : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace
      (supportWeight a b (boundaryAnnihilation (by decide) twoSiteOperators)
          (boundaryCreation (by decide) twoSiteOperators) *
        boundaryMatrixHom (by decide) twoSiteOperators M) =
      2 * (b * M 0 0 + a * M 1 1) := by
  rw [← boundaryMatrixHom_diagonal_weight, ← map_mul, boundaryMatrixHom_trace]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]

variable [StarRing A] [StarModule ℂ A]

theorem boundary_weight_dirac
    (hL : star (leftEndpoint hN ops) = leftEndpoint hN ops)
    (hR : star (rightEndpoint hN ops) = rightEndpoint hN ops) (a b : ℂ) :
    (KitaevBoundaryConstructedMetric.endpointKreinData hN ops hL hR).diracAdjoint
        (supportWeight a b (boundaryAnnihilation hN ops) (boundaryCreation hN ops)) =
      supportWeight (star a) (star b) (boundaryAnnihilation hN ops) (boundaryCreation hN ops) := by
  rw [← boundaryMatrixHom_diagonal_weight,
    KitaevBoundaryFaithful.boundaryMatrixHom_dirac hN ops hL hR]
  have hdiag : pairDiracMetric * (!![b, 0; 0, a] : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose *
      pairDiracMetric = !![star b, 0; 0, star a] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairDiracMetric, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  rw [hdiag, boundaryMatrixHom_diagonal_weight]

theorem boundary_weight_dirac_fixed
    (hL : star (leftEndpoint hN ops) = leftEndpoint hN ops)
    (hR : star (rightEndpoint hN ops) = rightEndpoint hN ops)
    (a b : ℂ) (ha : star a = a) (hb : star b = b) :
    (KitaevBoundaryConstructedMetric.endpointKreinData hN ops hL hR).diracAdjoint
        (supportWeight a b (boundaryAnnihilation hN ops) (boundaryCreation hN ops)) =
      supportWeight a b (boundaryAnnihilation hN ops) (boundaryCreation hN ops) := by
  rw [boundary_weight_dirac hN ops hL hR, ha, hb]

end InfoGeometry.Canonical.KitaevBoundaryWeights
