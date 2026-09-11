import InfoGeometry.Topology.DiracKahlerMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.PeirceBoundaryCochainComplex

/-!
  A concrete Dirac--Kähler datum for the filled triangular boundary.

  The carrier is the product of the three finite cochain spaces.  Using a
  product carrier gives Mathlib's native additive and module instances, while
  the maps below are exactly the incidence-matrix differential,
  transposed-incidence codifferential, and degree grading already used by the
  finite Hodge owners.
-/

namespace InfoGeometry.Topology.PeirceBoundaryDiracKahlerData

open InfoGeometry.Topology.PeirceBoundaryCochain
open InfoGeometry.Topology.DiscreteDiracHodge
open InfoGeometry.Topology.DiracKahlerMultiplication

noncomputable section

abbrev Carrier :=
  (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 1 → ℝ)

def differential : Carrier →ₗ[ℝ] Carrier :=
  { toFun := fun x =>
      (0, (vertexToEdge.mulVec x.1, edgeToFace.mulVec x.2.1))
    map_add' := by
      intro x y
      ext <;> simp
    map_smul' := by
      intro a x
      ext <;> simp [Matrix.mulVec_smul] }

def codifferential : Carrier →ₗ[ℝ] Carrier :=
  { toFun := fun x =>
      (vertexToEdge.transpose.mulVec x.2.1,
        (edgeToFace.transpose.mulVec x.2.2, 0))
    map_add' := by
      intro x y
      ext <;> simp
    map_smul' := by
      intro a x
      ext <;> simp [Matrix.mulVec_smul] }

def chirality : Carrier →ₗ[ℝ] Carrier :=
  { toFun := fun x => (x.1, (-x.2.1, x.2.2))
    map_add' := by
      intro x y
      ext <;> simp
      abel
    map_smul' := by
      intro a x
      ext <;> simp }

theorem differential_sq_zero :
    differential.comp differential = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · simp [differential, LinearMap.comp_apply]
  · apply Prod.ext
    · simp [differential, LinearMap.comp_apply]
    · have hmat :
          (edgeToFace * vertexToEdge).mulVec x.1 = 0 := by
        rw [vertexToEdge_edgeToFace_complex]
        simp
      simpa [differential, LinearMap.comp_apply, Matrix.mulVec_mulVec] using hmat

theorem codifferential_sq_zero :
    codifferential.comp codifferential = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · have hmat :
        (vertexToEdge.transpose * edgeToFace.transpose).mulVec x.2.2 = 0 := by
      rw [peirceBoundary_isAdjointCochainComplex]
      simp
    simpa [codifferential, LinearMap.comp_apply, Matrix.mulVec_mulVec] using hmat
  · apply Prod.ext
    · simp [codifferential, LinearMap.comp_apply]
    · simp [codifferential, LinearMap.comp_apply]

theorem differential_anticommutes_chirality :
    differential.comp chirality = -(chirality.comp differential) := by
  ext x <;>
    simp [differential, chirality, LinearMap.comp_apply]

theorem codifferential_anticommutes_chirality :
    codifferential.comp chirality =
      -(chirality.comp codifferential) := by
  ext x <;>
    simp [codifferential, chirality, LinearMap.comp_apply]

def data : Data Carrier :=
  { d := differential
    codifferential := codifferential
    chirality := chirality
    d_sq_zero := differential_sq_zero
    codifferential_sq_zero := codifferential_sq_zero
    d_anticommutes := differential_anticommutes_chirality
    codifferential_anticommutes := codifferential_anticommutes_chirality }

theorem data_dirac_square :
    (dirac data).comp (dirac data) = laplacian data :=
  dirac_square data

theorem data_dirac_anticommutes_chirality :
    (dirac data).comp data.chirality =
      -(data.chirality.comp (dirac data)) :=
  dirac_anticommutes_chirality data

theorem data_laplacian_commutes_chirality :
    (laplacian data).comp data.chirality =
      data.chirality.comp (laplacian data) :=
  laplacian_commutes_chirality data

end

end InfoGeometry.Topology.PeirceBoundaryDiracKahlerData
