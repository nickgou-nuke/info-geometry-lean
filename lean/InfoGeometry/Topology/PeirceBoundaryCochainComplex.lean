import InfoGeometry.Topology.PeirceDifferentialForm
import InfoGeometry.Topology.DiscreteDiracHodge
import InfoGeometry.Canonical.DiscreteDiracHodgeChiralBridge

namespace InfoGeometry.Topology.PeirceBoundaryCochain

open Matrix
open InfoGeometry.Canonical
open InfoGeometry.Topology.DiscreteDiracHodge

/-!
  A concrete finite cochain model for the triangular boundary chart.

  The three vertices, three oriented edges, and one face are represented by
  the usual incidence matrices.  This is an honest finite complex; it is not
  being identified with the full de Rham complex of the Peirce chart.
-/

noncomputable section

abbrev vertexToEdge : Matrix (Fin 3) (Fin 3) ℝ :=
  InfoGeometry.Canonical.DiscreteDiracHodgeChiralBridge.triangleBoundary1

abbrev edgeToFace : Matrix (Fin 1) (Fin 3) ℝ :=
  InfoGeometry.Canonical.DiscreteDiracHodgeChiralBridge.triangleBoundary2

theorem vertexToEdge_edgeToFace_complex :
    edgeToFace * vertexToEdge = 0 := by
  exact InfoGeometry.Canonical.DiscreteDiracHodgeChiralBridge.triangle_degree_one_cochain_complex

theorem peirceBoundary_isCochainComplex :
    IsCochainComplex vertexToEdge edgeToFace :=
  vertexToEdge_edgeToFace_complex

theorem peirceBoundary_isAdjointCochainComplex :
    IsAdjointCochainComplex vertexToEdge edgeToFace := by
  unfold IsAdjointCochainComplex
  rw [← Matrix.transpose_zero, ← Matrix.transpose_mul]
  congr 1
  exact vertexToEdge_edgeToFace_complex

abbrev PeirceBoundaryTotalForm := TotalForm 3 3 1

def peirceBoundaryDiracHodge
    (x : PeirceBoundaryTotalForm) : PeirceBoundaryTotalForm :=
  diracHodge vertexToEdge edgeToFace x

def peirceBoundaryHodgeLaplacian
    (x : PeirceBoundaryTotalForm) : PeirceBoundaryTotalForm :=
  hodgeLaplacian vertexToEdge edgeToFace x

theorem peirceBoundary_exteriorDerivative_sq_zero
    (x : PeirceBoundaryTotalForm) :
    exteriorDerivative vertexToEdge edgeToFace
      (exteriorDerivative vertexToEdge edgeToFace x) = 0 :=
  exteriorDerivative_sq_zero vertexToEdge edgeToFace
    peirceBoundary_isCochainComplex x

theorem peirceBoundary_codifferential_sq_zero
    (x : PeirceBoundaryTotalForm) :
    codifferential vertexToEdge edgeToFace
      (codifferential vertexToEdge edgeToFace x) = 0 :=
  codifferential_sq_zero vertexToEdge edgeToFace
    peirceBoundary_isAdjointCochainComplex x

theorem peirceBoundary_diracHodge_sq
    (x : PeirceBoundaryTotalForm) :
    peirceBoundaryDiracHodge
        (peirceBoundaryDiracHodge x) =
      peirceBoundaryHodgeLaplacian x := by
  exact diracHodge_sq_eq_hodgeLaplacian vertexToEdge edgeToFace
    peirceBoundary_isCochainComplex
    peirceBoundary_isAdjointCochainComplex x

theorem peirceBoundary_betti1_zero :
    EckmannDiscreteHodge.eckmannBetti1Zero vertexToEdge edgeToFace :=
  InfoGeometry.Canonical.DiscreteDiracHodgeChiralBridge.triangle_betti1_zero

theorem peirceBoundary_closed_one_form_is_exact
    (x : Fin 3 → ℝ)
    (hx : edgeToFace.mulVec x = 0) :
    ∃ y : Fin 3 → ℝ, vertexToEdge.mulVec y = x :=
  (peirceBoundary_betti1_zero).2 x hx

theorem peirceBoundary_harmonic_one_form_vanishes
    (x : Fin 3 → ℝ)
    (hClosed : edgeToFace.mulVec x = 0)
    (hCoClosed : vertexToEdge.transpose.mulVec x = 0) :
    x = 0 :=
  InfoGeometry.Canonical.DiscreteDiracHodgeChiralBridge.triangle_harmonic_one_forms_vanish
    x hClosed hCoClosed

theorem peirceBoundary_vertexCochain_is_source
    (x : PeirceBoundaryChart) :
    peirceBoundarySourceCoordinates x =
      (EuclideanSpace.equiv (Fin 3) ℝ) x :=
  rfl

end

end InfoGeometry.Topology.PeirceBoundaryCochain
