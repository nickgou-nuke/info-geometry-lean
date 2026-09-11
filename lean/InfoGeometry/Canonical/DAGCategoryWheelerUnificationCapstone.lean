import InfoGeometry.Canonical.DAGCategoryWheelerUnificationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.WheelerBoundaryHomologyBridge

namespace InfoGeometry.Canonical.DAGCategoryWheelerUnificationCapstone

open CategoryTheory
open InfoGeometry.Canonical.DAGCategoryWheeler
open InfoGeometry.Canonical.WheelerHomology

theorem dag_category_wheeler_canonical_capstone
    {nV nE nF : ℕ} (tc : DAGTwoComplexData nV nE nF)
    (A B C : TypeHeadObject)
    (f : QuiverMorphism A B) (g : QuiverMorphism B C)
    {C2 C1 C0 : Type*} [AddCommGroup C2] [AddCommGroup C1] [AddCommGroup C0]
    (Ch : ChainThreeStage C2 C1 C0)
    (h_exact : IsExactAtNode Ch)
    (x : C2) (z : C1) (hz : Ch.d1 z = 0) :
    (tc.b2 * tc.b1 = 0) ∧
    ((laplacian0 tc).transpose = laplacian0 tc) ∧
    (f.domHead = A.name ∧ g.codHead = C.name) ∧
    (Ch.d1 (Ch.d2 x) = 0) ∧
    (∃ y : C2, Ch.d2 y = z) := by
  exact ⟨dag_matrix_boundary_squared_zero tc,
    laplacian0_symmetric tc,
    quiver_composition_endpoints A B C f g,
    boundary_squared_zero Ch x,
    exact_node_cycle_resolved Ch h_exact z hz⟩

end InfoGeometry.Canonical.DAGCategoryWheelerUnificationCapstone
