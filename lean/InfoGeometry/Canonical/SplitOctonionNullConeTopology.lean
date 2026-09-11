import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionNullCone

/-!
# Topology of the real split-octonion null cone

The algebraic owner defines the real Zorn carrier and its split norm.  This
owner equips that finite coordinate carrier with the induced Euclidean
topology and proves only the basic topological consequences: continuity of
the norm and closedness of the null cone.  It does not introduce a
projectivisation or an exceptional-group action.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Physics.ZornMatrixSU3

abbrev SplitZornCoordinate :=
  (ℝ × ℝ) × ((Fin 3 → ℝ) × (Fin 3 → ℝ))

def splitZornCoordinates : SplitZornMatrix → SplitZornCoordinate :=
  fun X => ((X.a, X.b), (X.x, X.y))

instance : TopologicalSpace SplitZornMatrix :=
  TopologicalSpace.induced splitZornCoordinates inferInstance

theorem continuous_splitZornCoordinates :
    Continuous splitZornCoordinates :=
  continuous_induced_dom

theorem continuous_splitZorn_a :
    Continuous (fun X : SplitZornMatrix => X.a) := by
  exact continuous_fst.comp (continuous_fst.comp continuous_splitZornCoordinates)

theorem continuous_splitZorn_b :
    Continuous (fun X : SplitZornMatrix => X.b) := by
  exact continuous_snd.comp (continuous_fst.comp continuous_splitZornCoordinates)

theorem continuous_splitZorn_x :
    Continuous (fun X : SplitZornMatrix => X.x) := by
  exact continuous_fst.comp (continuous_snd.comp continuous_splitZornCoordinates)

theorem continuous_splitZorn_y :
    Continuous (fun X : SplitZornMatrix => X.y) := by
  exact continuous_snd.comp (continuous_snd.comp continuous_splitZornCoordinates)

theorem continuous_splitZorn_dotProduct :
    Continuous (fun X : SplitZornMatrix =>
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct X.x X.y) := by
  have h0 := (continuous_apply 0).comp continuous_splitZorn_x
  have h1 := (continuous_apply 1).comp continuous_splitZorn_x
  have h2 := (continuous_apply 2).comp continuous_splitZorn_x
  have k0 := (continuous_apply 0).comp continuous_splitZorn_y
  have k1 := (continuous_apply 1).comp continuous_splitZorn_y
  have k2 := (continuous_apply 2).comp continuous_splitZorn_y
  simpa [InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3] using
    (((h0.mul k0).add (h1.mul k1)).add (h2.mul k2))

theorem continuous_splitZorn_norm :
    Continuous (InfoGeometry.Physics.ZornMatrixSU3.norm :
      SplitZornMatrix → ℝ) := by
  have hab := continuous_splitZorn_a.mul continuous_splitZorn_b
  have hd := continuous_splitZorn_dotProduct
  simpa [InfoGeometry.Physics.ZornMatrixSU3.norm] using hab.sub hd

theorem isClosed_splitZornNullCone :
    IsClosed splitZornNullCone := by
  change IsClosed ((InfoGeometry.Physics.ZornMatrixSU3.norm :
    SplitZornMatrix → ℝ) ⁻¹' ({0} : Set ℝ))
  exact isClosed_singleton.preimage continuous_splitZorn_norm

theorem splitZornNullCone_mem_zero :
    (0 : SplitZornMatrix) ∈ splitZornNullCone := by
  simp [splitZornNullCone, InfoGeometry.Physics.ZornMatrixSU3.norm]

end InfoGeometry.Canonical
