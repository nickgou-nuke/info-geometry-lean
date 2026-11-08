import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ChiralOperatorSageLatentChart

/-!
# Explicit Sage generator coordinates in the chiral latent chart

The canonical Sage order is `{1, i, j, k, l, i.l, j.l, k.l}`.  This owner
records its exact images in the operator-valued coordinate order
`(u+, s+0, s+1, s+2, u-, s-0, s-1, s-2)`.  The entries remain elements of the
coefficient algebra; no commutativity or scalar diagonal model is introduced.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra
open InfoGeometry.Canonical
open InfoGeometry.Physics.NCG

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

def operatorSageGeneratorFeature (c : Fin 8) : OperatorSageFeatureSpace A :=
  match c with
  | 0 => ![1, 0, 0, 0, 1, 0, 0, 0]
  | 1 => ![0, -1, 0, 0, 0, 1, 0, 0]
  | 2 => ![0, 0, -1, 0, 0, 0, 1, 0]
  | 3 => ![0, 0, 0, -1, 0, 0, 0, 1]
  | 4 => ![1, 0, 0, 0, -1, 0, 0, 0]
  | 5 => ![0, 1, 0, 0, 0, 1, 0, 0]
  | 6 => ![0, 0, 1, 0, 0, 0, 1, 0]
  | 7 => ![0, 0, 0, 1, 0, 0, 0, 1]

theorem operatorSageObservationMap_topologicalGenerator (c : Fin 8) :
    operatorSageObservationMap
        (topologicalOperatorSageGenerator (A := A) c) =
      operatorSageGeneratorFeature (A := A) c := by
  fin_cases c <;>
    ext i <;>
    fin_cases i <;>
    simp [operatorSageObservationMap, operatorSageFeature,
      operatorSageGeneratorFeature, topologicalOperatorSageGenerator,
      operatorSageZornToTopological, operatorSageGenerator, operatorOne,
      operatorEll, operatorI, operatorJ, operatorK, operatorIEll,
      operatorJEll, operatorKEll, operatorAdd, operatorSub, nPlus, nMinus,
      sigmaPlus, sigmaMinus, operatorUnit]

end
end InfoGeometry.Topology
