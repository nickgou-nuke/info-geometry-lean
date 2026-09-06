import Mathlib
import InfoGeometry.Topology.ChiralOperatorSageLatentBasis
import InfoGeometry.Topology.ChiralOperatorBraidLatentFlow

/-!
# The cyclic colour orbit of the Sage generator table

The external colour action fixes the two scalar-cone generators `1` and `l`
and cycles the three operator directions in each chiral vector:
`i -> j -> k -> i` and `i.l -> j.l -> k.l -> i.l`.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra
open InfoGeometry.Canonical

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

def operatorSageGeneratorCycle : Fin 8 ≃ Fin 8 where
  toFun
    | 0 => 0
    | 1 => 2
    | 2 => 3
    | 3 => 1
    | 4 => 4
    | 5 => 6
    | 6 => 7
    | 7 => 5
  invFun
    | 0 => 0
    | 1 => 3
    | 2 => 1
    | 3 => 2
    | 4 => 4
    | 5 => 7
    | 6 => 5
    | 7 => 6
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem operatorSageGeneratorCycle_three (c : Fin 8) :
    operatorSageGeneratorCycle
        (operatorSageGeneratorCycle
          (operatorSageGeneratorCycle c)) = c := by
  fin_cases c <;> rfl

theorem chiralOperatorCycle_topologicalGenerator (c : Fin 8) :
    chiralOperatorCycle
        (topologicalOperatorSageGenerator (A := A) c) =
      topologicalOperatorSageGenerator (A := A)
        (operatorSageGeneratorCycle c) := by
  apply operatorSageFeatureHomeomorph.injective
  change operatorSageObservationMap
      (chiralOperatorCycle
        (topologicalOperatorSageGenerator (A := A) c)) =
    operatorSageObservationMap
      (topologicalOperatorSageGenerator (A := A)
        (operatorSageGeneratorCycle c))
  rw [operatorSageObservation_cycle_intertwines_map,
    operatorSageObservationMap_topologicalGenerator,
    operatorSageObservationMap_topologicalGenerator]
  funext i
  fin_cases c <;> fin_cases i <;>
    simp [operatorSageGeneratorFeature, operatorSageFeatureCycle,
      operatorSageGeneratorCycle]

theorem chiralOperatorCycle_topologicalGenerator_three
    (c : Fin 8) :
    chiralOperatorCycle
        (chiralOperatorCycle
          (chiralOperatorCycle
            (topologicalOperatorSageGenerator (A := A) c))) =
      topologicalOperatorSageGenerator (A := A) c := by
  rw [chiralOperatorCycle_topologicalGenerator,
    chiralOperatorCycle_topologicalGenerator,
    chiralOperatorCycle_topologicalGenerator,
    operatorSageGeneratorCycle_three]

end
end InfoGeometry.Topology
