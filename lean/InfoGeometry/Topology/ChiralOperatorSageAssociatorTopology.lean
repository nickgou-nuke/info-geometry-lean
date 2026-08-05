import Mathlib
import InfoGeometry.Topology.ChiralOperatorSageChiralCoordinateMultiplication

/-!
# Topological associator readout for the operator-valued Zorn product

The displayed Zorn multiplication is not promoted to an associative algebra.
Instead, this owner records its associator as a continuous map and transports
it through the chiral coordinate chart.  Non-vanishing requires a separate
coefficient-algebra witness and is intentionally not assumed here.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

def operatorSageTopologicalAssociator
    (X Y Z : OperatorSageTopologicalCarrier A) :
    OperatorSageTopologicalCarrier A :=
  operatorSageTopologicalMul
      (operatorSageTopologicalMul X Y) Z -
    operatorSageTopologicalMul X
      (operatorSageTopologicalMul Y Z)

def operatorSageChiralAssociator
    (X Y Z : ChiralConeCoordinates A) :
    ChiralConeCoordinates A :=
  operatorSageChiralMul
      (operatorSageChiralMul X Y) Z -
    operatorSageChiralMul X
      (operatorSageChiralMul Y Z)

@[simp] theorem operatorSageTopologicalToChiral_sub
    (X Y : OperatorSageTopologicalCarrier A) :
    operatorSageTopologicalToChiral (X - Y) =
      operatorSageTopologicalToChiral X -
        operatorSageTopologicalToChiral Y := by
  rfl

@[simp] theorem operatorSageChiralToTopological_sub
    (X Y : ChiralConeCoordinates A) :
    operatorSageChiralToTopological (X - Y) =
      operatorSageChiralToTopological X -
        operatorSageChiralToTopological Y := by
  rfl

theorem operatorSageTopologicalToChiral_associator
    (X Y Z : OperatorSageTopologicalCarrier A) :
    operatorSageTopologicalToChiral
        (operatorSageTopologicalAssociator X Y Z) =
      operatorSageChiralAssociator
        (operatorSageTopologicalToChiral X)
        (operatorSageTopologicalToChiral Y)
        (operatorSageTopologicalToChiral Z) := by
  rfl

theorem continuous_operatorSageTopologicalAssociator :
    Continuous (fun p : OperatorSageTopologicalCarrier A ×
      OperatorSageTopologicalCarrier A ×
        OperatorSageTopologicalCarrier A =>
      operatorSageTopologicalAssociator p.1 p.2.1 p.2.2) := by
  have hleft : Continuous
      (fun p : OperatorSageTopologicalCarrier A ×
        OperatorSageTopologicalCarrier A ×
          OperatorSageTopologicalCarrier A =>
        operatorSageTopologicalMul
          (operatorSageTopologicalMul p.1 p.2.1) p.2.2) := by
    exact continuous_operatorSageTopologicalMul.comp
      ((continuous_operatorSageTopologicalMul.comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd))
  have hright : Continuous
      (fun p : OperatorSageTopologicalCarrier A ×
        OperatorSageTopologicalCarrier A ×
          OperatorSageTopologicalCarrier A =>
        operatorSageTopologicalMul p.1
          (operatorSageTopologicalMul p.2.1 p.2.2)) := by
    exact continuous_operatorSageTopologicalMul.comp
      (continuous_fst.prodMk
        (continuous_operatorSageTopologicalMul.comp
          ((continuous_fst.comp continuous_snd).prodMk
            (continuous_snd.comp continuous_snd))))
  exact hleft.sub hright

theorem operatorSageChiralAssociator_toTopological
    (X Y Z : ChiralConeCoordinates A) :
    operatorSageChiralToTopological
        (operatorSageChiralAssociator X Y Z) =
      operatorSageTopologicalAssociator
        (operatorSageChiralToTopological X)
        (operatorSageChiralToTopological Y)
        (operatorSageChiralToTopological Z) := by
  rw [operatorSageChiralAssociator,
    operatorSageChiralToTopological_sub,
    operatorSageChiralMul_toTopological,
    operatorSageChiralMul_toTopological,
    operatorSageChiralMul_toTopological,
    operatorSageChiralMul_toTopological]
  rfl

theorem continuous_operatorSageChiralAssociator :
    Continuous (fun p : ChiralConeCoordinates A ×
      ChiralConeCoordinates A × ChiralConeCoordinates A =>
      operatorSageChiralAssociator p.1 p.2.1 p.2.2) := by
  have hleft : Continuous
      (fun p : ChiralConeCoordinates A ×
        ChiralConeCoordinates A × ChiralConeCoordinates A =>
        operatorSageChiralMul
          (operatorSageChiralMul p.1 p.2.1) p.2.2) := by
    exact continuous_operatorSageChiralMul.comp
      ((continuous_operatorSageChiralMul.comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd))
  have hright : Continuous
      (fun p : ChiralConeCoordinates A ×
        ChiralConeCoordinates A × ChiralConeCoordinates A =>
        operatorSageChiralMul p.1
          (operatorSageChiralMul p.2.1 p.2.2)) := by
    exact continuous_operatorSageChiralMul.comp
      (continuous_fst.prodMk
        (continuous_operatorSageChiralMul.comp
          ((continuous_fst.comp continuous_snd).prodMk
            (continuous_snd.comp continuous_snd))))
  exact hleft.sub hright

end
end InfoGeometry.Topology
