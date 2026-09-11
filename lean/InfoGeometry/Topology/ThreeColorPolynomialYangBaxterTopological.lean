import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ColorPolynomialYangBaxterBridge

/-!
# Topological adapter for the exact three-colour polynomial braid owner

The canonical owner proves the permutation-matrix polynomial and Artin
relations.  This module adds the product topologies on the finite function
spaces and transports those identities to continuous operator actions.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical.ThreeColorPolynomialYangBaxterBridge

noncomputable section

@[reducible] def TopologicalColorTensor2 := ColorTensor2
@[reducible] def TopologicalColorTensor3 := ColorTensor3

def topologicalRSwap (T : TopologicalColorTensor2) :
    TopologicalColorTensor2 :=
  R_swap T

def topologicalR12 (T : TopologicalColorTensor3) :
    TopologicalColorTensor3 :=
  R12 T

def topologicalR23 (T : TopologicalColorTensor3) :
    TopologicalColorTensor3 :=
  R23 T

theorem continuous_topologicalRSwap :
    Continuous topologicalRSwap := by
  unfold topologicalRSwap R_swap
  exact continuous_pi (fun c₁ =>
    continuous_pi (fun c₂ =>
      (continuous_apply c₁).comp (continuous_apply c₂)))

theorem continuous_topologicalR12 :
    Continuous topologicalR12 := by
  unfold topologicalR12 R12
  exact continuous_pi (fun c₁ =>
    continuous_pi (fun c₂ =>
      continuous_pi (fun c₃ =>
        (continuous_apply c₃).comp
          ((continuous_apply c₁).comp (continuous_apply c₂)))))

theorem continuous_topologicalR23 :
    Continuous topologicalR23 := by
  unfold topologicalR23 R23
  exact continuous_pi (fun c₁ =>
    continuous_pi (fun c₂ =>
      continuous_pi (fun c₃ =>
        (continuous_apply c₂).comp
          ((continuous_apply c₃).comp (continuous_apply c₁)))))

@[simp] theorem topologicalRSwap_quadratic
    (T : TopologicalColorTensor2) :
    topologicalRSwap (topologicalRSwap T) = T := by
  exact R_swap_quadratic_relation T

theorem topologicalR_yang_baxter
    (T : TopologicalColorTensor3) :
    topologicalR12 (topologicalR23 (topologicalR12 T)) =
      topologicalR23 (topologicalR12 (topologicalR23 T)) := by
  exact R_swap_yang_baxter T

def topologicalColourTensorAction
    (M : TopologicalColorTensor2) : TopologicalColorTensor2 :=
  tensorAction M

theorem continuous_topologicalColourTensorAction :
    Continuous topologicalColourTensorAction := by
  unfold topologicalColourTensorAction tensorAction
  exact continuous_pi (fun c₁ =>
    continuous_pi (fun c₂ =>
      (continuous_apply (colorShift c₂)).comp
        (continuous_apply (colorShift c₁))))

theorem topologicalRSwap_colour_equivariant
    (M : TopologicalColorTensor2) :
    topologicalRSwap (topologicalColourTensorAction M) =
      topologicalColourTensorAction (topologicalRSwap M) := by
  exact R_swap_color_equivariant M

end
end InfoGeometry.Topology
