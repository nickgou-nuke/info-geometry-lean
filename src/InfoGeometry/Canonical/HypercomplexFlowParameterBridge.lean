import InfoGeometry.Canonical.HypercomplexOneParameterFlows
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Dynamics.MoebiusTrifactorFlows

/-!
# Hypercomplex flow parameter bridge

The canonical matrix flow and the generic Moebius flow use the same matrix
carrier but are defined in different namespaces.  These readback lemmas make
that identification explicit without asserting a KAN decomposition.
-/

namespace InfoGeometry.Canonical.HypercomplexFlowParameterBridge

open InfoGeometry.Canonical.HypercomplexOneParameterFlows
open InfoGeometry.Dynamics.MoebiusFlow

theorem parabolicMat_eq_parabolicFlow
    (N : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    parabolicMat N t = parabolicFlow N t := by
  rfl

theorem hyperbolicMat_eq_hyperbolicFlow
    (H : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    hyperbolicMat H t = hyperbolicFlow H t := by
  rfl

theorem ellipticMat_eq_ellipticFlow
    (J : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    ellipticMat J t = ellipticFlow J t := by
  rfl

@[simp] theorem parabolicFlow_eval
    (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : N * N = 0) (t : ℝ) :
    (parabolicFlow_of_sq_eq_zero N hN).eval t = parabolicMat N t :=
  rfl

@[simp] theorem hyperbolicFlow_eval
    (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H * H = 1) (t : ℝ) :
    (hyperbolicFlow_of_sq_eq_one H hH).eval t = hyperbolicMat H t :=
  rfl

@[simp] theorem ellipticFlow_eval
    (J : Matrix (Fin 2) (Fin 2) ℂ) (hJ : J * J = -1) (t : ℝ) :
    (ellipticFlow_of_sq_eq_neg_one J hJ).eval t = ellipticMat J t :=
  rfl

end InfoGeometry.Canonical.HypercomplexFlowParameterBridge
