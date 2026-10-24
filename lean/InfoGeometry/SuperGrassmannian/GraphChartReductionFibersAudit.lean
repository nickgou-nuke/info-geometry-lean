/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.GraphChartReductionFibers
import InfoGeometry.SuperGrassmannian.GraphChartOddRegression

open InfoGeometry.SuperGrassmannian
open GraphChartBaseChange GraphChartOddRegression

example : Function.Injective (fun T : Fin 2 → Fin 1 → Matrix (Fin 2) (Fin 2) ℤ =>
    extend (RingHom.id _) (coordinateLinearMap T).graph) :=
  (graph_extension_injective_iff _).2 (fun _ _ h => h)

example (k : Type*) [CommRing k] :
    extend (ExteriorAlgebra.algebraMapInv : Coeff k →ₐ[k] k).toRingHom
        (coordinateLinearMap (fun _ _ : Fin 1 => theta k)).graph =
      extend (ExteriorAlgebra.algebraMapInv : Coeff k →ₐ[k] k).toRingHom
        (coordinateLinearMap (fun _ _ : Fin 1 => (0 : Coeff k))).graph := by
  rw [extend_graph_eq_iff_kernel]
  intro i j
  simp

example (k : Type*) [CommRing k] [Nontrivial k] :
    ¬ Function.Injective (fun T : Fin 1 → Fin 1 → Coeff k =>
      extend (ExteriorAlgebra.algebraMapInv : Coeff k →ₐ[k] k).toRingHom
        (coordinateLinearMap T).graph) := by
  rw [graph_extension_injective_iff]
  intro h
  apply theta_ne_zero k
  apply h
  simp

#print axioms GraphChartBaseChange.coordinateLinearMap_injective
#print axioms GraphChartBaseChange.extend_graph_eq_iff
#print axioms GraphChartBaseChange.extend_graph_eq_iff_kernel
#print axioms GraphChartBaseChange.graph_extension_injective_iff
#print axioms FreeSupermoduleChart.coefficientChart_extend_eq_iff_kernel
#print axioms GraphChartOddRegression.reduction_not_injective
