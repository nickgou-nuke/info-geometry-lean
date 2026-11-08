/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.FreeSupermoduleChart

/-! Exact information loss under coefficient change in finite free graph charts.
The extension is the existing target-module span, including for nonsurjective
ring maps. Graded chart fibers use the actual homogeneous submodules. -/

namespace InfoGeometry.SuperGrassmannian.GraphChartBaseChange

variable {A B I J : Type*} [Ring A] [Ring B] [Fintype I]

theorem coordinateLinearMap_injective :
    Function.Injective (coordinateLinearMap (A := A) (I := I) (J := J)) := by
  classical
  intro T U h
  funext i j
  have he := congrArg (fun f : (I → A) →ₗ[A] (J → A) =>
    f (Pi.single i 1) j) h
  simpa [coordinateLinearMap, Pi.single_apply] using he

/-- Two graphs become equal exactly when every coefficient has the same image. -/
theorem extend_graph_eq_iff (φ : A →+* B) (T U : I → J → A) :
    extend φ (coordinateLinearMap T).graph =
      extend φ (coordinateLinearMap U).graph ↔
        ∀ i j, φ (T i j) = φ (U i j) := by
  rw [extend_graph, extend_graph]
  constructor
  · intro h
    have he := coordinateLinearMap_injective (GradedGraphChart.graph_injective h)
    exact fun i j => congrFun (congrFun he i) j
  · intro h
    have he : (fun i j => φ (T i j)) = (fun i j => φ (U i j)) :=
      funext fun i => funext (h i)
    rw [he]

/-- The kernel, rather than just odd parity, classifies all collapsed coefficients. -/
theorem extend_graph_eq_iff_kernel (φ : A →+* B) (T U : I → J → A) :
    extend φ (coordinateLinearMap T).graph =
      extend φ (coordinateLinearMap U).graph ↔
        ∀ i j, φ (T i j - U i j) = 0 := by
  simp only [extend_graph_eq_iff, map_sub, sub_eq_zero]

/-- For nonempty source and target frames, faithfulness on all graph arrays
is equivalent to injectivity of the coefficient homomorphism. -/
theorem graph_extension_injective_iff [Nonempty I] [Nonempty J] (φ : A →+* B) :
    Function.Injective (fun T : I → J → A =>
      extend φ (coordinateLinearMap T).graph) ↔ Function.Injective φ := by
  constructor
  · intro h a b hab
    have he := h ((extend_graph_eq_iff φ (fun _ _ => a) (fun _ _ => b)).2
      (fun _ _ => hab))
    obtain ⟨i⟩ := ‹Nonempty I›
    obtain ⟨j⟩ := ‹Nonempty J›
    exact congrFun (congrFun he i) j
  · intro h T U he
    have hc := (extend_graph_eq_iff φ T U).1 he
    exact funext fun i => funext fun j => h (hc i j)

end InfoGeometry.SuperGrassmannian.GraphChartBaseChange

namespace InfoGeometry.SuperGrassmannian.FreeSupermoduleChart

open GraphChartBaseChange

variable {k A B I J : Type*} [CommRing k] [Ring A] [Ring B] [Algebra k A]
  (𝓐 : ZMod 2 → Submodule k A) [GradedAlgebra 𝓐]
  [Fintype I] [DecidableEq I]

/-- The same kernel criterion on genuine homogeneous chart points; no target
grading or surjectivity is required for equality of their extended submodules. -/
theorem coefficientChart_extend_eq_iff_kernel
    (d : I → ZMod 2) (e : J → ZMod 2) (φ : A →+* B)
    (T U : {T : I → J → A // ∀ i j, T i j ∈ 𝓐 (d i + e j)}) :
    extend φ (coefficientChartEquiv 𝓐 d e T).val =
      extend φ (coefficientChartEquiv 𝓐 d e U).val ↔
        ∀ i j, φ (T.val i j - U.val i j) = 0 := by
  simp only [coefficientChartEquiv_submodule, extend_graph_eq_iff_kernel]

end InfoGeometry.SuperGrassmannian.FreeSupermoduleChart
