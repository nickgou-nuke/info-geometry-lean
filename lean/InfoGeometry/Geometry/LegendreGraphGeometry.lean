/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.DualFlatKreinLegendreGraph
import InfoGeometry.SuperGrassmannian.GradedGraphChart
import InfoGeometry.Twistor.RealDualTwistor
import InfoGeometry.Twistor.RealTwistorIncidence
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Grassmannian

/-!
# Native geometry of Legendre tangent graphs

This module extends the existing algebraic graph owner on `V × Module.Dual ℝ V`.
The canonical symplectic orthogonal of the graph of a bilinear map is the graph
of its transpose. Symmetry therefore gives actual self-orthogonality and
maximal isotropy, without a dimension assumption. In finite dimension the
same graph gives a native `Module.Grassmannian` point; its quotient rank and
dimension follow from the existing graph equivalences.

The analytic statements differentiate the actual map `x ↦ (x, p x)` into the
continuous cotangent carrier. Only afterward do the native coercion linear
maps forget continuity and identify the derivative range with an algebraic
graph. A symmetric derivative gives a Lagrangian tangent subspace; symmetry
is an explicit hypothesis for an arbitrary covector field. For the derivative
field of an actual `C²` scalar potential, the final corollaries derive both
differentiability and Hessian symmetry from native Mathlib calculus.

The incidence bridge uses the existing real incidence submodule and a coordinate
swap. None of these constructions asserts a manifold atlas or supermanifold.
The fixed primal/dual grading preserves such a graph only when its map is zero.
-/

noncomputable section

namespace InfoGeometry.Geometry.LegendreGraphGeometry

open InfoGeometry.Twistor.RealDualTwistor
open InfoGeometry.Geometry.DualFlatKreinLegendreGraph
open InfoGeometry.SuperGrassmannian.GradedGraphChart

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The native twistor symplectic form agrees with the existing graph convention. -/
theorem symplecticForm_eq_canonicalSymplectic (z w : Carrier V) :
    symplecticForm z w = canonicalSymplectic z w := rfl

/-- The right symplectic orthogonal of a graph is the graph of the transposed
bilinear map. No symmetry, nondegeneracy or dimension assumption is needed. -/
theorem graph_symplectic_orthogonal (H : V →ₗ[ℝ] Module.Dual ℝ V) :
    (symplecticForm (V := V)).orthogonal H.graph = H.flip.graph := by
  ext z
  constructor
  · intro hz
    change z.2 = H.flip z.1
    apply LinearMap.ext
    intro u
    have hu := (LinearMap.BilinForm.mem_orthogonal_iff.mp hz)
      (u, H u) (show (u, H u) ∈ H.graph from rfl)
    change z.2 u - (H u) z.1 = 0 at hu
    exact sub_eq_zero.mp hu
  · intro hz
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro w hw
    change z.2 = H.flip z.1 at hz
    change w.2 = H w.1 at hw
    change z.2 w.1 - w.2 z.1 = 0
    rw [hz, hw]
    change (H w.1) z.1 - (H w.1) z.1 = 0
    exact sub_self _

/-- Symmetry is exactly the self-orthogonality condition on this graph chart. -/
theorem graph_self_orthogonal_iff_symmetric (H : V →ₗ[ℝ] Module.Dual ℝ V) :
    (symplecticForm (V := V)).orthogonal H.graph = H.graph ↔
      IsSymmetricDuality H := by
  constructor
  · intro h
    have hflip : H.flip = H :=
      graph_injective ((graph_symplectic_orthogonal H).symm.trans h)
    intro u v
    exact congrArg (fun F : V →ₗ[ℝ] Module.Dual ℝ V => F v u) hflip
  · intro hH
    have hflip : H.flip = H := by
      ext u v
      exact hH v u
    rw [graph_symplectic_orthogonal, hflip]

/-- A symmetric graph is maximal among symplectic-isotropic native submodules. -/
theorem symmetric_graph_maximal_isotropic
    (H : V →ₗ[ℝ] Module.Dual ℝ V) (hH : IsSymmetricDuality H)
    (S : Submodule ℝ (Carrier V)) (hHS : H.graph ≤ S)
    (hS : ∀ u ∈ S, ∀ v ∈ S, symplecticForm u v = 0) :
    S = H.graph := by
  apply le_antisymm
  · rw [← (graph_self_orthogonal_iff_symmetric H).2 hH]
    intro z hz
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro w hw
    exact hS w (hHS hw) z hz
  · exact hHS

/-- The genuine neutral metric on a symmetric graph pulls back to twice its
Hessian pairing; the graph need not be null for this different form. -/
theorem neutralForm_graph_pairing (H : V →ₗ[ℝ] Module.Dual ℝ V)
    (hH : IsSymmetricDuality H) (u v : V) :
    neutralForm (u, H u) (v, H v) = 2 * (H u) v := by
  change (H u) v + (H v) u = 2 * (H u) v
  rw [hH v u]
  ring

/-- Real graph incidence is the same native graph after exchanging the two
coordinates. No new incidence or Grassmannian carrier is introduced. -/
theorem incidenceSpace_eq_graph_comap_swap (H : V →ₗ[ℝ] Module.Dual ℝ V) :
    InfoGeometry.Twistor.RealTwistorIncidence.incidenceSpace H =
      H.graph.comap (LinearEquiv.prodComm ℝ (Module.Dual ℝ V) V).toLinearMap := by
  ext z
  rw [InfoGeometry.Twistor.RealTwistorIncidence.mem_incidenceSpace]
  rfl

/-- A graph is stable under the fixed primal/dual grading precisely when its
coordinate map vanishes. An arbitrary Hessian graph is not a graded chart point. -/
theorem graph_para_stable_iff_zero (H : V →ₗ[ℝ] Module.Dual ℝ V) :
    (∀ z ∈ H.graph, para z ∈ H.graph) ↔ H = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    have hu := h (u, H u) (show (u, H u) ∈ H.graph from rfl)
    change -(H u) = H u at hu
    have hv := LinearMap.congr_fun hu v
    change -((H u) v) = (H u) v at hv
    change (H u) v = 0
    linarith
  · rintro rfl z hz
    change z.2 = 0 at hz
    change -z.2 = 0
    rw [hz, neg_zero]

section FiniteDimension

variable [FiniteDimensional ℝ V]

/-- The graph has the dimension of its source, by its actual source equivalence. -/
theorem graph_finrank (H : V →ₗ[ℝ] Module.Dual ℝ V) :
    Module.finrank ℝ H.graph = Module.finrank ℝ V :=
  (graphSourceEquiv H).finrank_eq

/-- Every such graph has half the ambient real dimension. -/
theorem graph_half_dimension (H : V →ₗ[ℝ] Module.Dual ℝ V) :
    2 * Module.finrank ℝ H.graph = Module.finrank ℝ (Carrier V) := by
  rw [graph_finrank]
  change 2 * Module.finrank ℝ V =
    Module.finrank ℝ (V × Module.Dual ℝ V)
  rw [Module.finrank_prod, Subspace.dual_finrank_eq, two_mul]

/-- The graph as an actual native Grassmannian point. Mathlib's index is the
quotient rank; the graph quotient is explicitly the dual space. -/
def graphGrassmannian (H : V →ₗ[ℝ] Module.Dual ℝ V) :
    Module.Grassmannian ℝ (Carrier V) (Module.finrank ℝ V) where
  toSubmodule := H.graph
  finite_quotient := Module.Finite.equiv (graphQuotientEquiv H).symm
  projective_quotient := Module.Projective.of_equiv (graphQuotientEquiv H).symm
  rankAtStalk_eq p := by
    have h := congrFun (Module.rankAtStalk_eq_of_equiv (graphQuotientEquiv H)) p
    rw [h]
    simp [Module.rankAtStalk_eq_finrank_of_free, Subspace.dual_finrank_eq]

@[simp] theorem graphGrassmannian_toSubmodule (H : V →ₗ[ℝ] Module.Dual ℝ V) :
    (graphGrassmannian H).toSubmodule = H.graph := rfl

/-- Distinct graph coordinates produce distinct native Grassmannian points. -/
theorem graphGrassmannian_injective :
    Function.Injective (graphGrassmannian (V := V)) := by
  intro H K h
  apply graph_injective
  exact congrArg Module.Grassmannian.toSubmodule h

end FiniteDimension
end Algebraic

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The native continuous-to-algebraic dual coercion on the cotangent carrier. -/
def continuousDualCarrierMap :
    (E × (E →L[ℝ] ℝ)) →ₗ[ℝ] Carrier E :=
  (LinearMap.id : E →ₗ[ℝ] E).prodMap (ContinuousLinearMap.coeLM ℝ)

@[simp] theorem continuousDualCarrierMap_apply (z : E × (E →L[ℝ] ℝ)) :
    continuousDualCarrierMap z = (z.1, z.2.toLinearMap) := rfl

/-- Forget continuity in the value of a continuous covector-field derivative. -/
def algebraicDualDerivative (H : E →L[ℝ] (E →L[ℝ] ℝ)) :
    E →ₗ[ℝ] Module.Dual ℝ E :=
  (ContinuousLinearMap.coeLM ℝ).comp H.toLinearMap

@[simp] theorem algebraicDualDerivative_apply
    (H : E →L[ℝ] (E →L[ℝ] ℝ)) (u : E) :
    algebraicDualDerivative H u = (H u).toLinearMap := rfl

/-- The actual derivative of the nonlinear covector graph is the graph inclusion
of its derivative. This statement is made on the continuous-dual carrier. -/
theorem hasFDerivAt_covectorGraph (p : E → (E →L[ℝ] ℝ))
    (H : E →L[ℝ] (E →L[ℝ] ℝ)) (x : E) (hp : HasFDerivAt p H x) :
    HasFDerivAt (fun y : E => (y, p y))
      ((ContinuousLinearMap.id ℝ E).prod H) x :=
  (hasFDerivAt_id x).prodMk hp

/-- After the explicit forgetful map, the range of the actual derivative is
exactly the native algebraic graph. This is the tangent-subspace identification. -/
theorem covectorGraph_tangent_range (p : E → (E →L[ℝ] ℝ))
    (H : E →L[ℝ] (E →L[ℝ] ℝ)) (x : E) (hp : HasFDerivAt p H x) :
    LinearMap.range (continuousDualCarrierMap.comp
      (fderiv ℝ (fun y : E => (y, p y)) x).toLinearMap) =
      (algebraicDualDerivative H).graph := by
  rw [(hasFDerivAt_covectorGraph p H x hp).fderiv]
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    rfl
  · intro hz
    change z.2 = algebraicDualDerivative H z.1 at hz
    refine ⟨z.1, ?_⟩
    exact Prod.ext rfl hz.symm

/-- A symmetric derivative makes the actual graph tangent symplectically
self-orthogonal. No topology is imposed on the algebraic dual. -/
theorem covectorGraph_tangent_self_orthogonal (p : E → (E →L[ℝ] ℝ))
    (H : E →L[ℝ] (E →L[ℝ] ℝ)) (x : E) (hp : HasFDerivAt p H x)
    (hH : ∀ u v : E, H u v = H v u) :
    (symplecticForm (V := E)).orthogonal
        (LinearMap.range (continuousDualCarrierMap.comp
          (fderiv ℝ (fun y : E => (y, p y)) x).toLinearMap)) =
      LinearMap.range (continuousDualCarrierMap.comp
        (fderiv ℝ (fun y : E => (y, p y)) x).toLinearMap) := by
  rw [covectorGraph_tangent_range p H x hp]
  exact (graph_self_orthogonal_iff_symmetric (algebraicDualDerivative H)).2 hH

/-- In finite dimension, the native Grassmannian point represents precisely
the derivative range, rather than an unrelated chosen subspace. -/
theorem graphGrassmannian_eq_covectorGraph_tangent [FiniteDimensional ℝ E]
    (p : E → (E →L[ℝ] ℝ)) (H : E →L[ℝ] (E →L[ℝ] ℝ)) (x : E)
    (hp : HasFDerivAt p H x) :
    (graphGrassmannian (algebraicDualDerivative H)).toSubmodule =
      LinearMap.range (continuousDualCarrierMap.comp
        (fderiv ℝ (fun y : E => (y, p y)) x).toLinearMap) := by
  rw [graphGrassmannian_toSubmodule, covectorGraph_tangent_range p H x hp]

/-- For an actual `C²` potential, its derivative field has an actual derivative;
the nonlinear graph derivative is therefore the Hessian graph inclusion. -/
theorem hasFDerivAt_potentialGraph (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (fun y : E => (y, fderiv ℝ f y))
      ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ (fderiv ℝ f) x)) x := by
  have hp : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  exact hasFDerivAt_covectorGraph (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x
    hp.differentiableAt_one.hasFDerivAt

/-- Native Schwarz symmetry discharges the symmetry hypothesis for the actual
Hessian, after the explicit continuous-to-algebraic dual coercion. -/
theorem potentialHessian_symmetric (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) :
    IsSymmetricDuality (algebraicDualDerivative (fderiv ℝ (fderiv ℝ f) x)) :=
  hf.isSymmSndFDerivAt (by simp)

/-- The actual derivative graph of a `C²` scalar potential has a symplectically
self-orthogonal tangent space. Symmetry is derived here, not supplied. -/
theorem potentialGraph_tangent_self_orthogonal (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) :
    (symplecticForm (V := E)).orthogonal
        (LinearMap.range (continuousDualCarrierMap.comp
          (fderiv ℝ (fun y : E => (y, fderiv ℝ f y)) x).toLinearMap)) =
      LinearMap.range (continuousDualCarrierMap.comp
        (fderiv ℝ (fun y : E => (y, fderiv ℝ f y)) x).toLinearMap) := by
  have hp : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  exact covectorGraph_tangent_self_orthogonal (fderiv ℝ f)
    (fderiv ℝ (fderiv ℝ f) x) x hp.differentiableAt_one.hasFDerivAt
    (potentialHessian_symmetric f x hf)

/-- The native Grassmannian point of the actual Hessian represents the tangent
space of the derivative graph of a `C²` potential. -/
theorem graphGrassmannian_eq_potentialGraph_tangent [FiniteDimensional ℝ E]
    (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    (graphGrassmannian
      (algebraicDualDerivative (fderiv ℝ (fderiv ℝ f) x))).toSubmodule =
      LinearMap.range (continuousDualCarrierMap.comp
        (fderiv ℝ (fun y : E => (y, fderiv ℝ f y)) x).toLinearMap) := by
  have hp : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  exact graphGrassmannian_eq_covectorGraph_tangent (fderiv ℝ f)
    (fderiv ℝ (fderiv ℝ f) x) x hp.differentiableAt_one.hasFDerivAt

end Derivative

end InfoGeometry.Geometry.LegendreGraphGeometry
