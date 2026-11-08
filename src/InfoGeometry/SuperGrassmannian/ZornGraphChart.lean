/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftGrading
import InfoGeometry.SuperGrassmannian.GradedGraphChart
import Mathlib.RingTheory.Grassmannian
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Native Grassmannian graph points for the corrected Zorn splitting

This is an ordinary algebraic Grassmannian chart. The four in Mathlib's
Grassmannian is the quotient rank. No supermanifold or representability
claim is made. Every graph quotient is explicitly isomorphic to the fixed
negative half, so its projectivity and rank are consequences, not inputs.
-/
noncomputable section
namespace InfoGeometry.SuperGrassmannian.ZornGraphChart
open InfoGeometry.Algebra
variable {R : Type*} [CommRing R]

abbrev Positive (R : Type*) := R × ZornVec3 R
abbrev Negative (R : Type*) := ZornVec3 R × R

/-- Regroup the existing coordinates into the actual left Peirce halves. -/
def splitEquiv : ZornVectorMatrix R ≃ₗ[R] Positive R × Negative R where
  toEquiv := ZornVectorMatrix.coordEquiv.trans
    (Equiv.prodAssoc R (ZornVec3 R) (ZornVec3 R × R)).symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem splitEquiv_apply (X : ZornVectorMatrix R) :
    splitEquiv X = ((X.a, X.v), (X.w, X.b)) := rfl

@[simp] theorem splitEquiv_symm_apply (x : Positive R) (y : Negative R) :
    splitEquiv.symm (x, y) = (⟨x.1, x.2, y.1, y.2⟩ : ZornVectorMatrix R) := rfl

/-- The existing octonionic left projector is exactly the zero graph projector. -/
theorem splitEquiv_left_E11 (X : ZornVectorMatrix R) :
    splitEquiv (L_map (R := R) ZornVectorMatrix.E11 X) =
      ProjectorGraphChart.graphProjector (0 : Positive R →ₗ[R] Negative R) (splitEquiv X) := by
  rw [ZornVectorMatrix.left_E11_apply]
  rfl

/-- The quotient readout whose kernel is the graph in native Zorn coordinates. -/
def graphReadout (f : Positive R →ₗ[R] Negative R) : ZornVectorMatrix R →ₗ[R] Negative R :=
  ((-f).coprod LinearMap.id).comp splitEquiv.toLinearMap

@[simp] theorem graphReadout_apply (f : Positive R →ₗ[R] Negative R) (X : ZornVectorMatrix R) :
    graphReadout f X = -f (X.a, X.v) + (X.w, X.b) := rfl

theorem graphReadout_surjective (f : Positive R →ₗ[R] Negative R) :
    Function.Surjective (graphReadout f) := by
  intro y
  refine ⟨splitEquiv.symm (0, y), ?_⟩
  change -f 0 + y = y
  simp

/-- The existing graph submodule is transported, not replaced by a new predicate. -/
theorem graphKernel_eq_comap (f : Positive R →ₗ[R] Negative R) :
    LinearMap.ker (graphReadout f) = f.graph.comap splitEquiv.toLinearMap := by
  rw [LinearMap.graph_eq_ker_coprod]
  rfl

@[simp] theorem mem_graphKernel (f : Positive R →ₗ[R] Negative R) (X : ZornVectorMatrix R) :
    X ∈ LinearMap.ker (graphReadout f) ↔ (X.w, X.b) = f (X.a, X.v) := by
  change -f (X.a, X.v) + (X.w, X.b) = 0 ↔ _
  rw [neg_add_eq_sub, sub_eq_zero]

/-- An explicit quotient equivalence determines the Grassmannian rank. -/
def quotientEquiv (f : Positive R →ₗ[R] Negative R) :
    (ZornVectorMatrix R ⧸ LinearMap.ker (graphReadout f)) ≃ₗ[R] Negative R :=
  (graphReadout f).quotKerEquivOfSurjective (graphReadout_surjective f)

/-- The zero graph is precisely the image of the corrected projector. -/
theorem zero_graph_eq_range_left_E11 :
    LinearMap.ker (graphReadout (0 : Positive R →ₗ[R] Negative R)) =
      LinearMap.range (L_map (R := R) (ZornVectorMatrix.E11 : ZornVectorMatrix R)) := by
  ext X
  constructor
  · intro h
    have hzero : (X.w, X.b) = (0, 0) := (mem_graphKernel 0 X).mp h
    refine ⟨X, ?_⟩
    rw [ZornVectorMatrix.left_E11_apply]
    have hw := congrArg Prod.fst hzero
    have hb := congrArg Prod.snd hzero
    ext i <;> simp_all
  · rintro ⟨Y, rfl⟩
    rw [mem_graphKernel, ZornVectorMatrix.left_E11_apply]
    simp

section Grassmannian
variable [Nontrivial R]

/-- Actual native Grassmannian points, with finite projective rank-four quotients. -/
def grassmannianChart (f : Positive R →ₗ[R] Negative R) :
    Module.Grassmannian R (ZornVectorMatrix R) 4 where
  toSubmodule := LinearMap.ker (graphReadout f)
  finite_quotient := Module.Finite.equiv (quotientEquiv f).symm
  projective_quotient := Module.Projective.of_equiv (quotientEquiv f).symm
  rankAtStalk_eq p := by
    have h := congrFun (Module.rankAtStalk_eq_of_equiv (quotientEquiv f)) p
    rw [h]
    simp [Module.rankAtStalk_eq_finrank_of_free, Negative, ZornVec3, Module.finrank_prod]

/-- Distinct graph maps give distinct Grassmannian points, not just different complements. -/
theorem grassmannianChart_injective : Function.Injective (grassmannianChart (R := R)) := by
  intro f g h
  have hs := congrArg Module.Grassmannian.toSubmodule h
  change LinearMap.ker (graphReadout f) = LinearMap.ker (graphReadout g) at hs
  apply LinearMap.ext
  intro x
  let X := splitEquiv.symm (x, f x)
  have hf : X ∈ LinearMap.ker (graphReadout f) := by
    rw [mem_graphKernel]
    rfl
  have hg : X ∈ LinearMap.ker (graphReadout g) := hs ▸ hf
  exact (mem_graphKernel g X).mp hg

end Grassmannian
end InfoGeometry.SuperGrassmannian.ZornGraphChart
