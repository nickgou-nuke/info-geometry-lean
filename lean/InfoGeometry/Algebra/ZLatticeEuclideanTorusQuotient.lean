/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Portions adapted from `external_refs/riemann-masullo`
(`RiemannMasullo/ForMathlib/Algebra/Module/ZLattice/Quotient.lean`, Apache-2.0,
revision `be5d4cb0356d48406eae83233d73c99085b9a038`).
-/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Euclidean–Torus Quotient of Discrete `ℤ`-Submodules

Ports `exists_euclidean_torus_quotient` from `RiemannMasullo` to this checkout's
pinned Mathlib (`v4.34.1`, where `ContinuousLinearEquiv.prodCongr` lives in
`Mathlib.Topology.Algebra.Module.Equiv`): every discrete `ℤ`-submodule of a
finite-dimensional real normed space is the kernel of an open quotient homomorphism
onto `EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ))`.
-/

public section

noncomputable section

namespace InfoGeometry.Algebra.ZLatticeEuclideanTorusQuotient

open Module Set Topology

/-- A discrete integral submodule of a finite-dimensional real normed space is the kernel of
an open quotient map to a product of a Euclidean space and a finite-dimensional torus. -/
theorem exists_euclidean_torus_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ (m n : ℕ) (q : E →+ EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ))),
      IsOpenQuotientMap q ∧ q.ker = L.toAddSubgroup := by
  classical
  let W := Submodule.span ℝ (L : Set E)
  let M : Submodule ℤ W := L.comap (W.subtype.restrictScalars ℤ)
  let toL : M → L := fun x ↦ ⟨x.val.val, x.property⟩
  have : DiscreteTopology M := DiscreteTopology.of_continuous_injective
    (f := toL) ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (fun y : L ↦ (y : E)) h)))
  have hRange : (M : Set W) = range (L.inclusionSpan ℝ) := by
    ext x
    exact ⟨fun hx ↦ ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩
  have : IsZLattice ℝ M := ⟨hRange ▸ L.span_range_inclusionSpan ℝ⟩
  obtain ⟨V, hVW⟩ := W.exists_isCompl
  let m := finrank ℝ V
  let n := finrank ℤ M
  let b := (finBasis ℤ M).ofZLatticeBasis ℝ
  let eV : V ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (finBasis ℝ V).equivFun.toContinuousLinearEquiv.trans (EuclideanSpace.equiv _ ℝ).symm
  let eW : W ≃L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  let split := (V.prodEquivOfIsCompl W hVW.symm).toContinuousLinearEquiv
  let circle := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  let qW := AddMonoidHom.pi (fun i : Fin n ↦ circle.comp (Pi.evalAddMonoidHom (fun _ ↦ ℝ) i))
  have hCircle : IsOpenQuotientMap circle := QuotientAddGroup.isOpenQuotientMap_mk
  have hqW : IsOpenQuotientMap qW :=
    ⟨Function.Surjective.piMap (fun _ ↦ hCircle.surjective),
      continuous_pi (fun i ↦ hCircle.continuous.comp (continuous_apply i)),
      IsOpenMap.piMap (fun _ ↦ hCircle.isOpenMap) (Filter.Eventually.of_forall fun _ ↦
        hCircle.surjective)⟩
  let coords := split.symm.trans (ContinuousLinearEquiv.prodCongr eV eW)
  let q := ((AddMonoidHom.id _).prodMap qW).comp coords.toLinearEquiv.toAddEquiv.toAddMonoidHom
  refine ⟨m, n, q, ?_, ?_⟩
  · exact (IsOpenQuotientMap.id.prodMap hqW).comp coords.toHomeomorph.isOpenQuotientMap
  · have hW (w : W) : qW (eW w) = 0 ↔ w ∈ M := by
      rw [← (finBasis ℤ M).ofZLatticeBasis_span ℝ, b.mem_span_iff_repr_mem ℤ]
      rw [funext_iff]
      change (∀ i, ((b.repr w i : ℝ) : AddCircle (1 : ℝ)) = 0) ↔ _
      simp only [AddCircle.coe_eq_zero_iff, zsmul_one, Set.mem_range]
      rfl
    ext x
    change (eV (split.symm x).1, qW (eW (split.symm x).2)) = (0, 0) ↔ x ∈ L
    rw [Prod.mk.injEq, hW, ← eV.map_zero, eV.injective.eq_iff]
    constructor
    · rintro ⟨hV, hM⟩
      have hx := split.apply_symm_apply x
      change (split.symm x).1.val + (split.symm x).2.val = x at hx
      rw [hV, Submodule.coe_zero, zero_add] at hx
      exact hx ▸ hM
    · intro hx
      let w : W := ⟨x, Submodule.subset_span hx⟩
      have hsplit : split.symm x = (0, w) :=
        V.prodEquivOfIsCompl_symm_apply_right W hVW.symm w
      rw [hsplit]
      exact ⟨rfl, hx⟩

end InfoGeometry.Algebra.ZLatticeEuclideanTorusQuotient

end noncomputable section
