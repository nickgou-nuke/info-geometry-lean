import InfoGeometry.Topology.SymbolicLatentCompactHausdorffPrefixLimitCylinder
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCoordinatewiseAction

/-!
# Coordinatewise dynamics on the compact prefix limit

The canonical boundary/limit homeomorphism transports every coordinatewise
alphabet homeomorphism to the native inverse-limit carrier.  The transported
action preserves the compact-Hausdorff prefix-cylinder decomposition.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentCompactHausdorffPrefixLimitAction

open Set CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
open InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCylinder
open InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCoordinatewiseAction
open InfoGeometry.Topology.SymbolicLatentCompactHausdorffPrefixLimitCylinder

variable {A : Type} [TopologicalSpace A] [CompactSpace A] [T2Space A]

noncomputable def prefixLimitCoordinatewiseHomeomorph (γ : A ≃ₜ A) :
    ((limit (prefixDiagram (A := A)) : TopCat) : Type) ≃ₜ
      ((limit (prefixDiagram (A := A)) : TopCat) : Type) := by
  let e := TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A))
  exact (e.symm.trans (boundaryCoordinatewiseHomeomorph γ)).trans e

theorem prefixLimitCoordinatewiseHomeomorph_apply
    (γ : A ≃ₜ A)
    (x : ((limit (prefixDiagram (A := A)) : TopCat) : Type)) :
    prefixLimitCoordinatewiseHomeomorph (A := A) γ x =
      (TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A)))
        (boundaryCoordinatewiseHomeomorph γ
          (ConcreteCategory.hom (prefixBoundaryLimitIso (A := A)).inv x)) := by
  rfl

theorem prefixLimitCoordinatewiseHomeomorph_stage_apply
    (γ : A ≃ₜ A) (n : ℕ)
    (x : ((limit (prefixDiagram (A := A)) : TopCat) : Type))
    (i : Fin n) :
    (limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom
        (prefixLimitCoordinatewiseHomeomorph (A := A) γ x) i =
      γ ((limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom x i) := by
  rw [prefixLimitCoordinatewiseHomeomorph_apply]
  have h₁ := prefixBoundaryLimitIso_hom_apply (A := A) n
    (boundaryCoordinatewiseHomeomorph γ
      (ConcreteCategory.hom (prefixBoundaryLimitIso (A := A)).inv x)) i
  calc
    (limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom
          ((TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A)))
            (boundaryCoordinatewiseHomeomorph γ
              (ConcreteCategory.hom (prefixBoundaryLimitIso (A := A)).inv x))) i =
        γ (ConcreteCategory.hom (prefixBoundaryLimitIso (A := A)).inv x i) := by
          simpa [boundaryCoordinatewiseHomeomorph_apply] using h₁
    _ = γ ((limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom x i) := by
      congr 1
      have h₂ := prefixBoundaryLimitIso_hom_apply (A := A) n
        (ConcreteCategory.hom (prefixBoundaryLimitIso (A := A)).inv x) i
      rw [← h₂]
      congr 1
      exact congrArg (fun z =>
        (limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom z i)
        (congrArg (fun f => f x)
          (prefixBoundaryLimitIso (A := A)).inv_hom_id)

theorem prefixLimitCoordinatewiseHomeomorph_trans
    (γ δ : A ≃ₜ A) :
    (prefixLimitCoordinatewiseHomeomorph (A := A) γ).trans
        (prefixLimitCoordinatewiseHomeomorph (A := A) δ) =
      prefixLimitCoordinatewiseHomeomorph (A := A) (γ.trans δ) := by
  let e := TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A))
  ext x
  apply e.symm.injective
  have hformula (κ : A ≃ₜ A) (y : ↑(limit (prefixDiagram (A := A)))) :
      e.symm (prefixLimitCoordinatewiseHomeomorph (A := A) κ y) =
        boundaryCoordinatewiseHomeomorph κ (e.symm y) := by
    change e.symm (e (boundaryCoordinatewiseHomeomorph κ (e.symm y))) =
      boundaryCoordinatewiseHomeomorph κ (e.symm y)
    exact e.symm_apply_apply _
  have hboundary :
      boundaryCoordinatewiseHomeomorph δ
          (boundaryCoordinatewiseHomeomorph γ (e.symm x)) =
        boundaryCoordinatewiseHomeomorph (γ.trans δ) (e.symm x) := by
    ext n
    rfl
  rw [Homeomorph.trans_apply, hformula, hformula, hformula]
  exact hboundary

theorem prefixLimitCoordinatewiseHomeomorph_preimage_compactPrefixCylinder
    (γ : A ≃ₜ A) (n : ℕ) (w : Word (A := A) n) :
    prefixLimitCoordinatewiseHomeomorph (A := A) γ ⁻¹'
        compactHausdorffPrefixLimitCylinder (A := A) n (mapWord γ w) =
      compactHausdorffPrefixLimitCylinder (A := A) n w := by
  ext x
  have hcancel (z : Boundary (A := A)) :
      ConcreteCategory.hom (prefixBoundaryLimitIso (A := A)).inv
          ((TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A))) z) = z := by
    change (TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A))).symm
        ((TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A))) z) = z
    exact (TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A))).symm_apply_apply z
  simp only [Set.mem_preimage, prefixLimitCoordinatewiseHomeomorph,
    compactHausdorffPrefixLimitCylinder]
  change ConcreteCategory.hom (prefixBoundaryLimitIso (A := A)).inv
      ((TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A)))
        ((boundaryCoordinatewiseHomeomorph γ)
          (ConcreteCategory.hom (prefixBoundaryLimitIso (A := A)).inv x))) ∈
        compactPrefixCylinder (A := A) n (mapWord γ w) ↔
    ConcreteCategory.hom (prefixBoundaryLimitIso (A := A)).inv x ∈
      compactPrefixCylinder (A := A) n w
  rw [hcancel]
  exact Set.ext_iff.mp
    (boundaryCoordinatewiseHomeomorph_preimage_compactPrefixCylinder
      (A := A) γ n w) ((prefixBoundaryLimitIso (A := A)).inv.hom x)

theorem prefixLimitCoordinatewiseHomeomorph_image_compactPrefixCylinder
    (γ : A ≃ₜ A) (n : ℕ) (w : Word (A := A) n) :
    prefixLimitCoordinatewiseHomeomorph (A := A) γ ''
        compactHausdorffPrefixLimitCylinder (A := A) n w =
      compactHausdorffPrefixLimitCylinder (A := A) n (mapWord γ w) := by
  let H := prefixLimitCoordinatewiseHomeomorph (A := A) γ
  let C := compactHausdorffPrefixLimitCylinder (A := A) n w
  let C' := compactHausdorffPrefixLimitCylinder (A := A) n (mapWord γ w)
  have hpre : H ⁻¹' C' = C := by
    exact prefixLimitCoordinatewiseHomeomorph_preimage_compactPrefixCylinder
      (A := A) γ n w
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change H y ∈ C'
    have : y ∈ H ⁻¹' C' := by
      rw [hpre]
      exact hy
    exact this
  · intro hx
    refine ⟨H.symm x, ?_, H.apply_symm_apply x⟩
    have : H.symm x ∈ H ⁻¹' C' := by
      change H (H.symm x) ∈ C'
      simpa using hx
    rw [hpre] at this
    exact this

end InfoGeometry.Topology.SymbolicLatentCompactHausdorffPrefixLimitAction
