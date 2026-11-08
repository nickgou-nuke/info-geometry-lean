import InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCylinderSeparation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Coordinatewise homeomorphisms and compact prefix cylinders

An alphabet homeomorphism acts on the native boundary coordinatewise.  The
action transports a compact prefix cylinder to the cylinder with the
transformed finite word; no discreteness property is used.
-/

noncomputable section

namespace InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCoordinatewiseAction

open Set
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
open InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCylinder

variable {A : Type} [TopologicalSpace A] [CompactSpace A] [T2Space A]

def mapWord (γ : A ≃ₜ A) {n : ℕ} (w : Word (A := A) n) : Word (A := A) n :=
  fun i => γ (w i)

def boundaryCoordinatewiseHomeomorph (γ : A ≃ₜ A) :
    Boundary (A := A) ≃ₜ Boundary (A := A) where
  toEquiv :=
    { toFun := fun x n => γ (x n)
      invFun := fun x n => γ.symm (x n)
      left_inv := by
        intro x
        funext n
        simp
      right_inv := by
        intro x
        funext n
        simp }
  continuous_toFun := by
    apply continuous_pi
    intro n
    exact γ.continuous.comp (continuous_apply n)
  continuous_invFun := by
    apply continuous_pi
    intro n
    exact γ.symm.continuous.comp (continuous_apply n)

@[simp] theorem boundaryCoordinatewiseHomeomorph_apply
    (γ : A ≃ₜ A) (x : Boundary (A := A)) (n : ℕ) :
    boundaryCoordinatewiseHomeomorph γ x n = γ (x n) := rfl

theorem boundaryCoordinatewiseHomeomorph_preimage_compactPrefixCylinder
    (γ : A ≃ₜ A) (n : ℕ) (w : Word (A := A) n) :
    boundaryCoordinatewiseHomeomorph γ ⁻¹'
        compactPrefixCylinder (A := A) n (mapWord γ w) =
      compactPrefixCylinder (A := A) n w := by
  ext x
  constructor
  · intro hx
    apply (mem_compactPrefixCylinder_iff x).2
    intro i
    have hi := (mem_compactPrefixCylinder_iff
      (boundaryCoordinatewiseHomeomorph γ x)).mp hx i
    exact γ.injective hi
  · intro hx
    apply (mem_compactPrefixCylinder_iff
      (boundaryCoordinatewiseHomeomorph γ x)).2
    intro i
    exact congrArg γ ((mem_compactPrefixCylinder_iff x).mp hx i)

theorem isClosed_preimage_boundaryCoordinatewiseHomeomorph_compactPrefixCylinder
    (γ : A ≃ₜ A) (n : ℕ) (w : Word (A := A) n) :
    IsClosed
      (boundaryCoordinatewiseHomeomorph γ ⁻¹'
        compactPrefixCylinder (A := A) n (mapWord γ w)) := by
  rw [boundaryCoordinatewiseHomeomorph_preimage_compactPrefixCylinder]
  exact isClosed_compactPrefixCylinder n w

end InfoGeometry.Topology.NaryTreeBoundaryCompactHausdorffCoordinatewiseAction
