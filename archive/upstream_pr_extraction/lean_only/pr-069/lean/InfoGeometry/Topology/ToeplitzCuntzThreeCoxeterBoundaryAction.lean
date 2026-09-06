import InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
import InfoGeometry.Topology.PauliJungTrialityD4Topological

/-!
# Coordinatewise Coxeter action on the ternary boundary

This owner supplies the topological side of the triality bridge.  It takes a
color homeomorphism as input and acts coordinatewise on the ternary boundary.
The algebraic identification of that homeomorphism with the Toeplitz--Cuntz
Coxeter element is intentionally left to a separate cylinder-covariance
owner.
-/

noncomputable section

namespace InfoGeometry.Topology.ToeplitzCuntzThreeCoxeterBoundaryAction

open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
open InfoGeometry.Canonical

abbrev TernaryBoundary := Boundary (A := ColorChannel)

def boundaryAction (γ : ColorChannel ≃ₜ ColorChannel) :
    TernaryBoundary → TernaryBoundary :=
  fun x n => γ (x n)

def boundaryActionHomeomorph (γ : ColorChannel ≃ₜ ColorChannel) :
    TernaryBoundary ≃ₜ TernaryBoundary where
  toEquiv :=
    { toFun := boundaryAction γ
      invFun := boundaryAction γ.symm
      left_inv := by
        intro x
        funext n
        simp [boundaryAction]
      right_inv := by
        intro x
        funext n
        simp [boundaryAction] }
  continuous_toFun := by
    apply continuous_pi
    intro n
    exact γ.continuous.comp (continuous_apply n)
  continuous_invFun := by
    apply continuous_pi
    intro n
    exact γ.symm.continuous.comp (continuous_apply n)

@[simp] theorem boundaryActionHomeomorph_apply
    (γ : ColorChannel ≃ₜ ColorChannel)
    (x : TernaryBoundary) (n : ℕ) :
    boundaryActionHomeomorph γ x n = γ (x n) := rfl

@[simp] theorem boundaryActionHomeomorph_prefix
    (γ : ColorChannel ≃ₜ ColorChannel)
    (c : ColorChannel) (x : TernaryBoundary) :
    boundaryActionHomeomorph γ (boundaryCons c x) =
      boundaryCons (γ c) (boundaryActionHomeomorph γ x) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

theorem boundaryActionHomeomorph_cube
    (γ : ColorChannel ≃ₜ ColorChannel)
    (hγ : ∀ c, γ (γ (γ c)) = c)
    (x : TernaryBoundary) :
    boundaryActionHomeomorph γ
        (boundaryActionHomeomorph γ (boundaryActionHomeomorph γ x)) = x := by
  funext n
  simp [boundaryAction, hγ]

end InfoGeometry.Topology.ToeplitzCuntzThreeCoxeterBoundaryAction
