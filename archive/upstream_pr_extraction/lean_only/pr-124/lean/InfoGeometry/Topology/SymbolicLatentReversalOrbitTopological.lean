import InfoGeometry.Topology.SymbolicLatentInvolutionTopCat

namespace InfoGeometry.Topology

/-!
# Topological orbit transport under modular reversal

The reversal owner already proves one inclusion for the image of an orbit.
Involutivity gives the converse inclusion, and continuity upgrades the
involution to a genuine `Homeomorph`.
-/

def SymbolicLatentInvolution.toHomeomorph
    {X : Type*} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) : X ≃ₜ X where
  toFun := J
  invFun := J
  left_inv := J.left_inverse
  right_inv := J.right_inverse
  continuous_toFun := J.continuous
  continuous_invFun := J.continuous

@[simp] theorem SymbolicLatentInvolution.toHomeomorph_apply
    {X : Type*} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) (x : X) :
    J.toHomeomorph x = J x :=
  rfl

theorem SymbolicLatentModularReversal.orbit_image_eq
    {X : Type*} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    R.involution '' Φ.orbit x = Φ.orbit (R.involution x) := by
  apply Set.Subset.antisymm
  · exact R.orbit_image x
  · rintro y ⟨t, rfl⟩
    refine ⟨Φ.act (-t) x, ⟨-t, rfl⟩, ?_⟩
    simpa using R.reverses_flow (-t) x

theorem SymbolicLatentModularReversal.orbitClosure_image_eq
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    R.involution '' closure (Φ.orbit x) =
      closure (Φ.orbit (R.involution x)) := by
  change R.involution.toHomeomorph '' closure (Φ.orbit x) =
    closure (Φ.orbit (R.involution x))
  rw [R.involution.toHomeomorph.image_closure]
  change closure (R.involution '' Φ.orbit x) =
    closure (Φ.orbit (R.involution x))
  exact congrArg closure (R.orbit_image_eq x)

end InfoGeometry.Topology
