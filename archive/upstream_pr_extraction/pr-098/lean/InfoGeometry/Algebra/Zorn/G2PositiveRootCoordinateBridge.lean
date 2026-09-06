import InfoGeometry.Algebra.Zorn.G2ChevalleyPoincareCombinatorics
import InfoGeometry.Algebra.Zorn.G2PositiveRootsInvariance

/-!
# Coordinate carrier for the six positive `G₂` roots

The inductive labels used by the finite PC layer and the integer-coordinate
root carrier used by the reflection lemmas are equivalent.  This file only
establishes that finite carrier equivalence; it does not define a Weyl action
on the concrete automorphism group.
-/

namespace InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2Roots

def rootCoordinates : G2PositiveRoot → ℤ × ℤ
  | .alpha => (1, 0)
  | .beta => (0, 1)
  | .alpha_add_beta => (1, 1)
  | .two_alpha_beta => (2, 1)
  | .three_alpha_beta => (3, 1)
  | .three_alpha_two_beta => (3, 2)

private theorem rootCoordinates_injective :
    Function.Injective rootCoordinates := by
  intro a b h
  cases a <;> cases b <;> simp [rootCoordinates] at h ⊢

private theorem rootCoordinates_surjective :
    Function.Surjective (fun α : G2PositiveRoot =>
      (⟨rootCoordinates α, by
        cases α <;> simp [rootCoordinates, phiPlus]⟩ :
          {x : ℤ × ℤ // x ∈ phiPlus})) := by
  rintro ⟨x, hx⟩
  simp [phiPlus] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.alpha, rfl⟩
  · exact ⟨.beta, rfl⟩
  · exact ⟨.alpha_add_beta, rfl⟩
  · exact ⟨.two_alpha_beta, rfl⟩
  · exact ⟨.three_alpha_beta, rfl⟩
  · exact ⟨.three_alpha_two_beta, rfl⟩

/-- Canonical equivalence between abstract positive-root labels and the
integer-coordinate positive-root carrier. -/
noncomputable def rootCoordinateEquiv :
    G2PositiveRoot ≃ {x : ℤ × ℤ // x ∈ phiPlus} :=
  Equiv.ofBijective
    (fun α : G2PositiveRoot =>
      ⟨rootCoordinates α, by
        cases α <;> simp [rootCoordinates, phiPlus]⟩)
    ⟨by
      intro a b h
      exact rootCoordinates_injective (Subtype.ext_iff.mp h),
     rootCoordinates_surjective⟩

@[simp] theorem rootCoordinateEquiv_apply (α : G2PositiveRoot) :
    rootCoordinateEquiv α =
      (⟨rootCoordinates α, by
        cases α <;> simp [rootCoordinates, phiPlus]⟩ :
          {x : ℤ × ℤ // x ∈ phiPlus}) := by
  rfl

/-! The highest positive label is expressed in the same integer-coordinate
    carrier as the simple labels.  This is a coordinate identity, not an
    additional Euclidean or representation-theoretic assumption. -/

theorem rootCoordinates_three_alpha_two_beta :
    rootCoordinates .three_alpha_two_beta =
      3 • rootCoordinates .alpha + 2 • rootCoordinates .beta := by
  norm_num [rootCoordinates]

end InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
