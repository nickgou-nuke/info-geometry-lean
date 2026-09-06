import InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter
import InfoGeometry.Algebra.Zorn.G2RootInnerDerivationBridge
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

/-!
# Finite G₂ roots aligned with the native nonzero Cartan indices

This owner contains only the finite carrier alignment between the existing
`G2Root = RootLength × ZMod 6` carrier and the twelve nonzero indices in the
canonical fourteen-dimensional adjoint basis.  It deliberately does not assert
Weyl covariance of root derivations or any sign normalization.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment

open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2RootInnerDerivationBridge
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

abbrev NativeRootIndex :=
  InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.nonzeroIndex

/--
The canonical native adjoint-basis index attached to each finite `G2Root`.

The six short roots follow the repository order
`α, α+β, 2α+β, -α, -(α+β), -(2α+β)` and the six long roots follow
`β, 3α+β, 3α+2β, -β, -(3α+β), -(3α+2β)`.
-/
def rootIndexOf (r : G2Root) : NativeRootIndex :=
  ⟨G2ZornDerivationRootRepresentation.rootCoordinate r,
    rootCoordinate_ne_cartan_indices r⟩

@[simp] theorem rootIndexOf_short_zero :
    rootIndexOf (.Short, 0) = ⟨0, by decide, by decide⟩ := by
  apply Subtype.ext
  rfl

@[simp] theorem rootIndexOf_long_zero :
    rootIndexOf (.Long, 0) = ⟨1, by decide, by decide⟩ := by
  apply Subtype.ext
  rfl

theorem rootIndexOf_val (r : G2Root) :
    (rootIndexOf r).1 = G2ZornDerivationRootRepresentation.rootCoordinate r := rfl

set_option maxHeartbeats 1000000 in
theorem rootIndexOf_injective : Function.Injective rootIndexOf := by
  native_decide

/-- Every nonzero adjoint basis index is represented by a finite `G2Root`. -/
theorem rootIndexOf_surjective : Function.Surjective rootIndexOf := by
  intro i
  rcases i with ⟨i, hi6, hi13⟩
  fin_cases i
  · exact ⟨(.Short, 0), by rfl⟩
  · exact ⟨(.Long, 0), by rfl⟩
  · exact ⟨(.Long, 1), by rfl⟩
  · exact ⟨(.Short, 1), by rfl⟩
  · exact ⟨(.Short, 2), by rfl⟩
  · exact ⟨(.Long, 2), by rfl⟩
  · contradiction
  · exact ⟨(.Long, 3), by rfl⟩
  · exact ⟨(.Short, 3), by rfl⟩
  · exact ⟨(.Short, 4), by rfl⟩
  · exact ⟨(.Short, 5), by rfl⟩
  · exact ⟨(.Long, 4), by rfl⟩
  · exact ⟨(.Long, 5), by rfl⟩
  · contradiction

/-- Canonical equivalence between the two already-existing twelve-root carriers. -/
noncomputable def rootIndexEquiv : G2Root ≃ NativeRootIndex :=
  Equiv.ofBijective rootIndexOf ⟨rootIndexOf_injective, rootIndexOf_surjective⟩

@[simp] theorem rootIndexEquiv_apply (r : G2Root) :
    rootIndexEquiv r = rootIndexOf r := rfl

/-- Root negation agrees with the six opposite pairs in the native basis. -/
theorem rootIndexOf_negAction_value (r : G2Root) :
    (rootIndexOf (negAction r)).1 =
      match (rootIndexOf r).1 with
      | 0 => 8
      | 8 => 0
      | 3 => 9
      | 9 => 3
      | 4 => 10
      | 10 => 4
      | 1 => 7
      | 7 => 1
      | 2 => 11
      | 11 => 2
      | 5 => 12
      | 12 => 5
      | j => j := by
  rcases r with ⟨l, k⟩
  cases l <;> fin_cases k <;> native_decide

end InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
