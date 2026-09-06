import InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter
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
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

abbrev NativeRootIndex :=
  InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.nonzeroIndex

/--
The canonical native adjoint-basis index attached to each finite `G2Root`.

The six short roots follow the repository order
`α, α+β, 2α+β, -α, -(α+β), -(2α+β)` and the six long roots follow
`β, 3α+β, 3α+2β, -β, -(3α+β), -(3α+2β)`.
-/
def rootIndexOf : G2Root → NativeRootIndex
  | (.Short, k) =>
      match k.val with
      | 0 => ⟨10, by decide, by decide⟩
      | 1 => ⟨9, by decide, by decide⟩
      | 2 => ⟨8, by decide, by decide⟩
      | 3 => ⟨0, by decide, by decide⟩
      | 4 => ⟨3, by decide, by decide⟩
      | 5 => ⟨4, by decide, by decide⟩
      | _ => ⟨10, by decide, by decide⟩
  | (.Long, k) =>
      match k.val with
      | 0 => ⟨1, by decide, by decide⟩
      | 1 => ⟨11, by decide, by decide⟩
      | 2 => ⟨12, by decide, by decide⟩
      | 3 => ⟨5, by decide, by decide⟩
      | 4 => ⟨2, by decide, by decide⟩
      | 5 => ⟨7, by decide, by decide⟩
      | _ => ⟨1, by decide, by decide⟩

@[simp] theorem rootIndexOf_short_zero :
    rootIndexOf (.Short, 0) = ⟨10, by decide, by decide⟩ := by
  rfl

@[simp] theorem rootIndexOf_long_zero :
    rootIndexOf (.Long, 0) = ⟨1, by decide, by decide⟩ := by
  rfl

/-- The finite-root to native-index map is injective. -/
theorem rootIndexOf_injective : Function.Injective rootIndexOf := by
  intro r s h
  rcases r with ⟨lr, kr⟩
  rcases s with ⟨ls, ks⟩
  cases lr <;> cases ls <;> fin_cases kr <;> fin_cases ks <;>
    simp [rootIndexOf] at h ⊢

/-- Every nonzero adjoint basis index is represented by a finite `G2Root`. -/
theorem rootIndexOf_surjective : Function.Surjective rootIndexOf := by
  intro i
  rcases i with ⟨i, hi6, hi13⟩
  fin_cases i
  · exact ⟨(.Short, 3), by rfl⟩
  · exact ⟨(.Long, 0), by rfl⟩
  · exact ⟨(.Long, 4), by rfl⟩
  · exact ⟨(.Short, 4), by rfl⟩
  · exact ⟨(.Short, 5), by rfl⟩
  · exact ⟨(.Long, 3), by rfl⟩
  · contradiction
  · exact ⟨(.Long, 5), by rfl⟩
  · exact ⟨(.Short, 2), by rfl⟩
  · exact ⟨(.Short, 1), by rfl⟩
  · exact ⟨(.Short, 0), by rfl⟩
  · exact ⟨(.Long, 1), by rfl⟩
  · exact ⟨(.Long, 2), by rfl⟩
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
      | 0 => 10
      | 10 => 0
      | 1 => 5
      | 5 => 1
      | 2 => 11
      | 11 => 2
      | 3 => 9
      | 9 => 3
      | 4 => 8
      | 8 => 4
      | 7 => 12
      | 12 => 7
      | j => j := by
  rcases r with ⟨l, k⟩
  cases l <;> fin_cases k <;> rfl

end InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
