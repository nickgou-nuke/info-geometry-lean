import InfoGeometry.Canonical.E8RootDecomposition
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# E₈ roots as a Mathlib root pairing

This module transports the already verified finite coordinate E₈ root set to
Mathlib's native `RootPairing` interface. The base coordinate owner remains
independent of this representation-theoretic API.
-/

namespace InfoGeometry.Canonical.E8RootDecomposition

/-- The linear functional associated to a norm-two E₈ root. -/
def e8CorootFunctional (α : E8Root) : Module.Dual ℚ (Fin 8 → ℚ) where
  toFun := fun v => e8Dot v α.1
  map_add' := fun v w => e8Dot_add_left v w α.1
  map_smul' := fun c v => e8Dot_smul_left c v α.1

/-- The coroot functionals distinguish the explicit E₈ roots. -/
theorem e8CorootFunctional_injective : Function.Injective e8CorootFunctional := by
  intro α β h
  apply Subtype.ext
  funext i
  have hi := congrArg (fun f : Module.Dual ℚ (Fin 8 → ℚ) =>
    f (Pi.single i (1 : ℚ))) h
  have hα : e8Dot (Pi.single i (1 : ℚ)) α.1 = α.1 i := by
    simp [e8Dot, Pi.single_apply]
  have hβ : e8Dot (Pi.single i (1 : ℚ)) β.1 = β.1 i := by
    simp [e8Dot, Pi.single_apply]
  simpa [e8CorootFunctional, hα, hβ] using hi

/-- Mathlib `RootPairing` structure on the explicit 240 rational E₈ roots.

The root and coroot maps are both injective, the evaluation pairing is the
standard perfect pairing with the dual, and the reflection permutation is
the concrete coordinate reflection already proved closed above. -/
noncomputable def e8MathlibRootPairing :
    RootPairing E8Root ℚ (Fin 8 → ℚ) (Module.Dual ℚ (Fin 8 → ℚ)) where
  toLinearMap := Module.Dual.eval ℚ (Fin 8 → ℚ)
  root := ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
  coroot := ⟨e8CorootFunctional, e8CorootFunctional_injective⟩
  root_coroot_two := by
    intro α
    exact e8_roots_norm α.1 α.2
  reflectionPerm α :=
    { toFun := fun β => ⟨e8Reflection α.1 β.1,
        e8_roots_reflection_closed α.1 β.1 α.2 β.2⟩
      invFun := fun β => ⟨e8Reflection α.1 β.1,
        e8_roots_reflection_closed α.1 β.1 α.2 β.2⟩
      left_inv := fun β => Subtype.ext
        (e8Reflection_involutive α.1 β.1 (e8_roots_norm α.1 α.2))
      right_inv := fun β => Subtype.ext
        (e8Reflection_involutive α.1 β.1 (e8_roots_norm α.1 α.2)) }
  reflectionPerm_root := by
    intro α β
    rfl
  reflectionPerm_coroot := by
    intro α β
    apply LinearMap.ext
    intro v
    change e8Dot v β.1 - e8Dot α.1 β.1 * e8Dot v α.1 =
      e8Dot v (e8Reflection α.1 β.1)
    rw [e8Reflection, e8Dot_sub_right, e8Dot_smul_right,
      e8Dot_comm α.1 β.1]

/-- The native Mathlib root pairing has the five crystallographic Cartan
values already established for the coordinate E₈ roots. -/
theorem e8MathlibRootPairing_cartan_pairing (α β : E8Root) :
    e8MathlibRootPairing.pairing α β ∈ ({-2, -1, 0, 1, 2} : Finset ℚ) := by
  change e8Dot α.1 β.1 ∈ ({-2, -1, 0, 1, 2} : Finset ℚ)
  exact e8_roots_pairing_mem α.1 β.1 α.2 β.2

/-- The coordinate E₈ pairing is crystallographic in Mathlib's native sense:
every root-coroot pairing is the image of an integer. -/
theorem e8MathlibRootPairing_isCrystallographic :
    e8MathlibRootPairing.IsCrystallographic := by
  change e8MathlibRootPairing.IsValuedIn ℤ
  rw [RootPairing.isValuedIn_iff_mem_range]
  intro α β
  have h := e8MathlibRootPairing_cartan_pairing α β
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h
  · exact ⟨-2, by norm_num [h]⟩
  · exact ⟨-1, by norm_num [h]⟩
  · exact ⟨0, by norm_num [h]⟩
  · exact ⟨1, by norm_num [h]⟩
  · exact ⟨2, by norm_num [h]⟩

end InfoGeometry.Canonical.E8RootDecomposition
