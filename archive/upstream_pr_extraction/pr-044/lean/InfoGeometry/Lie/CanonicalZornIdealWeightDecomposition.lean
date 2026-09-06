import Mathlib.Algebra.Lie.Weights.Cartan
import InfoGeometry.Lie.CanonicalZornCartanRootSystem

/-!
# Weight decomposition of invariant Lie ideals

This file contains the two structural weight-space identities needed before
the Cartan-criterion backport.  They are the local form of the invariant
submodule decomposition used by newer Mathlib.
-/

section

namespace InfoGeometry.Lie.CanonicalZornIdealWeightDecomposition

open LieModule LieAlgebra

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M] [LieRing.IsNilpotent L]

theorem eq_iSup_inf_genWeightSpace
    [LieModule.IsTriangularizable K L M]
    (N : LieSubmodule K L M) :
    N = ⨆ χ : LieModule.Weight K L M, N ⊓ LieModule.genWeightSpace M χ := by
  refine le_antisymm ?_ (iSup_le fun χ ↦ inf_le_left)
  conv_lhs => rw [← N.map_incl_top, ← LieModule.iSup_genWeightSpace_eq_top' K L N,
    LieSubmodule.map_iSup]
  refine iSup_le fun χN ↦ ?_
  have hN := (LieSubmodule.map_mono
    (le_top : LieModule.genWeightSpace N χN ≤ ⊤)).trans N.map_incl_top.le
  refine (le_inf hN (LieModule.map_genWeightSpace_le _)).trans ?_
  by_cases h : LieModule.genWeightSpace M (χN : L → K) = ⊥
  · simp [h]
  · exact le_iSup_of_le ⟨_, h⟩ le_rfl

variable {R L : Type*} [Field R] [LieRing L] [LieAlgebra R L]
  [Module.Finite R L] [Module.Free R L]

def idealRestrict (I : LieIdeal R L) (H : LieSubalgebra R L) : LieSubmodule R H L :=
  { I with
    lie_mem := by
      intro h x hx
      exact I.lie_mem hx }

theorem lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra]
    [LieModule.IsTriangularizable R H L]
    (I : LieIdeal R L) :
    idealRestrict I H =
      (idealRestrict I H ⊓ H.toLieSubmodule) ⊔
        ⨆ α : LieModule.Weight R H L,
          ⨆ (_ : α.IsNonZero), idealRestrict I H ⊓ LieAlgebra.rootSpace H α := by
  refine le_antisymm ?_ (sup_le inf_le_left (iSup₂_le fun _ _ ↦ inf_le_left))
  conv_lhs => rw [eq_iSup_inf_genWeightSpace (idealRestrict I H)]
  refine iSup_le fun α ↦ ?_
  by_cases hα : α.IsZero
  · rw [show LieModule.genWeightSpace L (α : H → R) = H.toLieSubmodule by
      ext x
      simp [hα.eq]]
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)

end InfoGeometry.Lie.CanonicalZornIdealWeightDecomposition

end
