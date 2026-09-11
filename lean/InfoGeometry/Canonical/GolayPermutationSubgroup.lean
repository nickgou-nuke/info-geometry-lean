import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.LeechGolayCoordinateAction

/-! The exact pre-classification subgroup of coordinate symmetries preserving
the extended binary Golay code.  No identification with `M24` is asserted. -/
namespace InfoGeometry.Canonical.GolayPermutationSubgroup

open InfoGeometry.Combinatorics.ExtendedBinaryGolay
open InfoGeometry.Combinatorics.LeechLattice
open InfoGeometry.Canonical.LeechGolayCoordinateAction

def PreservesGolay (σ : Equiv.Perm (Fin 24)) : Prop :=
  ∀ c : Word24, c ∈ codeSubmodule ↔ permuteCoords σ c ∈ codeSubmodule

def golayPermutationSubgroup : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {σ | PreservesGolay σ}
  one_mem' := by intro c; simp [PreservesGolay]
  mul_mem' := by
    intro σ τ hσ hτ c
    change c ∈ codeSubmodule ↔ permuteCoords (σ * τ) c ∈ codeSubmodule
    rw [permuteCoords_comp]
    exact (hτ c).trans (hσ (permuteCoords τ c))
  inv_mem' := by
    intro σ hσ c
    have h := hσ (permuteCoords σ⁻¹ c)
    have hcancel : permuteCoords σ (permuteCoords σ⁻¹ c) = c := by
      rw [← permuteCoords_comp]
      simp
    rw [hcancel] at h
    exact h.symm

def toCoordinateAutomorphism (g : golayPermutationSubgroup) :
    GolayCoordinateAutomorphism where
  perm := g.1
  code_mem_iff := g.2

theorem mapsTo_numerator (g : golayPermutationSubgroup) :
    Set.MapsTo (toCoordinateAutomorphism g).onInteger numerator numerator :=
  (toCoordinateAutomorphism g).mapsTo_numerator

end InfoGeometry.Canonical.GolayPermutationSubgroup
