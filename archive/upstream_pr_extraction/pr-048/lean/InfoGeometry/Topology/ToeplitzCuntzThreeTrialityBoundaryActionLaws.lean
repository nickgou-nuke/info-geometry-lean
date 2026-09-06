import InfoGeometry.Topology.ToeplitzCuntzThreeTrialityBoundaryGroupoidColimit

/-!
# Group-action laws for the ternary boundary

The coordinatewise permutation action is packaged here as explicit laws for
`Homeomorph`.  This is the topological group-action surface; it is distinct
from inner conjugation by the algebraic Coxeter element.
-/

noncomputable section

namespace InfoGeometry.Topology.ToeplitzCuntzThreeTriality

open InfoGeometry.Canonical

@[simp] theorem boundaryPermutationHomeomorph_one :
    boundaryPermutationHomeomorph (1 : Equiv.Perm ColorChannel) =
      Homeomorph.refl TernaryBoundary := by
  ext x n
  rfl

theorem boundaryPermutationHomeomorph_mul
    (σ τ : Equiv.Perm ColorChannel) :
    boundaryPermutationHomeomorph (σ * τ) =
      (boundaryPermutationHomeomorph τ).trans
        (boundaryPermutationHomeomorph σ) := by
  ext x n
  rfl

@[simp] theorem boundaryPermutationHomeomorph_symm
    (σ : Equiv.Perm ColorChannel) :
    (boundaryPermutationHomeomorph σ).symm =
      boundaryPermutationHomeomorph σ.symm := by
  ext x n
  rfl

end InfoGeometry.Topology.ToeplitzCuntzThreeTriality

end
