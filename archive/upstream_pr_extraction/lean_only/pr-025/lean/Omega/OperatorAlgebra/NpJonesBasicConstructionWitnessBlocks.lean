import Omega.OperatorAlgebra.FoldBasicConstructionPairGroupoid

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

instance np_jones_basic_construction_witness_blocks_pair_groupoid_fintype
    (fold : Ω → X) (x : X) : Fintype (pairGroupoidArrow fold x) :=
  show Fintype (foldFiber fold x × foldFiber fold x) from inferInstance

/-- The witness multiplicity attached to the fiber over `x`. -/
def np_jones_basic_construction_witness_blocks_witness_multiplicity
    (fold : Ω → X) (x : X) : ℕ :=
  Fintype.card (foldFiber fold x)

end

theorem np_jones_basic_construction_witness_blocks_certified :
    ∀ {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X] (fold : Ω → X),
      FoldBasicConstructionPairGroupoidStatement fold ∧
        ∀ x : X,
          Nonempty (pairGroupoidArrow fold x ≃ foldFiber fold x × foldFiber fold x) ∧
            Fintype.card (pairGroupoidArrow fold x) =
              np_jones_basic_construction_witness_blocks_witness_multiplicity fold x ^ 2 := by
  intro Ω X _ _ _ _ fold
  refine ⟨paper_op_algebra_fold_basic_construction_pair_groupoid fold, ?_⟩
  intro x
  refine ⟨⟨Equiv.refl _⟩, ?_⟩
  simp [pairGroupoidArrow, np_jones_basic_construction_witness_blocks_witness_multiplicity,
    pow_two]

end Omega.OperatorAlgebra
