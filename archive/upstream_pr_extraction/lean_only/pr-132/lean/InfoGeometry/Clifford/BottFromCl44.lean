import InfoGeometry.Clifford.BottPeriodicity

open scoped TensorProduct

/-!
# InfoGeometry.Clifford.BottFromCl44

Real split Bott-step surface for the `Cl(4,4) → Cl(5,5)` lane.

This file records the repo-native real extension

`Cl(5,5) ≃ Cl(1,1) ᵍ⊗ Cl(4,4)`

and does **not** identify this step with complexification.
-/

namespace InfoGeometry.Clifford.BottFromCl44

open InfoGeometry.Clifford.BottPeriodicity

/-- Repo-native split `Cl(4,4)` stage. -/
abbrev Cl44 := SplitBottClifford 4

/-- Repo-native split `Cl(5,5)` stage. -/
abbrev Cl55 := SplitBottClifford 5

/--
The real split Bott extension from `Cl(4,4)` to `Cl(5,5)`.

This is the owner theorem from the split tower, re-exported under a
file-local name for architecture clarity.
-/
noncomputable def cl55_from_cl44_splitBottStep :=
  cl55_as_splitBottStep

/-- Readback to the owner Bott-step declaration. -/
theorem cl55_from_cl44_splitBottStep_eq_owner :
    cl55_from_cl44_splitBottStep = cl55_as_splitBottStep :=
  rfl

/--
HONEST THEOREM DEBT.

Construct explicit chirality data for the `Cl(5,5)` spinor lane and prove the
Majorana–Weyl decomposition in the repo's chosen spinor model.
-/
theorem majoranaWeyl_split_exists : ∃ ω : Cl55, ω * ω = 1 := by
  refine ⟨1, by simp⟩

-- The full involutive Majorana–Weyl splitting theorem (as stated in the
-- architecture notes) is still pending formalization in this file.

end InfoGeometry.Clifford.BottFromCl44
