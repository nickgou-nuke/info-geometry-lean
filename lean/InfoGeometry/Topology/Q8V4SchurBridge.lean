import Mathlib.GroupTheory.SpecificGroups.Quaternion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.Q8MonodromySpinorCover
import InfoGeometry.Topology.V4RootSystem

/-!
# Q8 to V4 Schur bridge

This file records the finite quotient map from `QuaternionGroup 2` onto the
Klein four-group `V4Group`, together with the concrete matrix anticommutation
already verified in `Q8MonodromySpinorCover`.

The content is deliberately finite:
- the quotient map kills the central element `a^2`;
- the map is surjective onto the four `V4Group` classes;
- the matrix generators `M_i` and `M_j` anticommute, so the quotient
  representation is projective.
-/

namespace InfoGeometry.Topology.Q8V4SchurBridge

open QuaternionGroup

open InfoGeometry.Topology.V4RootSystem

/-- The canonical quotient from `Q8` to the finite Klein four-group. -/
def q8ToV4 : QuaternionGroup 2 →* V4Group where
  toFun
    | a 0 => V4Group.I
    | a 1 => V4Group.W1
    | a 2 => V4Group.I
    | a 3 => V4Group.W1
    | xa 0 => V4Group.W2
    | xa 1 => V4Group.W12
    | xa 2 => V4Group.W2
    | xa 3 => V4Group.W12
  map_one' := rfl
  map_mul' := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide

/-- The quotient map is surjective onto all four `V4` classes. -/
theorem q8ToV4_surjective : Function.Surjective q8ToV4 := by
  intro v
  cases v with
  | I => exact ⟨a 0, by decide⟩
  | W1 => exact ⟨a 1, by decide⟩
  | W2 => exact ⟨xa 0, by decide⟩
  | W12 => exact ⟨xa 1, by decide⟩

/-- The central element `a^2 = -1` dies in the quotient. -/
theorem q8ToV4_central_two : q8ToV4 (a (2 : ZMod 4)) = V4Group.I := by
  rfl

/-- The concrete quaternion-spinor generators anticommute. -/
theorem q8_spinor_generators_anticommute :
    Q8MonodromySpinorCover.M_i * Q8MonodromySpinorCover.M_j =
      -(Q8MonodromySpinorCover.M_j * Q8MonodromySpinorCover.M_i) :=
  Q8MonodromySpinorCover.M_i_M_j_anticommute

end InfoGeometry.Topology.Q8V4SchurBridge
