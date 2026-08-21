import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Root-coordinate layer for the split `G₂(2)` Chevalley construction

The six positive roots are the coordinates of the unipotent radical.  This
file records that finite coordinate space without confusing it with the full
automorphism group: the latter requires the Weyl action and the Chevalley
commutator relations.
-/

namespace InfoGeometry.Algebra.Zorn.G2TwoChevalleyRootCoordinates

abbrev F2 := ZMod 2
abbrev PositiveRoot := Fin 6
abbrev PositiveRootCoordinates := PositiveRoot → F2

theorem positive_root_count : Fintype.card PositiveRoot = 6 := by
  rfl

theorem positive_root_coordinate_card :
    Fintype.card PositiveRootCoordinates = 64 := by
  simp [PositiveRootCoordinates]

def rootCoordinate (i : PositiveRoot) (t : F2) : PositiveRootCoordinates :=
  fun j => if j = i then t else 0

theorem rootCoordinate_at (i j : PositiveRoot) (t : F2) :
    rootCoordinate i t j = if j = i then t else 0 := by
  rfl

theorem rootCoordinate_zero (i : PositiveRoot) :
    rootCoordinate i 0 = 0 := by
  funext j
  by_cases h : j = i <;> simp [rootCoordinate, h]

theorem rootCoordinate_add (i : PositiveRoot) (s t : F2) :
    rootCoordinate i (s + t) =
      rootCoordinate i s + rootCoordinate i t := by
  funext j
  by_cases h : j = i <;> simp [rootCoordinate, h]

def rootSubgroup (i : PositiveRoot) : F2 →+ PositiveRootCoordinates where
  toFun := rootCoordinate i
  map_zero' := rootCoordinate_zero i
  map_add' s t := rootCoordinate_add i s t

theorem rootSubgroup_apply (i : PositiveRoot) (t : F2) :
    rootSubgroup i t = rootCoordinate i t :=
  rfl

theorem rootSubgroup_injective (i : PositiveRoot) :
    Function.Injective (rootSubgroup i) := by
  intro s t h
  have h_at := congrFun h i
  simpa [rootSubgroup, rootCoordinate] using h_at

theorem rootCoordinate_sum (x : PositiveRootCoordinates) :
    (∑ i : PositiveRoot, rootCoordinate i (x i)) = x := by
  funext j
  simp [rootCoordinate]

theorem positive_root_coordinates_additive :
    ∀ (x y : PositiveRootCoordinates),
      x + y = y + x := by
  intro x y
  funext i
  exact add_comm _ _

end InfoGeometry.Algebra.Zorn.G2TwoChevalleyRootCoordinates
