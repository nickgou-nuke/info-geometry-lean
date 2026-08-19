import Mathlib.Data.ZMod.Basic

/-!
# Canonical Klein-four orientation tag

The parity/time bookkeeping group is the native additive group
`(ZMod 2) × (ZMod 2)`.  Jones and optical modules should alias this owner
rather than declaring independent two-Boolean records.
-/

namespace InfoGeometry.Geometry.KleinFourTag

/-- The Klein four group, with parity and time coordinates. -/
abbrev Tag :=
  ZMod 2 × ZMod 2

/-- Identity sector. -/
def id : Tag :=
  (0, 0)

/-- Parity-reflection sector. -/
def P : Tag :=
  (1, 0)

/-- Time-orientation-reversal sector. -/
def T : Tag :=
  (0, 1)

/-- Combined parity-time sector. -/
def PT : Tag :=
  (1, 1)

/-- Parity coordinate. -/
def parity (tag : Tag) : ZMod 2 :=
  tag.1

/-- Time-orientation coordinate. -/
def time (tag : Tag) : ZMod 2 :=
  tag.2

@[simp] theorem parity_id : parity id = 0 := rfl
@[simp] theorem time_id : time id = 0 := rfl
@[simp] theorem parity_P : parity P = 1 := rfl
@[simp] theorem time_P : time P = 0 := rfl
@[simp] theorem parity_T : parity T = 0 := rfl
@[simp] theorem time_T : time T = 1 := rfl
@[simp] theorem parity_PT : parity PT = 1 := rfl
@[simp] theorem time_PT : time PT = 1 := rfl

/-- Every named orientation generator has order two. -/
@[simp] theorem P_add_self : P + P = id := by
  ext <;> decide

@[simp] theorem T_add_self : T + T = id := by
  ext <;> decide

@[simp] theorem PT_add_self : PT + PT = id := by
  ext <;> decide

/-- The combined sector is the sum of the parity and time generators. -/
@[simp] theorem P_add_T : P + T = PT := by
  rfl

theorem tag_eq_id_or_P_or_T_or_PT (tag : Tag) :
    tag = id ∨ tag = P ∨ tag = T ∨ tag = PT := by
  rcases tag with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [id, P, T, PT]

end InfoGeometry.Geometry.KleinFourTag
