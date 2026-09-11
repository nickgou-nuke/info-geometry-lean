import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.HexagonalSixRootTiling

/- The finite representatives are `Fin`; `zmodIndex` and `zmodColor` give the
   canonical additive-group presentations by `ZMod 6` and `ZMod 3`. -/
abbrev HexIndex := Fin 6
abbrev HexColor := Fin 3

noncomputable def zmodIndex : HexIndex ≃+ ZMod 6 := ZMod.finEquiv 6
noncomputable def zmodColor : HexColor ≃+ ZMod 3 := ZMod.finEquiv 3

inductive HexSheet
  | positive
  | negative
  deriving DecidableEq, Fintype

def positiveVertex (a : HexColor) : HexIndex :=
  ⟨(2 * a.val) % 6, by omega⟩

def negativeVertex (a : HexColor) : HexIndex :=
  ⟨(2 * a.val + 3) % 6, by omega⟩

def sheetOf (n : HexIndex) : HexSheet :=
  if n.val % 2 = 0 then .positive else .negative

def colorOf (n : HexIndex) : HexColor :=
  ⟨match n.val with
    | 0 => 0
    | 1 => 2
    | 2 => 1
    | 3 => 0
    | 4 => 2
    | _ => 1, by fin_cases n <;> decide⟩

def sheetColorEquiv : HexIndex ≃ HexSheet × HexColor where
  toFun n := (sheetOf n, colorOf n)
  invFun := fun p => match p with
    | (.positive, a) => positiveVertex a
    | (.negative, a) => negativeVertex a
  left_inv := by
    intro n
    fin_cases n <;> decide
  right_inv := by
    rintro ⟨s, a⟩
    cases s <;> fin_cases a <;> decide

theorem sheetColorEquiv_apply (n : HexIndex) :
    sheetColorEquiv n = (sheetOf n, colorOf n) := rfl

theorem positiveVertex_injective : Function.Injective positiveVertex := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [positiveVertex] at h ⊢

theorem negativeVertex_injective : Function.Injective negativeVertex := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [negativeVertex] at h ⊢

theorem positive_negative_disjoint (a b : HexColor) :
    positiveVertex a ≠ negativeVertex b := by
  fin_cases a <;> fin_cases b <;> simp [positiveVertex, negativeVertex]

theorem positiveVertex_range :
    Set.range positiveVertex = {0, 2, 4} := by
  apply Set.Subset.antisymm
  · rintro n ⟨a, rfl⟩
    fin_cases a <;> simp [positiveVertex]
  · intro n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨2, by decide⟩

theorem negativeVertex_range :
    Set.range negativeVertex = {1, 3, 5} := by
  apply Set.Subset.antisymm
  · rintro n ⟨a, rfl⟩
    fin_cases a <;> simp [negativeVertex]
  · intro n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl
    · exact ⟨2, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩

theorem alternating_cycles_disjoint :
    ({0, 2, 4} : Set HexIndex) ∩ {1, 3, 5} = ∅ := by
  ext n
  fin_cases n <;> simp

theorem alternating_cycles_cover :
    ({0, 2, 4} : Set HexIndex) ∪ {1, 3, 5} = Set.univ := by
  ext n
  fin_cases n <;> simp

def colorRotation (n : HexIndex) : HexIndex :=
  ⟨(n.val + 2) % 6, by omega⟩

def sheetReflection (n : HexIndex) : HexIndex :=
  ⟨(3 + 6 - n.val) % 6, by omega⟩

theorem colorRotation_cube (n : HexIndex) :
    colorRotation (colorRotation (colorRotation n)) = n := by
  fin_cases n <;> decide

theorem colorRotation_positive (a : HexColor) :
    colorRotation (positiveVertex a) = positiveVertex ⟨(a.val + 1) % 3, by omega⟩ := by
  fin_cases a <;> decide

theorem colorRotation_negative (a : HexColor) :
    colorRotation (negativeVertex a) = negativeVertex ⟨(a.val + 1) % 3, by omega⟩ := by
  fin_cases a <;> decide

theorem sheetReflection_involutive (n : HexIndex) :
    sheetReflection (sheetReflection n) = n := by
  fin_cases n <;> decide

theorem sheetReflection_positive (a : HexColor) :
    sheetReflection (positiveVertex a) =
      negativeVertex ⟨(3 - a.val) % 3, by omega⟩ := by
  fin_cases a <;> decide

theorem sheetReflection_negative (a : HexColor) :
    sheetReflection (negativeVertex a) =
      positiveVertex ⟨(3 - a.val) % 3, by omega⟩ := by
  fin_cases a <;> decide

theorem reflection_rotation_relation (n : HexIndex) :
    sheetReflection (colorRotation n) =
      colorRotation (colorRotation (sheetReflection n)) := by
  fin_cases n <;> decide

theorem sheetReflection_no_fixed (n : HexIndex) :
    sheetReflection n ≠ n := by
  fin_cases n <;> decide

theorem sheetReflection_orbits :
    sheetReflection 0 = 3 ∧
      sheetReflection 1 = 2 ∧
        sheetReflection 4 = 5 := by
  decide

end InfoGeometry.Canonical.HexagonalSixRootTiling
