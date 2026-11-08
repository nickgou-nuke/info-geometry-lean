import Mathlib.Data.Fintype.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionKleinFourTriality
import Mathlib.GroupTheory.Perm.Sign
import InfoGeometry.Geometry.KleinFourTag

namespace InfoGeometry.Canonical

/-!
## Grade automorphisms as permutations

We identify the three non‑zero grades of the Klein four group
`(1,0)`, `(0,1)`, `(1,1)` with the elements of `Fin 3` (via a small inductive
type `NonZeroGrade`).  Any additive equivalence `KleinFour ≃+ KleinFour`
induces a permutation of these three grades, giving a concrete `S₃`
action on the grading sector.
-/

-- The Klein‑four group used throughout the file

/-- The three non‑zero grades of `KleinFour`. -/
inductive NonZeroGrade
  | g₁ : NonZeroGrade   -- corresponds to (1,0)
  | g₂ : NonZeroGrade   -- corresponds to (0,1)
  | g₃ : NonZeroGrade   -- corresponds to (1,1)
  deriving Repr, DecidableEq, Inhabited

instance : Fintype NonZeroGrade where
  elems := {NonZeroGrade.g₁, NonZeroGrade.g₂, NonZeroGrade.g₃}
  complete := by intro x; cases x <;> decide

/-- Convert a `NonZeroGrade` to the corresponding `KleinFour` element. -/
@[simp]
def nonZeroGradeToKleinFour : NonZeroGrade → KleinFour
  | NonZeroGrade.g₁ => (1, 0)
  | NonZeroGrade.g₂ => (0, 1)
  | NonZeroGrade.g₃ => (1, 1)

/-- Convert a `KleinFour` element (assumed non‑zero) back to a `NonZeroGrade`. -/
noncomputable def kleinFourToNonZeroGrade! (g : KleinFour) : NonZeroGrade := by
  classical
  by_cases h₁ : g = (1, 0)
  · exact NonZeroGrade.g₁
  · by_cases h₂ : g = (0, 1)
    · exact NonZeroGrade.g₂
    · by_cases h₃ : g = (1, 1)
      · exact NonZeroGrade.g₃
      · exact NonZeroGrade.g₁

lemma nonZeroGrade_inv (x : KleinFour) (h : x ≠ (0,0)) :
    nonZeroGradeToKleinFour (kleinFourToNonZeroGrade! x) = x := by
  rcases x with ⟨a, b⟩
  fin_cases a <;> fin_cases b
  · exact False.elim (h rfl)
  · decide
  · decide
  · decide

lemma kleinFourToNonZeroGrade!_inv (g : NonZeroGrade) :
    kleinFourToNonZeroGrade! (nonZeroGradeToKleinFour g) = g := by
  cases g <;> simp [kleinFourToNonZeroGrade!, nonZeroGradeToKleinFour]

/-- Turn an additive equivalence of `KleinFour` into a permutation of the three
non‑zero grades. This yields the concrete `S₃`‑action we need. -/
noncomputable def gradeAutomorphismPerm (e : KleinFour ≃+ KleinFour) : Equiv.Perm NonZeroGrade :=
  { toFun := fun g => kleinFourToNonZeroGrade! (e (nonZeroGradeToKleinFour g))
    invFun := fun g => kleinFourToNonZeroGrade! (e.symm (nonZeroGradeToKleinFour g))
    left_inv := by
      intro g
      have hz : e (nonZeroGradeToKleinFour g) ≠ (0,0) := by
        intro h
        have h2 := congrArg e.symm h
        rw [AddEquiv.symm_apply_apply] at h2
        have h3 : e.symm (0,0) = (0,0) := map_zero e.symm
        rw [h3] at h2
        revert h2; cases g <;> decide
      have hinv := nonZeroGrade_inv (e (nonZeroGradeToKleinFour g)) hz
      change kleinFourToNonZeroGrade! (e.symm (nonZeroGradeToKleinFour (kleinFourToNonZeroGrade! (e (nonZeroGradeToKleinFour g))))) = g
      rw [hinv, AddEquiv.symm_apply_apply, kleinFourToNonZeroGrade!_inv]
    right_inv := by
      intro g
      have hz : e.symm (nonZeroGradeToKleinFour g) ≠ (0,0) := by
        intro h
        have h2 := congrArg e h
        rw [AddEquiv.apply_symm_apply] at h2
        have h3 : e (0,0) = (0,0) := map_zero e
        rw [h3] at h2
        revert h2; cases g <;> decide
      have hinv := nonZeroGrade_inv (e.symm (nonZeroGradeToKleinFour g)) hz
      change kleinFourToNonZeroGrade! (e (nonZeroGradeToKleinFour (kleinFourToNonZeroGrade! (e.symm (nonZeroGradeToKleinFour g))))) = g
      rw [hinv, AddEquiv.apply_symm_apply, kleinFourToNonZeroGrade!_inv] }

/-- The `swapGrade` additive equivalence defined in `SplitOctonionKleinFourTriality`
    swaps the two `ZMod 2` components. -/
@[simp]
def swapGradeAddEquiv : KleinFour ≃+ KleinFour :=
  { toFun := fun g => (g.2, g.1)
    invFun := fun g => (g.2, g.1)
    left_inv := by intro g; cases g; rfl
    right_inv := by intro g; cases g; rfl
    map_add' := by intro g h; cases g; cases h; rfl }

/-- The cyclic rotation `rotGrade` sends `(1,0) → (0,1) → (1,1) → (1,0)`. -/
@[simp]
def rotGradeAddEquiv : KleinFour ≃+ KleinFour :=
  { toFun := fun g =>
      match g with
      | (1, 0) => (0, 1)
      | (0, 1) => (1, 1)
      | (1, 1) => (1, 0)
      | (0, 0) => (0, 0)
    invFun := fun g =>
      match g with
      | (1, 0) => (1, 1)
      | (0, 1) => (1, 0)
      | (1, 1) => (0, 1)
      | (0, 0) => (0, 0)
    left_inv := by decide
    right_inv := by decide
    map_add' := by decide }

@[simp]
lemma gradeAutomorphismPerm_swap :
    gradeAutomorphismPerm (swapGradeAddEquiv) =
      (Equiv.swap NonZeroGrade.g₁ NonZeroGrade.g₂) := by
  ext g
  cases g <;>
    simp [gradeAutomorphismPerm, swapGradeAddEquiv, nonZeroGradeToKleinFour,
      kleinFourToNonZeroGrade!, Equiv.swap_apply_def]

def rotPerm : Equiv.Perm NonZeroGrade :=
  { toFun := fun g => match g with | .g₁ => .g₂ | .g₂ => .g₃ | .g₃ => .g₁
    invFun := fun g => match g with | .g₁ => .g₃ | .g₂ => .g₁ | .g₃ => .g₂
    left_inv := by intro g; cases g <;> rfl
    right_inv := by intro g; cases g <;> rfl }

@[simp]
lemma gradeAutomorphismPerm_rot :
    gradeAutomorphismPerm (rotGradeAddEquiv) = rotPerm := by
  ext g
  cases g <;>
    simp [gradeAutomorphismPerm, rotGradeAddEquiv, rotPerm,
      nonZeroGradeToKleinFour, kleinFourToNonZeroGrade!]

/-- The map `gradeAutomorphismPerm` is a group homomorphism from the additive
automorphism group of `KleinFour` to the symmetric group `S₃`. -/
noncomputable def gradeAutomorphismPermHom : AddAut KleinFour →+ Additive (Equiv.Perm NonZeroGrade) :=
  { toFun := fun e => Additive.ofMul (gradeAutomorphismPerm e)
    map_zero' := by
      ext g
      change kleinFourToNonZeroGrade! (nonZeroGradeToKleinFour g) = g
      exact kleinFourToNonZeroGrade!_inv g
    map_add' := by
      intro e₁ e₂
      ext g
      change kleinFourToNonZeroGrade! (e₁ (e₂ (nonZeroGradeToKleinFour g))) =
        kleinFourToNonZeroGrade! (e₁ (nonZeroGradeToKleinFour (kleinFourToNonZeroGrade! (e₂ (nonZeroGradeToKleinFour g)))))
      have hz : e₂ (nonZeroGradeToKleinFour g) ≠ (0,0) := by
        intro h
        have h2 := congrArg e₂.symm h
        rw [AddEquiv.symm_apply_apply] at h2
        have hz2 : e₂.symm (0,0) = (0,0) := map_zero e₂.symm
        rw [hz2] at h2
        cases g <;> revert h2 <;> decide
      generalize hx : e₂ (nonZeroGradeToKleinFour g) = x
      rw [hx] at hz
      have hinv := nonZeroGrade_inv x hz
      rw [hinv] }

end InfoGeometry.Canonical
