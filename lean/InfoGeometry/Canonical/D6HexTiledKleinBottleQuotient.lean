import InfoGeometry.Canonical.D6ReciprocalLatticeBrillouinZone
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# A finite six-mode Klein quotient

The carrier is a finite rectangular reciprocal torus `ZMod 4 × ZMod 3`.
The glide adds one horizontal reciprocal step and reflects the vertical
coordinate.  Its square is a nontrivial horizontal translation and its fourth
power is the identity.  The quotient is the genuine Lean quotient by the
resulting finite orbit relation.  This is a six-mode/Klein prototype, not yet
the full hexagonal lattice quotient: a later owner must supply the hexagonal
reciprocal lattice and prove which `D6` subgroup descends to this quotient.
-/

namespace InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient

abbrev TorusCell := ZMod 4 × ZMod 3

instance torusCellDecidableEq : DecidableEq TorusCell := inferInstance

def glide (p : TorusCell) : TorusCell := (p.1 + 1, -p.2)

def glide2 (p : TorusCell) : TorusCell := glide (glide p)

def glide3 (p : TorusCell) : TorusCell := glide (glide2 p)

def kleinOrbitRel (p q : TorusCell) : Prop :=
  q = p ∨ q = glide p ∨ q = glide2 p ∨ q = glide3 p

theorem glide_square (p : TorusCell) :
    glide2 p = (p.1 + 2, p.2) := by
  rcases p with ⟨x, y⟩
  change (x + 1 + 1, -(-y)) = (x + 2, y)
  apply Prod.ext
  · ring
  · simp

theorem glide_fourth (p : TorusCell) :
    glide (glide3 p) = p := by
  rcases p with ⟨x, y⟩
  change (x + 1 + 1 + 1 + 1, -(-(-(-y)))) = (x, y)
  apply Prod.ext
  · have hfour : (4 : ZMod 4) = 0 := by decide
    calc
      x + 1 + 1 + 1 + 1 = x + 4 := by ring
      _ = x := by rw [hfour, add_zero]
  · simp

theorem glide3_glide (p : TorusCell) :
    glide3 (glide p) = p := by
  change glide (glide (glide (glide p))) = p
  exact glide_fourth p

theorem glide2_glide2 (p : TorusCell) :
    glide2 (glide2 p) = p := by
  change glide (glide (glide (glide p))) = p
  exact glide_fourth p

theorem glide2_glide3 (p : TorusCell) :
    glide2 (glide3 p) = glide p := by
  simpa [glide2, glide3] using glide_fourth (glide p)

theorem glide3_glide2 (p : TorusCell) :
    glide3 (glide2 p) = glide p := by
  simpa [glide2, glide3] using glide_fourth (glide p)

theorem glide3_glide3 (p : TorusCell) :
    glide3 (glide3 p) = glide2 p := by
  simpa [glide2, glide3] using glide_fourth (glide2 p)

@[simp] theorem glide_glide (p : TorusCell) :
    glide (glide p) = glide2 p := rfl

@[simp] theorem glide_glide2 (p : TorusCell) :
    glide (glide2 p) = glide3 p := rfl

@[simp] theorem glide_glide3 (p : TorusCell) :
    glide (glide3 p) = p := glide_fourth p

@[simp] theorem glide2_glide (p : TorusCell) :
    glide2 (glide p) = glide3 p := by
  rfl

attribute [simp] glide3_glide glide2_glide2 glide2_glide3 glide3_glide2 glide3_glide3

theorem kleinOrbitRel_refl (p : TorusCell) : kleinOrbitRel p p := by
  exact Or.inl rfl

theorem kleinOrbitRel_symm {p q : TorusCell} :
    kleinOrbitRel p q → kleinOrbitRel q p := by
  intro h
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · subst q
    exact Or.inr (Or.inr (Or.inr (glide3_glide p).symm))
  · subst q
    exact Or.inr (Or.inr (Or.inl (glide2_glide2 p).symm))
  · subst q
    exact Or.inr (Or.inl (glide_fourth p).symm)

theorem kleinOrbitRel_trans {p q r : TorusCell} :
    kleinOrbitRel p q → kleinOrbitRel q r → kleinOrbitRel p r := by
  intro hpq hqr
  rcases hpq with rfl | rfl | rfl | rfl <;>
    rcases hqr with rfl | rfl | rfl | rfl <;>
      simp [kleinOrbitRel]

instance kleinOrbitSetoid : Setoid TorusCell where
  r := kleinOrbitRel
  iseqv :=
    { refl := kleinOrbitRel_refl
      symm := kleinOrbitRel_symm
      trans := kleinOrbitRel_trans }

abbrev KleinHexQuotient := Quotient kleinOrbitSetoid

def quotientMap (p : TorusCell) : KleinHexQuotient := Quotient.mk' p

theorem quotientMap_glide (p : TorusCell) :
    quotientMap (glide p) = quotientMap p := by
  apply Quotient.sound
  exact kleinOrbitRel_symm (Or.inr (Or.inl rfl))

theorem quotientMap_glide2 (p : TorusCell) :
    quotientMap (glide2 p) = quotientMap p := by
  apply Quotient.sound
  exact kleinOrbitRel_symm (Or.inr (Or.inr (Or.inl rfl)))

theorem quotientMap_glide3 (p : TorusCell) :
    quotientMap (glide3 p) = quotientMap p := by
  apply Quotient.sound
  exact kleinOrbitRel_symm (Or.inr (Or.inr (Or.inr rfl)))

theorem quotientMap_fourth_glide (p : TorusCell) :
    quotientMap (glide (glide3 p)) = quotientMap p := by
  rw [glide_fourth]

end InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient
