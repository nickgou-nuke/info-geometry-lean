import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Moduli.SimplexArnoldRational

/-! The open two-state simplex as a positive one-dimensional chamber.

This is an explicit set-level equivalence only; no moduli-space or metric
identification is asserted here.
-/

namespace InfoGeometry.Moduli.PositiveSimplexChamber

def OpenSimplex : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 = 1}

def PositiveChamber : Set ℝ := {x | 0 < x ∧ x < 1}

def simplexToChamber : OpenSimplex → PositiveChamber :=
  fun p => ⟨p.1.1, p.2.1, by linarith [p.2.2]⟩

def chamberToSimplex : PositiveChamber → OpenSimplex :=
  fun x => ⟨(x.1, 1 - x.1), by
    constructor
    · exact x.2.1
    constructor
    · exact sub_pos.mpr x.2.2
    · ring⟩

theorem chamberToSimplex_simplexToChamber (p : OpenSimplex) :
    chamberToSimplex (simplexToChamber p) = p := by
  apply Subtype.ext
  rcases p with ⟨⟨a, b⟩, ha, hb, hab⟩
  simp only [chamberToSimplex, simplexToChamber]
  congr
  linarith

theorem simplexToChamber_chamberToSimplex (x : PositiveChamber) :
    simplexToChamber (chamberToSimplex x) = x := by
  apply Subtype.ext
  rfl

def simplexChamberEquiv : OpenSimplex ≃ PositiveChamber where
  toFun := simplexToChamber
  invFun := chamberToSimplex
  left_inv := chamberToSimplex_simplexToChamber
  right_inv := simplexToChamber_chamberToSimplex

theorem chamber_odds_identity (x : PositiveChamber) :
    1 / (x : ℝ) + 1 / (1 - (x : ℝ)) =
      1 / ((x : ℝ) * (1 - (x : ℝ))) := by
  exact InfoGeometry.Moduli.SimplexArnoldRational.odds_identity
    (x : ℝ) (ne_of_gt x.2.1) (ne_of_gt (sub_pos.mpr x.2.2))

end InfoGeometry.Moduli.PositiveSimplexChamber
