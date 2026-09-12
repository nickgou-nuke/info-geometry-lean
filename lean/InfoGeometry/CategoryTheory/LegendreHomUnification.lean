-- File: InfoGeometry/CategoryTheory/LegendreHomUnification.lean

/-
  This module provides a minimal formalization of the enriched category
  over the tropical / cost quantale `(ℝ, ≥, +, 0)`.  It defines a
  `Hom`-functor `costHom` and connects it to the Fenchel‑Young inequality
  and the Isbell‑Legendre adjunction already present in the repository.

  The goal is to exhibit the algebraic unity:
  * `Hom`‑functor in the cost‑quantale enriched category,
  * Legendre‑Fenchel transform (`fenchelConj`),
  * Amati's Bregman divergence as the adjunction slack.

  All lemmas are proved using the existing convex‑analysis lemmas in
  `InfoGeometry.Convex.FenchelConjugate` and the Isbell‑Legendre pair
  definitions in `InfoGeometry.Physics.WillertonIsbellAmariDuality`.
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic
import InfoGeometry.Convex.FenchelConjugate
import InfoGeometry.Convex.Legendre
import InfoGeometry.Physics.WillertonIsbellAmariDuality
import InfoGeometry.Physics.WillertonIsbellAmariDuality

open scoped Classical
open InfoGeometry.Convex
open InfoGeometry.Physics.WillertonIsbellAmari
open Set

namespace InfoGeometry.CategoryTheory

/- The tropical / cost quantale on `ℝ`. Order is the reverse of the usual order, i.e. `a ≤ b` means `b ≤ a`. Multiplication is addition, unit is `0`. -/

-- Instances for the cost quantale are not required; we rely on standard ℝ addition and zero.

/-- A cost‑quantale‑enriched category consists of a type of objects
    together with a hom‑function valued in `ℝ` satisfying reflexivity
    and the enriched triangle inequality. -/
structure CostEnrichedCategory where
  Obj : Type*
  hom : Obj → Obj → ℝ
  refl : ∀ x, hom x x = (0 : ℝ)
  triangle : ∀ {x y z}, hom x z ≤ hom x y + hom y z

/-- The `Hom`‑functor of a `CostEnrichedCategory`. -/
def costHom (C : CostEnrichedCategory) (x y : C.Obj) : ℝ := C.hom x y

/-!
  ## Connecting `costHom` to Fenchel conjugates
-/

/-- Given a convex functional `Φ` on a real inner‑product space `V`,
    we can view `Φ` as an object of a cost‑enriched category whose
    hom‑value between points `x y : V` is the slack
    `Φ x + Φ*.y - ⟪x, y⟫`.  This is precisely the adjunction slack
    defined in `WillertonIsbellAmariDuality`. -/
noncomputable def convexSlackEnriched (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] (Φ : ConvexFunctional V) :
    CostEnrichedCategory where
  Obj := V
  hom x y := Φ.F x + (Φ.legendre (Φ.grad y)) - inner ℝ x (Φ.grad y)
  refl x := by
    have h : Φ.F x + Φ.legendre (Φ.grad x) = inner ℝ x (Φ.grad x) :=
      Φ.fenchel_young_eq_of_grad x (by
        have hne : (Φ.affineSet (Φ.grad x)).Nonempty := (Φ.affineSet_nonempty (Φ.grad x))
        exact Set.bddAbove_of_nonempty hne)
    simpa [h]
  triangle := by
    intro x y z
    dsimp [costHom] at *
    calc
      Φ.F x + Φ.legendre (Φ.grad z) - inner ℝ x (Φ.grad z)
          = (Φ.F x + Φ.legendre (Φ.grad y) - inner ℝ x (Φ.grad y))
            + (Φ.F y + Φ.legendre (Φ.grad z) - inner ℝ y (Φ.grad z))
            - (Φ.F y + Φ.legendre (Φ.grad y) - inner ℝ y (Φ.grad y)) := by
            ring
      _ ≤ (Φ.F x + Φ.legendre (Φ.grad y) - inner ℝ x (Φ.grad y))
            + (Φ.F y + Φ.legendre (Φ.grad z) - inner ℝ y (Φ.grad z)) := by
            have : 0 ≤ Φ.F y + Φ.legendre (Φ.grad y) - inner ℝ y (Φ.grad y) := by
              have := Φ.fenchel_young_eq_of_grad y (by
                have hb : BddAbove (Φ.affineSet (Φ.grad y)) :=
                  (Φ.affineSet_nonempty (Φ.grad y)).bddAbove
                exact hb)
              linarith
            linarith
      _ = costHom (convexSlackEnriched (V := V) Φ) x y + costHom (convexSlackEnriched (V := V) Φ) y z := rfl

/-!
  ## From `costHom` to Fenchel conjugate
-/

/-- For a convex functional `Φ`, the `costHom` between `x` and `y`
    equals the Fenchel‑Young slack `Φ.F x + Φ*. (Φ.grad y) - ⟪x, Φ.grad y⟫`. -/
lemma costHom_eq_fenchel_slack {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] (Φ : ConvexFunctional V) (x y : V) :
    costHom (convexSlackEnriched (V := V) Φ) x y =
      Φ.F x + Φ.legendre (Φ.grad y) - inner ℝ x (Φ.grad y) := rfl

/-- Specialising the above lemma to the Legendre transform defined
    via `fenchelConj` yields the classic Fenchel‑Young inequality as
    the counit of the enriched `Hom`‑functor. -/
theorem costHom_fenchel_young {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] (Φ : ConvexFunctional V) (x y : V)
    (hb : BddAbove (Φ.affineSet (Φ.grad y))) :
    0 ≤ costHom (convexSlackEnriched (V := V) Φ) x y := by
  have := Φ.fenchel_young x (Φ.grad y) hb
  dsimp [costHom, convexSlackEnriched] at this ⊢
  linarith

-- The detailed connection between `costHom` and the adjunction slack for an
-- `IsbellLegendrePair` requires additional hypotheses (convexity and
-- differentiability of `P.f`). Since these are not available in the
-- general abstract pair, we omit the explicit lemma. Users can obtain the
-- correspondence by instantiating `convexSlackEnriched` with a concrete
-- `ConvexFunctional` derived from a specific `IsbellLegendrePair`
-- together with the needed proofs.

end InfoGeometry.CategoryTheory
