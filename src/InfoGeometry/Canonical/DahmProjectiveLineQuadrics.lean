/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Projective.KleinQuadricPlucker

/-!
# Coordinate identities for projective line geometry

This file reuses the canonical `Plucker6` and `kleinQ` owner.  It proves two
algebraic consequences of the supplied senary-coordinate and boost formulas:

* a split-unit parameter `I` with `I² = ε` turns the Klein quadric into the
  three-pair form `Σ (x² - ε y²)`;
* the stated Lorentz boost preserves the Klein quadratic form and the displayed
  four-coordinate quadratic expression when `γ²(1-β²)=1`.

These coordinate results do not construct real Lie groups, identify their real
forms, prove a Coleman--Mandula theorem, or derive a physical gyromagnetic
factor.  The noncommutative waist-bracket result remains in the separate
Peirce/Plücker owner and is not identified with this scalar coordinate model.

#### BUCKET 1: CLOSED FINITE THEOREMS
The senary-coordinate formulas and the stated boost identities are proved
over a commutative ring from the displayed coordinate definitions.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
The boost invariances assume `γ²(1-β²)=1`; the senary signature formulas
assume the grading unit satisfies `I²=ε`.

#### BUCKET 3: OPEN CLOSURE DEBT
The representation-theoretic group identifications, compound-minor action,
spin-factor derivation, and physical interpretations require separate
constructions and proofs.
-/

namespace InfoGeometry.Canonical.DahmProjectiveLineQuadrics

open InfoGeometry.Projective.KleinQuadricPlucker

variable {R : Type*} [CommRing R]

/-- Senary coordinates, with the orientation chosen to match `kleinQ`. -/
def senaryCoordinates (I x₁ x₂ x₃ x₄ x₅ x₆ : R) : Plucker6 R where
  p01 := x₁ + I * x₂
  p23 := x₁ - I * x₂
  p02 := x₃ + I * x₄
  p13 := -(x₃ - I * x₄)
  p03 := x₅ + I * x₆
  p12 := x₅ - I * x₆

/-- The Klein form in senary coordinates for a grading unit with square `ε`. -/
theorem kleinQ_senaryCoordinates
    (I ε x₁ x₂ x₃ x₄ x₅ x₆ : R) (hI : I * I = ε) :
    Plucker6.kleinQ (senaryCoordinates I x₁ x₂ x₃ x₄ x₅ x₆) =
      (x₁ * x₁ - ε * (x₂ * x₂)) +
      (x₃ * x₃ - ε * (x₄ * x₄)) +
      (x₅ * x₅ - ε * (x₆ * x₆)) := by
  rw [show Plucker6.kleinQ (senaryCoordinates I x₁ x₂ x₃ x₄ x₅ x₆) =
      (x₁ + I * x₂) * (x₁ - I * x₂) +
        (x₃ + I * x₄) * (x₃ - I * x₄) +
        (x₅ + I * x₆) * (x₅ - I * x₆) by
        simp [senaryCoordinates, Plucker6.kleinQ]; ring]
  have pair (a b : R) : (a + I * b) * (a - I * b) = a * a - ε * (b * b) := by
    calc
      (a + I * b) * (a - I * b) = a * a - (I * I) * (b * b) := by ring
      _ = a * a - ε * (b * b) := by rw [hI]
  rw [pair, pair, pair]

/-- The compact-sign specialization (`ε = -1`) is a sum of six squares. -/
theorem kleinQ_senary_compact
    (I x₁ x₂ x₃ x₄ x₅ x₆ : R) (hI : I * I = -1) :
    Plucker6.kleinQ (senaryCoordinates I x₁ x₂ x₃ x₄ x₅ x₆) =
      x₁ * x₁ + x₂ * x₂ + x₃ * x₃ + x₄ * x₄ + x₅ * x₅ + x₆ * x₆ := by
  rw [kleinQ_senaryCoordinates I (-1) x₁ x₂ x₃ x₄ x₅ x₆ hI]
  ring

/-- The split-sign specialization (`ε = 1`) is a sum of three signed pairs. -/
theorem kleinQ_senary_split
    (I x₁ x₂ x₃ x₄ x₅ x₆ : R) (hI : I * I = 1) :
    Plucker6.kleinQ (senaryCoordinates I x₁ x₂ x₃ x₄ x₅ x₆) =
      (x₁ * x₁ - x₂ * x₂) +
      (x₃ * x₃ - x₄ * x₄) +
      (x₅ * x₅ - x₆ * x₆) := by
  rw [kleinQ_senaryCoordinates I 1 x₁ x₂ x₃ x₄ x₅ x₆ hI]
  ring

/-- The boost convention stated in the paper, acting on the canonical six-vector. -/
def lorentzBoost (γ β : R) (p : Plucker6 R) : Plucker6 R where
  p01 := p.p01
  p02 := γ * p.p02 - γ * β * p.p12
  p03 := γ * p.p03 - γ * β * p.p13
  p12 := γ * p.p12 - γ * β * p.p02
  p13 := γ * p.p13 - γ * β * p.p03
  p23 := p.p23

/-- The displayed boost preserves the Klein quadratic form under its unit condition. -/
theorem kleinQ_lorentzBoost
    (γ β : R) (p : Plucker6 R)
    (hγ : γ * γ * (1 - β * β) = 1) :
    Plucker6.kleinQ (lorentzBoost γ β p) = Plucker6.kleinQ p := by
  unfold Plucker6.kleinQ lorentzBoost
  calc
    p.p01 * p.p23 -
        (γ * p.p02 - γ * β * p.p12) * (γ * p.p13 - γ * β * p.p03) +
        (γ * p.p03 - γ * β * p.p13) * (γ * p.p12 - γ * β * p.p02)
      = p.p01 * p.p23 +
          (γ * γ * (1 - β * β)) * (-p.p02 * p.p13 + p.p03 * p.p12) := by ring
    _ = p.p01 * p.p23 - p.p02 * p.p13 + p.p03 * p.p12 := by rw [hγ]; ring

/-- The four-coordinate quadratic expression is invariant under the same boost. -/
theorem lineSpacetimeForm_lorentzBoost
    (γ β : R) (p : Plucker6 R)
    (hγ : γ * γ * (1 - β * β) = 1) :
    let q (v : Plucker6 R) :=
      v.p13 * v.p13 + v.p01 * v.p01 + v.p23 * v.p23 - v.p03 * v.p03
    q (lorentzBoost γ β p) = q p := by
  dsimp
  calc
    (γ * p.p13 - γ * β * p.p03) * (γ * p.p13 - γ * β * p.p03) +
        p.p01 * p.p01 + p.p23 * p.p23 -
        (γ * p.p03 - γ * β * p.p13) * (γ * p.p03 - γ * β * p.p13)
      = p.p01 * p.p01 + p.p23 * p.p23 +
          (γ * γ * (1 - β * β)) * (p.p13 * p.p13 - p.p03 * p.p03) := by ring
    _ = p.p13 * p.p13 + p.p01 * p.p01 + p.p23 * p.p23 - p.p03 * p.p03 := by
      rw [hγ]
      ring

end InfoGeometry.Canonical.DahmProjectiveLineQuadrics
