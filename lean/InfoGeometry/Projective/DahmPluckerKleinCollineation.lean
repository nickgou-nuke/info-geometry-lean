/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.KleinQuadric

/-!
# Plücker–Klein collineation law (after R. Dahm, `bfIS 03-2025`)

This module extends the owner `InfoGeometry.Projective.KleinQuadric`
(`Plucker6`, `kleinQ = p01 p23 - p02 p13 + p03 p12`, `Vec4.wedge`) with the
algebraic statements of Dahm's projective-line derivation that are genuinely
theorems about the carrier:

* **Klein senary coordinates over a noncommutative ring.**  For operator-valued
  coordinates `x₁, …, x₆ : B` in an arbitrary `[Ring B]`, the split substitution
  `p01 = x₁ + x₂, p23 = x₁ - x₂, …` gives the `SO(3,3)` form
  `(x₁² - x₂²) + (x₃² - x₄²) + (x₅² - x₆²)` **minus the commutator defect**
  `[x₁,x₂] + [x₃,x₄] + [x₅,x₆]`; with a central unit `I`, `I² = -1`, the elliptic
  substitution gives the `SO(6)` sum of six squares minus `I` times the same
  defect.  The classical forms are the commutative specialisation.
* **Compound (second exterior power) action.**  A `4 × 4` matrix `A` acts on
  Plücker coordinates by its `2 × 2` minors (`compound A`).  It is natural for
  the wedge (`wedge (A u) (A v) = compound A (wedge u v)`) and scales the Klein
  form by the Mathlib determinant: `kleinQ (compound A P) = A.det * kleinQ P`
  for **every** bivector `P`, decomposable or not.
* **Lorentz boost as a collineation.**  Dahm's induced boost on `P⁵` (Eq. 4) is
  `compound (boost γ β)`, and `det (boost γ β) = γ² - (γβ)²`, so Lorentz invariance
  of the Klein quadric is the determinant law at `det = 1`.  The line-spacetime
  form `p13² + p01² + p23² - p03²` is invariant under the same boost.
* **Pauli line matrix.**  `det [[-Z, X+iY], [X-iY, Z]] = -(X² + Y² + Z²)`.
* **Polar/null-system split.**  Over any `[Ring B]`, `A + Aᵀ` is symmetric,
  `A - Aᵀ` is skew, and they sum to `A + A`.

## Scope

Proved: the identities above, at the stated generality.  Not formalised here
(interpretive claims of the source, left open): the Coleman–Mandula discussion,
the `g = 2` force-pair argument, the `PG(3,2)` Fano-space reading of `su(4)`,
the real-form classification `so(6) ≅ su(4)`, `so(3,3) ≅ sl(4,ℝ)`, and the
`15 = 5 ⊕ 10` Cartan decomposition as Lie-algebra isomorphisms.
-/

namespace InfoGeometry.Projective.DahmPluckerKleinCollineation

open InfoGeometry.Projective.KleinQuadric
open Matrix

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem dahmPluckerKlein_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-! ## 1. Klein senary coordinates over a noncommutative ring -/

section Senary

variable {B : Type*} [Ring B]

/-- Split (`I² = +1`) Klein substitution, oriented for the owner convention
`p31 = -p13`. -/
def splitKleinMap (x₁ x₂ x₃ x₄ x₅ x₆ : B) : Plucker6 B where
  p01 := x₁ + x₂
  p23 := x₁ - x₂
  p02 := x₃ + x₄
  p13 := -(x₃ - x₄)
  p03 := x₅ + x₆
  p12 := x₅ - x₆

/-- Elliptic (`I² = -1`) Klein substitution with an explicit unit `I : B`. -/
def ellipticKleinMap (I x₁ x₂ x₃ x₄ x₅ x₆ : B) : Plucker6 B where
  p01 := x₁ + I * x₂
  p23 := x₁ - I * x₂
  p02 := x₃ + I * x₄
  p13 := -(x₃ - I * x₄)
  p03 := x₅ + I * x₆
  p12 := x₅ - I * x₆

/-- Commutator defect of the three Klein coordinate pairs. -/
def senaryDefect (x₁ x₂ x₃ x₄ x₅ x₆ : B) : B :=
  (x₁ * x₂ - x₂ * x₁) + (x₃ * x₄ - x₄ * x₃) + (x₅ * x₆ - x₆ * x₅)

/-- **Split Klein form over `[Ring B]`.**  The Klein quadric of the split
substitution is the `SO(3,3)` form minus the commutator defect. -/
theorem kleinQ_splitKleinMap (x₁ x₂ x₃ x₄ x₅ x₆ : B) :
    Plucker6.kleinQ (splitKleinMap x₁ x₂ x₃ x₄ x₅ x₆) =
      (x₁ * x₁ - x₂ * x₂) + (x₃ * x₃ - x₄ * x₄) + (x₅ * x₅ - x₆ * x₆) -
        senaryDefect x₁ x₂ x₃ x₄ x₅ x₆ := by
  simp only [Plucker6.kleinQ, splitKleinMap, senaryDefect]
  noncomm_ring

/-- One elliptic factor `(a + I b)(a - I b)` for a central `I` with `I² = -1`. -/
theorem elliptic_pair (I a b : B) (hI : ∀ c : B, I * c = c * I) (hII : I * I = -1) :
    (a + I * b) * (a - I * b) = a * a + b * b - I * (a * b - b * a) := by
  have h1 : a * (I * b) = I * (a * b) := by
    rw [← mul_assoc, ← hI a, mul_assoc]
  have h2 : I * b * (I * b) = -(b * b) := by
    calc I * b * (I * b) = I * (b * I) * b := by noncomm_ring
      _ = I * (I * b) * b := by rw [← hI b]
      _ = (I * I) * (b * b) := by noncomm_ring
      _ = -(b * b) := by rw [hII]; noncomm_ring
  calc (a + I * b) * (a - I * b)
      = a * a - a * (I * b) + I * b * a - I * b * (I * b) := by noncomm_ring
    _ = a * a - I * (a * b) + I * b * a - -(b * b) := by rw [h1, h2]
    _ = a * a + b * b - I * (a * b - b * a) := by noncomm_ring

/-- **Elliptic Klein form over `[Ring B]`.**  With a central `I`, `I² = -1`, the
Klein quadric of the elliptic substitution is the `SO(6)` sum of six squares
minus `I` times the commutator defect. -/
theorem kleinQ_ellipticKleinMap (I x₁ x₂ x₃ x₄ x₅ x₆ : B)
    (hI : ∀ c : B, I * c = c * I) (hII : I * I = -1) :
    Plucker6.kleinQ (ellipticKleinMap I x₁ x₂ x₃ x₄ x₅ x₆) =
      x₁ * x₁ + x₂ * x₂ + x₃ * x₃ + x₄ * x₄ + x₅ * x₅ + x₆ * x₆ -
        I * senaryDefect x₁ x₂ x₃ x₄ x₅ x₆ := by
  have e1 := elliptic_pair I x₁ x₂ hI hII
  have e2 := elliptic_pair I x₃ x₄ hI hII
  have e3 := elliptic_pair I x₅ x₆ hI hII
  have hneg : -((x₃ + I * x₄) * -(x₃ - I * x₄)) = (x₃ + I * x₄) * (x₃ - I * x₄) := by
    noncomm_ring
  simp only [Plucker6.kleinQ, ellipticKleinMap, senaryDefect]
  rw [sub_eq_add_neg ((x₁ + I * x₂) * (x₁ - I * x₂)), hneg, e1, e2, e3]
  noncomm_ring

end Senary

section SenaryComm

variable {R : Type*} [CommRing R]

/-- In a commutative ring the defect vanishes. -/
theorem senaryDefect_eq_zero (x₁ x₂ x₃ x₄ x₅ x₆ : R) :
    senaryDefect x₁ x₂ x₃ x₄ x₅ x₆ = 0 := by
  simp only [senaryDefect]; ring

/-- Classical `SO(3,3)` reading of the split Klein substitution. -/
theorem kleinQ_splitKleinMap_comm (x₁ x₂ x₃ x₄ x₅ x₆ : R) :
    Plucker6.kleinQ (splitKleinMap x₁ x₂ x₃ x₄ x₅ x₆) =
      (x₁ * x₁ - x₂ * x₂) + (x₃ * x₃ - x₄ * x₄) + (x₅ * x₅ - x₆ * x₆) := by
  rw [kleinQ_splitKleinMap, senaryDefect_eq_zero, sub_zero]

/-- Classical `SO(6)` reading of the elliptic Klein substitution
(e.g. `R = ℂ`, `I = Complex.I`). -/
theorem kleinQ_ellipticKleinMap_comm (I x₁ x₂ x₃ x₄ x₅ x₆ : R) (hII : I * I = -1) :
    Plucker6.kleinQ (ellipticKleinMap I x₁ x₂ x₃ x₄ x₅ x₆) =
      x₁ * x₁ + x₂ * x₂ + x₃ * x₃ + x₄ * x₄ + x₅ * x₅ + x₆ * x₆ := by
  rw [kleinQ_ellipticKleinMap I x₁ x₂ x₃ x₄ x₅ x₆ (fun c => mul_comm I c) hII,
    senaryDefect_eq_zero, mul_zero, sub_zero]

end SenaryComm

/-! ## 2. Compound action of a `4 × 4` matrix on Plücker coordinates -/

section Compound

variable {R : Type*} [CommRing R]

/-- Column action of a `4 × 4` matrix on `Vec4`. -/
def act (A : Matrix (Fin 4) (Fin 4) R) (u : Vec4 R) : Vec4 R where
  x0 := A 0 0 * u.x0 + A 0 1 * u.x1 + A 0 2 * u.x2 + A 0 3 * u.x3
  x1 := A 1 0 * u.x0 + A 1 1 * u.x1 + A 1 2 * u.x2 + A 1 3 * u.x3
  x2 := A 2 0 * u.x0 + A 2 1 * u.x1 + A 2 2 * u.x2 + A 2 3 * u.x3
  x3 := A 3 0 * u.x0 + A 3 1 * u.x1 + A 3 2 * u.x2 + A 3 3 * u.x3

/-- The `2 × 2` minor of `A` on rows `i, j` and columns `k, l`. -/
def minor2 (A : Matrix (Fin 4) (Fin 4) R) (i j k l : Fin 4) : R :=
  A i k * A j l - A i l * A j k

/-- Row `(i, j)` of the compound matrix applied to a Plücker vector. -/
def compoundRow (A : Matrix (Fin 4) (Fin 4) R) (i j : Fin 4) (P : Plucker6 R) : R :=
  minor2 A i j 0 1 * P.p01 + minor2 A i j 0 2 * P.p02 + minor2 A i j 0 3 * P.p03 +
    minor2 A i j 1 2 * P.p12 + minor2 A i j 1 3 * P.p13 + minor2 A i j 2 3 * P.p23

/-- The compound (second exterior power) action `Λ²A` on Plücker coordinates. -/
def compound (A : Matrix (Fin 4) (Fin 4) R) (P : Plucker6 R) : Plucker6 R where
  p01 := compoundRow A 0 1 P
  p02 := compoundRow A 0 2 P
  p03 := compoundRow A 0 3 P
  p12 := compoundRow A 1 2 P
  p13 := compoundRow A 1 3 P
  p23 := compoundRow A 2 3 P

/-- **Naturality.**  The line through `A u` and `A v` has Plücker coordinates
`compound A (wedge u v)`. -/
theorem wedge_act (A : Matrix (Fin 4) (Fin 4) R) (u v : Vec4 R) :
    Vec4.wedge (act A u) (act A v) = compound A (Vec4.wedge u v) := by
  rcases u with ⟨u0, u1, u2, u3⟩
  rcases v with ⟨v0, v1, v2, v3⟩
  ext <;> simp only [Vec4.wedge, act, compound, compoundRow, minor2] <;> ring

/-- Explicit Laplace expansion of the `4 × 4` determinant along the first row. -/
theorem det_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    A.det =
      A 0 0 * (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2)
              - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
              + A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))
      - A 0 1 * (A 1 0 * (A 2 2 * A 3 3 - A 2 3 * A 3 2)
              - A 1 2 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
              + A 1 3 * (A 2 0 * A 3 2 - A 2 2 * A 3 0))
      + A 0 2 * (A 1 0 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
              - A 1 1 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
              + A 1 3 * (A 2 0 * A 3 1 - A 2 1 * A 3 0))
      - A 0 3 * (A 1 0 * (A 2 1 * A 3 2 - A 2 2 * A 3 1)
              - A 1 1 * (A 2 0 * A 3 2 - A 2 2 * A 3 0)
              + A 1 2 * (A 2 0 * A 3 1 - A 2 1 * A 3 0)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc, Fin.succ]
  simp [Fin.lt_def]
  ring

/-- **Plücker–Klein collineation law** (Dahm, Eq. 5–6).  For every `4 × 4`
matrix `A` and every Plücker vector `P` (not only decomposable ones), the
compound action scales the Klein form by `det A`. -/
theorem kleinQ_compound (A : Matrix (Fin 4) (Fin 4) R) (P : Plucker6 R) :
    Plucker6.kleinQ (compound A P) = A.det * Plucker6.kleinQ P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rw [det_fin_four]
  simp only [Plucker6.kleinQ, compound, compoundRow, minor2]
  ring

/-- Collineations with `det A = 1` preserve the Klein form exactly. -/
theorem kleinQ_compound_of_det_eq_one (A : Matrix (Fin 4) (Fin 4) R) (hA : A.det = 1)
    (P : Plucker6 R) :
    Plucker6.kleinQ (compound A P) = Plucker6.kleinQ P := by
  rw [kleinQ_compound, hA, one_mul]

/-- Collineations map the Klein quadric (the line cone) into itself. -/
theorem isKlein_compound (A : Matrix (Fin 4) (Fin 4) R) {P : Plucker6 R}
    (hP : Plucker6.IsKlein P) : Plucker6.IsKlein (compound A P) := by
  unfold Plucker6.IsKlein at *
  rw [kleinQ_compound, hP, mul_zero]

end Compound

/-! ## 3. Lorentz boost as a collineation (Dahm, Eq. 4 and Sec. III.B) -/

section Boost

variable {R : Type*} [CommRing R]

/-- Boost in the `(x₀, x₁)` plane of `P³`. -/
def boost (γ β : R) : Matrix (Fin 4) (Fin 4) R :=
  !![γ, -(γ * β), 0, 0;
     -(γ * β), γ, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

theorem det_boost (γ β : R) : (boost γ β).det = γ * γ * (1 - β * β) := by
  rw [det_fin_four]
  simp [boost]
  ring

/-- The induced action on `P⁵` is Dahm's Eq. 4: `p23` is fixed, `p01` is scaled by
`det = γ²(1 - β²)`, and `(p02, p12)`, `(p03, p13)` are boosted doublets. -/
theorem compound_boost (γ β : R) (P : Plucker6 R) :
    compound (boost γ β) P =
      { p01 := γ * γ * (1 - β * β) * P.p01
        p02 := γ * P.p02 - γ * β * P.p12
        p03 := γ * P.p03 - γ * β * P.p13
        p12 := γ * P.p12 - γ * β * P.p02
        p13 := γ * P.p13 - γ * β * P.p03
        p23 := P.p23 } := by
  ext <;> simp [compound, compoundRow, minor2, boost] <;> ring

/-- **Lorentz invariance of the Klein quadric** as the collineation law at
`det (boost γ β) = 1`. -/
theorem kleinQ_compound_boost (γ β : R) (h : γ * γ * (1 - β * β) = 1) (P : Plucker6 R) :
    Plucker6.kleinQ (compound (boost γ β) P) = Plucker6.kleinQ P :=
  kleinQ_compound_of_det_eq_one _ (by rw [det_boost, h]) P

/-- Dahm's line-spacetime form `p13² + p01² + p23² - p03²` (Sec. III.B). -/
def lineSpacetime (P : Plucker6 R) : R :=
  P.p13 * P.p13 + P.p01 * P.p01 + P.p23 * P.p23 - P.p03 * P.p03

/-- **Lorentz invariance of the line-spacetime form** under the induced boost. -/
theorem lineSpacetime_compound_boost (γ β : R) (h : γ * γ * (1 - β * β) = 1)
    (P : Plucker6 R) :
    lineSpacetime (compound (boost γ β) P) = lineSpacetime P := by
  rw [compound_boost]
  simp only [lineSpacetime]
  have hp01 : γ * γ * (1 - β * β) * P.p01 = P.p01 := by rw [h, one_mul]
  rw [hp01]
  linear_combination (P.p13 * P.p13 - P.p03 * P.p03) * h

/-- `Y ∼ (p01 + p23)/√2`, `Z ∼ (p01 - p23)/√2`: `2(Y² + Z²) = 2(p01² + p23²)`. -/
theorem transverse_pair_sum (p01 p23 : R) :
    (p01 + p23) * (p01 + p23) + (p01 - p23) * (p01 - p23) =
      2 * (p01 * p01 + p23 * p23) := by
  ring

end Boost

/-! ## 4. Pauli line matrix (Dahm, Eq. 3) -/

/-- Plücker's fifth coordinate `η = rσ - sρ` for the Pauli line matrix. -/
theorem det_pauliLineMatrix (X Y Z : ℝ) :
    Matrix.det !![(-(Z : ℂ)), (X : ℂ) + (Y : ℂ) * Complex.I;
                  (X : ℂ) - (Y : ℂ) * Complex.I, (Z : ℂ)] =
      -((X : ℂ) ^ 2 + (Y : ℂ) ^ 2 + (Z : ℂ) ^ 2) := by
  rw [Matrix.det_fin_two_of]
  linear_combination (Y : ℂ) ^ 2 * Complex.I_sq

/-! ## 5. Polar / null-system split over a noncommutative ring (Dahm, Sec. II.B) -/

section PolarNull

variable {B : Type*} [Ring B] {n : Type*}

/-- The polar part `A + Aᵀ` is symmetric over any `[Ring B]`. -/
theorem polarPart_symm (A : Matrix n n B) : (A + Aᵀ)ᵀ = A + Aᵀ := by
  rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

/-- The null-system part `A - Aᵀ` is skew over any `[Ring B]`. -/
theorem nullPart_skew (A : Matrix n n B) : (A - Aᵀ)ᵀ = -(A - Aᵀ) := by
  rw [Matrix.transpose_sub, Matrix.transpose_transpose, neg_sub]

/-- Polar and null parts recombine to `A + A`. -/
theorem polar_add_null (A : Matrix n n B) : (A + Aᵀ) + (A - Aᵀ) = A + A := by
  abel

end PolarNull

end InfoGeometry.Projective.DahmPluckerKleinCollineation
