/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Combinatorics.MHVTriplets

/-!
# Non-planar MHV on-shell diagrams: bracket identities, the octahedron, doublets

Polynomial and combinatorial content of Lisitsyn–Oktem–Sherman-Bennett–Trnka,
"Grassmannian geometries for non-planar on-shell diagrams" (arXiv:2512.25005),
layered on the existing triplet owner `InfoGeometry.Combinatorics.MHVTriplets`.

* Operator spinor brackets: particle `j` carries spinor components `x j, y j` in an arbitrary
  ring of operators subject to the row-Manin relations; the bracket is the column
  determinant.  `C⊥ · λ = 0` holds for both rows of a triplet, and the **symmetrised**
  Schouten relation holds (explicit free-algebra certificates).  The unsymmetrised Schouten
  relation is not a consequence of the Manin relations.
* Octahedron (black `B = {123,345,561,264}`, white `W = {126,234,456,135}`):
  `doublets B = doublets W` in the owner sense, and `B` is non-vanishing.
* Genus bound: non-vanishing applied to the whole `T` plus an Euler relation
  `V + 2m = 3m + 2 - 2g` forces `g = 0`.

## Scope

Not proved: Theorem 3 of the paper (`f_T = f_{T'} ↔ D(T) = D(T') ↔` sphere moves), the
operator (Manin column-determinant) form of the octahedral `4 × 4` minors and of `U(1)`
decoupling, oriented regions, pseudo-positivity, or null boundaries.  The Euler relation is a hypothesis; no
triangulation is constructed here.
-/

namespace InfoGeometry.Combinatorics.NonPlanarOnShellBrackets

open InfoGeometry.Combinatorics.MHVTriplets

section ManinBrackets

/-! ### Spinor brackets with operator entries (Manin relations)

`x j, y j` are the two spinor components of particle `j`, valued in an arbitrary ring of
operators.  The row-Manin relations are: the `x`'s commute pairwise (`rX = 0`), the `y`'s commute
pairwise (`rY = 0`), and `[x j, y l] = [x l, y j]` (`rXY = 0`).  The bracket is the column
determinant `cdet j l = x j * y l - x l * y j`.  The commutative Schouten relation does **not**
follow from these relations (checked in the free algebra); its symmetrisation does. -/

variable {A : Type*} [Ring A] (x y : Fin 4 → A)

/-- Column-determinant bracket `(j l) = x j y l - x l y j`. -/
def cdet (j l : Fin 4) : A := x j * y l - x l * y j

/-- Commutator of two `x`-components. -/
def rX (j l : Fin 4) : A := x j * x l - x l * x j

/-- Commutator of two `y`-components. -/
def rY (j l : Fin 4) : A := y j * y l - y l * y j

/-- Manin cross relation `[x j, y l] - [x l, y j]`. -/
def rXY (j l : Fin 4) : A := x j * y l - y l * x j - (x l * y j - y j * x l)

variable {x y}

/-- `C⊥ · λ = 0` for the `x`-row of the triplet `(012)`, using only `rX = 0`. -/
theorem triplet_row_orthogonal_x (hX : ∀ j l, rX x j l = 0) :
    x 0 * cdet x y 1 2 - x 1 * cdet x y 0 2 + x 2 * cdet x y 0 1 = 0 := by
  have h : x 0 * cdet x y 1 2 - x 1 * cdet x y 0 2 + x 2 * cdet x y 0 1 =
      rX x 0 1 * y 2 - rX x 0 2 * y 1 + rX x 1 2 * y 0 := by
    simp only [cdet, rX]; noncomm_ring
  rw [h, hX, hX, hX]; simp

/-- `C⊥ · λ = 0` for the `y`-row of the triplet `(012)`, using `rY = 0` and `rXY = 0`. -/
theorem triplet_row_orthogonal_y (hY : ∀ j l, rY y j l = 0) (hXY : ∀ j l, rXY x y j l = 0) :
    y 0 * cdet x y 1 2 - y 1 * cdet x y 0 2 + y 2 * cdet x y 0 1 = 0 := by
  have h : y 0 * cdet x y 1 2 - y 1 * cdet x y 0 2 + y 2 * cdet x y 0 1 =
      -(rY y 0 1 * x 2) + y 2 * rXY x y 0 1 + rY y 0 2 * x 1 - y 1 * rXY x y 0 2 -
        rY y 1 2 * x 0 + y 0 * rXY x y 1 2 := by
    simp only [cdet, rY, rXY]; noncomm_ring
  rw [h]; simp [hY, hXY]

/-- **Symmetrised Schouten relation** for operator spinors: with `S = (01)(23) - (02)(13) +
(03)(12)` and `S' = (23)(01) - (13)(02) + (12)(03)`, `S + S' = 0` follows from `rX = 0` and
`rXY = 0` alone (explicit 24-term certificate, computed in the free algebra). -/
theorem schouten_symmetrised (hX : ∀ j l, rX x j l = 0) (hXY : ∀ j l, rXY x y j l = 0) :
    (cdet x y 0 1 * cdet x y 2 3 - cdet x y 0 2 * cdet x y 1 3 + cdet x y 0 3 * cdet x y 1 2) +
      (cdet x y 2 3 * cdet x y 0 1 - cdet x y 1 3 * cdet x y 0 2 +
        cdet x y 1 2 * cdet x y 0 3) = 0 := by
  have h :
      (cdet x y 0 1 * cdet x y 2 3 - cdet x y 0 2 * cdet x y 1 3 + cdet x y 0 3 * cdet x y 1 2) +
        (cdet x y 2 3 * cdet x y 0 1 - cdet x y 1 3 * cdet x y 0 2 +
          cdet x y 1 2 * cdet x y 0 3) =
        - y 2 * rX x 0 1 * y 3
        + y 3 * rX x 0 1 * y 2
        + rXY x y 0 1 * x 2 * y 3
        - rXY x y 0 1 * x 3 * y 2
        + y 1 * rX x 0 2 * y 3
        - y 3 * rX x 0 2 * y 1
        - rXY x y 0 2 * x 1 * y 3
        + rXY x y 0 2 * x 3 * y 1
        - y 1 * rX x 0 3 * y 2
        + y 2 * rX x 0 3 * y 1
        + rXY x y 0 3 * x 1 * y 2
        - rXY x y 0 3 * x 2 * y 1
        - y 0 * rX x 1 2 * y 3
        + y 3 * rX x 1 2 * y 0
        + rXY x y 1 2 * x 0 * y 3
        - rXY x y 1 2 * x 3 * y 0
        + y 0 * rX x 1 3 * y 2
        - y 2 * rX x 1 3 * y 0
        - rXY x y 1 3 * x 0 * y 2
        + rXY x y 1 3 * x 2 * y 0
        - y 0 * rX x 2 3 * y 1
        + y 1 * rX x 2 3 * y 0
        + rXY x y 2 3 * x 0 * y 1
        - rXY x y 2 3 * x 1 * y 0 := by
    simp only [cdet, rX, rXY]; noncomm_ring
  rw [h]; simp [hX, hXY]

/-- In the commutative specialisation every Manin relation holds, so the symmetrised relation
is twice the classical Schouten relation; it is recorded only as this specialisation. -/
theorem manin_relations_of_commute (hc : ∀ a b : A, a * b = b * a) :
    (∀ j l, rX x j l = 0) ∧ (∀ j l, rY y j l = 0) ∧ (∀ j l, rXY x y j l = 0) := by
  refine ⟨fun j l => ?_, fun j l => ?_, fun j l => ?_⟩ <;> simp only [rX, rY, rXY]
  · rw [hc (x j)]; simp
  · rw [hc (y j)]; simp
  · rw [hc (x j) (y l), hc (x l) (y j)]; simp

end ManinBrackets

/-! ### General index quadruples (`Gr(2,n)` with operator entries) -/

section GeneralIndex

variable {A : Type*} [Ring A] {ι : Type*} (x y : ι → A)

/-- Column-determinant bracket for an arbitrary index type. -/
def cdet' (j l : ι) : A := x j * y l - x l * y j

def rX' (j l : ι) : A := x j * x l - x l * x j

def rXY' (j l : ι) : A := x j * y l - y l * x j - (x l * y j - y j * x l)

variable {x y}

/-- Symmetrised Schouten relation for any four indices `a b c d`. -/
theorem schouten_symmetrised_general (hX : ∀ j l, rX' x j l = 0) (hXY : ∀ j l, rXY' x y j l = 0)
    (a b c d : ι) :
    (cdet' x y a b * cdet' x y c d - cdet' x y a c * cdet' x y b d +
        cdet' x y a d * cdet' x y b c) +
      (cdet' x y c d * cdet' x y a b - cdet' x y b d * cdet' x y a c +
        cdet' x y b c * cdet' x y a d) = 0 := by
  have h :
      (cdet' x y a b * cdet' x y c d - cdet' x y a c * cdet' x y b d +
          cdet' x y a d * cdet' x y b c) +
        (cdet' x y c d * cdet' x y a b - cdet' x y b d * cdet' x y a c +
          cdet' x y b c * cdet' x y a d) =
        - y c * rX' x a b * y d
        + y d * rX' x a b * y c
        + rXY' x y a b * x c * y d
        - rXY' x y a b * x d * y c
        + y b * rX' x a c * y d
        - y d * rX' x a c * y b
        - rXY' x y a c * x b * y d
        + rXY' x y a c * x d * y b
        - y b * rX' x a d * y c
        + y c * rX' x a d * y b
        + rXY' x y a d * x b * y c
        - rXY' x y a d * x c * y b
        - y a * rX' x b c * y d
        + y d * rX' x b c * y a
        + rXY' x y b c * x a * y d
        - rXY' x y b c * x d * y a
        + y a * rX' x b d * y c
        - y c * rX' x b d * y a
        - rXY' x y b d * x a * y c
        + rXY' x y b d * x c * y a
        - y a * rX' x c d * y b
        + y b * rX' x c d * y a
        + rXY' x y c d * x a * y b
        - rXY' x y c d * x b * y a := by
    simp only [cdet', rX', rXY']; noncomm_ring
  rw [h]; simp [hX, hXY]

/-- The five symmetrised Plücker relations of `Gr(2,5)` with operator entries. -/
theorem gr25_symmetrised_relations (x y : Fin 5 → A) (hX : ∀ j l, rX' x j l = 0)
    (hXY : ∀ j l, rXY' x y j l = 0) :
    ∀ m : Fin 5, ∃ a b c d : Fin 5, a < b ∧ b < c ∧ c < d ∧ m ∉ ({a, b, c, d} : Finset (Fin 5)) ∧
      (cdet' x y a b * cdet' x y c d - cdet' x y a c * cdet' x y b d +
          cdet' x y a d * cdet' x y b c) +
        (cdet' x y c d * cdet' x y a b - cdet' x y b d * cdet' x y a c +
          cdet' x y b c * cdet' x y a d) = 0 := by
  intro m
  have key := schouten_symmetrised_general hX hXY
  fin_cases m
  · exact ⟨1, 2, 3, 4, by decide, by decide, by decide, by decide, key 1 2 3 4⟩
  · exact ⟨0, 2, 3, 4, by decide, by decide, by decide, by decide, key 0 2 3 4⟩
  · exact ⟨0, 1, 3, 4, by decide, by decide, by decide, by decide, key 0 1 3 4⟩
  · exact ⟨0, 1, 2, 4, by decide, by decide, by decide, by decide, key 0 1 2 4⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by decide, key 0 1 2 3⟩

end GeneralIndex


/-! ### Doublets and non-vanishing for the octahedron (owner `MHVTriplets` notions) -/

section Octahedron

/-- Black faces `{1,2,3},{3,4,5},{5,6,1},{2,6,4}` (labels shifted to `Fin 6`). -/
def octBlack : Finset (Finset (Fin 6)) := {{0, 1, 2}, {2, 3, 4}, {4, 5, 0}, {1, 5, 3}}

/-- White faces `{6,2,1},{2,3,4},{4,5,6},{1,5,3}`. -/
def octWhite : Finset (Finset (Fin 6)) := {{5, 1, 0}, {1, 2, 3}, {3, 4, 5}, {0, 4, 2}}

theorem octahedron_pairCountAux_parity :
    ∀ i j : Fin 6, pairCountAux octBlack i j % 2 = pairCountAux octWhite i j % 2 := by
  decide

/-- The octahedral sphere move preserves the doublet set. -/
theorem octahedron_doublets_eq : doublets octBlack = doublets octWhite := by
  ext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [doublets_mem_iff, pairCount_mk, octahedron_pairCountAux_parity]

/-- The three antipodal diagonals `14, 25, 36` are not doublets. -/
theorem octahedron_diagonals_not_doublets :
    s(0, 3) ∉ doublets octBlack ∧ s(1, 4) ∉ doublets octBlack ∧ s(2, 5) ∉ doublets octBlack := by
  simp only [doublets_mem_iff, pairCount_mk]
  decide

/-- The black faces indexed by `Fin 4`. -/
def octBlackFace : Fin 4 → Finset (Fin 6) := ![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}, {1, 5, 3}]

theorem octBlackFace_injective : Function.Injective octBlackFace := by decide

theorem octBlack_eq_image : octBlack = Finset.univ.image octBlackFace := by decide

/-- Index-level non-vanishing: every nonempty set of `k` faces covers `≥ k + 2` vertices. -/
theorem octBlackFace_cover :
    ∀ I : Finset (Fin 4), I ≠ ∅ → (I.biUnion octBlackFace).card ≥ I.card + 2 := by decide

theorem octBlack_nonVanishing : nonVanishing octBlack := by
  intro S hS hne
  classical
  set I : Finset (Fin 4) := Finset.univ.filter (fun i => octBlackFace i ∈ S) with hI
  have hSI : S = I.image octBlackFace := by
    ext t
    constructor
    · intro ht
      have ht' : t ∈ Finset.univ.image octBlackFace := octBlack_eq_image ▸ hS ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht'
      exact Finset.mem_image.mpr ⟨i, by simp [hI, ht], rfl⟩
    · intro ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      simpa [hI] using hi
  have hIne : I ≠ ∅ := by
    rintro h
    apply hne
    rw [hSI, h, Finset.image_empty]
  rw [hSI, Finset.card_image_of_injective _ octBlackFace_injective, Finset.image_biUnion]
  exact octBlackFace_cover I hIne

end Octahedron

/-! ### Genus bound -/

/-- If `T ≠ ∅` is non-vanishing and its `V = |⋃ T|` vertices satisfy the Euler relation of a
closed bicolored triangulation with `|B| = |W| = |T|` (`F = 2|T|`, `E = 3|T|`) on a genus `g`
surface, then `g = 0`. -/
theorem genus_zero_of_nonVanishing {α : Type*} [Fintype α] [DecidableEq α]
    {T : Finset (Finset α)} (hT : nonVanishing T) (hne : T ≠ ∅) {g : ℤ} (hg : 0 ≤ g)
    (hEuler : ((T.biUnion id).card : ℤ) + 2 * T.card = 3 * T.card + 2 - 2 * g) : g = 0 := by
  have h := hT T (Finset.Subset.refl T) hne
  omega

/-- The octahedron: `V = 6`, `m = 4` satisfies the relation only at genus `0`. -/
theorem octBlack_vertices : (octBlack.biUnion id).card = 6 := by decide

end InfoGeometry.Combinatorics.NonPlanarOnShellBrackets
