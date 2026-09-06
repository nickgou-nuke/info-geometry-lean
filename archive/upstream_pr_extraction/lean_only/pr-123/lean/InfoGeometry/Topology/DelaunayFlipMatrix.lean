import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Rational Delaunay flip matrix layer

#### BUCKET 1: CLOSED FINITE THEOREMS
- `flip_inverse_identity`: the local rational `2 × 2` flip block is inverted by
  the reversed flip block.
- `flip_far_commute_embedded_blocks`: two independent `2 × 2` blocks embedded in
  disjoint diagonal slots of a `4 × 4` transport matrix commute.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
- The full `2n+1` triangle-basis insertion machinery.
- Presentation-level pure-braid invariance from inverse, far-commutativity, and
  pentagon moves.
- Analytic Voronoi/Delaunay geometry.
-/

namespace InfoGeometry.Topology.Delaunay

/-- Abstract parameter space for the rational flip matrices. -/
structure FlipLabels (ι : Type*) where
  ζ : ι → ℚ
  nonzero_den : ∀ {i k : ι}, i ≠ k → ζ i - ζ k ≠ 0

variable {ι : Type*} [DecidableEq ι] (labels : FlipLabels ι)

/-- The local 2×2 rational block for a Delaunay flip `ik → jl`. -/
noncomputable def flipBlock (i k j l : ι) (_hik : i ≠ k) : Matrix (Fin 2) (Fin 2) ℚ :=
  let zi := labels.ζ i
  let zk := labels.ζ k
  let zj := labels.ζ j
  let zl := labels.ζ l
  let den := zi - zk
  ![![ (zi - zl) / den, (zi - zj) / den ],
    ![ (zl - zk) / den, (zj - zk) / den ]]

/-- 1. Inverse Flip Identity: applying a flip and its inverse gives the identity block. -/
def flipInverseStatement (i k j l : ι) (hik : i ≠ k) (hjl : j ≠ l) : Prop :=
  flipBlock labels i k j l hik * flipBlock labels j l i k hjl = 1

omit [DecidableEq ι] in
/-- The symbolic 2×2 Delaunay flip block is inverted by the reversed flip. -/
theorem flip_inverse_identity (i k j l : ι) (hik : i ≠ k) (hjl : j ≠ l) :
    flipInverseStatement labels i k j l hik hjl := by
  unfold flipInverseStatement flipBlock
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp [labels.nonzero_den hik, labels.nonzero_den hjl]
    ring
  · field_simp [labels.nonzero_den hik, labels.nonzero_den hjl]
    ring
  · field_simp [labels.nonzero_den hik, labels.nonzero_den hjl]
    ring
  · field_simp [labels.nonzero_den hik, labels.nonzero_den hjl]
    ring

/-- Embed a local `2 × 2` flip block in the upper-left slot of a `4 × 4` matrix. -/
def upperLeftEmbed2 (A : Matrix (Fin 2) (Fin 2) ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  ![![A 0 0, A 0 1, 0, 0],
    ![A 1 0, A 1 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1]]

/-- Embed a local `2 × 2` flip block in the lower-right slot of a `4 × 4` matrix. -/
def lowerRightEmbed2 (B : Matrix (Fin 2) (Fin 2) ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, B 0 0, B 0 1],
    ![0, 0, B 1 0, B 1 1]]

/--
Far-commutativity for independent flips in the finite block model.

This proves the algebraic core only: two local flip matrices inserted into
disjoint triangle-basis slots commute because the nontrivial blocks do not
overlap.
-/
theorem flip_far_commute_embedded_blocks
    (A B : Matrix (Fin 2) (Fin 2) ℚ) :
    upperLeftEmbed2 A * lowerRightEmbed2 B =
      lowerRightEmbed2 B * upperLeftEmbed2 A := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [upperLeftEmbed2, lowerRightEmbed2, Matrix.mul_apply, Fin.sum_univ_four]

/-- 3. Pentagon Identity target.  The exact five-flip embedding remains open. -/
def pentagonStatement (_i _j _k _l _m : ι)
    (A₁ A₂ A₃ A₄ A₅ : Matrix (Fin 3) (Fin 3) ℚ) : Prop :=
  A₁ * A₂ * A₃ * A₄ * A₅ = 1

end InfoGeometry.Topology.Delaunay
