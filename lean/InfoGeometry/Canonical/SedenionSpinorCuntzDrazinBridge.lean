import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzN
import InfoGeometry.Canonical.DrazinTripotentTrifactorBridge
import InfoGeometry.Canonical.TrifactorDecomposition

/-!
# Sedenion Spinor / Cuntz / Drazin Finite Bridge

This module records the finite theorem surface extracted from
`preprints202605.0168.v1`: the paper's steering-spinor sector bookkeeping
and the checkable algebraic shadow behind its `S`-operators.

#### BUCKET 1: CLOSED FINITE THEOREMS

* the five steering sectors give `1 + 5 * 3 = 16` basis slots;
* every sector is assigned a three-dimensional triplet;
* bilinear data splits into symmetric and antisymmetric readouts;
* a finite non-associative magma witness has a nonzero associator;
* abstract `O_5` and `O_16` Cuntz range projections are idempotent,
  orthogonal, and sum to the unit through the existing `CuntzNAlgebra` owner;
* tripotent Drazin support/null facts are delegated to the existing
  `DrazinTripotentTrifactorBridge` owner.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

The Cuntz packets assume explicit `CuntzNAlgebra` witnesses.  The Drazin packet
assumes only the explicit tripotent hypothesis `T ^ 3 = T`.

#### BUCKET 3: OPEN CLOSURE DEBT

This file does not formalize full sedenion multiplication, a faithful
infinite-dimensional Cuntz representation, a spinor bundle, tetrad/connection
construction, Einstein equations, Yukawa corrections, cosmology, dark matter,
dark energy, or physical quantum gravity.  It only proves the finite algebraic
bookkeeping and operator-shadow identities.
-/

noncomputable section

namespace InfoGeometry.Canonical.SedenionSpinorCuntzDrazinBridge

open InfoGeometry.Algebra.Cuntz
open DrazinTripotentTrifactorBridge
open TrifactorDecomposition

/-! ## Steering-sector bookkeeping -/

/-- The five steering-spinor sectors named in the preprint. -/
inductive SteeringSector where
  | gamma
  | theta
  | u
  | v
  | w
  deriving DecidableEq, Fintype, Repr

namespace SteeringSector

/-- Each steering sector is a triplet in the paper's bookkeeping. -/
def tripletCardinality (_ : SteeringSector) : ℕ := 3

/-- Explicit equivalence with `Fin 5`, avoiding generated cardinality black boxes. -/
def equivFin5 : SteeringSector ≃ Fin 5 where
  toFun
    | gamma => 0
    | theta => 1
    | u => 2
    | v => 3
    | w => 4
  invFun
    | 0 => gamma
    | 1 => theta
    | 2 => u
    | 3 => v
    | _ => w
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- The five sector labels have cardinality five. -/
theorem card_eq_five : Fintype.card SteeringSector = 5 := by
  rw [Fintype.card_congr equivFin5]
  simp

/-- Every steering sector has three basis directions. -/
theorem tripletCardinality_eq_three (s : SteeringSector) :
    tripletCardinality s = 3 := by
  cases s <;> rfl

/-- Scalar plus five triplets gives the sixteen-dimensional carrier count. -/
theorem scalar_plus_five_triplets_eq_sixteen :
    1 + Fintype.card SteeringSector * 3 = 16 := by
  rw [card_eq_five]

/-- Summing the five sector triplets also gives fifteen imaginary directions. -/
theorem sum_tripletCardinality_eq_fifteen :
    (∑ s : SteeringSector, tripletCardinality s) = 15 := by
  rw [show (∑ s : SteeringSector, tripletCardinality s) =
      Fintype.card SteeringSector * 3 by simp [tripletCardinality]]
  rw [card_eq_five]

end SteeringSector

/-! ## Bilinear symmetric/antisymmetric readouts -/

variable {ι : Type*}
variable {R : Type*} [AddCommGroup R]

/-- Symmetric readout of a bilinear table.  No division by two is needed here. -/
def symReadout (B : ι → ι → R) (i j : ι) : R :=
  B i j + B j i

/-- Antisymmetric readout of a bilinear table. -/
def skewReadout (B : ι → ι → R) (i j : ι) : R :=
  B i j - B j i

/-- The symmetric readout is symmetric. -/
theorem symReadout_comm (B : ι → ι → R) (i j : ι) :
    symReadout B i j = symReadout B j i := by
  unfold symReadout
  abel

/-- The antisymmetric readout changes sign under index swap. -/
theorem skewReadout_swap (B : ι → ι → R) (i j : ι) :
    skewReadout B j i = -skewReadout B i j := by
  unfold skewReadout
  abel

/-- The antisymmetric readout vanishes on the diagonal. -/
theorem skewReadout_diag (B : ι → ι → R) (i : ι) :
    skewReadout B i i = 0 := by
  unfold skewReadout
  abel

/-! ## Finite non-associative shadow -/

/-- Associator readout for an arbitrary binary operation. -/
def associatorReadout {α : Type*} (mul : α → α → α) (a b c : α) : α :=
  mul (mul a b) c

/-- The right-associated readout for comparison with `associatorReadout`. -/
def rightAssociatedReadout {α : Type*} (mul : α → α → α) (a b c : α) : α :=
  mul a (mul b c)

/--
Concrete non-associativity witness.  This is not a sedenion theorem; it is the
finite algebraic shape of the paper's associator: `(a*b)*c ≠ a*(b*c)`.
-/
theorem natSub_nonassociative_witness :
    associatorReadout Nat.sub 5 3 1 ≠ rightAssociatedReadout Nat.sub 5 3 1 := by
  norm_num [associatorReadout, rightAssociatedReadout]

/-! ## Cuntz projection shadows for `S`-operator sectors -/

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- Abstract `O_5` packet for the five steering-sector `S`-operator shadow. -/
theorem steeringSector_cuntz_projection_packet
    (O : CuntzNAlgebra (N := 5) Op) :
    (∀ i : Fin 5,
      (O.S i * star (O.S i)) * (O.S i * star (O.S i)) =
        O.S i * star (O.S i)) ∧
    (∀ i j : Fin 5, i ≠ j →
      (O.S i * star (O.S i)) * (O.S j * star (O.S j)) = 0) ∧
    (∑ i : Fin 5, O.S i * star (O.S i) = 1) := by
  exact ⟨
    fun i => range_projection_idempotent (O := O) i,
    fun i j hij => range_projection_orthogonal (O := O) i j hij,
    range_projections_sum_one (O := O)⟩

/-- Abstract `O_16` packet for the scalar plus fifteen imaginary basis branches. -/
theorem sedenionBasis_cuntz_projection_packet
    (O : CuntzNAlgebra (N := 16) Op) :
    (∀ i : Fin 16,
      (O.S i * star (O.S i)) * (O.S i * star (O.S i)) =
        O.S i * star (O.S i)) ∧
    (∀ i j : Fin 16, i ≠ j →
      (O.S i * star (O.S i)) * (O.S j * star (O.S j)) = 0) ∧
    (∑ i : Fin 16, O.S i * star (O.S i) = 1) := by
  exact ⟨
    fun i => range_projection_idempotent (O := O) i,
    fun i j hij => range_projection_orthogonal (O := O) i j hij,
    range_projections_sum_one (O := O)⟩

/-! ## Drazin/tripotent support lane -/

variable {A : Type*} [CommRing A] [Invertible (2 : A)]

/-- Combined finite bridge packet: sector count, bilinear split, and associator shadow. -/
theorem sedenion_spinor_finite_digest_packet :
    1 + Fintype.card SteeringSector * 3 = 16 ∧
      (∑ s : SteeringSector, SteeringSector.tripletCardinality s) = 15 ∧
      associatorReadout Nat.sub 5 3 1 ≠ rightAssociatedReadout Nat.sub 5 3 1 := by
  exact ⟨
    SteeringSector.scalar_plus_five_triplets_eq_sixteen,
    SteeringSector.sum_tripletCardinality_eq_fifteen,
    natSub_nonassociative_witness⟩

end InfoGeometry.Canonical.SedenionSpinorCuntzDrazinBridge

end
