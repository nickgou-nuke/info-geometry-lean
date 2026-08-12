import InfoGeometry.Canonical.CantorCylinderLattice
import InfoGeometry.Canonical.KreinProjectorLattice
import InfoGeometry.Clifford.SplitQ11PhaseFlip
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Combined Cantor-Krein Sector Lattice

The product lattice combining Cantor spatial cells with Krein chirality.

At finite level `n`, a sector is defined by selecting both:
1. A Cantor spatial support: an element of the Boolean algebra of `Set (Fin n → Bool)`.
2. A Krein causal chirality: an element of the Krein sector Boolean algebra.

The combined sector lattice is the product lattice `Sector n = Set (Fin n → Bool) × KreinSector`.
Since both factors are complete Boolean algebras, the product is automatically a
complete Boolean algebra.

The combined sector projector selects the local corner algebra `E A E` where
physics takes place.
-/

namespace InfoGeometry.Canonical.SectorLattice

open CantorCylinderLattice
open KreinProjectorLattice
open KreinProjectorLattice.KreinSector
open InfoGeometry.Clifford
open SplitQ11PhaseFlip

/-- Local alias for the split `Cl(1,1)` carrier. -/
abbrev SectorAlg := CliffordAlgebra InfoGeometry.Clifford.splitQ11

/-! ## 1. Sector Type Definition -/

/-- A combined Cantor-Krein sector at level `n`. -/
def Sector (n : ℕ) : Type := Set (Fin n → Bool) × KreinSector

/-! ## 2. Boolean Algebra Structure -/

/-- The combined sector lattice is a Boolean algebra.

This is automatically derived by Mathlib since both `Set X` and `KreinSector`
are Boolean algebras, and the product of Boolean algebras is a Boolean algebra. -/
instance boolAlgebra (n : ℕ) : BooleanAlgebra (Sector n) :=
  Prod.instBooleanAlgebra

/-! ## 3. Completeness -/

/-- The combined sector lattice is a complete lattice.

Finite product of complete lattices is a complete lattice. -/
noncomputable instance completeLattice (n : ℕ) : CompleteLattice (Sector n) :=
  Prod.instCompleteLattice

/-! ## 4. Fundamental Physical Projectors -/

/-- The elementary sector projector $E_{n,w,\varepsilon} = e_{n,w} \otimes p_\varepsilon$. -/
def elementarySector (n : ℕ) (w : Fin n → Bool) (k : KreinSector) : Sector n :=
  (cylinder n w, k)

/-- Simultaneous localization (meet) of two elementary sectors. -/
theorem elementarySector_inf_eq_meet (n : ℕ) (w₁ w₂ : Fin n → Bool) (k₁ k₂ : KreinSector) :
    elementarySector n w₁ k₁ ⊓ elementarySector n w₂ k₂ =
      (cylinder n w₁ ⊓ cylinder n w₂, k₁ ⊓ k₂) :=
  rfl

/--
In the formal product lattice, spatial disjointness does *not* imply lattice disjointness,
because `(⊥, k)` is not equal to `(⊥, ⊥)` unless `k = ⊥`.

Physically, the representation map `Φ(e, p) = e ⊗ p` will quotient this out,
since `0 ⊗ p = 0`. Thus, `(⊥, k)` represents a "null sector" that evaluates to zero
in the operator algebra.
-/
theorem elementarySector_inf_spatial_bot {n : ℕ} {w₁ w₂ : Fin n → Bool}
    (k₁ k₂ : KreinSector) (h : w₁ ≠ w₂) :
    elementarySector n w₁ k₁ ⊓ elementarySector n w₂ k₂ = (⊥, k₁ ⊓ k₂) := by
  refine Prod.ext ?_ ?_
  · show cylinder n w₁ ⊓ cylinder n w₂ = ⊥
    exact cylinder_disjoint h
  · rfl

/-! ## 5. Pointwise completed finite projection lattice -/

/-- The pointwise finite Cantor-Krein projection lattice is Boolean. -/
example (n : ℕ) : BooleanAlgebra ((Fin n → Bool) → KreinSector) := inferInstance

/-- The pointwise finite Cantor-Krein projection lattice is complete. -/
noncomputable example (n : ℕ) : CompleteLattice ((Fin n → Bool) → KreinSector) := inferInstance

/-- Evaluate a pointwise sector assignment as an actual finite function of split projectors. -/
noncomputable def kreinMinusProjector : SectorAlg :=
  nullMinus * nullPlus

/-- The positive `ε` projector in the split `Cl(1,1)` algebra. -/
noncomputable def kreinPlusProjector : SectorAlg :=
  nullPlus * nullMinus

/-- The negative projector is idempotent. -/
theorem kreinMinusProjector_sq :
    kreinMinusProjector * kreinMinusProjector = kreinMinusProjector := by
  unfold kreinMinusProjector
  calc
    (nullMinus * nullPlus) * (nullMinus * nullPlus)
      = nullMinus * (nullPlus * nullMinus) * nullPlus := by
          rw [← mul_assoc, ← mul_assoc]
    _ = nullMinus * (1 - nullMinus * nullPlus) * nullPlus := by
          have hq : nullPlus * nullMinus = 1 - nullMinus * nullPlus := by
            have hs := nullMinus_mul_nullPlus_add_swap
            have h := congrArg (fun z : CliffordAlgebra splitQ11 => z - nullMinus * nullPlus) hs
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
          rw [hq]
    _ = (nullMinus * (1 - nullMinus * nullPlus)) * nullPlus := by rw [mul_assoc]
    _ = (nullMinus * 1 - nullMinus * (nullMinus * nullPlus)) * nullPlus := by rw [mul_sub, mul_one]
    _ = (nullMinus - nullMinus * (nullMinus * nullPlus)) * nullPlus := by simp
    _ = (nullMinus - (nullMinus * nullMinus) * nullPlus) * nullPlus := by rw [mul_assoc]
    _ = (nullMinus - 0 * nullPlus) * nullPlus := by rw [nullMinus_sq]
    _ = nullMinus * nullPlus := by simp

/-- The positive projector is idempotent. -/
theorem kreinPlusProjector_sq :
    kreinPlusProjector * kreinPlusProjector = kreinPlusProjector := by
  unfold kreinPlusProjector
  calc
    (nullPlus * nullMinus) * (nullPlus * nullMinus)
      = nullPlus * (nullMinus * nullPlus) * nullMinus := by
          rw [← mul_assoc, ← mul_assoc]
    _ = nullPlus * (1 - nullPlus * nullMinus) * nullMinus := by
          have hq : nullMinus * nullPlus = 1 - nullPlus * nullMinus := by
            have hs := nullMinus_mul_nullPlus_add_swap
            have h := congrArg (fun z : CliffordAlgebra splitQ11 => z - nullPlus * nullMinus) hs
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
          rw [hq]
    _ = (nullPlus * (1 - nullPlus * nullMinus)) * nullMinus := by rw [mul_assoc]
    _ = (nullPlus * 1 - nullPlus * (nullPlus * nullMinus)) * nullMinus := by rw [mul_sub, mul_one]
    _ = (nullPlus - nullPlus * (nullPlus * nullMinus)) * nullMinus := by simp
    _ = (nullPlus - (nullPlus * nullPlus) * nullMinus) * nullMinus := by rw [mul_assoc]
    _ = (nullPlus - 0 * nullMinus) * nullMinus := by rw [nullPlus_sq]
    _ = nullPlus * nullMinus := by simp

noncomputable def kreinSectorToAlg : KreinSector → SectorAlg
  | bot => 0
  | minus => kreinMinusProjector
  | plus => kreinPlusProjector
  | top => 1

noncomputable def projectionAssignmentToAlg {n : ℕ}
    (P : (Fin n → Bool) → KreinSector) : (Fin n → Bool) → SectorAlg :=
  fun w => kreinSectorToAlg (P w)

/-- Pointwise sector assignments evaluate to idempotents in the finite function algebra. -/
theorem projectionAssignmentToAlg_idempotent {n : ℕ} (P : (Fin n → Bool) → KreinSector) :
    IsIdempotentElem (projectionAssignmentToAlg P) := by
  rw [IsIdempotentElem]
  funext w
  cases hP : P w with
  | bot => simp [projectionAssignmentToAlg, kreinSectorToAlg, hP]
  | minus => simpa [projectionAssignmentToAlg, kreinSectorToAlg, hP] using kreinMinusProjector_sq
  | plus => simpa [projectionAssignmentToAlg, kreinSectorToAlg, hP] using kreinPlusProjector_sq
  | top => simp [projectionAssignmentToAlg, kreinSectorToAlg, hP]

/-- The elementary sector assignment supported at a single Cantor word. -/
def elementaryProjectionAssignment {n : ℕ}
    (w : Fin n → Bool) (k : KreinSector) : (Fin n → Bool) → KreinSector :=
  fun v => if v = w then k else ⊥

@[simp] theorem elementaryProjectionAssignment_self {n : ℕ}
    (w : Fin n → Bool) (k : KreinSector) :
    elementaryProjectionAssignment w k w = k := by
  simp [elementaryProjectionAssignment]

@[simp] theorem elementaryProjectionAssignment_of_ne {n : ℕ}
    {v w : Fin n → Bool} (h : v ≠ w) (k : KreinSector) :
    elementaryProjectionAssignment w k v = ⊥ := by
  simp [elementaryProjectionAssignment, h]

/-- The elementary finite sector projector is idempotent in the function algebra. -/
theorem elementaryProjectionAssignment_idempotent {n : ℕ}
    (w : Fin n → Bool) (k : KreinSector) :
    IsIdempotentElem (projectionAssignmentToAlg (elementaryProjectionAssignment w k)) :=
  projectionAssignmentToAlg_idempotent _
def refineProjectionAssignment {n : ℕ}
    (P : (Fin n → Bool) → KreinSector) : (Fin (n + 1) → Bool) → KreinSector :=
  fun v => P (truncateWord v)

/-- Coarse-graining is the right adjoint: meet the two children above each parent. -/
def coarseProjectionAssignment {n : ℕ}
    (Q : (Fin (n + 1) → Bool) → KreinSector) : (Fin n → Bool) → KreinSector :=
  fun w => Q (leftChild w) ⊓ Q (rightChild w)

/--
Refining an elementary Cantor-Krein sector gives the join of its two child
sectors with the same Krein chirality.
-/
theorem refineProjectionAssignment_elementary {n : ℕ}
    (w : Fin n → Bool) (k : KreinSector) :
    refineProjectionAssignment (elementaryProjectionAssignment w k) =
      elementaryProjectionAssignment (leftChild w) k ⊔
        elementaryProjectionAssignment (rightChild w) k := by
  funext v
  cases hlast : v (Fin.last n)
  · have hv : v = leftChild (truncateWord v) := by
      rw [(Fin.snoc_init_self v).symm]
      simp [truncateWord, leftChild, extendWord, hlast]
    by_cases hparent : truncateWord v = w
    · rw [hv, hparent]
      simp [refineProjectionAssignment, elementaryProjectionAssignment]
    · rw [hv]
      have hleft : leftChild (truncateWord v) ≠ leftChild w := fun h =>
        hparent (leftChild_injective h)
      have hright : leftChild (truncateWord v) ≠ rightChild w :=
        leftChild_ne_rightChild (truncateWord v) w
      simp [refineProjectionAssignment, elementaryProjectionAssignment, hparent, hleft, hright]
  · have hv : v = rightChild (truncateWord v) := by
      rw [(Fin.snoc_init_self v).symm]
      simp [truncateWord, rightChild, extendWord, hlast]
    by_cases hparent : truncateWord v = w
    · rw [hv, hparent]
      simp [refineProjectionAssignment, elementaryProjectionAssignment]
    · rw [hv]
      have hleft : rightChild (truncateWord v) ≠ leftChild w :=
        rightChild_ne_leftChild (truncateWord v) w
      have hright : rightChild (truncateWord v) ≠ rightChild w := fun h =>
        hparent (rightChild_injective h)
      simp [refineProjectionAssignment, elementaryProjectionAssignment, hparent, hleft, hright]

/--
The join of the two elementary child sectors coarse-grains back to the parent
elementary sector.
-/
theorem coarseProjectionAssignment_elementary_children {n : ℕ}
    (w : Fin n → Bool) (k : KreinSector) :
    coarseProjectionAssignment
        (elementaryProjectionAssignment (leftChild w) k ⊔
          elementaryProjectionAssignment (rightChild w) k) =
      elementaryProjectionAssignment w k := by
  funext v
  by_cases hparent : v = w
  · rw [hparent]
    simp [coarseProjectionAssignment, elementaryProjectionAssignment]
  · have hll : leftChild v ≠ leftChild w := fun h =>
      hparent (leftChild_injective h)
    have hlr : leftChild v ≠ rightChild w :=
      leftChild_ne_rightChild v w
    have hrl : rightChild v ≠ leftChild w :=
      rightChild_ne_leftChild v w
    have hrr : rightChild v ≠ rightChild w := fun h =>
      hparent (rightChild_injective h)
    simp [coarseProjectionAssignment, elementaryProjectionAssignment, hparent, hll, hlr, hrl, hrr]

/-- Pointwise projection refinement and coarse-graining form a Galois connection. -/
theorem projectionAssignment_galoisConnection (n : ℕ) :
    GaloisConnection (@refineProjectionAssignment n) (@coarseProjectionAssignment n) := by
  intro P Q
  constructor
  · intro h w
    apply le_inf
    · have hleft := h (leftChild w)
      simpa [refineProjectionAssignment, leftChild, extendWord, truncateWord] using hleft
    · have hright := h (rightChild w)
      simpa [refineProjectionAssignment, rightChild, extendWord, truncateWord] using hright
  · intro h v
    have hw := h (truncateWord v)
    cases hlast : v (Fin.last n)
    · have hleft : v = leftChild (truncateWord v) := by
        rw [(Fin.snoc_init_self v).symm]
        simp [truncateWord, leftChild, extendWord, hlast]
      have hle : P (truncateWord v) ≤ Q (leftChild (truncateWord v)) :=
        le_trans hw inf_le_left
      rw [hleft]
      simpa [refineProjectionAssignment, truncateWord, leftChild, extendWord] using hle
    · have hright : v = rightChild (truncateWord v) := by
        rw [(Fin.snoc_init_self v).symm]
        simp [truncateWord, rightChild, extendWord, hlast]
      have hle : P (truncateWord v) ≤ Q (rightChild (truncateWord v)) :=
        le_trans hw inf_le_right
      rw [hright]
      simpa [refineProjectionAssignment, truncateWord, rightChild, extendWord] using hle

/-- Projection refinement preserves arbitrary joins. -/
theorem refineProjectionAssignment_iSup {n : ℕ} {ι : Sort*}
    (P : ι → (Fin n → Bool) → KreinSector) :
    refineProjectionAssignment (⨆ i, P i) = ⨆ i, refineProjectionAssignment (P i) :=
  (projectionAssignment_galoisConnection n).l_iSup

/-- Projection coarse-graining preserves arbitrary meets. -/
theorem coarseProjectionAssignment_iInf {n : ℕ} {ι : Sort*}
    (Q : ι → (Fin (n + 1) → Bool) → KreinSector) :
    coarseProjectionAssignment (⨅ i, Q i) = ⨅ i, coarseProjectionAssignment (Q i) :=
  (projectionAssignment_galoisConnection n).u_iInf

end InfoGeometry.Canonical.SectorLattice
