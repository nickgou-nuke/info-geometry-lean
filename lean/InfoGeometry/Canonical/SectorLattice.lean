import InfoGeometry.Canonical.CantorCylinderLattice
import InfoGeometry.Canonical.KreinProjectorLattice
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Combined Cantor-Krein Sector Lattice

The product lattice combining Cantor spatial cells with Krein chirality.

At finite level `n`, a sector is defined by selecting both:
1. A Cantor spatial support: an element of the Boolean algebra of `Set (BinaryWord n)`.
2. A Krein causal chirality: an element of the Krein sector Boolean algebra.

The combined sector lattice is the product lattice `Sector n = Set (BinaryWord n) × KreinSector`.
Since both factors are complete Boolean algebras, the product is automatically a
complete Boolean algebra.

The combined sector projector selects the local corner algebra `E A E` where
physics takes place.
-/

namespace SectorLattice

open InfoGeometry.Canonical.CantorCylinderLattice
open InfoGeometry.Canonical.KreinProjectorLattice
open InfoGeometry.Clifford.SplitQ11PhaseFlip

/-! ## 1. Sector Type Definition -/

/-- A combined Cantor-Krein sector at level `n`. -/
def Sector (n : ℕ) : Type := Set (BinaryWord n) × KreinSector

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
def elementarySector (n : ℕ) (w : BinaryWord n) (k : KreinSector) : Sector n :=
  (cylinder n w, k)

/-- Simultaneous localization (meet) of two elementary sectors. -/
theorem elementarySector_inf_eq_meet (n : ℕ) (w₁ w₂ : BinaryWord n) (k₁ k₂ : KreinSector) :
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
theorem elementarySector_inf_spatial_bot {n : ℕ} {w₁ w₂ : BinaryWord n}
    (k₁ k₂ : KreinSector) (h : w₁ ≠ w₂) :
    elementarySector n w₁ k₁ ⊓ elementarySector n w₂ k₂ = (⊥, k₁ ⊓ k₂) := by
  refine Prod.ext ?_ ?_
  · show cylinder n w₁ ⊓ cylinder n w₂ = ⊥
    exact cylinder_disjoint h
  · rfl

/-! ## 5. Pointwise completed finite projection lattice -/

/--
The concrete finite Cantor-Krein projection lattice.

Unlike `Set (BinaryWord n) × KreinSector`, this records a separate local Krein
sector above every Cantor cell.  Joins, meets, complements, and arbitrary
suprema/infima are inherited pointwise from `KreinSector`.
-/
abbrev ProjectionAssignment (n : ℕ) : Type :=
  BinaryWord n → KreinSector

/-- The pointwise finite Cantor-Krein projection lattice is Boolean. -/
example (n : ℕ) : BooleanAlgebra (ProjectionAssignment n) := inferInstance

/-- The pointwise finite Cantor-Krein projection lattice is complete. -/
noncomputable example (n : ℕ) : CompleteLattice (ProjectionAssignment n) := inferInstance

/-- Evaluate a pointwise sector assignment as an actual finite function of split projectors. -/
noncomputable def projectionAssignmentToAlg {n : ℕ}
    (P : ProjectionAssignment n) : BinaryWord n → Alg :=
  fun w => KreinSector.toAlg (P w)

/-- Pointwise sector assignments evaluate to idempotents in the finite function algebra. -/
theorem projectionAssignmentToAlg_idempotent {n : ℕ} (P : ProjectionAssignment n) :
    IsIdempotentElem (projectionAssignmentToAlg P) := by
  rw [IsIdempotentElem]
  funext w
  simpa [projectionAssignmentToAlg, IsIdempotentElem] using
    KreinSector.toAlg_idempotent (P w)

/-- Pointwise meet evaluates to pointwise multiplication of split projectors. -/
theorem projectionAssignmentToAlg_inf_eq_mul {n : ℕ}
    (P Q : ProjectionAssignment n) :
    projectionAssignmentToAlg (P ⊓ Q) =
      projectionAssignmentToAlg P * projectionAssignmentToAlg Q := by
  funext w
  change KreinSector.toAlg (P w ⊓ Q w) = KreinSector.toAlg (P w) * KreinSector.toAlg (Q w)
  exact KreinSector.toAlg_inf_eq_mul (P w) (Q w)

/-- Pointwise join evaluates to the Boolean idempotent formula `p + q - p*q`. -/
theorem projectionAssignmentToAlg_sup_eq_add_sub_mul {n : ℕ}
    (P Q : ProjectionAssignment n) :
    projectionAssignmentToAlg (P ⊔ Q) =
      projectionAssignmentToAlg P + projectionAssignmentToAlg Q -
        projectionAssignmentToAlg P * projectionAssignmentToAlg Q := by
  funext w
  change KreinSector.toAlg (P w ⊔ Q w) =
    KreinSector.toAlg (P w) + KreinSector.toAlg (Q w) -
      KreinSector.toAlg (P w) * KreinSector.toAlg (Q w)
  exact KreinSector.toAlg_sup_eq_add_sub_mul (P w) (Q w)

/-- Pointwise complement evaluates to `1 - p`. -/
theorem projectionAssignmentToAlg_compl_eq_one_sub {n : ℕ}
    (P : ProjectionAssignment n) :
    projectionAssignmentToAlg Pᶜ = 1 - projectionAssignmentToAlg P := by
  funext w
  change KreinSector.toAlg (P w)ᶜ = 1 - KreinSector.toAlg (P w)
  exact KreinSector.toAlg_compl_eq_one_sub (P w)

/-- The elementary sector assignment supported at a single Cantor word. -/
def elementaryProjectionAssignment {n : ℕ}
    (w : BinaryWord n) (k : KreinSector) : ProjectionAssignment n :=
  fun v => if v = w then k else ⊥

@[simp] theorem elementaryProjectionAssignment_self {n : ℕ}
    (w : BinaryWord n) (k : KreinSector) :
    elementaryProjectionAssignment w k w = k := by
  simp [elementaryProjectionAssignment]

@[simp] theorem elementaryProjectionAssignment_of_ne {n : ℕ}
    {v w : BinaryWord n} (h : v ≠ w) (k : KreinSector) :
    elementaryProjectionAssignment w k v = ⊥ := by
  simp [elementaryProjectionAssignment, h]

/-- The elementary finite sector projector is idempotent in the function algebra. -/
theorem elementaryProjectionAssignment_idempotent {n : ℕ}
    (w : BinaryWord n) (k : KreinSector) :
    IsIdempotentElem (projectionAssignmentToAlg (elementaryProjectionAssignment w k)) :=
  projectionAssignmentToAlg_idempotent _

/-! ## 6. Explicit Cantor-Krein sector projectors -/

/-- The Cantor cylinder idempotent lifted to the local split-Clifford algebra. -/
noncomputable def cantorCylinderAlgFactor {n : ℕ} (w : BinaryWord n) : BinaryWord n → Alg :=
  cylinderIndicator Alg w

/-- Constant local Krein projector over a finite Cantor level. -/
noncomputable def constantKreinProjector {n : ℕ} (k : KreinSector) : BinaryWord n → Alg :=
  fun _ => KreinSector.toAlg k

/--
Concrete finite-function model of the combined sector projector
`E_{n,w,k} = e_{n,w} · p_k`.
-/
noncomputable def cantorKreinSectorProjector {n : ℕ}
    (w : BinaryWord n) (k : KreinSector) : BinaryWord n → Alg :=
  cantorCylinderAlgFactor w * constantKreinProjector k

@[simp] theorem cantorCylinderAlgFactor_apply_self {n : ℕ}
    (w : BinaryWord n) :
    cantorCylinderAlgFactor w w = (1 : Alg) := by
  simp [cantorCylinderAlgFactor, cylinderIndicator, cylinder]

@[simp] theorem cantorCylinderAlgFactor_apply_of_ne {n : ℕ}
    {v w : BinaryWord n} (h : v ≠ w) :
    cantorCylinderAlgFactor w v = (0 : Alg) := by
  simp [cantorCylinderAlgFactor, cylinderIndicator, cylinder, h]

@[simp] theorem constantKreinProjector_apply {n : ℕ}
    (k : KreinSector) (v : BinaryWord n) :
    constantKreinProjector k v = KreinSector.toAlg k :=
  rfl

@[simp] theorem cantorKreinSectorProjector_apply_self {n : ℕ}
    (w : BinaryWord n) (k : KreinSector) :
    cantorKreinSectorProjector w k w = KreinSector.toAlg k := by
  simp [cantorKreinSectorProjector]

@[simp] theorem cantorKreinSectorProjector_apply_of_ne {n : ℕ}
    {v w : BinaryWord n} (h : v ≠ w) (k : KreinSector) :
    cantorKreinSectorProjector w k v = 0 := by
  simp [cantorKreinSectorProjector, h]

/--
The explicit `χ_w · p_k` projector is the same finite-function object as the
elementary pointwise sector assignment.
-/
theorem cantorKreinSectorProjector_eq_projectionAssignmentToAlg {n : ℕ}
    (w : BinaryWord n) (k : KreinSector) :
    cantorKreinSectorProjector w k =
      projectionAssignmentToAlg (elementaryProjectionAssignment w k) := by
  funext v
  by_cases h : v = w
  · rw [h]
    simp [cantorKreinSectorProjector, projectionAssignmentToAlg]
  · calc
      cantorKreinSectorProjector w k v = 0 := by
        simp [cantorKreinSectorProjector, h]
      _ = projectionAssignmentToAlg (elementaryProjectionAssignment w k) v := by
        simp [projectionAssignmentToAlg, elementaryProjectionAssignment, h, KreinSector.toAlg]

/-- Combined Cantor-Krein sector projectors are idempotent. -/
theorem cantorKreinSectorProjector_idempotent {n : ℕ}
    (w : BinaryWord n) (k : KreinSector) :
    IsIdempotentElem (cantorKreinSectorProjector w k) := by
  rw [cantorKreinSectorProjector_eq_projectionAssignmentToAlg]
  exact elementaryProjectionAssignment_idempotent w k

/-- Distinct Cantor cells give orthogonal combined sector projectors. -/
theorem cantorKreinSectorProjector_mul_eq_zero_of_ne {n : ℕ}
    {w₁ w₂ : BinaryWord n} (h : w₁ ≠ w₂) (k₁ k₂ : KreinSector) :
    cantorKreinSectorProjector w₁ k₁ * cantorKreinSectorProjector w₂ k₂ = 0 := by
  funext v
  by_cases h₁ : v = w₁
  · rw [h₁]
    simp [cantorKreinSectorProjector, h]
  · simp [cantorKreinSectorProjector, h₁]

/-- Distinct elementary Cantor cells give orthogonal algebraic projectors. -/
theorem elementaryProjectionAssignment_mul_eq_zero_of_ne {n : ℕ}
    {w₁ w₂ : BinaryWord n} (h : w₁ ≠ w₂) (k₁ k₂ : KreinSector) :
    projectionAssignmentToAlg (elementaryProjectionAssignment w₁ k₁) *
      projectionAssignmentToAlg (elementaryProjectionAssignment w₂ k₂) = 0 := by
  funext v
  by_cases h₁ : v = w₁
  · change KreinSector.toAlg (elementaryProjectionAssignment w₁ k₁ v) *
        KreinSector.toAlg (elementaryProjectionAssignment w₂ k₂ v) = 0
    rw [h₁, elementaryProjectionAssignment_self, elementaryProjectionAssignment_of_ne h]
    change KreinSector.toAlg k₁ * (0 : Alg) = 0
    simp
  · change KreinSector.toAlg (elementaryProjectionAssignment w₁ k₁ v) *
        KreinSector.toAlg (elementaryProjectionAssignment w₂ k₂ v) = 0
    rw [elementaryProjectionAssignment_of_ne h₁]
    change (0 : Alg) * KreinSector.toAlg (elementaryProjectionAssignment w₂ k₂ v) = 0
    simp

/-- Refinement pulls a pointwise sector assignment back along `truncateWord`. -/
def refineProjectionAssignment {n : ℕ}
    (P : ProjectionAssignment n) : ProjectionAssignment (n + 1) :=
  fun v => P (truncateWord v)

/-- Coarse-graining is the right adjoint: meet the two children above each parent. -/
def coarseProjectionAssignment {n : ℕ}
    (Q : ProjectionAssignment (n + 1)) : ProjectionAssignment n :=
  fun w => Q (leftChild w) ⊓ Q (rightChild w)

/--
Refining an elementary Cantor-Krein sector gives the join of its two child
sectors with the same Krein chirality.
-/
theorem refineProjectionAssignment_elementary {n : ℕ}
    (w : BinaryWord n) (k : KreinSector) :
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
The concrete combined projector refines by splitting its Cantor cylinder into
the two child projectors with the same local Krein sector.
-/
theorem cantorKreinSectorProjector_refinement {n : ℕ}
    (w : BinaryWord n) (k : KreinSector) :
    projectionAssignmentToAlg (refineProjectionAssignment (elementaryProjectionAssignment w k)) =
      cantorKreinSectorProjector (leftChild w) k +
        cantorKreinSectorProjector (rightChild w) k := by
  rw [refineProjectionAssignment_elementary,
    projectionAssignmentToAlg_sup_eq_add_sub_mul]
  rw [← cantorKreinSectorProjector_eq_projectionAssignmentToAlg,
    ← cantorKreinSectorProjector_eq_projectionAssignmentToAlg]
  have hzero :
      cantorKreinSectorProjector (leftChild w) k *
          cantorKreinSectorProjector (rightChild w) k = 0 :=
    cantorKreinSectorProjector_mul_eq_zero_of_ne (leftChild_ne_rightChild w w) k k
  simp [hzero]

/--
The join of the two elementary child sectors coarse-grains back to the parent
elementary sector.
-/
theorem coarseProjectionAssignment_elementary_children {n : ℕ}
    (w : BinaryWord n) (k : KreinSector) :
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
    (P : ι → ProjectionAssignment n) :
    refineProjectionAssignment (⨆ i, P i) = ⨆ i, refineProjectionAssignment (P i) :=
  (projectionAssignment_galoisConnection n).l_iSup

/-- Projection coarse-graining preserves arbitrary meets. -/
theorem coarseProjectionAssignment_iInf {n : ℕ} {ι : Sort*}
    (Q : ι → ProjectionAssignment (n + 1)) :
    coarseProjectionAssignment (⨅ i, Q i) = ⨅ i, coarseProjectionAssignment (Q i) :=
  (projectionAssignment_galoisConnection n).u_iInf

end SectorLattice
