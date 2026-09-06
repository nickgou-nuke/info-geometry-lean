import Mathlib.Tactic
import InfoGeometry.Lie.Pin55KreinConformalBridge
import InfoGeometry.Lie.SplitOctonionNonmultiplicativity
import InfoGeometry.Clifford.SpinorRep
import InfoGeometry.Algebra.Zorn.Basic
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

set_option linter.unusedVariables false

/-!
# Pin(5,5) Krein Spinor Tower Bridge

This module establishes the divide-and-conquer tensor tower bridge between:
1. The 8D non-associative Zorn split-octonion algebra `CanonicalZorn`.
2. The 16D Bi-Split-Octonion Clifford module `BiSplitOctonions ≅ S₊ ⊕ S₋`.
3. The off-diagonal chiral representation mechanism reconciling Clifford actions with octonionic left multiplication.

All proofs are complete in native Lean 4 with 0 sorrys and 0 custom axioms.
-/

namespace InfoGeometry.Lie.Pin55SpinorTower

noncomputable section

open InfoGeometry.Lie.Pin55KreinConformalBridge
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.SplitOctonionNonmultiplicativity
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.CliffordTower

/-! ## 1. 16D Chiral Half-Spinor Projectors -/

/-- Positive chiral half-spinor projector `P₊(p, q) = p` on `BiSplitOctonions`. -/
def chiralProjPlus : BiSplitOctonions →ₗ[ℝ] CanonicalZorn where
  toFun pq := pq.1
  map_add' x y := rfl
  map_smul' c x := rfl

/-- Negative chiral half-spinor projector `P₋(p, q) = q` on `BiSplitOctonions`. -/
def chiralProjMinus : BiSplitOctonions →ₗ[ℝ] CanonicalZorn where
  toFun pq := pq.2
  map_add' x y := rfl
  map_smul' c x := rfl

/-- Embedding a split octonion into the positive chiral sector `S₊`. -/
def chiralEmbedPlus : CanonicalZorn →ₗ[ℝ] BiSplitOctonions where
  toFun Z := (Z, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Embedding a split octonion into the negative chiral sector `S₋`. -/
def chiralEmbedMinus : CanonicalZorn →ₗ[ℝ] BiSplitOctonions where
  toFun Z := (0, Z)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp] theorem chiralProjPlus_embedPlus (Z : CanonicalZorn) :
    chiralProjPlus (chiralEmbedPlus Z) = Z := rfl

@[simp] theorem chiralProjMinus_embedMinus (Z : CanonicalZorn) :
    chiralProjMinus (chiralEmbedMinus Z) = Z := rfl

@[simp] theorem chiralProjPlus_embedMinus (Z : CanonicalZorn) :
    chiralProjPlus (chiralEmbedMinus Z) = 0 := rfl

@[simp] theorem chiralProjMinus_embedPlus (Z : CanonicalZorn) :
    chiralProjMinus (chiralEmbedPlus Z) = 0 := rfl

/-- Complete reconstruction of a bi-split-octonion from its chiral half-spinor components. -/
theorem chiral_sum_projection (pq : BiSplitOctonions) :
    chiralEmbedPlus (chiralProjPlus pq) + chiralEmbedMinus (chiralProjMinus pq) = pq := by
  rcases pq with ⟨p, q⟩
  ext <;> simp [chiralEmbedPlus, chiralEmbedMinus, chiralProjPlus, chiralProjMinus]

/-! ## 2. Chiral Off-Diagonal Action of Split Octonions -/

/-- The Clifford action on `S₋` maps into `S₊` via split-octonion left multiplication. -/
theorem zornBiAction_chiralMinus_to_plus (Z W : CanonicalZorn) :
    chiralProjPlus (zornBiAction Z (chiralEmbedMinus W)) = Z * W := by
  dsimp [chiralProjPlus, chiralEmbedMinus, zornBiAction]

/-- The Clifford action on `S₊` maps into `S₋` via conjugate split-octonion left multiplication. -/
theorem zornBiAction_chiralPlus_to_minus (Z W : CanonicalZorn) :
    chiralProjMinus (zornBiAction Z (chiralEmbedPlus W)) = - (zornConj Z * W) := by
  dsimp [chiralProjMinus, chiralEmbedPlus, zornBiAction]

/-- The Clifford action on `S₊` vanishes under positive chiral projection (pure off-diagonal action). -/
theorem zornBiAction_diag_plus_vanishes (Z W : CanonicalZorn) :
    chiralProjPlus (zornBiAction Z (chiralEmbedPlus W)) = 0 := by
  change Z * 0 = 0
  exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero Z

/-- The Clifford action on `S₋` vanishes under negative chiral projection (pure off-diagonal action). -/
theorem zornBiAction_diag_minus_vanishes (Z W : CanonicalZorn) :
    chiralProjMinus (zornBiAction Z (chiralEmbedMinus W)) = 0 := by
  change - (zornConj Z * 0) = 0
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero, neg_zero]

/-! ## 3. The 16D Clifford Squaring Relation -/

/-- On the 16D bi-split-octonionic carrier, `zornBiAction` satisfies the Clifford squaring law. -/
theorem zornBiAction_clifford_law (Z : CanonicalZorn) (pq : BiSplitOctonions) :
    zornBiAction Z (zornBiAction Z pq) = - InfoGeometry.Algebra.Zorn.ZornMatrix.detZ Z • pq :=
  zornBiAction_sq Z pq

end

end InfoGeometry.Lie.Pin55SpinorTower
