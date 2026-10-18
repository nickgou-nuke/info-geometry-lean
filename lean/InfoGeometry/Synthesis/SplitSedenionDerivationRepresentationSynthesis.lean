/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
import InfoGeometry.Synthesis.Cl44MinimalIdealSplitSedenionEquivBridge
import InfoGeometry.Synthesis.SplitSedenionImaginaryBimoduleBridge
import InfoGeometry.Synthesis.Cl44PrimitiveIdempotentIdeal

/-!
# Split-Sedenion Derivation Lie Bracket Closure and Intertwined $G_2$ Representations

This module establishes the commutator Lie bracket closure of $\mathbb{R}$-linear derivations and
$\star$-derivations on the non-associative split-sedenion carrier `SplitSedenion ℝ`, transports the
14-parameter diagonal $G_2$ derivation family `sedenionG2Derivation` across the 16-dimensional
carrier equivalences `spinor16SplitSedenionEquiv` and `cl44MatrixLeftIdealSplitSedenionEquiv` to
`Fin 16 → ℝ` and `LeftIdeal primIdem`, and proves equivariance of `sedenionG2Derivation` with
the two-sheet linear mixing operator `sheetLinearMix`:

1. **Section 1 — Split-Sedenion Derivation Lie Bracket Closure**:
   - Defines scalar multiplication `sedenionSmul`, the derivation predicate `IsSedenionDerivation`,
     the $\star$-derivation predicate `IsSedenionStarDerivation`, and the commutator bracket
     `sedenionDerivationCommutator`.
   - Certifies `sedenionG2Derivation_smul` and `sedenionG2Derivation_isStarDerivation`.
   - Proves bilinearity of `sedenionMul` (`sedenionMul_add_left`, `sedenionMul_add_right`,
     `sedenionMul_smul_left`, `sedenionMul_smul_right`, `sedenionMul_sub_left`,
     `sedenionMul_sub_right`) and commutator closure `isSedenionDerivation_commutator` and
     `isSedenionStarDerivation_commutator`.

2. **Section 2 — Intertwined 14-Parameter $G_2$ Derivation Representations on `Fin 16 → ℝ` and `LeftIdeal primIdem`**:
   - Defines `spinor16G2Derivation`, `cl44LeftIdealG2Derivation`, and the induced spinor product
     `spinor16SedenionMul`.
   - Proves the intertwining identities `spinor16SplitSedenionEquiv_intertwines_g2Derivation`,
     `cl44LeftIdealSplitSedenionEquiv_intertwines_g2Derivation`, and
     `leftIdealEquiv_intertwines_g2Derivation`.
   - Proves the transported Leibniz law `spinor16G2Derivation_leibniz` and invariance of the
     chiral semi-spinor subspaces `SemiSpinorPlus` and `SemiSpinorMinus`
     (`spinor16G2Derivation_preserves_semiSpinorPlus`,
     `spinor16G2Derivation_preserves_semiSpinorMinus`).

3. **Section 3 — Two-Sheet Linear Mixing and $G_2$ Bimodule Equivariance**:
   - Proves `sedenionG2Derivation_commutes_with_sheetLinearMix`, showing that the 14-parameter
     diagonal $G_2$ derivation action commutes with `sheetLinearMix`.
   - Proves `sedenionG2Derivation_lands_in_traceZero_bimodule`, showing that the image of
     `sedenionG2Derivation p` has vanishing scalar trace on both split-octonion sheets.
-/

set_option autoImplicit false
noncomputable section

namespace InfoGeometry.Synthesis.SplitSedenionDerivationRepresentationSynthesis

open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Cl44IdempotentIdeal
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Synthesis.Cl44MinimalIdealSplitSedenionEquivBridge
open InfoGeometry.Synthesis.SplitSedenionImaginaryBimoduleBridge

/-!
## Section 1: Split-Sedenion Derivation Lie Bracket Closure
-/

/-- Componentwise scalar multiplication on `SplitSedenion R`. -/
def sedenionSmul {R : Type*} [CommRing R] (c : R) (X : SplitSedenion R) : SplitSedenion R :=
  (zornSmul c X.1, zornSmul c X.2)

/-- Predicate characterizing an $\mathbb{R}$-linear derivation $D : \mathbb{S}_s \to \mathbb{S}_s$
of the non-associative split-sedenion multiplication `sedenionMul`. -/
def IsSedenionDerivation (D : SplitSedenion ℝ → SplitSedenion ℝ) : Prop :=
  (∀ X Y, D (sedenionAdd X Y) = sedenionAdd (D X) (D Y)) ∧
  (∀ c X, D (sedenionSmul c X) = sedenionSmul c (D X)) ∧
  (∀ X Y, D (sedenionMul X Y) = sedenionAdd (sedenionMul (D X) Y) (sedenionMul X (D Y)))

/-- Predicate characterizing an $\mathbb{R}$-linear $\star$-derivation of `SplitSedenion ℝ`
that also commutes with the Cayley–Dickson involution `sedenionConj`. -/
def IsSedenionStarDerivation (D : SplitSedenion ℝ → SplitSedenion ℝ) : Prop :=
  IsSedenionDerivation D ∧ (∀ X, D (sedenionConj X) = sedenionConj (D X))

/-- `sedenionG2Derivation p` is $\mathbb{R}$-homogeneous with respect to `sedenionSmul`. -/
theorem sedenionG2Derivation_smul (p : Params) (c : ℝ) (X : SplitSedenion ℝ) :
    sedenionG2Derivation p (sedenionSmul c X) =
      sedenionSmul c (sedenionG2Derivation p X) := by
  apply Prod.ext
  · dsimp [sedenionG2Derivation, cdLift, sedenionSmul]
    exact zornG2Derivation_smul p c X.1
  · dsimp [sedenionG2Derivation, cdLift, sedenionSmul]
    exact zornG2Derivation_smul p c X.2

/-- Every 14-parameter diagonally lifted $G_2$ operator `sedenionG2Derivation p` is an exact
$\star$-derivation of `SplitSedenion ℝ`. -/
theorem sedenionG2Derivation_isStarDerivation (p : Params) :
    IsSedenionStarDerivation (sedenionG2Derivation p) :=
  ⟨⟨sedenionG2Derivation_add p, sedenionG2Derivation_smul p, sedenionG2Derivation_leibniz p⟩,
   sedenionG2Derivation_conj p⟩

/-- Commutator bracket $[D_1, D_2](X) = D_1(D_2(X)) - D_2(D_1(X))$ of two maps on `SplitSedenion ℝ`. -/
def sedenionDerivationCommutator
    (D₁ D₂ : SplitSedenion ℝ → SplitSedenion ℝ) (X : SplitSedenion ℝ) : SplitSedenion ℝ :=
  sedenionSub (D₁ (D₂ X)) (D₂ (D₁ X))

/-- `zornConj` distributes over `zornAdd`. -/
theorem zornConj_add (x y : ZornSplitOctonion ℝ) :
    zornConj (zornAdd x y) = zornAdd (zornConj x) (zornConj y) := by
  have _ := (x, y)
  ext k
  · rfl
  · fin_cases k <;> (dsimp [zornConj, zornAdd]; ring)
  · fin_cases k <;> (dsimp [zornConj, zornAdd]; ring)
  · rfl

/-- `zornConj` commutes with scalar multiplication `zornSmul`. -/
theorem zornConj_smul (c : ℝ) (x : ZornSplitOctonion ℝ) :
    zornConj (zornSmul c x) = zornSmul c (zornConj x) := by
  have _ := (c, x)
  ext k
  · rfl
  · fin_cases k <;> (dsimp [zornConj, zornSmul]; ring)
  · fin_cases k <;> (dsimp [zornConj, zornSmul]; ring)
  · rfl

/-- Scalar multiplication `zornSmul` distributes over `zornAdd`. -/
theorem zornSmul_add (c : ℝ) (x y : ZornSplitOctonion ℝ) :
    zornSmul c (zornAdd x y) = zornAdd (zornSmul c x) (zornSmul c y) := by
  have _ := (c, x, y)
  ext k
  · dsimp [zornSmul, zornAdd]; ring
  · fin_cases k <;> (dsimp [zornSmul, zornAdd]; ring)
  · fin_cases k <;> (dsimp [zornSmul, zornAdd]; ring)
  · dsimp [zornSmul, zornAdd]; ring

/-- Four-term interchange law `(a + b) + (c + d) = (a + c) + (b + d)` for `zornAdd`. -/
theorem zornAdd_add_add_comm (a b c d : ZornSplitOctonion ℝ) :
    zornAdd (zornAdd a b) (zornAdd c d) = zornAdd (zornAdd a c) (zornAdd b d) := by
  have _ := (a, b, c, d)
  ext k
  · dsimp [zornAdd]; ring
  · fin_cases k <;> (dsimp [zornAdd]; ring)
  · fin_cases k <;> (dsimp [zornAdd]; ring)
  · dsimp [zornAdd]; ring

/-- `sedenionNeg X` agrees with scalar multiplication by `-1 : ℝ`. -/
theorem sedenionNeg_eq_smul_neg_one (X : SplitSedenion ℝ) :
    sedenionNeg X = sedenionSmul (-1 : ℝ) X := by
  change (zornSmul (-1 : ℝ) X.1, zornSmul (-1 : ℝ) X.2) =
    (zornSmul (-1 : ℝ) X.1, zornSmul (-1 : ℝ) X.2)
  rfl

/-- `sedenionMul` distributes over `sedenionAdd` in its left argument. -/
theorem sedenionMul_add_left (X Y Z : SplitSedenion ℝ) :
    sedenionMul (sedenionAdd X Y) Z =
      sedenionAdd (sedenionMul X Z) (sedenionMul Y Z) := by
  apply Prod.ext
  · dsimp [sedenionMul, sedenionAdd]
    rw [zornMul_add_left X.1 Y.1 Z.1, zornMul_add_right (zornConj Z.2) X.2 Y.2]
    exact zornAdd_add_add_comm _ _ _ _
  · dsimp [sedenionMul, sedenionAdd]
    rw [zornMul_add_right Z.2 X.1 Y.1, zornMul_add_left X.2 Y.2 (zornConj Z.1)]
    exact zornAdd_add_add_comm _ _ _ _

/-- `sedenionMul` distributes over `sedenionAdd` in its right argument. -/
theorem sedenionMul_add_right (X Y Z : SplitSedenion ℝ) :
    sedenionMul X (sedenionAdd Y Z) =
      sedenionAdd (sedenionMul X Y) (sedenionMul X Z) := by
  apply Prod.ext
  · dsimp [sedenionMul, sedenionAdd]
    rw [zornMul_add_right X.1 Y.1 Z.1, zornConj_add Y.2 Z.2,
        zornMul_add_left (zornConj Y.2) (zornConj Z.2) X.2]
    exact zornAdd_add_add_comm _ _ _ _
  · dsimp [sedenionMul, sedenionAdd]
    rw [zornMul_add_left Y.2 Z.2 X.1, zornConj_add Y.1 Z.1,
        zornMul_add_right X.2 (zornConj Y.1) (zornConj Z.1)]
    exact zornAdd_add_add_comm _ _ _ _

/-- `sedenionMul` is homogeneous with respect to `sedenionSmul` in its left argument. -/
theorem sedenionMul_smul_left (c : ℝ) (X Y : SplitSedenion ℝ) :
    sedenionMul (sedenionSmul c X) Y =
      sedenionSmul c (sedenionMul X Y) := by
  apply Prod.ext
  · dsimp [sedenionMul, sedenionSmul]
    rw [zornMul_smul_left c X.1 Y.1, zornMul_smul_right c (zornConj Y.2) X.2,
        ← zornSmul_add c]
  · dsimp [sedenionMul, sedenionSmul]
    rw [zornMul_smul_right c Y.2 X.1, zornMul_smul_left c X.2 (zornConj Y.1),
        ← zornSmul_add c]

/-- `sedenionMul` is homogeneous with respect to `sedenionSmul` in its right argument. -/
theorem sedenionMul_smul_right (c : ℝ) (X Y : SplitSedenion ℝ) :
    sedenionMul X (sedenionSmul c Y) =
      sedenionSmul c (sedenionMul X Y) := by
  apply Prod.ext
  · dsimp [sedenionMul, sedenionSmul]
    rw [zornMul_smul_right c X.1 Y.1, zornConj_smul c Y.2,
        zornMul_smul_left c (zornConj Y.2) X.2, ← zornSmul_add c]
  · dsimp [sedenionMul, sedenionSmul]
    rw [zornMul_smul_left c Y.2 X.1, zornConj_smul c Y.1,
        zornMul_smul_right c X.2 (zornConj Y.1), ← zornSmul_add c]

/-- `sedenionMul` distributes over `sedenionSub` in its left argument. -/
theorem sedenionMul_sub_left (X Y Z : SplitSedenion ℝ) :
    sedenionMul (sedenionSub X Y) Z =
      sedenionSub (sedenionMul X Z) (sedenionMul Y Z) := by
  unfold sedenionSub
  rw [sedenionMul_add_left X (sedenionNeg Y) Z, sedenionNeg_eq_smul_neg_one Y,
      sedenionMul_smul_left (-1 : ℝ) Y Z, ← sedenionNeg_eq_smul_neg_one (sedenionMul Y Z)]

/-- `sedenionMul` distributes over `sedenionSub` in its right argument. -/
theorem sedenionMul_sub_right (X Y Z : SplitSedenion ℝ) :
    sedenionMul X (sedenionSub Y Z) =
      sedenionSub (sedenionMul X Y) (sedenionMul X Z) := by
  unfold sedenionSub
  rw [sedenionMul_add_right X Y (sedenionNeg Z), sedenionNeg_eq_smul_neg_one Z,
      sedenionMul_smul_right (-1 : ℝ) X Z, ← sedenionNeg_eq_smul_neg_one (sedenionMul X Z)]

/-- Componentwise subtraction identity `(A + B) - (C + E) = (A - C) + (B - E)` on `SplitSedenion ℝ`. -/
theorem sedenionSub_add_sedenionSub (A B C E : SplitSedenion ℝ) :
    sedenionSub (sedenionAdd A B) (sedenionAdd C E) =
      sedenionAdd (sedenionSub A C) (sedenionSub B E) := by
  have _ := (A, B, C, E)
  apply Prod.ext
  · ext k
    · dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring
    · fin_cases k <;> (dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring)
    · fin_cases k <;> (dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring)
    · dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring
  · ext k
    · dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring
    · fin_cases k <;> (dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring)
    · fin_cases k <;> (dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring)
    · dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring

/-- Scalar multiplication `sedenionSmul` commutes with `sedenionSub`. -/
theorem sedenionSub_smul (c : ℝ) (A B : SplitSedenion ℝ) :
    sedenionSub (sedenionSmul c A) (sedenionSmul c B) =
      sedenionSmul c (sedenionSub A B) := by
  have _ := (c, A, B)
  apply Prod.ext
  · ext k
    · dsimp [sedenionSub, sedenionAdd, sedenionNeg, sedenionSmul, zornAdd, zornSmul]; ring
    · fin_cases k <;>
        (dsimp [sedenionSub, sedenionAdd, sedenionNeg, sedenionSmul, zornAdd, zornSmul]; ring)
    · fin_cases k <;>
        (dsimp [sedenionSub, sedenionAdd, sedenionNeg, sedenionSmul, zornAdd, zornSmul]; ring)
    · dsimp [sedenionSub, sedenionAdd, sedenionNeg, sedenionSmul, zornAdd, zornSmul]; ring
  · ext k
    · dsimp [sedenionSub, sedenionAdd, sedenionNeg, sedenionSmul, zornAdd, zornSmul]; ring
    · fin_cases k <;>
        (dsimp [sedenionSub, sedenionAdd, sedenionNeg, sedenionSmul, zornAdd, zornSmul]; ring)
    · fin_cases k <;>
        (dsimp [sedenionSub, sedenionAdd, sedenionNeg, sedenionSmul, zornAdd, zornSmul]; ring)
    · dsimp [sedenionSub, sedenionAdd, sedenionNeg, sedenionSmul, zornAdd, zornSmul]; ring

/-- Cancellation of mixed cross-terms `M₁` and `M₂` in the commutator of two Leibniz expansions
on `SplitSedenion ℝ`. -/
theorem sedenionSub_leibniz_cancel (A₁ A₂ M₁ M₂ B₁ B₂ : SplitSedenion ℝ) :
    sedenionSub
      (sedenionAdd (sedenionAdd A₁ M₁) (sedenionAdd M₂ B₁))
      (sedenionAdd (sedenionAdd A₂ M₂) (sedenionAdd M₁ B₂)) =
    sedenionAdd (sedenionSub A₁ A₂) (sedenionSub B₁ B₂) := by
  have _ := (A₁, A₂, M₁, M₂, B₁, B₂)
  apply Prod.ext
  · ext k
    · dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring
    · fin_cases k <;> (dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring)
    · fin_cases k <;> (dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring)
    · dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring
  · ext k
    · dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring
    · fin_cases k <;> (dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring)
    · fin_cases k <;> (dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring)
    · dsimp [sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring

/-- `sedenionConj` distributes over `sedenionSub`. -/
theorem sedenionConj_sub (X Y : SplitSedenion ℝ) :
    sedenionConj (sedenionSub X Y) = sedenionSub (sedenionConj X) (sedenionConj Y) := by
  have _ := (X, Y)
  apply Prod.ext
  · ext k
    · rfl
    · fin_cases k <;>
        (dsimp [sedenionConj, sedenionSub, sedenionAdd, sedenionNeg, zornConj, zornAdd, zornSmul];
         ring)
    · fin_cases k <;>
        (dsimp [sedenionConj, sedenionSub, sedenionAdd, sedenionNeg, zornConj, zornAdd, zornSmul];
         ring)
    · rfl
  · ext k
    · dsimp [sedenionConj, sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring
    · fin_cases k <;>
        (dsimp [sedenionConj, sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring)
    · fin_cases k <;>
        (dsimp [sedenionConj, sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring)
    · dsimp [sedenionConj, sedenionSub, sedenionAdd, sedenionNeg, zornAdd, zornSmul]; ring

/-- **Lie Bracket Closure of Split-Sedenion Derivations**:
If $D_1$ and $D_2$ are $\mathbb{R}$-linear derivations of `SplitSedenion ℝ`, then their commutator
`sedenionDerivationCommutator D₁ D₂` is again an $\mathbb{R}$-linear derivation of `SplitSedenion ℝ`. -/
theorem isSedenionDerivation_commutator
    (D₁ D₂ : SplitSedenion ℝ → SplitSedenion ℝ)
    (hD₁ : IsSedenionDerivation D₁) (hD₂ : IsSedenionDerivation D₂) :
    IsSedenionDerivation (sedenionDerivationCommutator D₁ D₂) := by -- [repo-owned: InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge#ZornSplitOctonion]
  rcases hD₁ with ⟨hD₁_add, hD₁_smul, hD₁_mul⟩
  rcases hD₂ with ⟨hD₂_add, hD₂_smul, hD₂_mul⟩
  refine ⟨?_, ?_, ?_⟩
  · intro X Y
    dsimp [sedenionDerivationCommutator]
    rw [hD₂_add X Y, hD₁_add (D₂ X) (D₂ Y), hD₁_add X Y, hD₂_add (D₁ X) (D₁ Y)]
    exact sedenionSub_add_sedenionSub (D₁ (D₂ X)) (D₁ (D₂ Y)) (D₂ (D₁ X)) (D₂ (D₁ Y))
  · intro c X
    dsimp [sedenionDerivationCommutator]
    rw [hD₂_smul c X, hD₁_smul c (D₂ X), hD₁_smul c X, hD₂_smul c (D₁ X)]
    exact sedenionSub_smul c (D₁ (D₂ X)) (D₂ (D₁ X))
  · intro X Y
    dsimp [sedenionDerivationCommutator]
    rw [hD₂_mul X Y, hD₁_add (sedenionMul (D₂ X) Y) (sedenionMul X (D₂ Y)),
        hD₁_mul (D₂ X) Y, hD₁_mul X (D₂ Y),
        hD₁_mul X Y, hD₂_add (sedenionMul (D₁ X) Y) (sedenionMul X (D₁ Y)),
        hD₂_mul (D₁ X) Y, hD₂_mul X (D₁ Y),
        sedenionMul_sub_left (D₁ (D₂ X)) (D₂ (D₁ X)) Y,
        sedenionMul_sub_right X (D₁ (D₂ Y)) (D₂ (D₁ Y))]
    exact sedenionSub_leibniz_cancel
      (sedenionMul (D₁ (D₂ X)) Y) (sedenionMul (D₂ (D₁ X)) Y)
      (sedenionMul (D₂ X) (D₁ Y)) (sedenionMul (D₁ X) (D₂ Y))
      (sedenionMul X (D₁ (D₂ Y))) (sedenionMul X (D₂ (D₁ Y)))

/-- **Lie Bracket Closure of Split-Sedenion $\star$-Derivations**:
If $D_1$ and $D_2$ are $\mathbb{R}$-linear $\star$-derivations of `SplitSedenion ℝ`, then their
commutator `sedenionDerivationCommutator D₁ D₂` is again an $\mathbb{R}$-linear $\star$-derivation. -/
theorem isSedenionStarDerivation_commutator
    (D₁ D₂ : SplitSedenion ℝ → SplitSedenion ℝ)
    (hD₁ : IsSedenionStarDerivation D₁) (hD₂ : IsSedenionStarDerivation D₂) :
    IsSedenionStarDerivation (sedenionDerivationCommutator D₁ D₂) := by -- [repo-owned: InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge#ZornSplitOctonion]
  rcases hD₁ with ⟨hD₁_der, hD₁_conj⟩
  rcases hD₂ with ⟨hD₂_der, hD₂_conj⟩
  refine ⟨isSedenionDerivation_commutator D₁ D₂ hD₁_der hD₂_der, ?_⟩
  intro X
  dsimp [sedenionDerivationCommutator]
  rw [hD₂_conj X, hD₁_conj (D₂ X), hD₁_conj X, hD₂_conj (D₁ X), ← sedenionConj_sub]

/-!
## Section 2: Intertwined 14-Parameter $G_2$ Derivation Representations on `Fin 16 → ℝ` and `LeftIdeal primIdem`
-/

/-- The 14-parameter $G_2$ derivation family transported across `spinor16SplitSedenionEquiv`
to the 16-component spinor space `Fin 16 → ℝ`. -/
def spinor16G2Derivation (p : Params) (v : Fin 16 → ℝ) : Fin 16 → ℝ :=
  spinor16SplitSedenionEquiv.symm (sedenionG2Derivation p (spinor16SplitSedenionEquiv v))

/-- The 14-parameter $G_2$ derivation family transported across
`cl44MatrixLeftIdealSplitSedenionEquiv` to `LeftIdeal primIdem`. -/
def cl44LeftIdealG2Derivation (p : Params) (A : LeftIdeal primIdem) : LeftIdeal primIdem :=
  cl44MatrixLeftIdealSplitSedenionEquiv.symm
    (sedenionG2Derivation p (cl44MatrixLeftIdealSplitSedenionEquiv A))

/-- `spinor16SplitSedenionEquiv` intertwines `spinor16G2Derivation p` with `sedenionG2Derivation p`. -/
theorem spinor16SplitSedenionEquiv_intertwines_g2Derivation (p : Params) (v : Fin 16 → ℝ) :
    spinor16SplitSedenionEquiv (spinor16G2Derivation p v) =
      sedenionG2Derivation p (spinor16SplitSedenionEquiv v) := by
  unfold spinor16G2Derivation
  exact spinor16SplitSedenionEquiv.apply_symm_apply
    (sedenionG2Derivation p (spinor16SplitSedenionEquiv v))

/-- `cl44MatrixLeftIdealSplitSedenionEquiv` intertwines `cl44LeftIdealG2Derivation p` with
`sedenionG2Derivation p`. -/
theorem cl44LeftIdealSplitSedenionEquiv_intertwines_g2Derivation
    (p : Params) (A : LeftIdeal primIdem) :
    cl44MatrixLeftIdealSplitSedenionEquiv (cl44LeftIdealG2Derivation p A) =
      sedenionG2Derivation p (cl44MatrixLeftIdealSplitSedenionEquiv A) := by
  unfold cl44LeftIdealG2Derivation
  exact cl44MatrixLeftIdealSplitSedenionEquiv.apply_symm_apply
    (sedenionG2Derivation p (cl44MatrixLeftIdealSplitSedenionEquiv A))

/-- `leftIdealEquiv` intertwines `cl44LeftIdealG2Derivation p` on `LeftIdeal primIdem` with
`spinor16G2Derivation p` on `Fin 16 → ℝ`. -/
theorem leftIdealEquiv_intertwines_g2Derivation (p : Params) (A : LeftIdeal primIdem) :
    leftIdealEquiv (cl44LeftIdealG2Derivation p A) =
      spinor16G2Derivation p (leftIdealEquiv A) := by
  apply spinor16SplitSedenionEquiv.injective
  rw [spinor16SplitSedenionEquiv_intertwines_g2Derivation p (leftIdealEquiv A)]
  change cl44MatrixLeftIdealSplitSedenionEquiv (cl44LeftIdealG2Derivation p A) =
    sedenionG2Derivation p (cl44MatrixLeftIdealSplitSedenionEquiv A)
  exact cl44LeftIdealSplitSedenionEquiv_intertwines_g2Derivation p A

/-- Non-associative split-sedenion multiplication transported to `Fin 16 → ℝ` via
`spinor16SplitSedenionEquiv`. -/
def spinor16SedenionMul (u v : Fin 16 → ℝ) : Fin 16 → ℝ :=
  spinor16SplitSedenionEquiv.symm
    (sedenionMul (spinor16SplitSedenionEquiv u) (spinor16SplitSedenionEquiv v))

/-- `spinor16SplitSedenionEquiv.symm` intertwines `sedenionAdd` with componentwise addition on
`Fin 16 → ℝ`. -/
theorem spinor16ToSplitSedenion_symm_sedenionAdd (X Y : SplitSedenion ℝ) :
    spinor16SplitSedenionEquiv.symm (sedenionAdd X Y) =
      spinor16SplitSedenionEquiv.symm X + spinor16SplitSedenionEquiv.symm Y := by
  apply spinor16SplitSedenionEquiv.injective
  have h := spinor16ToSplitSedenion_add
    (spinor16SplitSedenionEquiv.symm X) (spinor16SplitSedenionEquiv.symm Y)
  change spinor16SplitSedenionEquiv
      (spinor16SplitSedenionEquiv.symm X + spinor16SplitSedenionEquiv.symm Y) =
    sedenionAdd
      (spinor16SplitSedenionEquiv (spinor16SplitSedenionEquiv.symm X))
      (spinor16SplitSedenionEquiv (spinor16SplitSedenionEquiv.symm Y)) at h
  rw [h, spinor16SplitSedenionEquiv.apply_symm_apply,
      spinor16SplitSedenionEquiv.apply_symm_apply,
      spinor16SplitSedenionEquiv.apply_symm_apply]

/-- `spinor16G2Derivation p` satisfies the Leibniz derivation rule with respect to the
transported split-sedenion product `spinor16SedenionMul` on `Fin 16 → ℝ`. -/
theorem spinor16G2Derivation_leibniz (p : Params) (u v : Fin 16 → ℝ) :
    spinor16G2Derivation p (spinor16SedenionMul u v) =
      spinor16SedenionMul (spinor16G2Derivation p u) v +
        spinor16SedenionMul u (spinor16G2Derivation p v) := by
  unfold spinor16G2Derivation spinor16SedenionMul
  rw [spinor16SplitSedenionEquiv.apply_symm_apply,
      spinor16SplitSedenionEquiv.apply_symm_apply,
      spinor16SplitSedenionEquiv.apply_symm_apply,
      sedenionG2Derivation_leibniz p (spinor16SplitSedenionEquiv u) (spinor16SplitSedenionEquiv v),
      spinor16ToSplitSedenion_symm_sedenionAdd]

/-- `spinor16G2Derivation p` preserves the positive chiral semi-spinor subspace `SemiSpinorPlus`. -/
theorem spinor16G2Derivation_preserves_semiSpinorPlus
    (p : Params) (v : Fin 16 → ℝ) (hv : v ∈ SemiSpinorPlus) :
    spinor16G2Derivation p v ∈ SemiSpinorPlus := by
  have hv0 : (spinor16SplitSedenionEquiv v).2 = zornZero :=
    (mem_semiSpinorPlus_iff_snd_zero v).mp hv
  rw [mem_semiSpinorPlus_iff_snd_zero]
  have hint := spinor16SplitSedenionEquiv_intertwines_g2Derivation p v
  change spinor16ToSplitSedenion (spinor16G2Derivation p v) =
    sedenionG2Derivation p (spinor16SplitSedenionEquiv v) at hint
  rw [hint]
  dsimp [sedenionG2Derivation, cdLift]
  rw [hv0]
  exact zornG2Derivation_zornZero p

/-- `spinor16G2Derivation p` preserves the negative chiral semi-spinor subspace `SemiSpinorMinus`. -/
theorem spinor16G2Derivation_preserves_semiSpinorMinus
    (p : Params) (v : Fin 16 → ℝ) (hv : v ∈ SemiSpinorMinus) :
    spinor16G2Derivation p v ∈ SemiSpinorMinus := by
  have hv0 : (spinor16SplitSedenionEquiv v).1 = zornZero :=
    (mem_semiSpinorMinus_iff_fst_zero v).mp hv
  rw [mem_semiSpinorMinus_iff_fst_zero]
  have hint := spinor16SplitSedenionEquiv_intertwines_g2Derivation p v
  change spinor16ToSplitSedenion (spinor16G2Derivation p v) =
    sedenionG2Derivation p (spinor16SplitSedenionEquiv v) at hint
  rw [hint]
  dsimp [sedenionG2Derivation, cdLift]
  rw [hv0]
  exact zornG2Derivation_zornZero p

/-!
## Section 3: Two-Sheet Linear Mixing & $G_2$ Bimodule Equivariance
-/

/-- The 14-parameter diagonal $G_2$ derivation `sedenionG2Derivation p` commutes with the
4-parameter two-sheet linear mixing operator `sheetLinearMix s₀₀ s₀₁ s₁₀ s₁₁`. -/
theorem sedenionG2Derivation_commutes_with_sheetLinearMix
    (p : Params) (s₀₀ s₀₁ s₁₀ s₁₁ : ℝ) (X : SplitSedenion ℝ) :
    sedenionG2Derivation p (sheetLinearMix s₀₀ s₀₁ s₁₀ s₁₁ X) =
      sheetLinearMix s₀₀ s₀₁ s₁₀ s₁₁ (sedenionG2Derivation p X) := by
  unfold sedenionG2Derivation
  exact cdLift_commutes_with_sheetLinearMix (zornG2Derivation p)
    (zornG2Derivation_add p) (zornG2Derivation_smul p) s₀₀ s₀₁ s₁₀ s₁₁ X

/-- Every `sedenionG2Derivation p X` lands in the 14-dimensional trace-free bimodule sector
$\operatorname{Im}(\mathbb{O}_s) \times \operatorname{Im}(\mathbb{O}_s)$ where both split-octonion
components have vanishing scalar trace. -/
theorem sedenionG2Derivation_lands_in_traceZero_bimodule
    (p : Params) (X : SplitSedenion ℝ) :
    IsImaginarySedenion (sedenionG2Derivation p X) ∧
      (sedenionG2Derivation p X).2.a + (sedenionG2Derivation p X).2.b = 0 := by
  refine ⟨?_, ?_⟩
  · dsimp [IsImaginarySedenion, sedenionG2Derivation, cdLift]
    exact zornG2Derivation_trace_zero p X.1
  · dsimp [sedenionG2Derivation, cdLift]
    exact zornG2Derivation_trace_zero p X.2

end InfoGeometry.Synthesis.SplitSedenionDerivationRepresentationSynthesis
