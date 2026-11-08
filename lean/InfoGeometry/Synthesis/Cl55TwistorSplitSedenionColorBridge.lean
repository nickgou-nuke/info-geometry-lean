/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
import InfoGeometry.Synthesis.Cl44MinimalIdealSplitSedenionEquivBridge
import InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
import InfoGeometry.Canonical.SplitOctonionClifford33Soldering
import InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis

/-!
# $\mathrm{Cl}(5,5)$ Twistor, Split-Sedenion, and Peircian Lepton–Quark Coordinate Bridge

This module bridges the 16-component $\mathrm{Cl}(5,5)$ twistor carrier
`Twistor55 ℝ = (Fin 8 → ℝ) × (Fin 8 → ℝ)` and the Günaydin–Gürsey lepton–quark multiplet
carrier `GunaydinGurseyMultiplet ℝ` from `InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis`
with the split-sedenion pair carrier `SplitSedenion ℝ = ZornSplitOctonion ℝ × ZornSplitOctonion ℝ`
and the matrix-model principal left ideal `LeftIdeal primIdem` from
`InfoGeometry.Synthesis.Cl44MinimalIdealSplitSedenionEquivBridge`:

1. **Section 1 — 16D Carrier Equivalence `Twistor55 ℝ ≃ SplitSedenion ℝ` & Composite `LeftIdeal primIdem ≃ Twistor55 ℝ`**:
   - Defines `twistor55ToSplitSedenion`, `splitSedenionToTwistor55`, and the mutual inverse
     equivalence `twistor55SplitSedenionEquiv : Twistor55 ℝ ≃ SplitSedenion ℝ`.
   - Proves additivity `twistor55ToSplitSedenion_add` and defines the composite carrier
     equivalence `cl44MatrixLeftIdealTwistor55Equiv : LeftIdeal primIdem ≃ Twistor55 ℝ`.
2. **Section 2 — Peircian Zorn Lepton–Quark Coordinate Equivalence `ZornSplitOctonion ℝ ≃ GunaydinGurseyMultiplet ℝ`**:
   - Defines `zornToLeptonQuarkMultiplet` and `leptonQuarkMultipletToZorn`, grouping the two
     diagonal Peircian scalars `(z.a, z.b)` into the two scalar slots and the off-diagonal
     vectors `(z.u, z.v)` into two three-coordinate slots, packaging
     `zornLeptonQuarkEquiv`. These are carrier coordinates; this does not prove an SU(3)
     or gauge representation.
   - Proves additivity `zornToLeptonQuarkMultiplet_add` and an exact coordinate formula for
     `zornNorm` in the owner's Günaydin–Gürsey basis. The formula follows the owner's Fock
     index order and Jordan–Wigner sign convention; it is not a singlet determinant minus a
     Euclidean triplet pairing.
3. **Section 3 — Super-Andreev Sheet Reflection on `SplitSedenion ℝ` (`ℤ₄` Order & `sedenionNorm` Negation)**:
   - Defines `sedenionAndreevSheetSwap (X₁, X₂) = (-X₂, X₁)` on `SplitSedenion ℝ` and proves
     that `splitSedenionToTwistor55` intertwines it with the twistor sheet reflection
     `(ψ, χ) ↦ (-χ, ψ)` of `superAndreevReflect`.
   - Certifies `sedenionAndreevSheetSwap_sq`, `sedenionAndreevSheetSwap_order_four`, and
     exact split-norm negation `sedenionNorm_sedenionAndreevSheetSwap`.
-/

set_option autoImplicit false
noncomputable section

namespace InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge

open InfoGeometry.Cl44IdempotentIdeal
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
open InfoGeometry.Synthesis.Cl44MinimalIdealSplitSedenionEquivBridge

/-!
## Section 1: 16D Carrier Equivalence `Twistor55 ℝ ≃ SplitSedenion ℝ` & Composite `LeftIdeal primIdem ≃ Twistor55 ℝ`
-/

/-- Maps a 16-component $\mathrm{Cl}(5,5)$ twistor $Z = (\psi, \chi) \in \mathrm{Twistor55}\, \mathbb{R}$
to a split-sedenion pair `(fin8ToZorn Z.1, fin8ToZorn Z.2)` in `SplitSedenion ℝ`. -/
def twistor55ToSplitSedenion (Z : Twistor55 ℝ) : SplitSedenion ℝ :=
  (fin8ToZorn Z.1, fin8ToZorn Z.2)

/-- Maps a split-sedenion pair $X = (X_1, X_2) \in \mathrm{SplitSedenion}\, \mathbb{R}$ to a
16-component $\mathrm{Cl}(5,5)$ twistor `(zornToFin8 X.1, zornToFin8 X.2)` in `Twistor55 ℝ`. -/
def splitSedenionToTwistor55 (X : SplitSedenion ℝ) : Twistor55 ℝ :=
  (zornToFin8 X.1, zornToFin8 X.2)

/-- `splitSedenionToTwistor55` is a right inverse to `twistor55ToSplitSedenion`. -/
theorem twistor55ToSplitSedenion_splitSedenionToTwistor55 (X : SplitSedenion ℝ) :
    twistor55ToSplitSedenion (splitSedenionToTwistor55 X) = X := by
  apply Prod.ext
  · dsimp [twistor55ToSplitSedenion, splitSedenionToTwistor55]
    exact fin8ToZorn_right_inv X.1
  · dsimp [twistor55ToSplitSedenion, splitSedenionToTwistor55]
    exact fin8ToZorn_right_inv X.2

/-- `splitSedenionToTwistor55` is a left inverse to `twistor55ToSplitSedenion`. -/
theorem splitSedenionToTwistor55_twistor55ToSplitSedenion (Z : Twistor55 ℝ) :
    splitSedenionToTwistor55 (twistor55ToSplitSedenion Z) = Z := by
  apply Prod.ext
  · dsimp [twistor55ToSplitSedenion, splitSedenionToTwistor55]
    exact fin8ToZorn_left_inv Z.1
  · dsimp [twistor55ToSplitSedenion, splitSedenionToTwistor55]
    exact fin8ToZorn_left_inv Z.2

/-- Explicit 16-dimensional carrier equivalence `Twistor55 ℝ ≃ SplitSedenion ℝ` identifying the
two 8-component semi-spinor sheets of $\mathbb{T}_{(5,5)} = \mathbf{8}_s \oplus \mathbf{8}_c$
with the two Zorn split-octonion components of `SplitSedenion ℝ`. -/
def twistor55SplitSedenionEquiv : Twistor55 ℝ ≃ SplitSedenion ℝ where
  toFun := twistor55ToSplitSedenion
  invFun := splitSedenionToTwistor55
  left_inv := splitSedenionToTwistor55_twistor55ToSplitSedenion
  right_inv := twistor55ToSplitSedenion_splitSedenionToTwistor55

/-- `twistor55ToSplitSedenion` transports componentwise twistor addition to `sedenionAdd`. -/
theorem twistor55ToSplitSedenion_add (Z W : Twistor55 ℝ) :
    twistor55ToSplitSedenion (Z + W) =
      sedenionAdd (twistor55ToSplitSedenion Z) (twistor55ToSplitSedenion W) := by
  apply Prod.ext
  · dsimp [twistor55ToSplitSedenion, sedenionAdd]
    exact fin8ToZorn_add Z.1 W.1
  · dsimp [twistor55ToSplitSedenion, sedenionAdd]
    exact fin8ToZorn_add Z.2 W.2

/-- Composite 16-dimensional carrier equivalence between the matrix-model principal left ideal
`LeftIdeal primIdem` and the $\mathrm{Cl}(5,5)$ twistor carrier `Twistor55 ℝ`. -/
def cl44MatrixLeftIdealTwistor55Equiv : LeftIdeal primIdem ≃ Twistor55 ℝ :=
  cl44MatrixLeftIdealSplitSedenionEquiv.trans twistor55SplitSedenionEquiv.symm

/-!
## Section 2: Peircian Zorn Lepton–Quark Multiplet Equivalence `ZornSplitOctonion ℝ ≃ GunaydinGurseyMultiplet ℝ`
-/

/-- Maps a Zorn split-octonion $z = \begin{pmatrix} a & u \\ v & b \end{pmatrix}$ to the
coordinate carrier `(![z.a, z.b], z.u, z.v)` in `GunaydinGurseyMultiplet ℝ`. The slots are
labelled by the corresponding singlet/triplet decomposition in that carrier; this map alone
does not establish a gauge-group representation. -/
def zornToLeptonQuarkMultiplet (z : ZornSplitOctonion ℝ) : GunaydinGurseyMultiplet ℝ :=
  gunaydinGurseySplit (zornToFin8 z)

/-- Reconstructs a Zorn split-octonion in `ZornSplitOctonion ℝ` from a Günaydin–Gürsey
lepton–quark multiplet `m : GunaydinGurseyMultiplet ℝ`. -/
def leptonQuarkMultipletToZorn (m : GunaydinGurseyMultiplet ℝ) : ZornSplitOctonion ℝ :=
  fin8ToZorn (gunaydinGurseyCombine m)

/-- `leptonQuarkMultipletToZorn` is a right inverse to `zornToLeptonQuarkMultiplet`. -/
theorem zornToLeptonQuarkMultiplet_leptonQuarkMultipletToZorn
    (m : GunaydinGurseyMultiplet ℝ) :
    zornToLeptonQuarkMultiplet (leptonQuarkMultipletToZorn m) = m := by
  change gunaydinGurseySplit
    (zornToFin8 (fin8ToZorn (gunaydinGurseyCombine m))) = m
  rw [fin8ToZorn_left_inv]
  exact (gunaydinGurseyEquiv ℝ).right_inv m

/-- `leptonQuarkMultipletToZorn` is a left inverse to `zornToLeptonQuarkMultiplet`. -/
theorem leptonQuarkMultipletToZorn_zornToLeptonQuarkMultiplet
    (z : ZornSplitOctonion ℝ) :
    leptonQuarkMultipletToZorn (zornToLeptonQuarkMultiplet z) = z := by
  change fin8ToZorn
    (gunaydinGurseyCombine (gunaydinGurseySplit (zornToFin8 z))) = z
  have h := (gunaydinGurseyEquiv ℝ).left_inv (zornToFin8 z)
  change gunaydinGurseyCombine
    (gunaydinGurseySplit (zornToFin8 z)) = zornToFin8 z at h
  rw [h]
  exact fin8ToZorn_right_inv z

/-- Peircian coordinate-carrier equivalence `ZornSplitOctonion ℝ ≃ GunaydinGurseyMultiplet ℝ`
aligning Zorn's $(1 + 1) + (3 + 3)$ vector-matrix decomposition with the named carrier. -/
def zornLeptonQuarkEquiv : ZornSplitOctonion ℝ ≃ GunaydinGurseyMultiplet ℝ where
  toFun := zornToLeptonQuarkMultiplet
  invFun := leptonQuarkMultipletToZorn
  left_inv := leptonQuarkMultipletToZorn_zornToLeptonQuarkMultiplet
  right_inv := zornToLeptonQuarkMultiplet_leptonQuarkMultipletToZorn

/-- `zornToLeptonQuarkMultiplet` transports `zornAdd` to componentwise addition on
`GunaydinGurseyMultiplet ℝ`. -/
theorem zornToLeptonQuarkMultiplet_add (x y : ZornSplitOctonion ℝ) :
    zornToLeptonQuarkMultiplet (zornAdd x y) =
      zornToLeptonQuarkMultiplet x + zornToLeptonQuarkMultiplet y := by
  change gunaydinGurseySplit (zornToFin8 (zornAdd x y)) =
    gunaydinGurseySplit (zornToFin8 x) + gunaydinGurseySplit (zornToFin8 y)
  rw [zornToFin8_zornAdd]
  exact (gunaydinGurseyEquiv ℝ).map_add (zornToFin8 x) (zornToFin8 y)

/-- Exact coordinate expression for the Zorn split quadratic form in the owner's
Günaydin–Gürsey coordinates. The mixed and signed terms reflect the Fock index order and
Jordan–Wigner sign in `fin8ToZorn`; this is not the unsigned triplet dot-product formula. -/
theorem zornNorm_eq_gunaydin_gursey_coordinates (z : ZornSplitOctonion ℝ) :
    zornNorm z =
      (zornToLeptonQuarkMultiplet z).1 0 * (zornToLeptonQuarkMultiplet z).2.2 2 -
        (zornToLeptonQuarkMultiplet z).2.1 2 * (zornToLeptonQuarkMultiplet z).2.1 1 +
        (zornToLeptonQuarkMultiplet z).2.1 0 * (zornToLeptonQuarkMultiplet z).2.2 0 -
        (zornToLeptonQuarkMultiplet z).1 1 * (zornToLeptonQuarkMultiplet z).2.2 1 := by
  simp [zornToLeptonQuarkMultiplet, gunaydinGurseySplit,
    zornToFin8, zornNorm, vec3Dot]
  ring

/-!
## Section 3: Super-Andreev Sheet Reflection on `SplitSedenion ℝ` (`ℤ₄` Order & `sedenionNorm` Negation)
-/

/-- The Super-Andreev semi-spinor sheet reflection on `SplitSedenion ℝ`, mapping
$(X_1, X_2) \mapsto (-X_2, X_1)$. -/
def sedenionAndreevSheetSwap (X : SplitSedenion ℝ) : SplitSedenion ℝ :=
  (zornSmul (-1 : ℝ) X.2, X.1)

/-- `zornToFin8` intertwines scalar multiplication by `-1` with vector negation on `Fin 8 → ℝ`. -/
theorem zornToFin8_neg_one_smul (z : ZornSplitOctonion ℝ) :
    zornToFin8 (zornSmul (-1 : ℝ) z) = -zornToFin8 z := by
  have _ := z
  ext i
  fin_cases i <;> simp [zornToFin8, zornSmul]

/-- `splitSedenionToTwistor55` intertwines `sedenionAndreevSheetSwap` with the twistor sheet
reflection $(\psi, \chi) \mapsto (-\chi, \psi)$ of `superAndreevReflect`. -/
theorem splitSedenionToTwistor55_sedenionAndreevSheetSwap (X : SplitSedenion ℝ) :
    splitSedenionToTwistor55 (sedenionAndreevSheetSwap X) =
      (-(splitSedenionToTwistor55 X).2, (splitSedenionToTwistor55 X).1) := by
  apply Prod.ext
  · dsimp [splitSedenionToTwistor55, sedenionAndreevSheetSwap]
    exact zornToFin8_neg_one_smul X.2
  · rfl

/-- Applying `sedenionAndreevSheetSwap` twice negates both split-octonion components (`sedenionNeg`). -/
theorem sedenionAndreevSheetSwap_sq (X : SplitSedenion ℝ) :
    sedenionAndreevSheetSwap (sedenionAndreevSheetSwap X) =
      (zornSmul (-1 : ℝ) X.1, zornSmul (-1 : ℝ) X.2) := by
  have _ := X
  rfl

/-- Scaling a Zorn split-octonion twice by `-1` is the identity. -/
theorem zornSmul_neg_one_neg_one (z : ZornSplitOctonion ℝ) :
    zornSmul (-1 : ℝ) (zornSmul (-1 : ℝ) z) = z := by
  have _ := z
  ext i
  · dsimp [zornSmul]
    ring
  · fin_cases i <;> (dsimp [zornSmul]; ring)
  · fin_cases i <;> (dsimp [zornSmul]; ring)
  · dsimp [zornSmul]
    ring

/-- The fourth iterate of `sedenionAndreevSheetSwap` is the identity. Together with
`sedenionAndreevSheetSwap_sq`, this proves its square is componentwise negation and its order
divides four; exact order four would additionally require a nonzero witness. -/
theorem sedenionAndreevSheetSwap_order_four (X : SplitSedenion ℝ) :
    sedenionAndreevSheetSwap
      (sedenionAndreevSheetSwap (sedenionAndreevSheetSwap (sedenionAndreevSheetSwap X))) = X := by
  apply Prod.ext
  · dsimp [sedenionAndreevSheetSwap]
    exact zornSmul_neg_one_neg_one X.1
  · dsimp [sedenionAndreevSheetSwap]
    exact zornSmul_neg_one_neg_one X.2

/-- The Zorn quadratic norm is invariant under scalar negation `zornSmul (-1)`. -/
theorem zornNorm_neg_one_smul (z : ZornSplitOctonion ℝ) :
    zornNorm (zornSmul (-1 : ℝ) z) = zornNorm z := by
  have _ := z
  dsimp [zornNorm, zornSmul, vec3Dot]
  ring

/-- `sedenionAndreevSheetSwap` reverses the sign of the $(8,8)$ split-sedenion norm
$N_{\mathbb{S}_s}(X_1, X_2) = N_{\mathbb{O}_s}(X_1) - N_{\mathbb{O}_s}(X_2)$, exchanging
     timelike and spacelike norm sectors while preserving the null cone $N_{\mathbb{S}_s}(X) = 0$. -/
theorem sedenionNorm_sedenionAndreevSheetSwap (X : SplitSedenion ℝ) :
    sedenionNorm (sedenionAndreevSheetSwap X) = -sedenionNorm X := by
  dsimp [sedenionNorm, sedenionAndreevSheetSwap]
  rw [zornNorm_neg_one_smul X.2]
  ring

end InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge
