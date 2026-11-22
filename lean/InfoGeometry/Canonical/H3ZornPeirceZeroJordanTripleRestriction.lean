/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitAlbertPeirceZeroJordanTripleRestriction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitAlbertPeirceQuadraticRepresentation
import InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary
import InfoGeometry.Canonical.H3ZornExplicitPeirceJordanSoldering
import InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge

/-! Compatibility path for the upstream H3 Peirce-zero triple restriction.
The theorem is delegated to the current Split-Albert owner. -/
namespace InfoGeometry.Canonical.H3ZornPeirceZeroJordanTripleRestriction

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
open InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary

abbrev H3 := H3Zorn ℝ

theorem candidateJordanTriple_preserves_peirceZero
    {x y z : H3} (hx : InPeirceZero x) (hy : InPeirceZero y)
    (hz : InPeirceZero z) :
    InPeirceZero (jordanTriple x y z) :=
  SplitAlbertPeirceZeroJordanTripleRestriction.candidateJordanTriple_preserves_peirceZero
    hx hy hz

theorem peirceZero_triple_closure
    (x y z : H3) (hx : InPeirceZero x) (hy : InPeirceZero y)
    (hz : InPeirceZero z) :
    InPeirceZero (jordanTriple x y z) :=
  candidateJordanTriple_preserves_peirceZero hx hy hz


abbrev Spin10 := SplitSpacetime10

theorem peirceZeroEmbed_injective : Function.Injective peirceZeroEmbed := by
  intro x y h
  have hα2 := congrArg (fun Z : H3Zorn ℝ => Z.α₂) h
  have hα3 := congrArg (fun Z : H3Zorn ℝ => Z.α₃) h
  have hb := congrArg (fun Z : H3Zorn ℝ => Z.b) h
  rcases x with ⟨⟨x2, x3⟩, xb⟩
  rcases y with ⟨⟨y2, y3⟩, yb⟩
  simp [peirceZeroEmbed] at hα2 hα3 hb
  subst y2; subst y3; subst yb
  rfl

theorem add_preserves_peirceZero {X Y : H3} (hX : InPeirceZero X) (hY : InPeirceZero Y) :
    InPeirceZero (X + Y) := by
  rcases hX with ⟨hX1, hXa, hXc⟩
  rcases hY with ⟨hY1, hYa, hYc⟩
  simp [InPeirceZero, H3Zorn.add_readback, hX1, hXa, hXc, hY1, hYa, hYc]

theorem jordanTriple_preserves_peirceZero {x y z : H3}
    (hx : InPeirceZero x) (hy : InPeirceZero y) (hz : InPeirceZero z) :
    InPeirceZero (jordanTriple x y z) := by
  unfold jordanTriple
  apply sub_preserves_peirceZero
  · exact add_preserves_peirceZero
      (candidateJordanMul_preserves_peirceZero
        (candidateJordanMul_preserves_peirceZero hx hy) hz)
      (candidateJordanMul_preserves_peirceZero
        (candidateJordanMul_preserves_peirceZero hz hy) hx)
  · exact candidateJordanMul_preserves_peirceZero
      (candidateJordanMul_preserves_peirceZero hx hz) hy

noncomputable def jordanMul10 (x y : Spin10) : Spin10 :=
  fromH3 (candidateJordanMul (peirceZeroEmbed x) (peirceZeroEmbed y))

theorem peirceZeroEmbed_jordanMul10 (x y : Spin10) :
    peirceZeroEmbed (jordanMul10 x y) =
      candidateJordanMul (peirceZeroEmbed x) (peirceZeroEmbed y) := by
  apply (eq_peirceZeroEmbed_of_mem
    (candidateJordanMul_preserves_peirceZero
      (peirceZeroEmbed_mem x) (peirceZeroEmbed_mem y))).symm

noncomputable def jordanTriple10 (x y z : Spin10) : Spin10 :=
  jordanMul10 (jordanMul10 x y) z +
    jordanMul10 (jordanMul10 z y) x - jordanMul10 (jordanMul10 x z) y

theorem peirceZeroEmbed_add (x y : Spin10) :
    peirceZeroEmbed (x + y) = peirceZeroEmbed x + peirceZeroEmbed y := by
  rcases x with ⟨⟨x2, x3⟩, xb⟩
  rcases y with ⟨⟨y2, y3⟩, yb⟩
  apply H3Zorn.ext_h3 <;> simp [peirceZeroEmbed, H3Zorn.add_readback]

end InfoGeometry.Canonical.H3ZornPeirceZeroJordanTripleRestriction
