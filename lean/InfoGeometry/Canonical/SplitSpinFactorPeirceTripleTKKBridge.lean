/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitSpinFactorTKKSO66
import InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66
import InfoGeometry.Canonical.SplitSpinFactorHomothetySO55
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.H3ZornPeirceZeroJordanTripleRestriction

/-! Compatibility path for the Peirce/TKK bridge.  The active repository
proves the Peirce-zero restriction and conformal TKK identities in separate
owners; this bridge exposes their common carrier without asserting a new
ambient exceptional identification. -/
namespace InfoGeometry.Canonical.SplitSpinFactorPeirceTripleTKKBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
open InfoGeometry.Canonical.SplitSpinFactorTKKSO66
open InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66
open InfoGeometry.Canonical.SplitSpinFactorHomothetySO55

abbrev H3 := H3Zorn ℝ
abbrev V10 := SplitSpinFactorTKKSO66.V10

theorem jordanTriple_preserves_peirceZero
    {x y z : H3} (hx : InPeirceZero x) (hy : InPeirceZero y)
    (hz : InPeirceZero z) :
    InPeirceZero (jordanTriple x y z) := by
  exact InfoGeometry.Canonical.H3ZornPeirceZeroJordanTripleRestriction.peirceZero_triple_closure
    x y z hx hy hz


noncomputable def spinJordanMul (x y : V10) : V10 :=
  let p := zornPolar x.2 y.2
  (((x.1.1 * y.1.1 + (1 / 2 : ℝ) * p),
    (x.1.2 * y.1.2 + (1 / 2 : ℝ) * p)),
    (1 / 2 : ℝ) •
      ((x.1.1 + x.1.2) • y.2 + (y.1.1 + y.1.2) • x.2))

noncomputable def spinJordanTriple (x y z : V10) : V10 :=
  spinJordanMul (spinJordanMul x y) z +
    spinJordanMul (spinJordanMul z y) x - spinJordanMul (spinJordanMul x z) y

def spinTraceReverse (y : V10) : V10 := ((y.1.2, y.1.1), -y.2)

@[simp] theorem spinTraceReverse_involutive (y : V10) :
    spinTraceReverse (spinTraceReverse y) = y := by
  rcases y with ⟨⟨y2, y3⟩, ⟨a, v, w, b⟩⟩
  simp [spinTraceReverse, ZornVectorMatrix.neg]

noncomputable def conformalSpinTriple (x y z : V10) : V10 :=
  SplitSpinFactorTKKConformalSO66.B10 x y • z + SplitSpinFactorTKKConformalSO66.B10 y z • x - SplitSpinFactorTKKConformalSO66.B10 x z • y

noncomputable def conformalZeroAction (x y : V10) : Module.End ℝ V10 :=
  (-SplitSpinFactorTKKConformalSO66.B10 x y) • LinearMap.id + SplitSpinFactorTKKSO66.rankTwoRotation x y

@[simp] theorem conformalZeroAction_apply (x y z : V10) :
    conformalZeroAction x y z = -conformalSpinTriple x y z := by
  simp [conformalZeroAction, conformalSpinTriple, rankTwoRotation, SplitSpinFactorTKKSO66.B10_symm]
  module

end InfoGeometry.Canonical.SplitSpinFactorPeirceTripleTKKBridge
