/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.H3ZornJordanIdentity
import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary

/-! Compatibility owner for the upstream Peirce-quadratic path.  The
implementation is delegated to the current native fixed-tripoten owner. -/
noncomputable section

namespace InfoGeometry.Canonical.SplitAlbertPeirceQuadraticRepresentation

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation

abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev H3 := InfoGeometry.Algebra.H3Zorn ℝ
abbrev PeirceZeroCoord := InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary.PeirceZeroCoord

abbrev InPeirceZero := SplitAlbertPeirceZeroQuadraticRepresentation.InPeirceZero
abbrev U10 := SplitAlbertPeirceZeroQuadraticRepresentation.U10

theorem peirceZeroEmbed_intertwines_U10 (u v : PeirceZeroCoord) :
    SplitAlbertTripotentPeirceBoundary.peirceZeroEmbed (U10 u v) =
      InfoGeometry.Algebra.H3Zorn.U
        (SplitAlbertTripotentPeirceBoundary.peirceZeroEmbed u)
        (SplitAlbertTripotentPeirceBoundary.peirceZeroEmbed v) :=
  SplitAlbertPeirceZeroQuadraticRepresentation.peirceZeroEmbed_U10 u v

theorem U_preserves_peirceZero
    {y x : H3} (hy : InPeirceZero y) (hx : InPeirceZero x) :
    InPeirceZero (InfoGeometry.Algebra.H3Zorn.U y x) :=
  SplitAlbertPeirceZeroQuadraticRepresentation.U_preserves_peirceZero hy hx

@[simp] theorem peirceZeroEmbed_mem (p : PeirceZeroCoord) :
    InPeirceZero (peirceZeroEmbed p) := by
  exact SplitAlbertPeirceZeroQuadraticRepresentation.peirceZeroEmbed_mem p

/-- Every coordinatewise Peirce-zero element is reconstructed by the native
`PeirceZeroCoord` embedding. -/
theorem peirceZeroEmbed_extract (X : H3Zorn ℝ) (hX : InPeirceZero X) :
    peirceZeroEmbed ((X.α₂, X.α₃), X.b) = X := by
  exact (SplitAlbertPeirceZeroQuadraticRepresentation.eq_peirceZeroEmbed_of_mem hX).symm

/-- The repository's cubic `U`-operator is exactly the usual quadratic Jordan
representation

`U_y(x) = 2 y ∘ (y ∘ x) - y² ∘ x`

for the installed native Jordan multiplication on `H3Zorn ℝ`. -/
theorem U_eq_jordan_quadratic (y x : H3Zorn ℝ) :
    H3Zorn.U y x =
      (2 : ℝ) • (y * (y * x)) - (y * y) * x := by
  rw [← quadraticJordanOp_eq_U]
  simp [quadraticJordanOp, candidateJordanMul_eq_mul]

/-- Peirce-zero is closed under the native Jordan product.  This is the
coordinate form of `V₀(e₁) ∘ V₀(e₁) ⊆ V₀(e₁)`. -/
theorem jordanMul_preserves_peirceZero
    {X Y : H3Zorn ℝ} (hX : InPeirceZero X) (hY : InPeirceZero Y) :
    InPeirceZero (X * Y) := by
  change InPeirceZero (candidateJordanMul X Y)
  exact SplitAlbertPeirceZeroQuadraticRepresentation.candidateJordanMul_preserves_peirceZero hX hY

/-- Readback of the already-verified metric convention: the ten-dimensional
transversal quadratic form is the split `(5,5)` form. -/
theorem transversal_metric_is_q55 (p : PeirceZeroCoord) :
    h2SplitDet p.1.1 p.1.2 p.2 =
      q55Real (h2ToVec55 p.1.1 p.1.2 p.2) := by
  exact h2SplitDet_eq_q55Real p.1.1 p.1.2 p.2

end InfoGeometry.Canonical.SplitAlbertPeirceQuadraticRepresentation
end noncomputable section
