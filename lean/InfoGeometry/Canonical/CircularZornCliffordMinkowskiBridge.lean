/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CliffordTowerMinkowskiTransport
import InfoGeometry.Lie.SplitOctonionCircularQuadraticCoherence

/-! # Circular Zorn and native Clifford Lorentz sections

The matched circular section and the selected stage-four Clifford vector
carry the same quadratic form. This is a comparison of specific elements
and forms, not an algebra homomorphism from the alternative Zorn algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.CircularZornCliffordMinkowskiBridge

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl44MinkowskiSubspace
open InfoGeometry.Canonical.CliffordTowerMinkowskiTransport
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates
open InfoGeometry.Lie.SplitOctonionCircularQuadraticCoherence
open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Lie.SplitOctonionErlangenInvariant

/-- The actual split-octonion element whose circular coordinates match the
same four-vector on both Peirce sectors. -/
def circularZornVector (t x y z : ℝ) : InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn :=
  circularPeirceBasis.equivFun.symm (minkowskiDiagonalEmbedding ![t, x, y, z])

/-- Linear matched-section embedding into the native Zorn carrier. -/
def circularZornSection : (Fin 4 → ℝ) →ₗ[ℝ]
    InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn :=
  circularPeirceBasis.equivFun.symm.toLinearMap.comp minkowskiDiagonalEmbedding

/-- Both circular four-component readouts recover the original input. -/
theorem circularZornSection_two_readouts (u : Fin 4 → ℝ) (i : Fin 4) :
    circularPeirceBasis.equivFun (circularZornSection u) (Fin.castAdd 4 i) = u i ∧
    circularPeirceBasis.equivFun (circularZornSection u) (Fin.addNat i 4) = u i := by
  simp only [circularZornSection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, minkowskiDiagonalEmbedding_apply_left,
    minkowskiDiagonalEmbedding_apply_right, and_self]

/-- The Zorn section is injective: no four-vector information is discarded. -/
theorem circularZornSection_injective : Function.Injective circularZornSection := by
  intro u v h
  funext i
  have hc := congrArg (fun Z => circularPeirceBasis.equivFun Z (Fin.castAdd 4 i)) h
  rw [(circularZornSection_two_readouts u i).1,
    (circularZornSection_two_readouts v i).1] at hc
  exact hc

/-- The Zorn quadratic form of the matched circular section equals the
native quadratic form of the selected stage-four Clifford vector. -/
theorem circularZornVector_norm_eq_clifford_quad (t x y z : ℝ) :
    canonicalDetQuadratic (circularZornVector t x y z) =
      Qsplit 4 (minkowskiVector t x y z) := by
  change circularPeirceQuadratic (minkowskiDiagonalEmbedding ![t, x, y, z]) = _
  rw [circularPeirceQuadratic_eq_circularWittQuadratic,
    circularWittQuadratic_minkowskiDiagonal, minkowskiVector_quadratic]
  simp
  ring

/-- The two injective linear sections agree on the full quadratic form. -/
theorem circularZornSection_quadratic (u : Fin 4 → ℝ) :
    canonicalDetQuadratic (circularZornSection u) = Qsplit 4 (minkowskiLinear u) := by
  have hu : ![u 0, u 1, u 2, u 3] = u := by
    funext i
    fin_cases i <;> rfl
  have h := circularZornVector_norm_eq_clifford_quad (u 0) (u 1) (u 2) (u 3)
  simpa only [circularZornVector, circularZornSection, LinearMap.comp_apply,
    LinearEquiv.coe_coe, minkowskiLinear, LinearMap.coe_mk, AddHom.coe_mk, hu] using h

/-- The two concrete four-dimensional images are linearly equivalent. -/
def circularZornToCliffordSection :
    LinearMap.range circularZornSection ≃ₗ[ℝ] LinearMap.range minkowskiLinear :=
  (LinearEquiv.ofInjective circularZornSection circularZornSection_injective).symm.trans
    (LinearEquiv.ofInjective minkowskiLinear minkowskiLinear_injective)

/-- The linear equivalence preserves the native Zorn and split Clifford
quadratic forms on these specific four-dimensional subspaces. -/
theorem circularZornToCliffordSection_isometry (Z : LinearMap.range circularZornSection) :
    Qsplit 4 (circularZornToCliffordSection Z : SplitSpace 4) =
      canonicalDetQuadratic (Z : InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn) := by
  obtain ⟨u, rfl⟩ := (LinearEquiv.ofInjective circularZornSection
    circularZornSection_injective).surjective Z
  simpa [circularZornToCliffordSection] using (circularZornSection_quadratic u).symm

/-- The native Zorn determinant restricted to the matched section. -/
def circularZornSectionForm : QuadraticForm ℝ (LinearMap.range circularZornSection) :=
  canonicalDetQuadratic.comp (LinearMap.range circularZornSection).subtype

/-- The native split quadratic form restricted to the selected Clifford plane. -/
def cliffordMinkowskiSectionForm : QuadraticForm ℝ (LinearMap.range minkowskiLinear) :=
  (Qsplit 4).comp (LinearMap.range minkowskiLinear).subtype

/-- A native Mathlib isometry of the two selected quadratic spaces. -/
def circularZornCliffordIsometry :
    circularZornSectionForm.IsometryEquiv cliffordMinkowskiSectionForm :=
  QuadraticMap.IsometryEquiv.mk circularZornToCliffordSection
    circularZornToCliffordSection_isometry

/-- Every orthogonal automorphism of the Clifford four-plane transports to
an orthogonal automorphism of the actual circular Zorn section. -/
def transportCliffordIsometry
    (g : cliffordMinkowskiSectionForm.IsometryEquiv cliffordMinkowskiSectionForm) :
    circularZornSectionForm.IsometryEquiv circularZornSectionForm :=
  circularZornCliffordIsometry.trans (g.trans circularZornCliffordIsometry.symm)

/-- The Zorn and Clifford actions intertwine under the proved isometry. -/
theorem transportCliffordIsometry_intertwines
    (g : cliffordMinkowskiSectionForm.IsometryEquiv cliffordMinkowskiSectionForm)
    (Z : LinearMap.range circularZornSection) :
    circularZornCliffordIsometry (transportCliffordIsometry g Z) =
      g (circularZornCliffordIsometry Z) := by
  change circularZornCliffordIsometry
    (circularZornCliffordIsometry.symm (g (circularZornCliffordIsometry Z))) = _
  exact circularZornCliffordIsometry.apply_symm_apply _

/-- Transport preserves composition on the full selected four-plane. -/
theorem transportCliffordIsometry_comp
    (g h : cliffordMinkowskiSectionForm.IsometryEquiv cliffordMinkowskiSectionForm)
    (Z : LinearMap.range circularZornSection) :
    transportCliffordIsometry (h.trans g) Z =
      transportCliffordIsometry g (transportCliffordIsometry h Z) := by
  change circularZornCliffordIsometry.symm (g (h (circularZornCliffordIsometry Z))) =
    circularZornCliffordIsometry.symm
      (g (circularZornCliffordIsometry
        (circularZornCliffordIsometry.symm (h (circularZornCliffordIsometry Z)))))
  rw [circularZornCliffordIsometry.apply_symm_apply]

/-- The same Zorn quadratic value controls the square of the transported
Clifford vector at every later finite stage. -/
theorem circularZornVector_tower_square (n : ℕ) (h : 4 ≤ n) (t x y z : ℝ) :
    towerMinkowskiVector n h t x y z * towerMinkowskiVector n h t x y z =
      algebraMap ℝ (SplitClNNAlg n) (canonicalDetQuadratic (circularZornVector t x y z)) := by
  rw [circularZornVector_norm_eq_clifford_quad, minkowskiVector_quadratic]
  exact towerMinkowskiVector_square n h t x y z

/-- The Zorn polar form on two matched sections gives twice their
Minkowski pairing. -/
theorem circularZornVector_polar (t x y z s a b c : ℝ) :
    circularPeircePolar
      (circularPeirceBasis.equivFun (circularZornVector t x y z))
      (circularPeirceBasis.equivFun (circularZornVector s a b c)) =
      2 * (t * s - x * a - y * b - z * c) := by
  simp only [circularZornVector, LinearEquiv.apply_symm_apply,
    circularPeircePolar_minkowskiDiagonal]
  simp
  ring

/-- The cross-sheet polar form is the scalar in the anticommutator of the
corresponding native Clifford vectors at every later finite stage. -/
theorem circularZornVector_tower_anticommutator (n : ℕ) (h : 4 ≤ n)
    (t x y z s a b c : ℝ) :
    towerMinkowskiVector n h t x y z * towerMinkowskiVector n h s a b c +
      towerMinkowskiVector n h s a b c * towerMinkowskiVector n h t x y z =
      algebraMap ℝ (SplitClNNAlg n)
        (circularPeircePolar
          (circularPeirceBasis.equivFun (circularZornVector t x y z))
          (circularPeirceBasis.equivFun (circularZornVector s a b c))) := by
  rw [circularZornVector_polar]
  exact towerMinkowskiVector_anticommutator n h t x y z s a b c

end InfoGeometry.Canonical.CircularZornCliffordMinkowskiBridge

end
