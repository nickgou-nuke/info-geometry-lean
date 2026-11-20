/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.CuntzDeformedSuperPoincare
import InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge

/-!
# Real operator form of the chiral Cuntz super-Poincaré relation

The Cuntz presentation is stored as complex `2 × 2` matrices. This adapter
transports its operator equation through the repository's faithful real
`4 × 4` matrix representation. The output carrier is real; multiplication by
the complex unit is retained as the real endomorphism `complexStructure`,
which squares to `-1` and commutes with every realified operator. This is a
finite-dimensional coefficient bridge, not an identification of arbitrary
Cuntz momentum with the geometric `FourSpace` translation parameter.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCuntzSuperPoincareBridge

open InfoGeometry.Physics.CuntzDeformedSuperPoincare
open InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge

local notation "Mat2C" => InfoGeometry.Algebra.FiniteSpin.Mat2C
local notation "Mat4R" => InfoGeometry.Algebra.FiniteSpin.Mat4R

/-- The realified operator anticommutator and momentum matrices of a chiral
operator presentation. -/
structure RealifiedChiralPresentation where
  antiQQbar : Mat4R
  Pspinor : Mat4R
  super_poincare : antiQQbar = (2 : ℝ) • Pspinor

/-- A complex chiral operator presentation has a faithful real matrix
presentation, preserving its operator-valued super-Poincaré equation. -/
def realifyPresentation (S : ChiralOperatorPresentation) :
    RealifiedChiralPresentation where
  antiQQbar := realify S.antiQQbar
  Pspinor := realify S.Pspinor
  super_poincare := by
    rw [S.super_poincare]
    exact realify_real_smul 2 S.Pspinor

/-- The realified relation is an equation of real `4 × 4` operators. -/
theorem realify_super_poincare (S : ChiralOperatorPresentation) :
    realify S.antiQQbar = (2 : ℝ) • realify S.Pspinor :=
  (realifyPresentation S).super_poincare

/-- Both real operators in the realified super-Poincaré relation commute
with the real complex-structure endomorphism. -/
theorem realify_super_poincare_commutes_with_J (S : ChiralOperatorPresentation) :
    realify S.antiQQbar * complexStructure =
        complexStructure * realify S.antiQQbar ∧
      realify S.Pspinor * complexStructure =
        complexStructure * realify S.Pspinor := by
  exact ⟨realify_commutes_complexStructure _,
    realify_commutes_complexStructure _⟩

/-- The real complex-structure operator carried by the realified chiral
presentation is an actual endomorphism satisfying `J² = -1`. -/
theorem realified_chiral_complexStructure_square :
    complexStructure * complexStructure = -(1 : Mat4R) :=
  complexStructure_sq

/-- The real matrix relation also holds after passing to real endomorphisms
of the four-coordinate real spinor carrier. -/
theorem realify_super_poincare_as_real_endomorphisms
    (S : ChiralOperatorPresentation) :
    Matrix.toLin' (realify S.antiQQbar) =
      (2 : ℝ) • Matrix.toLin' (realify S.Pspinor) := by
  rw [realify_super_poincare]
  exact (Matrix.toLin' : Mat4R ≃ₗ[ℝ] _).map_smul 2 _

end InfoGeometry.Canonical.RealCuntzSuperPoincareBridge
