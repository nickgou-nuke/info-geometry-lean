import Mathlib
import InfoGeometry.OperatorAlgebra.ChiralCliffordSplit

/-!
# Algebraic two-factor split-octonion Dirac reduction

This owner records the finite algebraic content common to two-factor
split-octonion Dirac expressions.  A pure Zorn vector acts by native left
multiplication, and applying that action twice is scalar multiplication by
the vector quadratic coefficient.  No spacetime derivative, PDE, or
physical spinor identification is introduced here.
-/

namespace InfoGeometry.Canonical.SplitOctonionDiracTwoFactorAlgebraicReduction

noncomputable section

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford

abbrev DiracCarrier := ZornMatrix ℝ

def twoFactorDiracAction (D Ψ : DiracCarrier) : DiracCarrier := D * Ψ

def twoFactorDiracLeftOp (D : DiracCarrier) : DiracCarrier →ₗ[ℝ] DiracCarrier where
  toFun := twoFactorDiracAction D
  map_add' := by
    intro Ψ Φ
    change D * (Ψ + Φ) = D * Ψ + D * Φ
    exact mul_add' D Ψ Φ
  map_smul' := by
    intro c Ψ
    change D * (c • Ψ) = c • (D * Ψ)
    exact mul_smul' c D Ψ

theorem twoFactorDiracAction_eq_leftOp (D Ψ : DiracCarrier) :
    twoFactorDiracAction D Ψ = twoFactorDiracLeftOp D Ψ := rfl

theorem twoFactorDirac_square_apply
    (D Ψ : DiracCarrier) (ha : D.a = 0) (hb : D.b = 0) :
    twoFactorDiracAction D (twoFactorDiracAction D Ψ) =
      (dot D.x D.y) • Ψ := by
  exact vector_clifford_relation D ha hb Ψ

theorem twoFactorDirac_square
    (D : DiracCarrier) (ha : D.a = 0) (hb : D.b = 0) :
    (twoFactorDiracLeftOp D).comp (twoFactorDiracLeftOp D) =
      (dot D.x D.y) • (1 : DiracCarrier →ₗ[ℝ] DiracCarrier) := by
  apply LinearMap.ext
  intro Ψ
  change twoFactorDiracAction D (twoFactorDiracAction D Ψ) =
    (dot D.x D.y) • Ψ
  exact twoFactorDirac_square_apply D Ψ ha hb

end
end InfoGeometry.Canonical.SplitOctonionDiracTwoFactorAlgebraicReduction
