/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Lie.CanonicalZornRegularOperators
import InfoGeometry.Exceptional.CompositionTriality
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Native real Zorn infinitesimal triality

## Audited contract

The carrier, product, norm, conjugation, and Dirac action in this file are the
existing canonical real Zorn objects. The polar form is the unnormalized
`zornNorm.polarBilin`: its value at `(a, b)` is `N(a + b) - N(a) - N(b)`.
Consequently the vector bivector has coefficient `1 / 2`, while the two spin
bivectors are the diagonal blocks of the gamma commutator with coefficient
`1 / 4`. The related triple is ordered `(spinPlus, vector, spinMinus)`.

The triality identity follows from the existing Clifford square relation by
polarization and an identity in the associative algebra of endomorphisms.
It does not assume that Zorn multiplication is associative. Skew-adjointness
is with respect to the existing polar bilinear form. No Clifford faithfulness,
classification of triality triples, or group isomorphism is asserted here.

The source intake uses the opposite signs in the two cross-product slots;
the existing `ZornPinorReconstruction.orientation` supplies that transport.
All statements below use the canonical multiplication directly.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornInfinitesimalTriality

open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

local notation "P" => QuadraticMap.polarBilin (zornNorm (R := ℝ))
local notation "Γ" => (diracGammaLinear (R := ℝ))
local notation "L" => leftRegularRepresentation

/-- Coordinate readout of the existing, unnormalized norm polar form. -/
theorem zornNorm_polarBilin_apply (a b : ZornMatrix ℝ) :
    P a b = a.a * b.b + a.b * b.a -
      ZornMatrix.dot a.x b.y - ZornMatrix.dot a.y b.x := by
  change zornNorm (a + b) - zornNorm a - zornNorm b = _
  simp only [zornNorm_apply, zornNormFun, ZornMatrix.add_a,
    ZornMatrix.add_b, ZornMatrix.add_x, ZornMatrix.add_y,
    ZornMatrix.dot, Pi.add_apply]
  ring

/-- The vector action of a bivector, using the native norm polar form. -/
def vectorBivector (a b : ZornMatrix ℝ) : Module.End ℝ (ZornMatrix ℝ) :=
  (1 / 2 : ℝ) • ((P b).smulRight a - (P a).smulRight b)

/-- The upper spin block of the quarter gamma commutator. -/
def spinPlusBivector (a b : ZornMatrix ℝ) : Module.End ℝ (ZornMatrix ℝ) :=
  (1 / 4 : ℝ) • (L a * L (zornConj b) - L b * L (zornConj a))

/-- The lower spin block of the quarter gamma commutator. -/
def spinMinusBivector (a b : ZornMatrix ℝ) : Module.End ℝ (ZornMatrix ℝ) :=
  (1 / 4 : ℝ) • (L (zornConj a) * L b - L (zornConj b) * L a)

@[simp] theorem vectorBivector_apply (a b v : ZornMatrix ℝ) :
    vectorBivector a b v = (1 / 2 : ℝ) • (P b v • a - P a v • b) := rfl

@[simp] theorem spinPlusBivector_apply (a b s : ZornMatrix ℝ) :
    spinPlusBivector a b s =
      (1 / 4 : ℝ) • (a * (zornConj b * s) - b * (zornConj a * s)) := rfl

@[simp] theorem spinMinusBivector_apply (a b s : ZornMatrix ℝ) :
    spinMinusBivector a b s =
      (1 / 4 : ℝ) • (zornConj a * (b * s) - zornConj b * (a * s)) := rfl

/-- The existing Dirac square identity polarizes to the Clifford CAR. -/
theorem diracGammaLinear_anticommutator (a b : ZornMatrix ℝ) :
    Γ a * Γ b + Γ b * Γ a =
      P a b • (1 : Module.End ℝ (DiracSpinor16 (R := ℝ))) := by
  simpa only [QuadraticMap.polarBilin_apply_apply,
    Algebra.algebraMap_eq_smul_one] using
    (CliffordAlgebra.mul_add_swap_eq_polar_of_forall_mul_self_eq
      (Q := zornNorm (R := ℝ)) Γ diracGamma_sq a b)

/-- The quarter gamma commutator has the two existing spinor summands as its
diagonal blocks; no new matrix or spinor carrier is introduced. -/
theorem dirac_bivector_apply (a b : ZornMatrix ℝ)
    (ψ : DiracSpinor16 (R := ℝ)) :
    ((1 / 4 : ℝ) • (Γ a * Γ b - Γ b * Γ a)) ψ =
      (spinPlusBivector a b ψ.1, spinMinusBivector a b ψ.2) := rfl

/-- The bivector commutator intertwines the vector and Dirac actions. Its proof
uses associativity only in the algebra of native linear endomorphisms. -/
theorem dirac_bivector_commutator (a b v : ZornMatrix ℝ) :
    ((1 / 4 : ℝ) • (Γ a * Γ b - Γ b * Γ a)) * Γ v -
      Γ v * ((1 / 4 : ℝ) • (Γ a * Γ b - Γ b * Γ a)) =
        Γ (vectorBivector a b v) := by
  calc
    ((1 / 4 : ℝ) • (Γ a * Γ b - Γ b * Γ a)) * Γ v -
        Γ v * ((1 / 4 : ℝ) • (Γ a * Γ b - Γ b * Γ a)) =
        (1 / 4 : ℝ) •
          ((Γ a * Γ b - Γ b * Γ a) * Γ v -
            Γ v * (Γ a * Γ b - Γ b * Γ a)) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_sub]
    _ = (1 / 4 : ℝ) •
        (Γ a * (Γ b * Γ v + Γ v * Γ b) -
          Γ b * (Γ a * Γ v + Γ v * Γ a) -
          (Γ a * Γ v + Γ v * Γ a) * Γ b +
          (Γ b * Γ v + Γ v * Γ b) * Γ a) := by
      congr 1
      simp only [mul_sub, sub_mul, mul_add, add_mul, mul_assoc]
      abel
    _ = Γ (vectorBivector a b v) := by
      simp only [diracGammaLinear_anticommutator, vectorBivector_apply,
        mul_smul_comm, smul_mul_assoc, mul_one, one_mul, map_smul, map_sub]
      module

/-- The exact native related-triple identity, obtained by evaluating the
Dirac intertwining identity on the lower spinor summand. -/
theorem bivector_triality_apply (a b v s : ZornMatrix ℝ) :
    spinPlusBivector a b (v * s) =
      vectorBivector a b v * s + v * spinMinusBivector a b s := by
  have h := congrArg
    (fun T : Module.End ℝ (DiracSpinor16 (R := ℝ)) => (T (0, s)).1)
    (dirac_bivector_commutator a b v)
  change
    (((1 / 4 : ℝ) • (Γ a * Γ b - Γ b * Γ a)) (Γ v (0, s))).1 -
      (Γ v (((1 / 4 : ℝ) • (Γ a * Γ b - Γ b * Γ a)) (0, s))).1 =
        (Γ (vectorBivector a b v) (0, s)).1 at h
  simp only [dirac_bivector_apply] at h
  change spinPlusBivector a b (v * s) - v * spinMinusBivector a b s =
    vectorBivector a b v * s at h
  exact sub_eq_iff_eq_add.mp h

/-- The vector action is skew for the actual norm polar form. -/
theorem vectorBivector_skew (a b u v : ZornMatrix ℝ) :
    P (vectorBivector a b u) v + P u (vectorBivector a b v) = 0 := by
  have hsymm (x y : ZornMatrix ℝ) : P x y = P y x :=
    QuadraticMap.polar_comm (zornNorm (R := ℝ)) x y
  have hscalar :
      (1 / 2 : ℝ) * (P b u * P a v - P a u * P b v) +
        (1 / 2 : ℝ) * (P b v * P a u - P a v * P b u) = (0 : ℝ) := by
    ring
  simp only [vectorBivector_apply, map_smul, map_sub, LinearMap.smul_apply,
    LinearMap.sub_apply, smul_eq_mul]
  rw [hsymm u a, hsymm u b]
  exact hscalar

/-- Native Mathlib packaging of the vector action's skew-adjointness. -/
theorem vectorBivector_isSkewAdjoint (a b : ZornMatrix ℝ) :
    LinearMap.IsSkewAdjoint P (vectorBivector a b) := by
  intro u v
  change P (vectorBivector a b u) v = P u (-(vectorBivector a b v))
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left (vectorBivector_skew a b u v)

/-- A constructed related triple for the existing canonical multiplication,
in the established `(spinPlus, vector, spinMinus)` slot order. -/
def bivectorTrialityTriple (a b : ZornMatrix ℝ) :
    InfoGeometry.Exceptional.CompositionTriality.TrialityTriple
      leftRegularRepresentation where
  t₁ := spinPlusBivector a b
  t₂ := vectorBivector a b
  t₃ := spinMinusBivector a b
  triality := by
    intro v s
    exact bivector_triality_apply a b v s

end InfoGeometry.Canonical.ZornInfinitesimalTriality
