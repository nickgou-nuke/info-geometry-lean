/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealDualTwistor
import InfoGeometry.Twistor.RealTwistorPolynomialCCR
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.StdBasis

/-!
# Soldering real polynomial CCR to the genuine dual carrier

The standard finite coordinate basis supplies a native linear equivalence
with the algebraic dual.  Its evaluation pairing is proved to equal the
coefficient contraction used by polynomial quantization.  Consequently the
CCR are stated on `V × Module.Dual ℝ V` itself.  This finite-dimensional
coordinate identification is not applied to the infinite polynomial module.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealPolynomialCCR

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual basis-induced equivalence from coordinates to their dual. -/
def coordinateDual : Coordinates ι ≃ₗ[ℝ] Module.Dual ℝ (Coordinates ι) :=
  (Pi.basisFun ℝ ι).toDualEquiv

theorem coordinateDual_apply (a b : Coordinates ι) :
    coordinateDual b a = contraction a b := by
  have ha : ∑ i, a i • (Pi.basisFun ℝ ι) i = a := by
    simpa using (Pi.basisFun ℝ ι).sum_repr a
  calc
    coordinateDual b a = coordinateDual b (∑ i, a i • (Pi.basisFun ℝ ι) i) :=
      congrArg (coordinateDual b) ha.symm
    _ = contraction a b := by
      simp only [coordinateDual, Module.Basis.toDualEquiv_apply, map_sum, map_smul,
        Module.Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, contraction]

/-- Exact finite-coordinate identification of the native real dual phase space. -/
def dualPhaseEquiv : Coeff ι ≃ₗ[ℝ] RealDualTwistor.Carrier (Coordinates ι) :=
  (LinearEquiv.refl ℝ (Coordinates ι)).prodCongr coordinateDual

@[simp] theorem dualPhaseEquiv_apply (A : Coeff ι) :
    dualPhaseEquiv A = (A.1, coordinateDual A.2) := rfl

/-- Compatibility of the operator CCR form with canonical dual evaluation. -/
theorem symplecticForm_dualPhaseEquiv (A B : Coeff ι) :
    RealDualTwistor.symplecticForm (dualPhaseEquiv A) (dualPhaseEquiv B) = omega A B := by
  simp only [dualPhaseEquiv_apply, RealDualTwistor.symplecticForm_apply,
    coordinateDual_apply, omega]
  rw [contraction_comm B.1 A.2]

/-- Polynomial quantization takes an actual vector and an actual covector. -/
def quantizeDual (h : ℝ) (A : RealDualTwistor.Carrier (Coordinates ι)) : Operator ι :=
  quantize h (dualPhaseEquiv.symm A)

/-- The central CCR coefficient is the canonical symplectic evaluation form. -/
theorem quantizeDual_commutator (h : ℝ)
    (A B : RealDualTwistor.Carrier (Coordinates ι)) :
    quantizeDual h A * quantizeDual h B - quantizeDual h B * quantizeDual h A =
      (h * RealDualTwistor.symplecticForm A B) • (1 : Operator ι) := by
  have hs := symplecticForm_dualPhaseEquiv (dualPhaseEquiv.symm A) (dualPhaseEquiv.symm B)
  simp only [LinearEquiv.apply_symm_apply] at hs
  unfold quantizeDual
  rw [quantize_commutator, ← hs]

end InfoGeometry.Twistor.RealPolynomialCCR
