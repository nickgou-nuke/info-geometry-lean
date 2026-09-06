import Mathlib.Tactic
import InfoGeometry.Arithmetic.MobiusDirichletInverseBridge
import InfoGeometry.Arithmetic.MobiusPrimonParity
import InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter
import InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

/-!
# InfoGeometry.Arithmetic.MellinDirichletConvolutionSymmetry

This file packages two already-existing owner lanes into a single theorem-safe
bridge:

1. finite Mellin/Dirichlet arithmetic:
   * Möbius is the Dirichlet inverse of zeta;
   * the finite Möbius Dirichlet polynomial equals the finite fermionic Euler
     product;
   * the finite Majorana/Liouville readout matches the Möbius-graded thermal
     character.

2. coordinate symmetries of the completed-zeta chart:
   * the antiunitary critical mirror fixes exactly the critical locus;
   * in centered coordinates the mirror negates the normal coordinate;
   * the standard `1/2` is the normalized midpoint of the marked pair `0,1`.

No infinite convergence theorem, analytic continuation theorem, or Riemann
property claim is introduced here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.MellinDirichletConvolutionSymmetry

open scoped ArithmeticFunction.Moebius
open scoped BigOperators

open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.MobiusDirichletInverseBridge
open InfoGeometry.Arithmetic.MobiusPrimonParity
open InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

/-! ## Arithmetic / Mellin-Dirichlet side -/

@[rep_depth thermo]
theorem zeta_mul_moebius_eq_one_complex :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * ArithmeticFunction.moebius) = 1 := by
  exact ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)

@[rep_depth thermo]
theorem moebius_mul_zeta_eq_one_complex :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) * ArithmeticFunction.zeta) = 1 := by
  exact ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ)

@[rep_depth thermo]
theorem zeta_moebius_apply_delta (n : ℕ) :
    (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * ArithmeticFunction.moebius) n) =
      if n = 1 then 1 else 0 := by
  rw [zeta_mul_moebius_eq_one_complex]
  by_cases h : n = 1
  · simp [h]
  · simp [h]

@[rep_depth thermo]
theorem moebius_zeta_apply_delta (n : ℕ) :
    (((ArithmeticFunction.moebius : ArithmeticFunction ℂ) * ArithmeticFunction.zeta) n) =
      if n = 1 then 1 else 0 := by
  rw [moebius_mul_zeta_eq_one_complex]
  by_cases h : n = 1
  · simp [h]
  · simp [h]

@[rep_depth thermo]
theorem finite_prime_register_mobius_euler_bridge
    (P : PrimeRegister) (x : ℕ → ℂ) :
    finiteMobiusDirichletPolynomial P x = finiteFermionicEulerProduct P x := by
  exact finiteMobiusDirichletPolynomial_eq_finiteFermionicEulerProduct P x

@[rep_depth thermo]
theorem finite_majorana_character_eq_mobius_graded_character
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteMajoranaChiralityCharacter P q =
      PrimeMajoranaWittenCharacter.mobiusGradedThermalCharacter P q := by
  exact finiteMajoranaChiralityCharacter_eq_mobiusGradedThermalCharacter P q

@[rep_depth thermo]
theorem squarefree_primon_majorana_eq_mobius
    {P : PrimeRegister} (S : SquareFreePrimonState P) :
    S.majoranaChirality = S.mobiusReadout := by
  exact SquareFreePrimonState.majoranaChirality_eq_mobiusReadout S

/-! ## Symmetry / fixed-locus side -/

@[rep_depth thermo]
theorem critical_mirror_fixed_locus_iff_centered_zero (z : ZetaAffineChart) :
    ZetaAffineChart.chartCriticalMirror z = z ↔ ZetaAffineChart.centeredSigma z = 0 := by
  rw [ZetaAffineChart.fixed_chartCriticalMirror_iff_criticalLine,
    ZetaAffineChart.chartCriticalLine_iff_centeredSigma_eq_zero]

@[rep_depth thermo]
theorem critical_mirror_negates_centered_sigma (z : ZetaAffineChart) :
    ZetaAffineChart.centeredSigma (ZetaAffineChart.chartCriticalMirror z) =
      -ZetaAffineChart.centeredSigma z := by
  exact ZetaAffineChart.centeredSigma_chartCriticalMirror z

@[rep_depth thermo]
theorem standard_midpoint_is_half :
    ZetaAffineChart.markedPairMidpoint 0 1 = (1 / 2 : ℝ) := by
  exact ZetaAffineChart.standard_markedPairMidpoint

@[rep_depth thermo]
theorem standard_marked_pair_half_is_fixed :
    ZetaAffineChart.markedPairReflection 0 1 (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
  rw [ZetaAffineChart.standard_markedPairReflection_eq_functional_real]
  norm_num

@[rep_depth thermo]
theorem normalized_midpoint_of_standard_pair_is_half :
    ZetaAffineChart.markedPairScaleCoordinate 0 1
      (ZetaAffineChart.markedPairMidpoint 0 1) = (1 / 2 : ℝ) := by
  simpa using ZetaAffineChart.markedPairScaleCoordinate_midpoint
    (a := 0) (b := 1) (by norm_num : (1 : ℝ) ≠ 0)

@[rep_depth thermo]
theorem standard_reflection_in_scale_coordinate (x : ℝ) :
    ZetaAffineChart.markedPairScaleCoordinate 0 1
      (ZetaAffineChart.markedPairReflection 0 1 x) =
      1 - ZetaAffineChart.markedPairScaleCoordinate 0 1 x := by
  simpa using ZetaAffineChart.markedPairScaleCoordinate_reflection
    (a := 0) (b := 1) (x := x) (by norm_num : (1 : ℝ) ≠ 0)

end InfoGeometry.Arithmetic.MellinDirichletConvolutionSymmetry
