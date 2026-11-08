/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.InnerConjugationJet
import InfoGeometry.Algebra.ChiralRealHyperbolicRotor
import InfoGeometry.Krein.DoubledAdjoint
import InfoGeometry.Krein.Representation
import InfoGeometry.OperatorAlgebra.KreinInnerDerivation

/-!
# Algebraic Hestenes–Krein generator and Clifford inversion

Use the actual operators on `DoubledSpace E`, not a replacement matrix carrier.
With the installed metric `spectral_epsilon`, the split generator is the
Krein-skew sheet swap `modular_j`. The negative Clifford vector `complex_i`
reverses this generator and its real polynomial rotors. It is not identified
with the metric involution or with a complex anti-linear conjugation.

The infinitesimal statement is exact in Mathlib's dual-number ring. The rotor
coefficients satisfy `c*c-s*s=1`; no particular time parametrization is assumed.
Coordinate convention checks: `scripts/check_hestenes_weyl_generator.py`.
-/

noncomputable section

namespace InfoGeometry.Krein.HestenesWeylGenerator

open InfoGeometry.OperatorAlgebra
open TrivSqZeroExt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The native negative Clifford vector, with its two-sided inverse. -/
def inversion : (DoubledEnd E)ˣ where
  val := complex_i
  inv := -complex_i
  val_inv := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [complex_i, modular_j, spectral_epsilon]
  inv_val := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [complex_i, modular_j, spectral_epsilon]

local notation "G" => (modular_j : DoubledEnd E)
local notation "W" => inversion (E := E)

/-- The Clifford inversion reverses the actual split generator. -/
theorem inversion_generator :
    (W : DoubledEnd E) * G * (↑W⁻¹ : DoubledEnd E) = -G := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [inversion, complex_i, modular_j, spectral_epsilon]

/-- The real rotor's reverse is its Krein adjoint for this fixed metric. -/
theorem rotor_kreinAdjoint (c s : ℝ) :
    KreinSpace.kreinAdjoint (hyperbolicRotor G c s) =
      reverseHyperbolicRotor G c s := by
  have hG := modular_j_kreinSkewAdjoint (E := E)
  change KreinSpace.kreinAdjoint G = -G at hG
  simp only [hyperbolicRotor, reverseHyperbolicRotor, KreinSpace.kreinAdjoint_add,
    KreinSpace.kreinAdjoint_smul, hG, smul_neg]
  rw [show KreinSpace.kreinAdjoint (1 : DoubledEnd E) = 1 from
    KreinSpace.kreinAdjoint_id]
  exact (sub_eq_add_neg _ _).symm

/-- A normalized real rotor is a genuine unit, not just a sandwich expression. -/
def rotorUnit (c s : ℝ) (hcs : c * c - s * s = 1) : (DoubledEnd E)ˣ where
  val := hyperbolicRotor G c s
  inv := reverseHyperbolicRotor G c s
  val_inv := hyperbolicRotor_mul_reverse _ c s (modular_j_involution E) hcs
  inv_val := reverseHyperbolicRotor_mul _ c s (modular_j_involution E) hcs

/-- Krein preservation is derived from the adjoint and inverse laws. -/
theorem rotor_isKreinIsometry (c s : ℝ) (hcs : c * c - s * s = 1) :
    KreinSpace.IsKreinIsometry (hyperbolicRotor G c s) := by
  apply (KreinSpace.isKreinIsometry_iff_star_comp_self _).2
  change KreinSpace.kreinAdjoint (hyperbolicRotor G c s) * hyperbolicRotor G c s = 1
  rw [rotor_kreinAdjoint]
  exact reverseHyperbolicRotor_mul _ c s (modular_j_involution E) hcs

/-- Inversion sends every polynomial rotor to its reverse. -/
theorem inversion_rotor (c s : ℝ) :
    (W : DoubledEnd E) * hyperbolicRotor G c s * (↑W⁻¹ : DoubledEnd E) =
      reverseHyperbolicRotor G c s := by
  calc
    _ = c • ((W : DoubledEnd E) * (↑W⁻¹ : DoubledEnd E)) +
        s • ((W : DoubledEnd E) * G * (↑W⁻¹ : DoubledEnd E)) := by
      simp only [hyperbolicRotor, mul_add, add_mul, mul_smul_comm,
        smul_mul_assoc, mul_one]
    _ = _ := by
      rw [Units.mul_inv, inversion_generator]
      simp only [reverseHyperbolicRotor, smul_neg]
      exact (sub_eq_add_neg _ _).symm

/-- The reversal holds in the unit group itself. -/
theorem inversion_rotorUnit (c s : ℝ) (hcs : c * c - s * s = 1) :
    W * rotorUnit (E := E) c s hcs * W⁻¹ = (rotorUnit c s hcs)⁻¹ := by
  apply Units.ext
  exact inversion_rotor c s

/-- Inversion intertwines the infinitesimal action with its negative. -/
theorem inversion_commutator (X : DoubledEnd E) :
    (W : DoubledEnd E) * kreinCommutator G X * (↑W⁻¹ : DoubledEnd E) =
      -kreinCommutator G ((W : DoubledEnd E) * X * (↑W⁻¹ : DoubledEnd E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [inversion, kreinCommutator, complex_i, modular_j, spectral_epsilon]
  abel

/-- The native commutator is the exact first-order coefficient of conjugation. -/
theorem firstJet (X : DoubledEnd E) :
    (InfoGeometry.Core.InnerConjugationJet.unit G : DualNumber (DoubledEnd E)) *
        inl X * (↑(InfoGeometry.Core.InnerConjugationJet.unit G)⁻¹ :
          DualNumber (DoubledEnd E)) =
      inl X + inr (kreinCommutator G X) := by
  simpa only [inr_zero, add_zero, zero_add, kreinCommutator_apply] using
    InfoGeometry.Core.InnerConjugationJet.conjugate G X 0

/-- The infinitesimal action on the metric sign is the native real phase axis. -/
theorem commutator_spectral_epsilon :
    kreinCommutator G spectral_epsilon = (2 : ℝ) • (complex_i : DoubledEnd E) := by
  change (G).comp (spectral_epsilon (E := E)) - (spectral_epsilon (E := E)).comp G = _
  rw [spectral_epsilon_comp_modular_j]
  change (complex_i : DoubledEnd E) - -complex_i = (2 : ℝ) • complex_i
  module

/-- A concrete nonzero action on the native real doubled carrier. -/
theorem commutator_nonzero :
    kreinCommutator (modular_j : DoubledEnd ℝ) spectral_epsilon ≠ 0 := by
  intro h
  have hv := congrArg (fun T : DoubledEnd ℝ =>
    WithLp.snd (T (to_doubled (1 : ℝ) 0))) h
  norm_num [commutator_spectral_epsilon, complex_i, modular_j, spectral_epsilon] at hv

/-- Bilingual transport: the Clifford commutator acts on the same doubled carrier. -/
theorem clifford_commutator (X : CliffordAlgebra InfoGeometry.Clifford.splitQ11) :
    cl11Rep (E := E)
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0) * X -
        X * CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)) =
      kreinCommutator G (cl11Rep X) := by
  simp only [map_sub, map_mul, cl11Rep_ι_one_zero, kreinCommutator_apply]

/-- Bilingual transport of the rotor, without changing its coefficients. -/
theorem clifford_rotor (c s : ℝ) :
    cl11Rep (E := E) (hyperbolicRotor
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)) c s) =
      hyperbolicRotor G c s := by
  simp only [hyperbolicRotor, map_add, map_smul, map_one, cl11Rep_ι_one_zero]

end InfoGeometry.Krein.HestenesWeylGenerator
