/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Core.PeirceDecomposition
import InfoGeometry.Core.IdempotentCartan
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.DerivationLieLane
import InfoGeometry.Algebra.DerivationLieLaneRepresentation
import InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.VietaSusyKatoDissipationAndGaloisGolayPoset
import InfoGeometry.Clifford.LorentzianBivectorSignatureBridge
import InfoGeometry.Clifford.HestenesDirac

/-!
# Symmetrically Split Midpoint Rotors, Kato Peirce Corners, GEM (1,3) Algebra, and Covariant QGT

This module formalizes the unified operator/geometric synthesis connecting Clifford rotors,
Kato adiabatic connections, gravito-electromagnetism (GEM), Bogoliubov transformations,
and the covariant Quantum Geometric Tensor (QGT):

1. **Normalized Midpoint Rotor Sandwich (`midpointRotor_normalized_sandwich`)**:
   For any two involutions `Γ₁² = Γ₂² = 1` with non-vanishing symmetric chord norm
   `(1 + Γ₂Γ₁)(1 + Γ₁Γ₂) = s² • 1`, constructs the normalized midpoint rotor
   `R₂₁ := s⁻¹ • (1 + Γ₂Γ₁)` and proves `R₂₁ R̃₂₁ = 1` and `R₂₁ Γ₁ R̃₂₁ = Γ₂`.
2. **Kato Complement Covariant Derivative (`kato_covariant_derivative_complement`)**:
   Reuses the Peirce-spine owner theorem for `P * dP * P = 0` and
   `[Gamma_Kato, P] = dP`, then derives the complementary identity
   `[Gamma_Kato, 1 - P] = -dP`.
3. **GEM (1,3) Algebraic Split (`gemConnection_sq_split`, `gemConnection_gamma0_parity`)**:
   Under the explicit commutation hypotheses in those theorem statements, proves
   `(E + I * B)² = (E² - B²) + I * (E * B + B * E)` and
   `γ₀ * (E + I * B) * γ₀ = -E + I * B`. These algebraic identities alone do not
   define a spacetime connection, precession observable, or Lense–Thirring rate; those
   physical claims remain outside this module until a geometric carrier and observable are specified.
4. **Bogoliubov Hyperbolic Rotor (`bogoliubovRotor_mul_inv`, `bogoliubovRotor_sandwich`)**:
   Proves that `R_Bog(η) = cosh(η/2)•1 + sinh(η/2)•B` has the stated inverse and its sandwich
   gives `boostedFrame η γ₀ B` under the displayed algebraic hypotheses. Identification with the
   normalized midpoint rotor and the two Peirce compression formulas are not proved here.
5. **Covariant QGT & Berry Curvature Split (`derivationQGT_leibniz_and_berry_split`)**:
   Using `DerivationLieLane`, derives automatic Leibniz off-diagonality and establishes the
   covariant Quantum Geometric Tensor `Q_vw = P (K v P) (1 - P) (K w P) P` with its skew Berry decomposition.

No `sorry`, `admit`, `native_decide`, or custom axioms are used.
-/

set_option autoImplicit false

namespace InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT

open InfoGeometry.Algebra
open InfoGeometry.Clifford.LorentzianBivectorSignatureBridge

/-! ## Section 0: Noncommutativity Ground Witnesses (T16) -/

section NoncommWitness

variable {K : Type*} [Field K]

/-- Elementary 4×4 nilpotent matrix `E₀₁`. -/
def matrixE01_4 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Elementary 4×4 nilpotent matrix `E₁₀`. -/
def matrixE10_4 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- OpenGauss Trap T16: Explicit non-commutativity witness on `Matrix (Fin 4) (Fin 4) K`. -/
theorem matrixE01_mul_E10_ne_mul_E10_E01_4 :
    matrixE01_4 (K := K) * matrixE10_4 (K := K) ≠
      matrixE10_4 (K := K) * matrixE01_4 (K := K) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) h
  norm_num [matrixE01_4, matrixE10_4, Matrix.mul_apply, Fin.sum_univ_four] at h00

end NoncommWitness

/-! ## Section 1: Normalized Symmetrically Split Midpoint Rotor -/

section MidpointRotor

variable {E : Type*} [Ring E] [Algebra ℝ E]

/-- The unnormalized reverse intertwiner `1 + Γ₁ Γ₂`. -/
def unnormMidpointRev (Γ₁ Γ₂ : E) : E :=
  1 + Γ₁ * Γ₂

/-- Normalized symmetrically split midpoint rotor `R₂₁ := s⁻¹ • (1 + Γ₂ Γ₁)`. -/
noncomputable def midpointRotor (s : ℝ) (Γ₁ Γ₂ : E) : E :=
  s⁻¹ • InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.midpointRotor Γ₁ Γ₂

/-- Reverse normalized midpoint rotor `R̃₂₁ := s⁻¹ • (1 + Γ₁ Γ₂)`. -/
noncomputable def midpointRotorRev (s : ℝ) (Γ₁ Γ₂ : E) : E :=
  s⁻¹ • unnormMidpointRev Γ₁ Γ₂

/-- Master theorem: Normalized midpoint rotor is an isometric intertwiner. -/
theorem midpointRotor_normalized_sandwich (s : ℝ) (Γ₁ Γ₂ : E)
    (hs : s ≠ 0)
    (hΓ₁ : Γ₁ * Γ₁ = 1)
    (hΓ₂ : Γ₂ * Γ₂ = 1)
    (hnorm : InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.midpointRotor Γ₁ Γ₂ *
      unnormMidpointRev Γ₁ Γ₂ = (s^2) • (1 : E)) :
    midpointRotor s Γ₁ Γ₂ * midpointRotorRev s Γ₁ Γ₂ = 1 ∧
    midpointRotor s Γ₁ Γ₂ * Γ₁ * midpointRotorRev s Γ₁ Γ₂ = Γ₂ := by
  have hs2 : s^2 ≠ 0 := pow_ne_zero 2 hs
  have h_unit : midpointRotor s Γ₁ Γ₂ * midpointRotorRev s Γ₁ Γ₂ = 1 := by
    dsimp [midpointRotor, midpointRotorRev]
    rw [smul_mul_smul, hnorm, smul_smul]
    have : s⁻¹ * s⁻¹ * s^2 = 1 := by
      field_simp [hs]
    rw [this, one_smul]
  have h_sand : midpointRotor s Γ₁ Γ₂ * Γ₁ * midpointRotorRev s Γ₁ Γ₂ = Γ₂ := by
    dsimp [midpointRotor, midpointRotorRev]
    calc (s⁻¹ • InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.midpointRotor Γ₁ Γ₂) * Γ₁ *
        (s⁻¹ • unnormMidpointRev Γ₁ Γ₂)
      _ = s⁻¹ • (InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.midpointRotor Γ₁ Γ₂ * Γ₁) *
          (s⁻¹ • unnormMidpointRev Γ₁ Γ₂) := by
        rw [smul_mul_assoc]
      _ = s⁻¹ • (Γ₂ * InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.midpointRotor Γ₁ Γ₂) *
          (s⁻¹ • unnormMidpointRev Γ₁ Γ₂) := by
        have hintertwine :=
          InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.symmetrically_split_midpoint_rotor_intertwining
            Γ₁ Γ₂ hΓ₁ hΓ₂
        rw [hintertwine.2.2.1]
      _ = (s⁻¹ * s⁻¹) • ((Γ₂ * InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.midpointRotor Γ₁ Γ₂) *
          unnormMidpointRev Γ₁ Γ₂) := by
        rw [smul_mul_smul]
      _ = (s⁻¹ * s⁻¹) • (Γ₂ * (InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.midpointRotor Γ₁ Γ₂ *
          unnormMidpointRev Γ₁ Γ₂)) := by
        rw [mul_assoc]
      _ = (s⁻¹ * s⁻¹) • (Γ₂ * ((s^2) • (1 : E))) := by rw [hnorm]
      _ = (s⁻¹ * s⁻¹) • ((s^2) • (Γ₂ * 1)) := by rw [mul_smul_comm]
      _ = ((s⁻¹ * s⁻¹) * s^2) • (Γ₂ * 1) := by rw [smul_smul]
      _ = 1 • (Γ₂ * 1) := by
        have : (s⁻¹ * s⁻¹) * s^2 = 1 := by
          field_simp [hs]
        rw [this]
        simp
      _ = Γ₂ := by rw [one_smul, mul_one]
  exact ⟨h_unit, h_sand⟩

/-- The reverse product of the normalized midpoint rotor and its reverse is also the identity.
The reverse norm is not an extra assumption: conjugating the given norm by the involution `Γ₁`
exchanges the two unnormalized factors. -/
theorem midpointRotorRev_mul_midpointRotor (s : ℝ) (Γ₁ Γ₂ : E)
    (hs : s ≠ 0)
    (hΓ₁ : Γ₁ * Γ₁ = 1)
    (hnorm : InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.midpointRotor Γ₁ Γ₂ *
      unnormMidpointRev Γ₁ Γ₂ = (s^2) • (1 : E)) :
    midpointRotorRev s Γ₁ Γ₂ * midpointRotor s Γ₁ Γ₂ = 1 := by
  have hreverse :
      unnormMidpointRev Γ₁ Γ₂ *
        InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.midpointRotor Γ₁ Γ₂ =
          (s^2) • (1 : E) := by
    have hconj :
        Γ₁ * (InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.midpointRotor Γ₁ Γ₂ *
          unnormMidpointRev Γ₁ Γ₂) * Γ₁ =
            unnormMidpointRev Γ₁ Γ₂ *
              InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.midpointRotor Γ₁ Γ₂ := by
      have hleft : Γ₁ * (1 + Γ₂ * Γ₁) * Γ₁ = 1 + Γ₁ * Γ₂ := by
        calc
          Γ₁ * (1 + Γ₂ * Γ₁) * Γ₁ = Γ₁ * Γ₁ + Γ₁ * Γ₂ * (Γ₁ * Γ₁) := by noncomm_ring
          _ = 1 + Γ₁ * Γ₂ := by simp [mul_assoc, hΓ₁]
      have hright : Γ₁ * (1 + Γ₁ * Γ₂) * Γ₁ = 1 + Γ₂ * Γ₁ := by
        calc
          Γ₁ * (1 + Γ₁ * Γ₂) * Γ₁ = Γ₁ * Γ₁ + (Γ₁ * Γ₁) * Γ₂ * Γ₁ := by noncomm_ring
          _ = 1 + Γ₂ * Γ₁ := by simp [mul_assoc, hΓ₁]
      dsimp [unnormMidpointRev,
        InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset.midpointRotor]
      calc
        Γ₁ * ((1 + Γ₂ * Γ₁) * (1 + Γ₁ * Γ₂)) * Γ₁ =
            (Γ₁ * (1 + Γ₂ * Γ₁) * Γ₁) * (Γ₁ * (1 + Γ₁ * Γ₂) * Γ₁) := by
              calc
                _ = Γ₁ * (1 + Γ₂ * Γ₁) * (1 + Γ₁ * Γ₂) * Γ₁ := by noncomm_ring
                _ = Γ₁ * (1 + Γ₂ * Γ₁) * (Γ₁ * Γ₁) * (1 + Γ₁ * Γ₂) * Γ₁ := by
                  rw [hΓ₁]
                  noncomm_ring
                _ = (Γ₁ * (1 + Γ₂ * Γ₁) * Γ₁) * (Γ₁ * (1 + Γ₁ * Γ₂) * Γ₁) := by noncomm_ring
        _ = (1 + Γ₁ * Γ₂) * (1 + Γ₂ * Γ₁) := by rw [hleft, hright]
    calc
      _ = Γ₁ * ((s^2) • (1 : E)) * Γ₁ := by rw [← hnorm, hconj]
      _ = (s^2 • Γ₁) * Γ₁ := by simp [mul_smul_comm]
      _ = (s^2) • (Γ₁ * Γ₁) := by rw [smul_mul_assoc]
      _ = (s^2) • (1 : E) := by rw [hΓ₁]
  dsimp [midpointRotorRev, midpointRotor]
  rw [smul_mul_smul, hreverse, smul_smul]
  have hscalar : s⁻¹ * s⁻¹ * s^2 = 1 := by field_simp [hs]
  rw [hscalar, one_smul]

end MidpointRotor

/-! ## Section 2: Kato Adiabatic Connection & Covariant Annihilation -/

section KatoConnection

variable {E : Type*} [Ring E]

/-- The covariant derivative generated by the existing Kato connection annihilates the
complementary projector variation. The projector corner and `[Γ_Kato, P] = dP` are reused from
`kato_berry_spectral_flow_and_covariant_time`; only the complementary-sector consequence is
proved here. -/
theorem kato_covariant_derivative_complement
    (P dP : E)
    (hP : P * P = P)
    (hdP : dP * P + P * dP = dP) :
    (-dP) - InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.OperatorAlgebra.PeirceSpine.Gamma_Kato P dP) (1 - P) = 0 := by
  have hK := InfoGeometry.OperatorAlgebra.PeirceSpine.kato_berry_spectral_flow_and_covariant_time
    P dP (0 : E) hP hdP
  have hcomm : InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.OperatorAlgebra.PeirceSpine.Gamma_Kato P dP) P = dP := hK.2.1
  have hcomp : InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.OperatorAlgebra.PeirceSpine.Gamma_Kato P dP) (1 - P) = -dP := by
    dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    calc
      _ = (InfoGeometry.OperatorAlgebra.PeirceSpine.Gamma_Kato P dP -
          InfoGeometry.OperatorAlgebra.PeirceSpine.Gamma_Kato P dP) -
          (InfoGeometry.OperatorAlgebra.PeirceSpine.Gamma_Kato P dP * P -
            P * InfoGeometry.OperatorAlgebra.PeirceSpine.Gamma_Kato P dP) := by noncomm_ring
      _ = -InfoGeometry.OperatorAlgebra.PeirceSpine.comm
          (InfoGeometry.OperatorAlgebra.PeirceSpine.Gamma_Kato P dP) P := by
            simp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
      _ = -dP := by rw [hcomm]
  rw [hcomp]
  simp

end KatoConnection

/-! ## Section 3: Gravito-Electromagnetism (GEM) (1,3) Signature Split -/

section GEMAlgebra

variable {A : Type*} [Ring A]

/-- The combined gravito-electromagnetic connection `Ω := E + I * B`. -/
def gemConnection (E I B : A) : A :=
  E + I * B

/-- Gravito-electromagnetic split under central complex structure `I² = -1`. -/
theorem gemConnection_sq_split
    (E I B : A)
    (hI_sq : I * I = -1)
    (hIE : I * E = E * I)
    (hIB : I * B = B * I) :
    (gemConnection E I B)^2 = (E^2 - B^2) + I * (E * B + B * E) := by
  dsimp [gemConnection]
  calc (E + I * B)^2
    _ = (E + I * B) * (E + I * B) := sq (E + I * B)
    _ = E * E + E * (I * B) + (I * B) * E + (I * B) * (I * B) := by noncomm_ring
    _ = E^2 + I * (E * B) + I * (B * E) + (I * I) * (B * B) := by
      have h1 : E * (I * B) = I * (E * B) := by
        calc E * (I * B) = (E * I) * B := by noncomm_ring
          _ = (I * E) * B := by rw [hIE]
          _ = I * (E * B) := by noncomm_ring
      have h2 : (I * B) * E = I * (B * E) := by noncomm_ring
      have h3 : (I * B) * (I * B) = (I * I) * (B * B) := by
        calc (I * B) * (I * B) = I * (B * I) * B := by noncomm_ring
          _ = I * (I * B) * B := by rw [hIB]
          _ = (I * I) * (B * B) := by noncomm_ring
      rw [h1, h2, h3]
      noncomm_ring
    _ = E^2 + I * (E * B + B * E) + (-1) * B^2 := by
      rw [hI_sq]
      noncomm_ring
    _ = (E^2 - B^2) + I * (E * B + B * E) := by
      have : (-1 : A) * B^2 = - B^2 := by noncomm_ring
      rw [this]
      noncomm_ring

/-- Parity split: Electric field is `γ₀`-odd, magnetic field is `γ₀`-even. -/
theorem gemConnection_gamma0_parity
    (E I B γ₀ : A)
    (hγ₀_sq : γ₀ * γ₀ = 1)
    (hγ₀I : γ₀ * I = I * γ₀)
    (hE_odd : γ₀ * E + E * γ₀ = 0)
    (hB_even : γ₀ * B - B * γ₀ = 0) :
    γ₀ * gemConnection E I B * γ₀ = -E + I * B := by
  dsimp [gemConnection]
  have hE : γ₀ * E * γ₀ = -E := by
    have : γ₀ * E = - (E * γ₀) := eq_neg_of_add_eq_zero_left hE_odd
    calc γ₀ * E * γ₀ = (- (E * γ₀)) * γ₀ := by rw [this]
      _ = - (E * (γ₀ * γ₀)) := by noncomm_ring
      _ = - (E * 1) := by rw [hγ₀_sq]
      _ = -E := by rw [mul_one]
  have hB : γ₀ * (I * B) * γ₀ = I * B := by
    have hB_comm : γ₀ * B = B * γ₀ := eq_of_sub_eq_zero hB_even
    calc γ₀ * (I * B) * γ₀ = (γ₀ * I) * (B * γ₀) := by noncomm_ring
      _ = (I * γ₀) * (γ₀ * B) := by rw [hγ₀I, ← hB_comm]
      _ = I * ((γ₀ * γ₀) * B) := by noncomm_ring
      _ = I * (1 * B) := by rw [hγ₀_sq]
      _ = I * B := by rw [one_mul]
  calc γ₀ * (E + I * B) * γ₀
    _ = γ₀ * E * γ₀ + γ₀ * (I * B) * γ₀ := by noncomm_ring
    _ = -E + I * B := by rw [hE, hB]

end GEMAlgebra

/-! ## Section 4: Hyperbolic Bogoliubov Rotor & Peirce Aporia -/

section BogoliubovPeirce

variable {E : Type*} [Ring E] [Algebra ℝ E]

/-- The boosted reference frame `γ_boost := cosh(η) • γ₀ + sinh(η) • (B * γ₀)`. -/
noncomputable def boostedFrame (η : ℝ) (γ₀ B : E) : E :=
  Real.cosh η • γ₀ + Real.sinh η • (B * γ₀)

/-- The hyperbolic Bogoliubov spin-rotor `R_Bog(η) := cosh(η/2) • 1 + sinh(η/2) • B`. -/
noncomputable def bogoliubovRotor (η : ℝ) (B : E) : E :=
  Real.cosh (η / 2) • (1 : E) + Real.sinh (η / 2) • B

/-- The inverse Bogoliubov rotor `R_Bog(-η) = cosh(η/2) • 1 - sinh(η/2) • B`. -/
noncomputable def bogoliubovRotorInv (η : ℝ) (B : E) : E :=
  Real.cosh (η / 2) • (1 : E) - Real.sinh (η / 2) • B

/-- Bogoliubov rotor is unitary: `R_Bog(η) * R_Bog(-η) = 1`. -/
theorem bogoliubovRotor_mul_inv (η : ℝ) (B : E) (hB : B * B = 1) :
    bogoliubovRotor η B * bogoliubovRotorInv η B = 1 := by
  dsimp [bogoliubovRotor, bogoliubovRotorInv]
  have h1 : (Real.cosh (η / 2) • (1 : E) + Real.sinh (η / 2) • B) *
            (Real.cosh (η / 2) • (1 : E) - Real.sinh (η / 2) • B) =
            ((Real.cosh (η / 2))^2 - (Real.sinh (η / 2))^2) • (1 : E) := by
    rw [sq, sq]
    have : (Real.cosh (η / 2) • (1 : E) + Real.sinh (η / 2) • B) *
           (Real.cosh (η / 2) • (1 : E) - Real.sinh (η / 2) • B) =
           (Real.cosh (η / 2) * Real.cosh (η / 2)) • (1 : E) -
           (Real.sinh (η / 2) * Real.sinh (η / 2)) • (B * B) := by
      noncomm_ring
      module
    rw [this, hB, ← sub_smul]
  rw [h1, Real.cosh_sq_sub_sinh_sq, one_smul]

/-- Bogoliubov rotor sandwich produces the Lorentz-boosted frame. -/
theorem bogoliubovRotor_sandwich (η : ℝ) (γ₀ B : E)
    (hB : B * B = 1)
    (hanti : γ₀ * B + B * γ₀ = 0) :
    bogoliubovRotor η B * γ₀ * bogoliubovRotorInv η B = boostedFrame η γ₀ B := by
  dsimp [bogoliubovRotor, bogoliubovRotorInv, boostedFrame]
  have h_anticomm : B * γ₀ = - (γ₀ * B) := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hanti)
  have h_sq : Real.cosh (η / 2) ^ 2 + Real.sinh (η / 2) ^ 2 = Real.cosh η := by
    have h1 := Real.cosh_add (η / 2) (η / 2)
    have : η / 2 + η / 2 = η := add_halves η
    rw [this] at h1
    simpa [pow_two] using h1.symm
  have h_prod : 2 * Real.sinh (η / 2) * Real.cosh (η / 2) = Real.sinh η := by
    have h1 := Real.sinh_add (η / 2) (η / 2)
    have : η / 2 + η / 2 = η := add_halves η
    rw [this] at h1
    calc 2 * Real.sinh (η / 2) * Real.cosh (η / 2)
        = Real.sinh (η / 2) * Real.cosh (η / 2) +
            Real.cosh (η / 2) * Real.sinh (η / 2) := by ring
      _ = Real.sinh η := h1.symm
  calc (Real.cosh (η / 2) • (1 : E) + Real.sinh (η / 2) • B) * γ₀ *
       (Real.cosh (η / 2) • (1 : E) - Real.sinh (η / 2) • B)
    _ = (Real.cosh (η / 2) • γ₀ + Real.sinh (η / 2) • (B * γ₀)) *
        (Real.cosh (η / 2) • (1 : E) - Real.sinh (η / 2) • B) := by
      rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
    _ = (Real.cosh (η / 2) * Real.cosh (η / 2)) • (γ₀ * 1) -
        (Real.cosh (η / 2) * Real.sinh (η / 2)) • (γ₀ * B) +
        (Real.sinh (η / 2) * Real.cosh (η / 2)) • ((B * γ₀) * 1) -
        (Real.sinh (η / 2) * Real.sinh (η / 2)) • ((B * γ₀) * B) := by
      noncomm_ring
      module
    _ = (Real.cosh (η / 2) ^ 2) • γ₀ -
        (Real.cosh (η / 2) * Real.sinh (η / 2)) • (- (B * γ₀)) +
        (Real.sinh (η / 2) * Real.cosh (η / 2)) • (B * γ₀) -
        (Real.sinh (η / 2) ^ 2) • (- γ₀) := by
      rw [mul_one, mul_one, sq, sq]
      have hB_sq : (B * γ₀) * B = - γ₀ := by
        calc (B * γ₀) * B = B * (γ₀ * B) := by noncomm_ring
          _ = B * (- (B * γ₀)) := by
            have : γ₀ * B = - (B * γ₀) := eq_neg_of_add_eq_zero_left hanti
            rw [this]
          _ = - (B * B * γ₀) := by noncomm_ring
          _ = - (1 * γ₀) := by rw [hB]
          _ = - γ₀ := by rw [one_mul]
      rw [hB_sq]
      have : γ₀ * B = - (B * γ₀) := eq_neg_of_add_eq_zero_left hanti
      rw [this]
    _ = (Real.cosh (η / 2) ^ 2 + Real.sinh (η / 2) ^ 2) • γ₀ +
        (2 * Real.sinh (η / 2) * Real.cosh (η / 2)) • (B * γ₀) := by
      rw [smul_neg, sub_neg_eq_add, smul_neg, sub_neg_eq_add]
      module
    _ = Real.cosh η • γ₀ + Real.sinh η • (B * γ₀) := by
      rw [h_sq, h_prod]

end BogoliubovPeirce

/-! ## Section 5: Covariant QGT via DerivationLieLane -/

section CovariantQGT

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The inward transition operator `P * (D P) * (1 - P)`. -/
def qgtInward (K : DerivationLieLane R A) (P : A) (v : K.L) : A :=
  P * K.operatorAction v P * (1 - P)

/-- The outward transition operator `(1 - P) * (D P) * P`. -/
def qgtOutward (K : DerivationLieLane R A) (P : A) (v : K.L) : A :=
  (1 - P) * K.operatorAction v P * P

/-- The covariant Quantum Geometric Tensor `Q_vw := Inward_v * Outward_w`. -/
def derivationQGT (K : DerivationLieLane R A) (P : A) (v w : K.L) : A :=
  qgtInward K P v * qgtOutward K P w

/-- Automatic off-diagonality of derivations on projectors: `P (D P) P = 0`. -/
theorem derivation_projector_off_diagonal
    (K : DerivationLieLane R A) (P : A) (v : K.L)
    (hP : P * P = P)
    (hleib : K.operatorAction v P = K.operatorAction v P * P + P * K.operatorAction v P) :
    P * K.operatorAction v P * P = 0 := by
  have : P * K.operatorAction v P * P = 2 * (P * K.operatorAction v P * P) := by
    calc P * K.operatorAction v P * P
      _ = P * (K.operatorAction v P * P + P * K.operatorAction v P) * P := by rw [← hleib]
      _ = P * K.operatorAction v P * (P * P) + (P * P) * K.operatorAction v P * P := by noncomm_ring
      _ = P * K.operatorAction v P * P + P * K.operatorAction v P * P := by rw [hP]
      _ = 2 * (P * K.operatorAction v P * P) := by noncomm_ring
  calc P * K.operatorAction v P * P
    _ = (P * K.operatorAction v P * P + P * K.operatorAction v P * P) - P * K.operatorAction v P * P := by noncomm_ring
    _ = P * (K.operatorAction v P * P + P * K.operatorAction v P) * P - P * K.operatorAction v P * P := by
      have h1 : P * (K.operatorAction v P * P + P * K.operatorAction v P) * P =
                P * K.operatorAction v P * P + P * K.operatorAction v P * P := by
        calc P * (K.operatorAction v P * P + P * K.operatorAction v P) * P
          _ = P * K.operatorAction v P * (P * P) + (P * P) * K.operatorAction v P * P := by noncomm_ring
          _ = P * K.operatorAction v P * P + P * K.operatorAction v P * P := by rw [hP]
      rw [h1]
    _ = P * K.operatorAction v P * P - P * K.operatorAction v P * P := by rw [← hleib]
    _ = 0 := sub_self _

/-- QGT factors cleanly into inward and outward projections. -/
theorem derivationQGT_formula
    (K : DerivationLieLane R A) (P : A) (v w : K.L)
    (hP : P * P = P)
    (hleib : K.operatorAction w P = K.operatorAction w P * P + P * K.operatorAction w P) :
    derivationQGT K P v w = P * K.operatorAction v P * K.operatorAction w P * P := by
  dsimp [derivationQGT, qgtInward, qgtOutward]
  have hoff : P * K.operatorAction w P * P = 0 := derivation_projector_off_diagonal K P w hP hleib
  calc (P * K.operatorAction v P * (1 - P)) * ((1 - P) * K.operatorAction w P * P)
    _ = P * K.operatorAction v P * ((1 - P) * (1 - P)) * K.operatorAction w P * P := by noncomm_ring
    _ = P * K.operatorAction v P * (1 - P) * K.operatorAction w P * P := by
      have : (1 - P) * (1 - P) = 1 - P := by
        calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
          _ = 1 - P - P + P := by rw [hP]
          _ = 1 - P := by noncomm_ring
      rw [this]
    _ = P * K.operatorAction v P * 1 * K.operatorAction w P * P -
        P * K.operatorAction v P * P * K.operatorAction w P * P := by noncomm_ring
    _ = P * K.operatorAction v P * K.operatorAction w P * P -
        P * K.operatorAction v P * (P * K.operatorAction w P * P) := by noncomm_ring
    _ = P * K.operatorAction v P * K.operatorAction w P * P -
        P * K.operatorAction v P * 0 := by rw [hoff]
    _ = P * K.operatorAction v P * K.operatorAction w P * P := by
      rw [mul_zero, sub_zero]

/-- The skew-symmetric part of the QGT recovers the Berry curvature. -/
theorem derivationQGT_skew_berry
    (K : DerivationLieLane R A) (P : A) (v w : K.L)
    (hP : P * P = P)
    (hleib_v : K.operatorAction v P = K.operatorAction v P * P + P * K.operatorAction v P)
    (hleib_w : K.operatorAction w P = K.operatorAction w P * P + P * K.operatorAction w P) :
    derivationQGT K P v w - derivationQGT K P w v =
      P * (K.operatorAction v P * K.operatorAction w P - K.operatorAction w P * K.operatorAction v P) * P := by
  rw [derivationQGT_formula K P v w hP hleib_w,
      derivationQGT_formula K P w v hP hleib_v]
  noncomm_ring

end CovariantQGT

end InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT
