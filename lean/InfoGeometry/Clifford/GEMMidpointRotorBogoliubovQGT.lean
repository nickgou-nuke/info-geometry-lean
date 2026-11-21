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
import InfoGeometry.Algebra.DerivationLieLaneRepresentation
import InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.VietaSusyKatoDissipationAndGaloisGolayPoset
import InfoGeometry.Clifford.LorentzianBivectorSignatureBridge
import InfoGeometry.Clifford.HestenesDirac

/-!
# Symmetrically Split Midpoint Rotors, Kato Peirce Corners, GEM (1,3) Algebra, and Covariant QGT

This module formalizes the unified algebraic/operator synthesis connecting Clifford midpoint rotors,
Kato adiabatic connections, gravito-electromagnetism (GEM), hyperbolic Bogoliubov spin factors,
and the covariant Quantum Geometric Tensor (QGT):

1. **Normalized Midpoint Rotor Sandwich (`unnormMidpointRotor`, `midpointRotor_normalized_sandwich`)**:
   For any two involutions `Γ₁² = Γ₂² = 1` with invertible symmetric chord norm
   `(1 + Γ₂Γ₁)(1 + Γ₁Γ₂) = s² • 1`, constructs the normalized midpoint rotor
   `R₂₁ := s⁻¹ • (1 + Γ₂Γ₁)` and proves `R₂₁ R̃₂₁ = 1`, `R̃₂₁ R₂₁ = 1`, and `R₂₁ Γ₁ R̃₂₁ = Γ₂`.
2. **Kato Peirce Corners & Covariant Annihilation (`kato_peirce_corner_and_covariant_annihilation`)**:
   Expresses `Gamma_Kato P dP = coneMinus P dP - conePlus P dP = -(invS P) * genPhi P dP dP`,
   establishes `4 • Gamma_Kato P dP = -comm (invS P) (2 • dP)`, and proves covariant annihilation
   on both `P` and `1 - P` (plus the `DerivationLieLane` specialization).
3. **GEM (1,3) Algebraic Split & Dirac Witness (`gemConnection_sq_split_and_lenseThirring_rate`,
   `mat4C_dirac_gamma_noncommutative_witness`)**:
   Proves the `(E + I * B)²` split, `γ₀`-parity separation, algebraic Lense–Thirring half-rate
   `-(1/2 : ℝ) • B`, Hestenes STA pseudoscalar `I₅` sign contrast, and a closed `Mat4C` Dirac
   noncommutativity witness.
4. **Bogoliubov Hyperbolic Rotor & Peirce Aporia (`bogoliubovRotor_eq_midpointRotor_and_sandwich`,
   `bogoliubovRotor_peirce_aporia_neg_sinhSq`)**:
   Identifies `R_Bog(η)` with the normalized midpoint rotor between `γ₀` and `boostedFrame η γ₀ B`,
   and proves the Peirce compression laws `P_out P_in P_out = cosh²(η/2) P_out` and
   `P_out Q_in P_out = -sinh²(η/2) P_out`.
5. **Covariant QGT & Berry Split (`derivationQGT_leibniz_offDiagonal_and_berry_split`)**:
   Derives automatic Leibniz off-diagonality on both `P` and `1 - P` from
   `K.operatorAction_leibniz v P P`, factors `derivationQGT` via `PeirceSpine.conePlus`/`coneMinus`,
   extracts the skew Berry commutator, and establishes the `ℂ`-linear symmetric/skew `-i` split.

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

section UnnormMidpoint
variable {E : Type*} [Ring E]

/-- The unnormalized forward intertwiner `1 + Γ₂ Γ₁`. -/
def unnormMidpointRotor (Γ₁ Γ₂ : E) : E :=
  1 + Γ₂ * Γ₁

/-- The unnormalized reverse intertwiner `1 + Γ₁ Γ₂`. -/
def unnormMidpointRev (Γ₁ Γ₂ : E) : E :=
  1 + Γ₁ * Γ₂

/-- Algebraic intertwining and symmetric norm commutation for unnormalized midpoint rotors. -/
theorem unnormMidpointRotor_intertwining (Γ₁ Γ₂ : E)
    (hΓ₁ : Γ₁ * Γ₁ = 1) (hΓ₂ : Γ₂ * Γ₂ = 1) :
    unnormMidpointRotor Γ₁ Γ₂ * Γ₁ = Γ₁ + Γ₂ ∧
    Γ₂ * unnormMidpointRotor Γ₁ Γ₂ = Γ₁ + Γ₂ ∧
    unnormMidpointRotor Γ₁ Γ₂ * Γ₁ = Γ₂ * unnormMidpointRotor Γ₁ Γ₂ ∧
    unnormMidpointRotor Γ₁ Γ₂ * unnormMidpointRev Γ₁ Γ₂ = 2 + Γ₂ * Γ₁ + Γ₁ * Γ₂ ∧
    unnormMidpointRev Γ₁ Γ₂ * unnormMidpointRotor Γ₁ Γ₂ = 2 + Γ₂ * Γ₁ + Γ₁ * Γ₂ := by
  have h_left : unnormMidpointRotor Γ₁ Γ₂ * Γ₁ = Γ₁ + Γ₂ := by
    dsimp [unnormMidpointRotor]
    calc (1 + Γ₂ * Γ₁) * Γ₁
      _ = Γ₁ + Γ₂ * (Γ₁ * Γ₁) := by noncomm_ring
      _ = Γ₁ + Γ₂ * 1 := by rw [hΓ₁]
      _ = Γ₁ + Γ₂ := by rw [mul_one]
  have h_right : Γ₂ * unnormMidpointRotor Γ₁ Γ₂ = Γ₁ + Γ₂ := by
    dsimp [unnormMidpointRotor]
    calc Γ₂ * (1 + Γ₂ * Γ₁)
      _ = Γ₂ + (Γ₂ * Γ₂) * Γ₁ := by noncomm_ring
      _ = Γ₂ + 1 * Γ₁ := by rw [hΓ₂]
      _ = Γ₁ + Γ₂ := by rw [one_mul, add_comm]
  have h_intertwine : unnormMidpointRotor Γ₁ Γ₂ * Γ₁ = Γ₂ * unnormMidpointRotor Γ₁ Γ₂ := by
    rw [h_left, h_right]
  have h_prod1 :
      unnormMidpointRotor Γ₁ Γ₂ * unnormMidpointRev Γ₁ Γ₂ = 2 + Γ₂ * Γ₁ + Γ₁ * Γ₂ := by
    dsimp [unnormMidpointRotor, unnormMidpointRev]
    calc (1 + Γ₂ * Γ₁) * (1 + Γ₁ * Γ₂)
      _ = 1 + Γ₂ * Γ₁ + Γ₁ * Γ₂ + Γ₂ * (Γ₁ * Γ₁) * Γ₂ := by noncomm_ring
      _ = 1 + Γ₂ * Γ₁ + Γ₁ * Γ₂ + (Γ₂ * Γ₂) := by rw [hΓ₁, mul_one]
      _ = (1 + 1) + Γ₂ * Γ₁ + Γ₁ * Γ₂ := by rw [hΓ₂]; abel
      _ = 2 + Γ₂ * Γ₁ + Γ₁ * Γ₂ := by rw [one_add_one_eq_two]
  have h_prod2 :
      unnormMidpointRev Γ₁ Γ₂ * unnormMidpointRotor Γ₁ Γ₂ = 2 + Γ₂ * Γ₁ + Γ₁ * Γ₂ := by
    dsimp [unnormMidpointRotor, unnormMidpointRev]
    calc (1 + Γ₁ * Γ₂) * (1 + Γ₂ * Γ₁)
      _ = 1 + Γ₁ * Γ₂ + Γ₂ * Γ₁ + Γ₁ * (Γ₂ * Γ₂) * Γ₁ := by noncomm_ring
      _ = 1 + Γ₁ * Γ₂ + Γ₂ * Γ₁ + (Γ₁ * Γ₁) := by rw [hΓ₂, mul_one]
      _ = (1 + 1) + Γ₂ * Γ₁ + Γ₁ * Γ₂ := by rw [hΓ₁]; abel
      _ = 2 + Γ₂ * Γ₁ + Γ₁ * Γ₂ := by rw [one_add_one_eq_two]
  exact ⟨h_left, h_right, h_intertwine, h_prod1, h_prod2⟩

end UnnormMidpoint

variable {E : Type*} [Ring E] [Algebra ℝ E]

/-- Normalized symmetrically split midpoint rotor `R₂₁ := s⁻¹ • (1 + Γ₂ Γ₁)`. -/
noncomputable def midpointRotor (s : ℝ) (Γ₁ Γ₂ : E) : E :=
  s⁻¹ • unnormMidpointRotor Γ₁ Γ₂

/-- Reverse normalized midpoint rotor `R̃₂₁ := s⁻¹ • (1 + Γ₁ Γ₂)`. -/
noncomputable def midpointRotorRev (s : ℝ) (Γ₁ Γ₂ : E) : E :=
  s⁻¹ • unnormMidpointRev Γ₁ Γ₂

/-- Master Group 1 theorem: Normalized midpoint rotor satisfies both unit laws and intertwining. -/
theorem midpointRotor_normalized_sandwich (s : ℝ) (Γ₁ Γ₂ : E)
    (hs : s ≠ 0)
    (hΓ₁ : Γ₁ * Γ₁ = 1)
    (hΓ₂ : Γ₂ * Γ₂ = 1)
    (hnorm : unnormMidpointRotor Γ₁ Γ₂ * unnormMidpointRev Γ₁ Γ₂ = (s ^ 2) • (1 : E)) :
    midpointRotor s Γ₁ Γ₂ * midpointRotorRev s Γ₁ Γ₂ = 1 ∧
    midpointRotorRev s Γ₁ Γ₂ * midpointRotor s Γ₁ Γ₂ = 1 ∧
    midpointRotor s Γ₁ Γ₂ * Γ₁ * midpointRotorRev s Γ₁ Γ₂ = Γ₂ := by
  have hintertwine := unnormMidpointRotor_intertwining Γ₁ Γ₂ hΓ₁ hΓ₂
  have hscalar : s⁻¹ * s⁻¹ * s ^ 2 = 1 := by
    field_simp [hs]
  have h_unit : midpointRotor s Γ₁ Γ₂ * midpointRotorRev s Γ₁ Γ₂ = 1 := by
    dsimp [midpointRotor, midpointRotorRev]
    rw [smul_mul_smul, hnorm, smul_smul, hscalar, one_smul]
  have h_rev_norm :
      unnormMidpointRev Γ₁ Γ₂ * unnormMidpointRotor Γ₁ Γ₂ = (s ^ 2) • (1 : E) := by
    rw [hintertwine.2.2.2.2, ← hintertwine.2.2.2.1, hnorm]
  have h_rev_unit : midpointRotorRev s Γ₁ Γ₂ * midpointRotor s Γ₁ Γ₂ = 1 := by
    dsimp [midpointRotor, midpointRotorRev]
    rw [smul_mul_smul, h_rev_norm, smul_smul, hscalar, one_smul]
  have h_sand : midpointRotor s Γ₁ Γ₂ * Γ₁ * midpointRotorRev s Γ₁ Γ₂ = Γ₂ := by
    dsimp [midpointRotor, midpointRotorRev]
    calc (s⁻¹ • unnormMidpointRotor Γ₁ Γ₂) * Γ₁ * (s⁻¹ • unnormMidpointRev Γ₁ Γ₂)
      _ = s⁻¹ • (unnormMidpointRotor Γ₁ Γ₂ * Γ₁) * (s⁻¹ • unnormMidpointRev Γ₁ Γ₂) := by
        rw [smul_mul_assoc]
      _ = s⁻¹ • (Γ₂ * unnormMidpointRotor Γ₁ Γ₂) * (s⁻¹ • unnormMidpointRev Γ₁ Γ₂) := by
        rw [hintertwine.2.2.1]
      _ = (s⁻¹ * s⁻¹) • ((Γ₂ * unnormMidpointRotor Γ₁ Γ₂) * unnormMidpointRev Γ₁ Γ₂) := by
        rw [smul_mul_smul]
      _ = (s⁻¹ * s⁻¹) • (Γ₂ * (unnormMidpointRotor Γ₁ Γ₂ * unnormMidpointRev Γ₁ Γ₂)) := by
        rw [mul_assoc]
      _ = (s⁻¹ * s⁻¹) • (Γ₂ * ((s ^ 2) • (1 : E))) := by rw [hnorm]
      _ = (s⁻¹ * s⁻¹) • ((s ^ 2) • (Γ₂ * 1)) := by rw [mul_smul_comm]
      _ = ((s⁻¹ * s⁻¹) * s ^ 2) • (Γ₂ * 1) := by rw [smul_smul]
      _ = (1 : ℝ) • (Γ₂ * 1) := by rw [hscalar]
      _ = Γ₂ := by rw [one_smul, mul_one]
  exact ⟨h_unit, h_rev_unit, h_sand⟩

/-- The reverse product of the normalized midpoint rotor and its reverse is also the identity.
The reverse norm follows by conjugating the given norm by the involution `Γ₁`. -/
theorem midpointRotorRev_mul_midpointRotor (s : ℝ) (Γ₁ Γ₂ : E)
    (hs : s ≠ 0)
    (hΓ₁ : Γ₁ * Γ₁ = 1)
    (hnorm : unnormMidpointRotor Γ₁ Γ₂ * unnormMidpointRev Γ₁ Γ₂ = (s ^ 2) • (1 : E)) :
    midpointRotorRev s Γ₁ Γ₂ * midpointRotor s Γ₁ Γ₂ = 1 := by
  have hreverse :
      unnormMidpointRev Γ₁ Γ₂ * unnormMidpointRotor Γ₁ Γ₂ = (s ^ 2) • (1 : E) := by
    have hleft : Γ₁ * unnormMidpointRotor Γ₁ Γ₂ * Γ₁ = unnormMidpointRev Γ₁ Γ₂ := by
      dsimp [unnormMidpointRotor, unnormMidpointRev]
      calc Γ₁ * (1 + Γ₂ * Γ₁) * Γ₁
        _ = Γ₁ * Γ₁ + Γ₁ * Γ₂ * (Γ₁ * Γ₁) := by noncomm_ring
        _ = 1 + Γ₁ * Γ₂ * 1 := by rw [hΓ₁]
        _ = 1 + Γ₁ * Γ₂ := by rw [mul_one]
    have hright : Γ₁ * unnormMidpointRev Γ₁ Γ₂ * Γ₁ = unnormMidpointRotor Γ₁ Γ₂ := by
      dsimp [unnormMidpointRotor, unnormMidpointRev]
      calc Γ₁ * (1 + Γ₁ * Γ₂) * Γ₁
        _ = Γ₁ * Γ₁ + (Γ₁ * Γ₁) * Γ₂ * Γ₁ := by noncomm_ring
        _ = 1 + 1 * Γ₂ * Γ₁ := by rw [hΓ₁]
        _ = 1 + Γ₂ * Γ₁ := by rw [one_mul]
    have hconj :
        Γ₁ * (unnormMidpointRotor Γ₁ Γ₂ * unnormMidpointRev Γ₁ Γ₂) * Γ₁ =
          unnormMidpointRev Γ₁ Γ₂ * unnormMidpointRotor Γ₁ Γ₂ := by
      calc Γ₁ * (unnormMidpointRotor Γ₁ Γ₂ * unnormMidpointRev Γ₁ Γ₂) * Γ₁
        _ = Γ₁ * unnormMidpointRotor Γ₁ Γ₂ * unnormMidpointRev Γ₁ Γ₂ * Γ₁ := by noncomm_ring
        _ = Γ₁ * unnormMidpointRotor Γ₁ Γ₂ * (Γ₁ * Γ₁) * unnormMidpointRev Γ₁ Γ₂ * Γ₁ := by
          rw [hΓ₁]
          noncomm_ring
        _ = (Γ₁ * unnormMidpointRotor Γ₁ Γ₂ * Γ₁) * (Γ₁ * unnormMidpointRev Γ₁ Γ₂ * Γ₁) := by
          noncomm_ring
        _ = unnormMidpointRev Γ₁ Γ₂ * unnormMidpointRotor Γ₁ Γ₂ := by rw [hleft, hright]
    calc unnormMidpointRev Γ₁ Γ₂ * unnormMidpointRotor Γ₁ Γ₂
      _ = Γ₁ * (unnormMidpointRotor Γ₁ Γ₂ * unnormMidpointRev Γ₁ Γ₂) * Γ₁ := hconj.symm
      _ = Γ₁ * ((s ^ 2) • (1 : E)) * Γ₁ := by rw [hnorm]
      _ = ((s ^ 2) • (Γ₁ * 1)) * Γ₁ := by rw [mul_smul_comm]
      _ = (s ^ 2) • (Γ₁ * Γ₁) := by rw [mul_one, smul_mul_assoc]
      _ = (s ^ 2) • (1 : E) := by rw [hΓ₁]
  dsimp [midpointRotorRev, midpointRotor]
  rw [smul_mul_smul, hreverse, smul_smul]
  have hscalar : s⁻¹ * s⁻¹ * s ^ 2 = 1 := by
    field_simp [hs]
  rw [hscalar, one_smul]

end MidpointRotor

/-! ## Section 2: Kato Adiabatic Connection & Covariant Annihilation -/

section KatoConnection

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine hiding comm

section KatoRing
variable {E : Type*} [Ring E]

/-- Master Group 2 theorem: Kato Peirce-corner expression, `-(invS P) * genPhi` form,
`4 • Gamma_Kato = -comm (invS P) (2 • dP)` factor identity, and covariant annihilation on both
`P` and `1 - P`. -/
theorem kato_peirce_corner_and_covariant_annihilation
    (P dP : E)
    (hP : P * P = P)
    (hdP : dP * P + P * dP = dP) :
    Gamma_Kato P dP = coneMinus P dP - conePlus P dP ∧
    coneMinus P dP - conePlus P dP =
      -(invS P) * genPhi P dP dP ∧
    (4 : ℕ) • Gamma_Kato P dP =
      -PeirceSpine.comm (invS P) ((2 : ℕ) • dP) ∧
    dP - PeirceSpine.comm (Gamma_Kato P dP) P = 0 ∧
    (-dP) - PeirceSpine.comm (Gamma_Kato P dP) (1 - P) = 0 := by
  have h_corner :
      Gamma_Kato P dP = coneMinus P dP - conePlus P dP := by
    dsimp [Gamma_Kato, PeirceSpine.comm, coneMinus, conePlus]
    noncomm_ring
  have h_invS_phi :
      invS P * genPhi P dP dP = conePlus P dP - coneMinus P dP := by
    dsimp [invS, genPhi]
    calc (P - (1 - P)) * (conePlus P dP + coneMinus P dP)
      _ = 2 • (P * conePlus P dP) + 2 • (P * coneMinus P dP) -
            conePlus P dP - coneMinus P dP := by
        rw [two_nsmul]
        noncomm_ring
      _ = 2 • conePlus P dP + 2 • (0 : E) -
            conePlus P dP - coneMinus P dP := by
        rw [P_mul_conePlus hP dP, P_mul_coneMinus hP dP]
      _ = conePlus P dP - coneMinus P dP := by
        rw [nsmul_zero, two_nsmul]
        noncomm_ring
  have h_neg_invS_phi :
      coneMinus P dP - conePlus P dP = -(invS P) * genPhi P dP dP := by
    rw [neg_mul, h_invS_phi, neg_sub]
  have h_four :
      (4 : ℕ) • Gamma_Kato P dP = -PeirceSpine.comm (invS P) ((2 : ℕ) • dP) := by
    have h4 : (4 : ℕ) = 2 + 2 := by norm_num
    dsimp [Gamma_Kato, PeirceSpine.comm, invS]
    rw [h4, add_nsmul, two_nsmul, two_nsmul]
    noncomm_ring
  have hK := kato_berry_spectral_flow_and_covariant_time P dP (0 : E) hP hdP
  have hcomm : PeirceSpine.comm (Gamma_Kato P dP) P = dP := hK.2.1
  have h_ann_P : dP - PeirceSpine.comm (Gamma_Kato P dP) P = 0 := by
    rw [hcomm, sub_self]
  have hcomp : PeirceSpine.comm (Gamma_Kato P dP) (1 - P) = -dP := by
    calc PeirceSpine.comm (Gamma_Kato P dP) (1 - P)
      _ = -PeirceSpine.comm (Gamma_Kato P dP) P := by
        dsimp [PeirceSpine.comm]
        noncomm_ring
      _ = -dP := by rw [hcomm]
  have h_ann_comp : (-dP) - PeirceSpine.comm (Gamma_Kato P dP) (1 - P) = 0 := by
    rw [hcomp, sub_self]
  exact ⟨h_corner, h_neg_invS_phi, h_four, h_ann_P, h_ann_comp⟩

/-- The covariant derivative generated by the existing Kato connection annihilates the
complementary projector variation. -/
theorem kato_covariant_derivative_complement
    (P dP : E)
    (hP : P * P = P)
    (hdP : dP * P + P * dP = dP) :
    (-dP) - PeirceSpine.comm (Gamma_Kato P dP) (1 - P) = 0 :=
  (kato_peirce_corner_and_covariant_annihilation P dP hP hdP).2.2.2.2

end KatoRing

/-- `DerivationLieLane` specialization of Kato covariant annihilation: automatically derives
`d(1 - P) = -dP` and `dP * P + P * dP = dP` from `K.operatorAction_leibniz`. -/
theorem kato_derivation_covariant_annihilation
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (P : A) (v : K.L)
    (hP : P * P = P) :
    K.operatorAction v (1 - P) = -K.operatorAction v P ∧
    Gamma_Kato P (K.operatorAction v P) =
      coneMinus P (K.operatorAction v P) - conePlus P (K.operatorAction v P) ∧
    coneMinus P (K.operatorAction v P) - conePlus P (K.operatorAction v P) =
      -(invS P) * genPhi P (K.operatorAction v P) (K.operatorAction v P) ∧
    (4 : ℕ) • Gamma_Kato P (K.operatorAction v P) =
      -PeirceSpine.comm (invS P) ((2 : ℕ) • K.operatorAction v P) ∧
    K.operatorAction v P - PeirceSpine.comm (Gamma_Kato P (K.operatorAction v P)) P = 0 ∧
    K.operatorAction v (1 - P) -
      PeirceSpine.comm (Gamma_Kato P (K.operatorAction v P)) (1 - P) = 0 := by
  have hd1 : K.operatorAction v (1 : A) = 0 := by
    have h11 : K.operatorAction v (1 * 1) =
        K.operatorAction v 1 * 1 + 1 * K.operatorAction v 1 :=
      K.operatorAction_leibniz v 1 1
    rw [one_mul, mul_one, one_mul] at h11
    calc K.operatorAction v (1 : A)
      _ = (K.operatorAction v 1 + K.operatorAction v 1) - K.operatorAction v 1 := by abel
      _ = K.operatorAction v 1 - K.operatorAction v 1 := by rw [← h11]
      _ = 0 := sub_self _
  have hd_comp : K.operatorAction v (1 - P) = -K.operatorAction v P := by
    rw [map_sub, hd1, zero_sub]
  have hdP : K.operatorAction v P * P + P * K.operatorAction v P = K.operatorAction v P := by
    calc K.operatorAction v P * P + P * K.operatorAction v P
      _ = K.operatorAction v (P * P) := (K.operatorAction_leibniz v P P).symm
      _ = K.operatorAction v P := by rw [hP]
  have hkato :=
    kato_peirce_corner_and_covariant_annihilation P (K.operatorAction v P) hP hdP
  have hcomp_ann :
      K.operatorAction v (1 - P) -
        PeirceSpine.comm (Gamma_Kato P (K.operatorAction v P)) (1 - P) = 0 := by
    rw [hd_comp]
    exact hkato.2.2.2.2
  exact ⟨hd_comp, hkato.1, hkato.2.1, hkato.2.2.1, hkato.2.2.2.1, hcomp_ann⟩

end KatoConnection

/-! ## Section 3: Gravito-Electromagnetism (GEM) (1,3) Signature Split & Dirac Witness -/

section GEMAlgebra

section GEMRing
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
    (gemConnection E I B) ^ 2 = (E ^ 2 - B ^ 2) + I * (E * B + B * E) := by
  dsimp [gemConnection]
  calc (E + I * B) ^ 2
    _ = (E + I * B) * (E + I * B) := sq (E + I * B)
    _ = E * E + E * (I * B) + (I * B) * E + (I * B) * (I * B) := by noncomm_ring
    _ = E ^ 2 + I * (E * B) + I * (B * E) + (I * I) * (B * B) := by
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
    _ = E ^ 2 + I * (E * B + B * E) + (-1) * B ^ 2 := by
      rw [hI_sq]
      noncomm_ring
    _ = (E ^ 2 - B ^ 2) + I * (E * B + B * E) := by
      have hneg : (-1 : A) * B ^ 2 = -B ^ 2 := by noncomm_ring
      rw [hneg]
      noncomm_ring

/-- Parity split under central `I`: electric field is `γ₀`-odd, magnetic field is `γ₀`-even. -/
theorem gemConnection_gamma0_parity
    (E I B γ₀ : A)
    (hγ₀_sq : γ₀ * γ₀ = 1)
    (hγ₀I : γ₀ * I = I * γ₀)
    (hE_odd : γ₀ * E + E * γ₀ = 0)
    (hB_even : γ₀ * B - B * γ₀ = 0) :
    γ₀ * gemConnection E I B * γ₀ = -E + I * B := by
  dsimp [gemConnection]
  have hE : γ₀ * E * γ₀ = -E := by
    have hE' : γ₀ * E = -(E * γ₀) := eq_neg_of_add_eq_zero_left hE_odd
    calc γ₀ * E * γ₀ = (-(E * γ₀)) * γ₀ := by rw [hE']
      _ = -(E * (γ₀ * γ₀)) := by noncomm_ring
      _ = -(E * 1) := by rw [hγ₀_sq]
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

/-- Hestenes STA pseudoscalar sign contrast: when `{γ₀, I₅} = 0` and `[γ₀, B] = 0`,
conjugation by `γ₀` flips the sign of `I₅ * B`, yielding `-E - I₅ * B`. -/
theorem gemConnection_sta_pseudoscalar_contrast
    (E I₅ B γ₀ : A)
    (hγ₀_sq : γ₀ * γ₀ = 1)
    (hγ₀I₅_anti : γ₀ * I₅ + I₅ * γ₀ = 0)
    (hE_odd : γ₀ * E + E * γ₀ = 0)
    (hB_even : γ₀ * B - B * γ₀ = 0) :
    γ₀ * gemConnection E I₅ B * γ₀ = -E - I₅ * B := by
  dsimp [gemConnection]
  have hE : γ₀ * E * γ₀ = -E := by
    have hE' : γ₀ * E = -(E * γ₀) := eq_neg_of_add_eq_zero_left hE_odd
    calc γ₀ * E * γ₀ = (-(E * γ₀)) * γ₀ := by rw [hE']
      _ = -(E * (γ₀ * γ₀)) := by noncomm_ring
      _ = -(E * 1) := by rw [hγ₀_sq]
      _ = -E := by rw [mul_one]
  have hB_comm : γ₀ * B = B * γ₀ := eq_of_sub_eq_zero hB_even
  have hI₅ : γ₀ * I₅ = -(I₅ * γ₀) := eq_neg_of_add_eq_zero_left hγ₀I₅_anti
  have hIB : γ₀ * (I₅ * B) * γ₀ = -(I₅ * B) := by
    calc γ₀ * (I₅ * B) * γ₀ = (γ₀ * I₅) * (B * γ₀) := by noncomm_ring
      _ = (-(I₅ * γ₀)) * (γ₀ * B) := by rw [hI₅, ← hB_comm]
      _ = -(I₅ * ((γ₀ * γ₀) * B)) := by noncomm_ring
      _ = -(I₅ * (1 * B)) := by rw [hγ₀_sq]
      _ = -(I₅ * B) := by rw [one_mul]
  calc γ₀ * (E + I₅ * B) * γ₀
    _ = γ₀ * E * γ₀ + γ₀ * (I₅ * B) * γ₀ := by noncomm_ring
    _ = -E + -(I₅ * B) := by rw [hE, hIB]
    _ = -E - I₅ * B := sub_eq_add_neg (-E) (I₅ * B) |>.symm

end GEMRing

section GEMRealAlgebra
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Algebraic Lense–Thirring precession half-rate `-(1/2 : ℝ) • B`. -/
noncomputable def lenseThirringPrecession (B : A) : A :=
  -(1 / 2 : ℝ) • B

/-- Master Group 3 theorem: GEM square split, `γ₀`-parity separation, algebraic
Lense–Thirring precession recovery `-(1/2 : ℝ) • B`, and `γ₀`-invariance. -/
theorem gemConnection_sq_split_and_lenseThirring_rate
    (E I B γ₀ : A)
    (hγ₀_sq : γ₀ * γ₀ = 1)
    (hI_sq : I * I = -1)
    (hγ₀I : γ₀ * I = I * γ₀)
    (hIE : I * E = E * I)
    (hIB : I * B = B * I)
    (hE_odd : γ₀ * E + E * γ₀ = 0)
    (hB_even : γ₀ * B - B * γ₀ = 0) :
    (gemConnection E I B) ^ 2 = (E ^ 2 - B ^ 2) + I * (E * B + B * E) ∧
    γ₀ * gemConnection E I B * γ₀ = -E + I * B ∧
    gemConnection E I B + γ₀ * gemConnection E I B * γ₀ = (2 : ℝ) • (I * B) ∧
    (2 : ℝ) • lenseThirringPrecession B = -B ∧
    (1 / 4 : ℝ) • (I * (gemConnection E I B + γ₀ * gemConnection E I B * γ₀)) =
      lenseThirringPrecession B ∧
    γ₀ * lenseThirringPrecession B * γ₀ = lenseThirringPrecession B := by
  have hsq := gemConnection_sq_split E I B hI_sq hIE hIB
  have hpar := gemConnection_gamma0_parity E I B γ₀ hγ₀_sq hγ₀I hE_odd hB_even
  have hsum : gemConnection E I B + γ₀ * gemConnection E I B * γ₀ = (2 : ℝ) • (I * B) := by
    rw [hpar]
    dsimp [gemConnection]
    calc (E + I * B) + (-E + I * B)
      _ = I * B + I * B := by abel
      _ = (1 : ℝ) • (I * B) + (1 : ℝ) • (I * B) := by rw [one_smul]
      _ = ((1 : ℝ) + 1) • (I * B) := (add_smul (1 : ℝ) 1 (I * B)).symm
      _ = (2 : ℝ) • (I * B) := by norm_num
  have hdouble : (2 : ℝ) • lenseThirringPrecession B = -B := by
    dsimp [lenseThirringPrecession]
    rw [smul_smul]
    have hcoeff : (2 : ℝ) * (-(1 / 2)) = -1 := by norm_num
    rw [hcoeff, neg_one_smul]
  have hrate :
      (1 / 4 : ℝ) • (I * (gemConnection E I B + γ₀ * gemConnection E I B * γ₀)) =
        lenseThirringPrecession B := by
    rw [hsum, mul_smul_comm, smul_smul, ← mul_assoc, hI_sq, neg_one_mul, smul_neg, ← neg_smul]
    dsimp [lenseThirringPrecession]
    have hcoeff : -((1 / 4 : ℝ) * 2) = -(1 / 2) := by norm_num
    rw [hcoeff]
  have hinv : γ₀ * lenseThirringPrecession B * γ₀ = lenseThirringPrecession B := by
    have hB_comm : γ₀ * B = B * γ₀ := eq_of_sub_eq_zero hB_even
    have h_conj : γ₀ * B * γ₀ = B := by
      calc γ₀ * B * γ₀ = B * γ₀ * γ₀ := by rw [hB_comm]
        _ = B * (γ₀ * γ₀) := by rw [mul_assoc]
        _ = B := by rw [hγ₀_sq, mul_one]
    dsimp [lenseThirringPrecession]
    rw [mul_smul_comm, smul_mul_assoc, h_conj]
  exact ⟨hsq, hpar, hsum, hdouble, hrate, hinv⟩

end GEMRealAlgebra

section DiracWitness

/-- Weyl-basis Dirac matrix `γ₀` in `FiniteSpin.Mat4C`. -/
def diracGamma0 : FiniteSpin.Mat4C :=
  !![(0 : ℂ), 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- Weyl-basis Dirac matrix `γ₁` in `FiniteSpin.Mat4C`. -/
def diracGamma1 : FiniteSpin.Mat4C :=
  !![(0 : ℂ), 0, 0, 1;
     0, 0, 1, 0;
     0, -1, 0, 0;
     -1, 0, 0, 0]

/-- Weyl-basis Dirac matrix `γ₂` in `FiniteSpin.Mat4C`. -/
def diracGamma2 : FiniteSpin.Mat4C :=
  !![(0 : ℂ), 0, 0, -Complex.I;
     0, 0, Complex.I, 0;
     0, Complex.I, 0, 0;
     -Complex.I, 0, 0, 0]

/-- Weyl-basis Dirac matrix `γ₃` in `FiniteSpin.Mat4C`. -/
def diracGamma3 : FiniteSpin.Mat4C :=
  !![(0 : ℂ), 0, 1, 0;
     0, 0, 0, -1;
     -1, 0, 0, 0;
     0, 1, 0, 0]

/-- Hestenes spacetime pseudoscalar `I₅ := γ₀ γ₁ γ₂ γ₃` in `FiniteSpin.Mat4C`. -/
def diracI5 : FiniteSpin.Mat4C :=
  diracGamma0 * diracGamma1 * diracGamma2 * diracGamma3

/-- Central complex unit `i • 1` in `FiniteSpin.Mat4C`. -/
def diracIcentral : FiniteSpin.Mat4C :=
  Complex.I • (1 : FiniteSpin.Mat4C)

/-- Electric bivector `E := γ₁ γ₀` in `FiniteSpin.Mat4C`. -/
def diracE : FiniteSpin.Mat4C :=
  diracGamma1 * diracGamma0

/-- Magnetic bivector `B := γ₂ γ₃` in `FiniteSpin.Mat4C`. -/
def diracB : FiniteSpin.Mat4C :=
  diracGamma2 * diracGamma3

private theorem diracGamma0_sq : diracGamma0 * diracGamma0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracGamma0, Matrix.mul_apply, Fin.sum_univ_four]

private theorem diracGamma1_sq : diracGamma1 * diracGamma1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracGamma1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.neg_apply]

private theorem diracGamma2_sq : diracGamma2 * diracGamma2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracGamma2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.neg_apply]

private theorem diracGamma3_sq : diracGamma3 * diracGamma3 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracGamma3, Matrix.mul_apply, Fin.sum_univ_four, Matrix.neg_apply]

private theorem diracGamma0_gamma1_anticomm : diracGamma0 * diracGamma1 + diracGamma1 * diracGamma0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracGamma0, diracGamma1]

private theorem diracGamma0_gamma2_anticomm : diracGamma0 * diracGamma2 + diracGamma2 * diracGamma0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracGamma0, diracGamma2]

private theorem diracGamma0_gamma3_anticomm : diracGamma0 * diracGamma3 + diracGamma3 * diracGamma0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracGamma0, diracGamma3]

private theorem diracGamma2_gamma3_anticomm : diracGamma2 * diracGamma3 + diracGamma3 * diracGamma2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracGamma2, diracGamma3]

/-- Closed `Matrix (Fin 4) (Fin 4) ℂ` Dirac noncommutativity witness (T16/T17) and explicit
`I` central vs `I₅` pseudoscalar sign contrast under `γ₀`-conjugation. -/
theorem mat4C_dirac_gamma_noncommutative_witness :
    diracGamma0 * diracGamma1 ≠ diracGamma1 * diracGamma0 ∧
    diracGamma0 * diracGamma0 = 1 ∧
    diracGamma1 * diracGamma1 = -1 ∧
    diracGamma2 * diracGamma2 = -1 ∧
    diracGamma3 * diracGamma3 = -1 ∧
    diracE * diracE = 1 ∧
    diracB * diracB = -1 ∧
    diracI5 * diracI5 = -1 ∧
    diracGamma0 * diracI5 + diracI5 * diracGamma0 = 0 ∧
    diracGamma0 * gemConnection diracE diracIcentral diracB * diracGamma0 =
      -diracE + diracIcentral * diracB ∧
    diracGamma0 * gemConnection diracE diracI5 diracB * diracGamma0 =
      -diracE - diracI5 * diracB ∧
    -diracE + diracIcentral * diracB ≠ -diracE - diracI5 * diracB := by
  have hnoncomm : diracGamma0 * diracGamma1 ≠ diracGamma1 * diracGamma0 := by
    intro h
    have h01 := congrArg (fun M : FiniteSpin.Mat4C => M 0 1) h
    norm_num [diracGamma0, diracGamma1, Matrix.mul_apply, Fin.sum_univ_four] at h01
  have hE_sq : diracE * diracE = 1 :=
    mixed_bivector_sq_one diracGamma0_sq diracGamma1_sq diracGamma0_gamma1_anticomm
  have hB_sq : diracB * diracB = -1 :=
    negative_bivector_sq_neg_one diracGamma2_sq diracGamma3_sq diracGamma2_gamma3_anticomm
  have h01' : diracGamma0 * diracGamma1 = -(diracGamma1 * diracGamma0) :=
    eq_neg_of_add_eq_zero_left diracGamma0_gamma1_anticomm
  have h02 : diracGamma2 * diracGamma0 = -(diracGamma0 * diracGamma2) :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact diracGamma0_gamma2_anticomm)
  have h03 : diracGamma3 * diracGamma0 = -(diracGamma0 * diracGamma3) :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact diracGamma0_gamma3_anticomm)
  have h01_mat : diracGamma0 * diracGamma1 =
      !![(0 : ℂ), -1, 0, 0;
         -1, 0, 0, 0;
         0, 0, 0, 1;
         0, 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diracGamma0, diracGamma1, Matrix.mul_apply, Fin.sum_univ_four]
  have h23_mat : diracB =
      !![(0 : ℂ), -Complex.I, 0, 0;
         -Complex.I, 0, 0, 0;
         0, 0, 0, -Complex.I;
         0, 0, -Complex.I, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diracB, diracGamma2, diracGamma3, Matrix.mul_apply, Fin.sum_univ_four]
  have hI5_mat : diracI5 =
      !![(Complex.I : ℂ), 0, 0, 0;
         0, Complex.I, 0, 0;
         0, 0, -Complex.I, 0;
         0, 0, 0, -Complex.I] := by
    have hsplit : diracI5 = (diracGamma0 * diracGamma1) * diracB := by
      dsimp [diracI5, diracB]
      noncomm_ring
    rw [hsplit, h01_mat, h23_mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four]
  have hI5_anti : diracGamma0 * diracI5 + diracI5 * diracGamma0 = 0 := by
    rw [hI5_mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diracGamma0]
  have hI5_sq : diracI5 * diracI5 = -1 := by
    rw [hI5_mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.neg_apply]
  have hE_odd : diracGamma0 * diracE + diracE * diracGamma0 = 0 := by
    dsimp [diracE]
    calc diracGamma0 * (diracGamma1 * diracGamma0) + (diracGamma1 * diracGamma0) * diracGamma0
      _ = (diracGamma0 * diracGamma1) * diracGamma0 + diracGamma1 * (diracGamma0 * diracGamma0) := by
        noncomm_ring
      _ = (-(diracGamma1 * diracGamma0)) * diracGamma0 + diracGamma1 * 1 := by
        rw [h01', diracGamma0_sq]
      _ = -(diracGamma1 * (diracGamma0 * diracGamma0)) + diracGamma1 := by noncomm_ring
      _ = -(diracGamma1 * 1) + diracGamma1 := by rw [diracGamma0_sq]
      _ = 0 := by noncomm_ring
  have hB_even : diracGamma0 * diracB - diracB * diracGamma0 = 0 := by
    dsimp [diracB]
    calc diracGamma0 * (diracGamma2 * diracGamma3) - (diracGamma2 * diracGamma3) * diracGamma0
      _ = diracGamma0 * diracGamma2 * diracGamma3 - diracGamma2 * (diracGamma3 * diracGamma0) := by
        noncomm_ring
      _ = diracGamma0 * diracGamma2 * diracGamma3 + (diracGamma2 * diracGamma0) * diracGamma3 := by
        rw [h03]; noncomm_ring
      _ = diracGamma0 * diracGamma2 * diracGamma3 - (diracGamma0 * diracGamma2) * diracGamma3 := by
        rw [h02]; noncomm_ring
      _ = 0 := sub_self _
  have hγ₀I_central : diracGamma0 * diracIcentral = diracIcentral * diracGamma0 := by
    dsimp [diracIcentral]
    rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have h_central_conj :
      diracGamma0 * gemConnection diracE diracIcentral diracB * diracGamma0 =
        -diracE + diracIcentral * diracB :=
    gemConnection_gamma0_parity diracE diracIcentral diracB diracGamma0
      diracGamma0_sq hγ₀I_central hE_odd hB_even
  have h_sta_conj :
      diracGamma0 * gemConnection diracE diracI5 diracB * diracGamma0 =
        -diracE - diracI5 * diracB :=
    gemConnection_sta_pseudoscalar_contrast diracE diracI5 diracB diracGamma0
      diracGamma0_sq hI5_anti hE_odd hB_even
  have h_contrast : -diracE + diracIcentral * diracB ≠ -diracE - diracI5 * diracB := by
    intro h
    have h01_diff := congrArg (fun M : FiniteSpin.Mat4C => M 0 1) h
    rw [hI5_mat, h23_mat] at h01_diff
    simp [diracE, diracIcentral, diracGamma0, diracGamma1] at h01_diff
    norm_num at h01_diff
  exact ⟨hnoncomm, diracGamma0_sq, diracGamma1_sq, diracGamma2_sq, diracGamma3_sq,
    hE_sq, hB_sq, hI5_sq, hI5_anti, h_central_conj, h_sta_conj, h_contrast⟩

end DiracWitness

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

/-- Negating rapidity in `bogoliubovRotor` equals `bogoliubovRotorInv`. -/
theorem bogoliubovRotor_neg_eq_inv (η : ℝ) (B : E) :
    bogoliubovRotor (-η) B = bogoliubovRotorInv η B := by
  dsimp [bogoliubovRotor, bogoliubovRotorInv]
  rw [neg_div, Real.cosh_neg, Real.sinh_neg, neg_smul, sub_eq_add_neg]

/-- Bogoliubov rotor is unitary: `R_Bog(η) * R_Bog(-η) = 1`. -/
theorem bogoliubovRotor_mul_inv (η : ℝ) (B : E) (hB : B * B = 1) :
    bogoliubovRotor η B * bogoliubovRotorInv η B = 1 := by
  dsimp [bogoliubovRotor, bogoliubovRotorInv]
  have h1 : (Real.cosh (η / 2) • (1 : E) + Real.sinh (η / 2) • B) *
            (Real.cosh (η / 2) • (1 : E) - Real.sinh (η / 2) • B) =
            ((Real.cosh (η / 2)) ^ 2 - (Real.sinh (η / 2)) ^ 2) • (1 : E) := by
    rw [sq, sq]
    have hexpand :
        (Real.cosh (η / 2) • (1 : E) + Real.sinh (η / 2) • B) *
          (Real.cosh (η / 2) • (1 : E) - Real.sinh (η / 2) • B) =
          (Real.cosh (η / 2) * Real.cosh (η / 2)) • (1 : E) -
          (Real.sinh (η / 2) * Real.sinh (η / 2)) • (B * B) := by
      noncomm_ring
      module
    rw [hexpand, hB, ← sub_smul]
  rw [h1, Real.cosh_sq_sub_sinh_sq, one_smul]

/-- Bogoliubov rotor sandwich produces the Lorentz-boosted frame. -/
theorem bogoliubovRotor_sandwich (η : ℝ) (γ₀ B : E)
    (hB : B * B = 1)
    (hanti : γ₀ * B + B * γ₀ = 0) :
    bogoliubovRotor η B * γ₀ * bogoliubovRotorInv η B = boostedFrame η γ₀ B := by
  dsimp [bogoliubovRotor, bogoliubovRotorInv, boostedFrame]
  have h_sq : Real.cosh (η / 2) ^ 2 + Real.sinh (η / 2) ^ 2 = Real.cosh η := by
    have h1 := Real.cosh_add (η / 2) (η / 2)
    have hhalf : η / 2 + η / 2 = η := add_halves η
    rw [hhalf, ← pow_two, ← pow_two] at h1
    exact h1.symm
  have h_prod : 2 * Real.sinh (η / 2) * Real.cosh (η / 2) = Real.sinh η := by
    have h1 := Real.sinh_add (η / 2) (η / 2)
    have hhalf : η / 2 + η / 2 = η := add_halves η
    rw [hhalf] at h1
    calc 2 * Real.sinh (η / 2) * Real.cosh (η / 2)
        = Real.sinh (η / 2) * Real.cosh (η / 2) +
            Real.cosh (η / 2) * Real.sinh (η / 2) := by ring
      _ = Real.sinh η := h1.symm
  have hγ₀B : γ₀ * B = -(B * γ₀) := eq_neg_of_add_eq_zero_left hanti
  have hB_sq : (B * γ₀) * B = -γ₀ := by
    calc (B * γ₀) * B = B * (γ₀ * B) := by noncomm_ring
      _ = B * (-(B * γ₀)) := by rw [hγ₀B]
      _ = -(B * B * γ₀) := by noncomm_ring
      _ = -(1 * γ₀) := by rw [hB]
      _ = -γ₀ := by rw [one_mul]
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
        (Real.cosh (η / 2) * Real.sinh (η / 2)) • (-(B * γ₀)) +
        (Real.sinh (η / 2) * Real.cosh (η / 2)) • (B * γ₀) -
        (Real.sinh (η / 2) ^ 2) • (-γ₀) := by
      rw [mul_one, mul_one, sq, sq, hB_sq, hγ₀B]
    _ = (Real.cosh (η / 2) ^ 2 + Real.sinh (η / 2) ^ 2) • γ₀ +
        (2 * Real.sinh (η / 2) * Real.cosh (η / 2)) • (B * γ₀) := by
      rw [smul_neg, sub_neg_eq_add, smul_neg, sub_neg_eq_add]
      module
    _ = Real.cosh η • γ₀ + Real.sinh η • (B * γ₀) := by
      rw [h_sq, h_prod]

/-- The boosted frame `boostedFrame η γ₀ B` is an involution (`γ_boost² = 1`). -/
theorem boostedFrame_sq (η : ℝ) (γ₀ B : E)
    (hγ₀ : γ₀ * γ₀ = 1)
    (hB : B * B = 1)
    (hanti : γ₀ * B + B * γ₀ = 0) :
    boostedFrame η γ₀ B * boostedFrame η γ₀ B = 1 := by
  have hBγ₀_sq : (B * γ₀) * (B * γ₀) = -1 :=
    positive_bivector_sq_neg_one hB hγ₀ (by rw [add_comm]; exact hanti)
  have hγ₀_Bγ₀ : γ₀ * (B * γ₀) + (B * γ₀) * γ₀ = 0 := by
    have hγ₀B : γ₀ * B = -(B * γ₀) := eq_neg_of_add_eq_zero_left hanti
    calc γ₀ * (B * γ₀) + (B * γ₀) * γ₀
      _ = (γ₀ * B) * γ₀ + B * (γ₀ * γ₀) := by noncomm_ring
      _ = (-(B * γ₀)) * γ₀ + B * 1 := by rw [hγ₀B, hγ₀]
      _ = -(B * (γ₀ * γ₀)) + B := by noncomm_ring
      _ = -(B * 1) + B := by rw [hγ₀]
      _ = 0 := by noncomm_ring
  dsimp [boostedFrame]
  calc (Real.cosh η • γ₀ + Real.sinh η • (B * γ₀)) *
        (Real.cosh η • γ₀ + Real.sinh η • (B * γ₀))
    _ = (Real.cosh η * Real.cosh η) • (γ₀ * γ₀) +
        (Real.cosh η * Real.sinh η) • (γ₀ * (B * γ₀) + (B * γ₀) * γ₀) +
        (Real.sinh η * Real.sinh η) • ((B * γ₀) * (B * γ₀)) := by
      noncomm_ring
      module
    _ = (Real.cosh η * Real.cosh η) • (1 : E) +
        (Real.cosh η * Real.sinh η) • (0 : E) +
        (Real.sinh η * Real.sinh η) • (-1 : E) := by
      rw [hγ₀, hγ₀_Bγ₀, hBγ₀_sq]
    _ = (Real.cosh η ^ 2 - Real.sinh η ^ 2) • (1 : E) := by
      rw [smul_zero, add_zero, smul_neg, ← sub_eq_add_neg, sq, sq, ← sub_smul]
    _ = 1 := by rw [Real.cosh_sq_sub_sinh_sq, one_smul]

/-- CCR hyperbolic normalization `cosh²(η/2) = 1 + sinh²(η/2)` via `SplitComplex.bogoliubov_ccr_preservation`. -/
theorem bogoliubovRotor_ccr_norm (η : ℝ) :
    Real.cosh (η / 2) * Real.cosh (η / 2) = 1 + Real.sinh (η / 2) * Real.sinh (η / 2) := by
  have hhyp : Real.cosh (η / 2) * Real.cosh (η / 2) - Real.sinh (η / 2) * Real.sinh (η / 2) = 1 := by
    rw [← sq, ← sq]
    exact Real.cosh_sq_sub_sinh_sq (η / 2)
  exact HyperbolicBogoliubovSplitAlgebra.SplitComplex.bogoliubov_ccr_preservation
    (Real.cosh (η / 2)) (Real.sinh (η / 2)) hhyp

/-- Acceptance Theorem 4a: The Bogoliubov rotor equals the normalized midpoint rotor between `γ₀`
and `boostedFrame η γ₀ B`, with explicit norm factor `(2 * Real.cosh (η / 2)) ^ 2`. -/
theorem bogoliubovRotor_eq_midpointRotor_and_sandwich
    (η : ℝ) (γ₀ B : E)
    (hγ₀ : γ₀ * γ₀ = 1)
    (hB : B * B = 1)
    (hanti : γ₀ * B + B * γ₀ = 0) :
    2 * Real.cosh (η / 2) ≠ 0 ∧
    unnormMidpointRotor γ₀ (boostedFrame η γ₀ B) *
        unnormMidpointRev γ₀ (boostedFrame η γ₀ B) =
      ((2 * Real.cosh (η / 2)) ^ 2) • (1 : E) ∧
    bogoliubovRotor η B =
      midpointRotor (2 * Real.cosh (η / 2)) γ₀ (boostedFrame η γ₀ B) ∧
    bogoliubovRotor (-η) B =
      midpointRotorRev (2 * Real.cosh (η / 2)) γ₀ (boostedFrame η γ₀ B) ∧
    bogoliubovRotor η B * bogoliubovRotor (-η) B = 1 ∧
    bogoliubovRotor (-η) B * bogoliubovRotor η B = 1 ∧
    bogoliubovRotor η B * γ₀ * bogoliubovRotor (-η) B = boostedFrame η γ₀ B := by
  have hcosh_pos : 0 < Real.cosh (η / 2) := Real.cosh_pos (η / 2)
  have hs : 2 * Real.cosh (η / 2) ≠ 0 := by linarith
  have h_one_add_cosh : 1 + Real.cosh η = 2 * Real.cosh (η / 2) * Real.cosh (η / 2) := by
    have h1 := Real.cosh_two_mul (η / 2)
    have h2 : 2 * (η / 2) = η := by ring
    rw [h2] at h1
    have hcs := Real.cosh_sq_sub_sinh_sq (η / 2)
    linarith [sq (Real.cosh (η / 2)), sq (Real.sinh (η / 2))]
  have h_sinh_double : Real.sinh η = 2 * Real.cosh (η / 2) * Real.sinh (η / 2) := by
    have h1 := Real.sinh_two_mul (η / 2)
    have h2 : 2 * (η / 2) = η := by ring
    rw [h2] at h1
    calc Real.sinh η = 2 * Real.sinh (η / 2) * Real.cosh (η / 2) := h1
      _ = 2 * Real.cosh (η / 2) * Real.sinh (η / 2) := by ring
  have h_unnorm_fwd :
      unnormMidpointRotor γ₀ (boostedFrame η γ₀ B) =
        (2 * Real.cosh (η / 2)) • bogoliubovRotor η B := by
    dsimp [unnormMidpointRotor, boostedFrame, bogoliubovRotor]
    calc 1 + (Real.cosh η • γ₀ + Real.sinh η • (B * γ₀)) * γ₀
      _ = (1 : ℝ) • (1 : E) + Real.cosh η • (γ₀ * γ₀) + Real.sinh η • (B * (γ₀ * γ₀)) := by
        rw [one_smul, add_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc, add_assoc]
      _ = (1 + Real.cosh η) • (1 : E) + Real.sinh η • B := by
        rw [hγ₀, mul_one, add_smul, add_assoc]
      _ = (2 * Real.cosh (η / 2) * Real.cosh (η / 2)) • (1 : E) +
          (2 * Real.cosh (η / 2) * Real.sinh (η / 2)) • B := by
        rw [h_one_add_cosh, h_sinh_double]
      _ = (2 * Real.cosh (η / 2)) •
          (Real.cosh (η / 2) • (1 : E) + Real.sinh (η / 2) • B) := by
        rw [smul_add, smul_smul, smul_smul]
  have hγ₀B : γ₀ * B = -(B * γ₀) := eq_neg_of_add_eq_zero_left hanti
  have hγ₀Bγ₀ : γ₀ * (B * γ₀) = -B := by
    calc γ₀ * (B * γ₀) = (γ₀ * B) * γ₀ := by noncomm_ring
      _ = (-(B * γ₀)) * γ₀ := by rw [hγ₀B]
      _ = -(B * (γ₀ * γ₀)) := by noncomm_ring
      _ = -(B * 1) := by rw [hγ₀]
      _ = -B := by rw [mul_one]
  have h_unnorm_rev :
      unnormMidpointRev γ₀ (boostedFrame η γ₀ B) =
        (2 * Real.cosh (η / 2)) • bogoliubovRotor (-η) B := by
    rw [bogoliubovRotor_neg_eq_inv]
    dsimp [unnormMidpointRev, boostedFrame, bogoliubovRotorInv]
    calc 1 + γ₀ * (Real.cosh η • γ₀ + Real.sinh η • (B * γ₀))
      _ = (1 : ℝ) • (1 : E) + Real.cosh η • (γ₀ * γ₀) + Real.sinh η • (γ₀ * (B * γ₀)) := by
        rw [one_smul, mul_add, mul_smul_comm, mul_smul_comm, add_assoc]
      _ = (1 + Real.cosh η) • (1 : E) - Real.sinh η • B := by
        rw [hγ₀, hγ₀Bγ₀, smul_neg, ← sub_eq_add_neg, add_smul]
      _ = (2 * Real.cosh (η / 2) * Real.cosh (η / 2)) • (1 : E) -
          (2 * Real.cosh (η / 2) * Real.sinh (η / 2)) • B := by
        rw [h_one_add_cosh, h_sinh_double]
      _ = (2 * Real.cosh (η / 2)) •
          (Real.cosh (η / 2) • (1 : E) - Real.sinh (η / 2) • B) := by
        rw [smul_sub, smul_smul, smul_smul]
  have h_fwd_eq :
      bogoliubovRotor η B =
        midpointRotor (2 * Real.cosh (η / 2)) γ₀ (boostedFrame η γ₀ B) := by
    dsimp [midpointRotor]
    rw [h_unnorm_fwd, inv_smul_smul₀ hs]
  have h_rev_eq :
      bogoliubovRotor (-η) B =
        midpointRotorRev (2 * Real.cosh (η / 2)) γ₀ (boostedFrame η γ₀ B) := by
    dsimp [midpointRotorRev]
    rw [h_unnorm_rev, inv_smul_smul₀ hs]
  have h_norm :
      unnormMidpointRotor γ₀ (boostedFrame η γ₀ B) *
          unnormMidpointRev γ₀ (boostedFrame η γ₀ B) =
        ((2 * Real.cosh (η / 2)) ^ 2) • (1 : E) := by
    rw [h_unnorm_fwd, h_unnorm_rev, smul_mul_smul, bogoliubovRotor_neg_eq_inv,
      bogoliubovRotor_mul_inv η B hB, sq]
  have h_boost_sq : boostedFrame η γ₀ B * boostedFrame η γ₀ B = 1 :=
    boostedFrame_sq η γ₀ B hγ₀ hB hanti
  have h_mid :=
    midpointRotor_normalized_sandwich (2 * Real.cosh (η / 2)) γ₀ (boostedFrame η γ₀ B)
      hs hγ₀ h_boost_sq h_norm
  have h_u1 : bogoliubovRotor η B * bogoliubovRotor (-η) B = 1 := by
    rw [h_fwd_eq, h_rev_eq]
    exact h_mid.1
  have h_u2 : bogoliubovRotor (-η) B * bogoliubovRotor η B = 1 := by
    rw [h_fwd_eq, h_rev_eq]
    exact h_mid.2.1
  have h_sand : bogoliubovRotor η B * γ₀ * bogoliubovRotor (-η) B = boostedFrame η γ₀ B := by
    rw [h_fwd_eq, h_rev_eq]
    exact h_mid.2.2
  exact ⟨hs, h_norm, h_fwd_eq, h_rev_eq, h_u1, h_u2, h_sand⟩

/-- Acceptance Theorem 4b: Hyperbolic Bogoliubov Peirce aporia — compressing `P_in` and `Q_in`
into the boosted projector `P_out` produces `+cosh²(η/2)` and `-sinh²(η/2)` (exact negative sign). -/
theorem bogoliubovRotor_peirce_aporia_neg_sinhSq
    (η : ℝ) (γ₀ B : E)
    (hγ₀ : γ₀ * γ₀ = 1)
    (hB : B * B = 1)
    (hanti : γ₀ * B + B * γ₀ = 0) :
    let P_in : E := (1 / 2 : ℝ) • (1 + γ₀)
    let Q_in : E := 1 - P_in
    let P_out : E := (1 / 2 : ℝ) • (1 + boostedFrame η γ₀ B)
    P_in * P_in = P_in ∧
    P_out * P_out = P_out ∧
    P_out * P_in * P_out = (Real.cosh (η / 2)) ^ 2 • P_out ∧
    P_out * Q_in * P_out = -((Real.sinh (η / 2)) ^ 2) • P_out ∧
    P_out * P_in * P_out + P_out * Q_in * P_out = P_out := by
  let Γ_out : E := boostedFrame η γ₀ B
  let P_in : E := (1 / 2 : ℝ) • (1 + γ₀)
  let Q_in : E := 1 - P_in
  let P_out : E := (1 / 2 : ℝ) • (1 + Γ_out)
  have hΓ_out_sq : Γ_out * Γ_out = 1 := boostedFrame_sq η γ₀ B hγ₀ hB hanti
  have hPin_sq : P_in * P_in = P_in := by
    dsimp [P_in]
    have hsq : (1 + γ₀) * (1 + γ₀) = (2 : ℝ) • (1 + γ₀) := by
      calc (1 + γ₀) * (1 + γ₀)
        _ = 1 + γ₀ + γ₀ + γ₀ * γ₀ := by noncomm_ring
        _ = 1 + γ₀ + γ₀ + 1 := by rw [hγ₀]
        _ = (1 + γ₀) + (1 + γ₀) := by abel
        _ = (1 : ℝ) • (1 + γ₀) + (1 : ℝ) • (1 + γ₀) := by rw [one_smul]
        _ = ((1 : ℝ) + 1) • (1 + γ₀) := (add_smul (1 : ℝ) 1 (1 + γ₀)).symm
        _ = (2 : ℝ) • (1 + γ₀) := by norm_num
    rw [smul_mul_smul, hsq, smul_smul]
    have hc : (1 / 2 : ℝ) * (1 / 2) * 2 = 1 / 2 := by norm_num
    rw [hc]
  have hPout_sq : P_out * P_out = P_out := by
    dsimp [P_out]
    have hsq : (1 + Γ_out) * (1 + Γ_out) = (2 : ℝ) • (1 + Γ_out) := by
      calc (1 + Γ_out) * (1 + Γ_out)
        _ = 1 + Γ_out + Γ_out + Γ_out * Γ_out := by noncomm_ring
        _ = 1 + Γ_out + Γ_out + 1 := by rw [hΓ_out_sq]
        _ = (1 + Γ_out) + (1 + Γ_out) := by abel
        _ = (1 : ℝ) • (1 + Γ_out) + (1 : ℝ) • (1 + Γ_out) := by rw [one_smul]
        _ = ((1 : ℝ) + 1) • (1 + Γ_out) := (add_smul (1 : ℝ) 1 (1 + Γ_out)).symm
        _ = (2 : ℝ) • (1 + Γ_out) := by norm_num
    rw [smul_mul_smul, hsq, smul_smul]
    have hc : (1 / 2 : ℝ) * (1 / 2) * 2 = 1 / 2 := by norm_num
    rw [hc]
  have h_anticomm_boost : Γ_out * γ₀ + γ₀ * Γ_out = (2 * Real.cosh η) • (1 : E) := by
    have hγ₀Bγ₀ : γ₀ * (B * γ₀) = -B := by
      have hγ₀B : γ₀ * B = -(B * γ₀) := eq_neg_of_add_eq_zero_left hanti
      calc γ₀ * (B * γ₀) = (γ₀ * B) * γ₀ := by noncomm_ring
        _ = (-(B * γ₀)) * γ₀ := by rw [hγ₀B]
        _ = -(B * (γ₀ * γ₀)) := by noncomm_ring
        _ = -(B * 1) := by rw [hγ₀]
        _ = -B := by rw [mul_one]
    dsimp [Γ_out, boostedFrame]
    calc (Real.cosh η • γ₀ + Real.sinh η • (B * γ₀)) * γ₀ +
          γ₀ * (Real.cosh η • γ₀ + Real.sinh η • (B * γ₀))
      _ = Real.cosh η • (γ₀ * γ₀) + Real.sinh η • (B * (γ₀ * γ₀)) +
          (Real.cosh η • (γ₀ * γ₀) + Real.sinh η • (γ₀ * (B * γ₀))) := by
        rw [add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
          mul_assoc]
      _ = Real.cosh η • (1 : E) + Real.sinh η • B +
          (Real.cosh η • (1 : E) - Real.sinh η • B) := by
        rw [hγ₀, mul_one, hγ₀Bγ₀, smul_neg, ← sub_eq_add_neg]
      _ = Real.cosh η • (1 : E) + Real.cosh η • (1 : E) := by abel
      _ = (Real.cosh η + Real.cosh η) • (1 : E) := (add_smul _ _ _).symm
      _ = (2 * Real.cosh η) • (1 : E) := by
        have htwo : Real.cosh η + Real.cosh η = 2 * Real.cosh η := by ring
        rw [htwo]
  have h_sand_γ₀ : P_out * γ₀ * P_out = Real.cosh η • P_out := by
    have h_inner : (1 + Γ_out) * γ₀ * (1 + Γ_out) = (2 * Real.cosh η) • (1 + Γ_out) := by
      calc (1 + Γ_out) * γ₀ * (1 + Γ_out)
        _ = (γ₀ + Γ_out * γ₀) + (γ₀ * Γ_out + Γ_out * γ₀ * Γ_out) := by noncomm_ring
        _ = (Γ_out * γ₀ + γ₀ * Γ_out) + (γ₀ + Γ_out * γ₀ * Γ_out) := by abel
        _ = (Γ_out * γ₀ + γ₀ * Γ_out) + (Γ_out * (Γ_out * γ₀ + γ₀ * Γ_out)) := by
          have h_id : Γ_out * (Γ_out * γ₀ + γ₀ * Γ_out) = γ₀ + Γ_out * γ₀ * Γ_out := by
            calc Γ_out * (Γ_out * γ₀ + γ₀ * Γ_out)
              _ = (Γ_out * Γ_out) * γ₀ + Γ_out * γ₀ * Γ_out := by noncomm_ring
              _ = 1 * γ₀ + Γ_out * γ₀ * Γ_out := by rw [hΓ_out_sq]
              _ = γ₀ + Γ_out * γ₀ * Γ_out := by rw [one_mul]
          rw [h_id]
        _ = (2 * Real.cosh η) • (1 : E) + Γ_out * ((2 * Real.cosh η) • (1 : E)) := by
          rw [h_anticomm_boost]
        _ = (2 * Real.cosh η) • (1 : E) + (2 * Real.cosh η) • Γ_out := by
          rw [mul_smul_comm, mul_one]
        _ = (2 * Real.cosh η) • (1 + Γ_out) := (smul_add _ _ _).symm
    dsimp [P_out]
    calc ((1 / 2 : ℝ) • (1 + Γ_out)) * γ₀ * ((1 / 2 : ℝ) • (1 + Γ_out))
      _ = ((1 / 2 : ℝ) * (1 / 2)) • ((1 + Γ_out) * γ₀ * (1 + Γ_out)) := by
        rw [smul_mul_assoc, smul_mul_smul]
      _ = ((1 / 2 : ℝ) * (1 / 2)) • ((2 * Real.cosh η) • (1 + Γ_out)) := by rw [h_inner]
      _ = (((1 / 2 : ℝ) * (1 / 2)) * (2 * Real.cosh η)) • (1 + Γ_out) := by rw [smul_smul]
      _ = (Real.cosh η * (1 / 2 : ℝ)) • (1 + Γ_out) := by
        have hc : (1 / 2 : ℝ) * (1 / 2) * (2 * Real.cosh η) = Real.cosh η * (1 / 2) := by ring
        rw [hc]
      _ = Real.cosh η • ((1 / 2 : ℝ) • (1 + Γ_out)) := by rw [smul_smul]
  have h_half_cosh : (1 / 2 : ℝ) * (1 + Real.cosh η) = (Real.cosh (η / 2)) ^ 2 := by
    have h1 := Real.cosh_two_mul (η / 2)
    have h2 : 2 * (η / 2) = η := by ring
    rw [h2] at h1
    have hcs := Real.cosh_sq_sub_sinh_sq (η / 2)
    linarith [sq (Real.cosh (η / 2)), sq (Real.sinh (η / 2))]
  have h_Pin_comp : P_out * P_in * P_out = (Real.cosh (η / 2)) ^ 2 • P_out := by
    have hexp1 : P_out * P_in * P_out = (1 / 2 : ℝ) • (P_out * (1 + γ₀) * P_out) := by
      show P_out * ((1 / 2 : ℝ) • (1 + γ₀)) * P_out = (1 / 2 : ℝ) • (P_out * (1 + γ₀) * P_out)
      rw [mul_smul_comm (1 / 2 : ℝ) P_out (1 + γ₀), smul_mul_assoc]
    calc P_out * P_in * P_out
      _ = (1 / 2 : ℝ) • (P_out * (1 + γ₀) * P_out) := hexp1
      _ = (1 / 2 : ℝ) • (P_out * P_out + P_out * γ₀ * P_out) := by
        have hexp : P_out * (1 + γ₀) * P_out = P_out * P_out + P_out * γ₀ * P_out := by
          noncomm_ring
        rw [hexp]
      _ = (1 / 2 : ℝ) • ((1 : ℝ) • P_out + Real.cosh η • P_out) := by
        rw [hPout_sq, h_sand_γ₀, one_smul]
      _ = (1 / 2 : ℝ) • ((1 + Real.cosh η) • P_out) := by
        rw [← add_smul]
      _ = ((1 / 2 : ℝ) * (1 + Real.cosh η)) • P_out := by rw [smul_smul]
      _ = (Real.cosh (η / 2)) ^ 2 • P_out := by rw [h_half_cosh]
  have h_Qin_comp : P_out * Q_in * P_out = -((Real.sinh (η / 2)) ^ 2) • P_out := by
    have h_cs : 1 - (Real.cosh (η / 2)) ^ 2 = -((Real.sinh (η / 2)) ^ 2) := by
      have hcs := Real.cosh_sq_sub_sinh_sq (η / 2)
      linarith
    calc P_out * (1 - P_in) * P_out
      _ = P_out * P_out - P_out * P_in * P_out := by noncomm_ring
      _ = (1 : ℝ) • P_out - (Real.cosh (η / 2)) ^ 2 • P_out := by
        rw [hPout_sq, h_Pin_comp, one_smul]
      _ = (1 - (Real.cosh (η / 2)) ^ 2) • P_out := by rw [sub_smul]
      _ = -((Real.sinh (η / 2)) ^ 2) • P_out := by rw [h_cs]
  have h_sum : P_out * P_in * P_out + P_out * Q_in * P_out = P_out := by
    rw [h_Pin_comp, h_Qin_comp, ← add_smul]
    have hcs := Real.cosh_sq_sub_sinh_sq (η / 2)
    have h1 : (Real.cosh (η / 2)) ^ 2 + -((Real.sinh (η / 2)) ^ 2) = 1 := by linarith
    rw [h1, one_smul]
  exact ⟨hPin_sq, hPout_sq, h_Pin_comp, h_Qin_comp, h_sum⟩

end BogoliubovPeirce

/-! ## Section 5: Covariant QGT via DerivationLieLane -/

section CovariantQGT

section RingLevel
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The inward transition operator `conePlus P (K.operatorAction v P)`. -/
def qgtInward (K : DerivationLieLane R A) (P : A) (v : K.L) : A :=
  InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P (K.operatorAction v P)

/-- The outward transition operator `coneMinus P (K.operatorAction v P)`. -/
def qgtOutward (K : DerivationLieLane R A) (P : A) (v : K.L) : A :=
  InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P (K.operatorAction v P)

/-- The covariant Quantum Geometric Tensor `Q_vw := qgtInward K P v * qgtOutward K P w`. -/
def derivationQGT (K : DerivationLieLane R A) (P : A) (v w : K.L) : A :=
  qgtInward K P v * qgtOutward K P w

private theorem derivation_leibniz_idemp
    (K : DerivationLieLane R A) (P : A) (v : K.L) (hP : P * P = P) :
    K.operatorAction v P = K.operatorAction v P * P + P * K.operatorAction v P := by
  calc K.operatorAction v P
    _ = K.operatorAction v (P * P) := by rw [hP]
    _ = K.operatorAction v P * P + P * K.operatorAction v P :=
      K.operatorAction_leibniz v P P

/-- Automatic off-diagonality of derivations on projectors: `P * (D P) * P = 0`. -/
theorem derivation_projector_off_diagonal
    (K : DerivationLieLane R A) (P : A) (v : K.L)
    (hP : P * P = P) :
    P * K.operatorAction v P * P = 0 := by
  have hleib := derivation_leibniz_idemp K P v hP
  have h1 : P * (K.operatorAction v P * P + P * K.operatorAction v P) * P =
      P * K.operatorAction v P * P + P * K.operatorAction v P * P := by
    calc P * (K.operatorAction v P * P + P * K.operatorAction v P) * P
      _ = P * K.operatorAction v P * (P * P) + (P * P) * K.operatorAction v P * P := by
        noncomm_ring
      _ = P * K.operatorAction v P * P + P * K.operatorAction v P * P := by rw [hP]
  calc P * K.operatorAction v P * P
    _ = (P * K.operatorAction v P * P + P * K.operatorAction v P * P) -
          P * K.operatorAction v P * P := by noncomm_ring
    _ = P * (K.operatorAction v P * P + P * K.operatorAction v P) * P -
          P * K.operatorAction v P * P := by rw [← h1]
    _ = P * K.operatorAction v P * P - P * K.operatorAction v P * P := by rw [← hleib]
    _ = 0 := sub_self _

/-- Automatic off-diagonality on the complement `(1 - P) * (D P) * (1 - P) = 0`. -/
theorem derivation_complement_off_diagonal
    (K : DerivationLieLane R A) (P : A) (v : K.L)
    (hP : P * P = P) :
    (1 - P) * K.operatorAction v P * (1 - P) = 0 := by
  have hleib := derivation_leibniz_idemp K P v hP
  have hPcomp : P * (1 - P) = 0 := by
    calc P * (1 - P)
      _ = P - P * P := by noncomm_ring
      _ = P - P := by rw [hP]
      _ = 0 := sub_self _
  have hcompP : (1 - P) * P = 0 := by
    calc (1 - P) * P
      _ = P - P * P := by noncomm_ring
      _ = P - P := by rw [hP]
      _ = 0 := sub_self _
  calc (1 - P) * K.operatorAction v P * (1 - P)
    _ = (1 - P) * (K.operatorAction v P * P + P * K.operatorAction v P) * (1 - P) := by
      rw [← hleib]
    _ = (1 - P) * K.operatorAction v P * (P * (1 - P)) +
          ((1 - P) * P) * K.operatorAction v P * (1 - P) := by
      noncomm_ring
    _ = (1 - P) * K.operatorAction v P * 0 + 0 * K.operatorAction v P * (1 - P) := by
      rw [hPcomp, hcompP]
    _ = 0 := by noncomm_ring

/-- QGT contraction: `derivationQGT K P v w = P * K.operatorAction v P * K.operatorAction w P * P`. -/
theorem derivationQGT_formula
    (K : DerivationLieLane R A) (P : A) (v w : K.L)
    (hP : P * P = P) :
    derivationQGT K P v w = P * K.operatorAction v P * K.operatorAction w P * P := by
  dsimp [derivationQGT, qgtInward, qgtOutward,
    InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
    InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus]
  have hoff : P * K.operatorAction w P * P = 0 :=
    derivation_projector_off_diagonal K P w hP
  have hcomp_sq : (1 - P) * (1 - P) = 1 - P := by
    calc (1 - P) * (1 - P)
      _ = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P - P + P := by rw [hP]
      _ = 1 - P := by noncomm_ring
  calc (P * K.operatorAction v P * (1 - P)) * ((1 - P) * K.operatorAction w P * P)
    _ = P * K.operatorAction v P * ((1 - P) * (1 - P)) * K.operatorAction w P * P := by
      noncomm_ring
    _ = P * K.operatorAction v P * (1 - P) * K.operatorAction w P * P := by
      rw [hcomp_sq]
    _ = P * K.operatorAction v P * K.operatorAction w P * P -
          P * K.operatorAction v P * (P * K.operatorAction w P * P) := by
      noncomm_ring
    _ = P * K.operatorAction v P * K.operatorAction w P * P -
          P * K.operatorAction v P * 0 := by
      rw [hoff]
    _ = P * K.operatorAction v P * K.operatorAction w P * P := by
      noncomm_ring

/-- Skew-symmetric QGT recovers the Peirce-compressed Berry commutator. -/
theorem derivationQGT_skew_berry
    (K : DerivationLieLane R A) (P : A) (v w : K.L)
    (hP : P * P = P) :
    derivationQGT K P v w - derivationQGT K P w v =
      P * InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (K.operatorAction v P) (K.operatorAction w P) * P := by
  rw [derivationQGT_formula K P v w hP, derivationQGT_formula K P w v hP]
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  noncomm_ring

end RingLevel

/-- Acceptance Theorem 5: Automatic Leibniz off-diagonality on both `P` and `1 - P`,
QGT contraction, skew Berry commutator, and `ℂ`-linear symmetric/skew `-i` decomposition. -/
theorem derivationQGT_leibniz_offDiagonal_and_berry_split
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Algebra ℂ A]
    (K : DerivationLieLane R A) (P : A) (v w : K.L)
    (hP : P * P = P) :
    P * K.operatorAction v P * P = 0 ∧
    (1 - P) * K.operatorAction v P * (1 - P) = 0 ∧
    derivationQGT K P v w = P * K.operatorAction v P * K.operatorAction w P * P ∧
    derivationQGT K P v w - derivationQGT K P w v =
      P * InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (K.operatorAction v P) (K.operatorAction w P) * P ∧
    (2 : ℂ) • derivationQGT K P v w =
      (derivationQGT K P v w + derivationQGT K P w v) +
        Complex.I • ((-Complex.I) • (derivationQGT K P v w - derivationQGT K P w v)) := by
  refine ⟨derivation_projector_off_diagonal K P v hP,
    derivation_complement_off_diagonal K P v hP,
    derivationQGT_formula K P v w hP,
    derivationQGT_skew_berry K P v w hP, ?_⟩
  have hI : Complex.I * (-Complex.I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  have htwo : (2 : ℂ) • derivationQGT K P v w =
      derivationQGT K P v w + derivationQGT K P v w := by
    rw [← one_add_one_eq_two, add_smul, one_smul]
  calc (2 : ℂ) • derivationQGT K P v w
    _ = derivationQGT K P v w + derivationQGT K P v w := htwo
    _ = (derivationQGT K P v w + derivationQGT K P w v) +
          (derivationQGT K P v w - derivationQGT K P w v) := by abel
    _ = (derivationQGT K P v w + derivationQGT K P w v) +
          (1 : ℂ) • (derivationQGT K P v w - derivationQGT K P w v) := by
      rw [one_smul]
    _ = (derivationQGT K P v w + derivationQGT K P w v) +
          (Complex.I * (-Complex.I)) • (derivationQGT K P v w - derivationQGT K P w v) := by
      rw [hI]
    _ = (derivationQGT K P v w + derivationQGT K P w v) +
          Complex.I • ((-Complex.I) • (derivationQGT K P v w - derivationQGT K P w v)) := by
      rw [smul_smul]

end CovariantQGT

end InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT
