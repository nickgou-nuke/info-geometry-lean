/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Twistor.WittenSpinorHelicity
import InfoGeometry.Bridge.OperatorPauliLubanskiLift
import InfoGeometry.Canonical.OperatorZornSpinCasimirLift
import InfoGeometry.Physics.SDiffCoadjointHelicityCasimir
import InfoGeometry.Physics.NuclearAngularMomentum
import InfoGeometry.Physics.NuclearSymmetrySectors
import InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
import InfoGeometry.Physics.NuclearInternalExternalParityFactorization
import InfoGeometry.Physics.NuclearQuantumNumberPacket
import InfoGeometry.Physics.NuclearChargeSpinSymmetry
import InfoGeometry.Physics.NuclearRotationalBand
import InfoGeometry.Physics.NuclearGiantResonance

/-!
# Seam C: Helicity to Nuclear $K^\pi$-Projection Synthesis

This module builds a kernel-checked, carrier-exact typed bridge connecting spinor/fluid helicity
and chiral spin structures to nuclear rotational $K^\pi$-projection and quantum-number packets:

1. **Massless Spinor-Helicity (`WittenSpinorHelicity`)**: `U(1)` little-group reality
   preservation (`u1_littleGroup_preserves_reality`, `littleGroup_preserves_reality_iff_u1`),
   null `pauliMomentum` reality slice (`real_null_pauliMomentum_spinorOuter_reality`),
   weights `±2` on `epsPlus`/`epsMinus` (`epsPlus_littleGroup`, `epsMinus_littleGroup`),
   and pairing `trace_epsPlus_mul_pauliBar_epsMinus = -1`, kept distinct from massive 3-state
   `SpinSpace 2`.
2. **Spin-1/2 Operator Bridge (`OperatorZornSpinCasimirLift`, `OperatorPauliLubanskiLift`,
   `NuclearRotationalBand`, `NuclearAngularMomentum`)**: Exact identification of
   `OperatorZornSpinCasimirLift` generators (`spinZ`, `spinRaise`, `spinLower`, `spinHalfCasimir`)
   with `(spinIrrep 1)` / `spinHalfSU2Rep` and `spinCasimirOp 1` on `SpinSpace 1 = Fin 2 → ℂ`,
   matching eigenvectors `positiveHelicitySpinor = spinKet 1 0` and
   `negativeHelicitySpinor = spinKet 1 1`, explicit non-commutativity witnesses
   (`spinRaise * spinLower ≠ spinLower * spinRaise`), and separation between massless null
   `W² = 0` (`pauliLubanski_null_norm`) and massive rest-frame Casimir `-m² s(s+1)`.
3. **Continuous `SDiff` Fluid Helicity vs Discrete `twoK` (`SDiffCoadjoint`)**:
   Unconditional coadjoint-invariant sign projection `sdiffHelicitySignParity` together with the
   non-trivial `QuantizedSDiffHelicityHypothesis` (`Type`) bridge carrying
   `0 < helicityScale` and `|totalHelicity state| = helicityScale * (twoK : ℝ)`.
4. **Nuclear $K^\pi$-Bands, Four-Parity Factorization, Galois/Charge-Spin, & Multipoles**:
   Typed `HelicityToNuclearKPacket` (`Type`) mapping into `NuclearTaxonomyPacket` and
   `KParitySector`, preserving uncollapsed `FourParityCarrier` involutions
   (`piOp ≠ fermionOp`, `fermionOp ≠ wmOp`, `wmOp ≠ mengParityOp`, `[k0Op, wmOp] ≠ 0`),
   unsigned `RotationalBandhead.twoK : ℕ` vs signed `KParitySector.twoK : ℤ`,
   `k0Alternating_iff_packet_staggering`, `QuantumNumberSymmetry`/`galoisExtendedAction`,
   and `E1`/`M1`/`E2` multipole parity selection rules.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.HelicityNuclearKProjectionSynthesis

open Matrix
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Twistor.WittenSpinorHelicity
open InfoGeometry.Physics.LorentzBoostMinkowski
open InfoGeometry.Physics.PauliLubanskiFiniteBridge
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Bridge.OperatorPauliLubanskiLift
open InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge
open InfoGeometry.Canonical.OperatorZornSpinCasimirLift
open InfoGeometry.Canonical
open InfoGeometry.Physics.SDiffCoadjoint
open InfoGeometry.Physics.NuclearAngularMomentum
open InfoGeometry.Physics.NuclearSymmetrySectors
open InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
open InfoGeometry.Physics.NuclearInternalExternalParityFactorization
open InfoGeometry.Physics.NuclearCartanProjectorParityBridge
open InfoGeometry.Physics.NuclearWignerSupermultiplet
open InfoGeometry.Physics.NuclearQuantumNumberPacket
open InfoGeometry.Canonical.BostConnesGalois
open InfoGeometry.Physics.NuclearChargeSpinSymmetry
open InfoGeometry.Physics.NuclearRotationalBand
open InfoGeometry.Physics.NuclearGiantResonance

/-! ## Section 1: Massless Spinor-Helicity `U(1)` Little Group & `K^π` Sector Projections -/

/-- Massless spin-1 helicity branch (`±1`, scaling as `c^{∓2}` under `U(1)` little group). -/
inductive MasslessHelicityBranch where
  | plusOne
  | minusOne
  deriving DecidableEq, Repr

/-- Explicit two-element equivalence `MasslessHelicityBranch ≃ Fin 2`. -/
def MasslessHelicityBranch.equivFin2 : MasslessHelicityBranch ≃ Fin 2 where
  toFun
    | .plusOne => 0
    | .minusOne => 1
  invFun i := if i = 0 then .plusOne else .minusOne
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype MasslessHelicityBranch :=
  Fintype.ofEquiv (Fin 2) MasslessHelicityBranch.equivFin2.symm

/-- Signed doubled helicity `±2 : ℤ` of a massless spin-1 branch. -/
def MasslessHelicityBranch.signedTwoHelicity : MasslessHelicityBranch → ℤ
  | .plusOne => 2
  | .minusOne => -2

/-- Unsigned bandhead label `twoK = 2 : ℕ` of a massless spin-1 branch. -/
def MasslessHelicityBranch.unsignedTwoK : MasslessHelicityBranch → ℕ
  | .plusOne => 2
  | .minusOne => 2

/-- Spatial parity label attached to a massless helicity branch. -/
def MasslessHelicityBranch.toSpatialParity : MasslessHelicityBranch → SpatialParity
  | .plusOne => .positive
  | .minusOne => .negative

/-- Signed `K^π` projection `⟨±2, π⟩` of a massless spin-1 helicity branch. -/
def MasslessHelicityBranch.toKParitySector (h : MasslessHelicityBranch) : KParitySector :=
  ⟨h.signedTwoHelicity, h.toSpatialParity⟩

/-- Unsigned rotational bandhead label `⟨2, π⟩` of a massless spin-1 helicity branch. -/
def MasslessHelicityBranch.toBandhead (h : MasslessHelicityBranch) : RotationalBandhead :=
  ⟨h.unsignedTwoK, h.toSpatialParity⟩

/-- Spin-1/2 circular helicity branch (`±1/2`, matching `zornSpinPlusProjector`/`Minus`). -/
inductive SpinHalfHelicityBranch where
  | plusHalf
  | minusHalf
  deriving DecidableEq, Repr

/-- Explicit two-element equivalence `SpinHalfHelicityBranch ≃ Fin 2`. -/
def SpinHalfHelicityBranch.equivFin2 : SpinHalfHelicityBranch ≃ Fin 2 where
  toFun
    | .plusHalf => 0
    | .minusHalf => 1
  invFun i := if i = 0 then .plusHalf else .minusHalf
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype SpinHalfHelicityBranch :=
  Fintype.ofEquiv (Fin 2) SpinHalfHelicityBranch.equivFin2.symm

/-- Signed doubled helicity `±1 : ℤ` of a spin-1/2 branch. -/
def SpinHalfHelicityBranch.signedTwoK : SpinHalfHelicityBranch → ℤ
  | .plusHalf => 1
  | .minusHalf => -1

/-- Unsigned `twoK = 1 : ℕ` of a spin-1/2 branch. -/
def SpinHalfHelicityBranch.unsignedTwoK : SpinHalfHelicityBranch → ℕ
  | .plusHalf => 1
  | .minusHalf => 1

/-- Canonical spin-1/2 ket in `SpinSpace 1` associated to a circular helicity branch. -/
def SpinHalfHelicityBranch.toSpinKet : SpinHalfHelicityBranch → SpinSpace 1
  | .plusHalf => spinKet 1 0
  | .minusHalf => spinKet 1 1

/-- Unsigned bandhead `⟨1, π⟩` associated to a spin-1/2 branch and parity `π`. -/
def SpinHalfHelicityBranch.toBandhead (π : SpatialParity) : RotationalBandhead :=
  ⟨1, π⟩

/-- `U(1)` spinor-helicity reality slice, `epsPlus`/`epsMinus` weights `∓2`, inner pairing `-1`,
and distinction between 2-state massless helicity (`twoK = 2`) and 3-state massive `SpinSpace 2`. -/
theorem witten_u1_little_group_helicity_and_bandhead
    (P : Fin 4 → ℝ) (q qTilde lambda lambdaTilde : Spinor2) (c : ℂ) (r : ℝ)
    (hc : star c * c = 1) (hr : r ≠ 0) (hlam : lambda ≠ 0)
    (hP_ne : spinorOuter lambda lambdaTilde ≠ 0)
    (hP : pauliMomentum (realFourMomentum P) = spinorOuter lambda lambdaTilde)
    (hq : spinorBracket q lambda ≠ 0) (hqTilde : spinorBracket qTilde lambdaTilde ≠ 0) :
    (P 0 ^ 2 - P 1 ^ 2 - P 2 ^ 2 - P 3 ^ 2 = 0 ∧
      ∃ r0 : ℝ, r0 ≠ 0 ∧ lambdaTilde = (r0 : ℂ) • star lambda) ∧
    (c⁻¹ • ((r : ℂ) • star lambda) = (r : ℂ) • star (c • lambda)) ∧
    (c ≠ 0 →
      (c⁻¹ • ((r : ℂ) • star lambda) = (r : ℂ) • star (c • lambda) ↔ star c * c = 1)) ∧
    (epsPlus q (c • lambda) (c⁻¹ • lambdaTilde) = (c * c)⁻¹ • epsPlus q lambda lambdaTilde) ∧
    (epsMinus qTilde (c • lambda) (c⁻¹ • lambdaTilde) =
      (c * c) • epsMinus qTilde lambda lambdaTilde) ∧
    (Matrix.trace (epsPlus q lambda lambdaTilde * pauliBar (epsMinus qTilde lambda lambdaTilde)) =
      -1) ∧
    (MasslessHelicityBranch.plusOne.toKParitySector ≠
      MasslessHelicityBranch.minusOne.toKParitySector) ∧
    (Fintype.card MasslessHelicityBranch = 2 ∧
      Fintype.card (Fin (2 + 1)) = 3 ∧
      Fintype.card MasslessHelicityBranch ≠ Fintype.card (Fin (2 + 1))) := by
  have hcard : Fintype.card MasslessHelicityBranch = 2 := by
    rw [Fintype.card_congr MasslessHelicityBranch.equivFin2]
    decide
  refine ⟨real_null_pauliMomentum_spinorOuter_reality P lambda lambdaTilde hP_ne hP,
    u1_littleGroup_preserves_reality c hc r lambda,
    fun hnz => littleGroup_preserves_reality_iff_u1 c hnz r hr lambda hlam,
    epsPlus_littleGroup c q lambda lambdaTilde,
    epsMinus_littleGroup c qTilde lambda lambdaTilde,
    trace_epsPlus_mul_pauliBar_epsMinus q qTilde lambda lambdaTilde hq hqTilde,
    by decide,
    ⟨hcard, by decide, by rw [hcard]; decide⟩⟩

/-! ## Section 2: Exact Spin-1/2 Operator Bridge & Massive vs Null Pauli–Lubanski Separation -/

/-- Exact matrix-to-endomorphism match: `OperatorZornSpinCasimirLift.spinZ = (spinIrrep 1).J_zero`. -/
theorem operatorZorn_spinZ_eq_spinIrrep_J_zero :
    Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinZ =
      (spinIrrep 1).J_zero := by
  apply LinearMap.ext; intro ψ; ext k
  fin_cases k <;>
    (simp [InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinZ,
      InfoGeometry.Quantum.PauliSoldering.σ3, spinIrrep,
      InfoGeometry.Physics.NuclearRotationalBand.spinZ, spinMValue,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; try ring)

/-- Exact matrix-to-endomorphism match: `OperatorZornSpinCasimirLift.spinRaise = (spinIrrep 1).J_plus`. -/
theorem operatorZorn_spinRaise_eq_spinIrrep_J_plus :
    Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinRaise =
      (spinIrrep 1).J_plus := by
  apply LinearMap.ext; intro ψ; ext k
  fin_cases k <;>
    simp [InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinRaise,
      InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.sigmaPlus,
      InfoGeometry.Optics.ChiralLorentzOperatorLift.create,
      spinIrrep, InfoGeometry.Physics.NuclearRotationalBand.spinPlus,
      InfoGeometry.Physics.NuclearRotationalBand.spinPlusCoeff,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Exact matrix-to-endomorphism match: `OperatorZornSpinCasimirLift.spinLower = (spinIrrep 1).J_minus`. -/
theorem operatorZorn_spinLower_eq_spinIrrep_J_minus :
    Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinLower =
      (spinIrrep 1).J_minus := by
  apply LinearMap.ext; intro ψ; ext k
  fin_cases k <;>
    simp [InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinLower,
      InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.sigmaMinus,
      InfoGeometry.Optics.ChiralLorentzOperatorLift.annihilate,
      spinIrrep, InfoGeometry.Physics.NuclearRotationalBand.spinMinus,
      InfoGeometry.Physics.NuclearRotationalBand.spinMinusCoeff,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Exact Casimir match: `OperatorZornSpinCasimirLift.spinHalfCasimir` lifts to `spinCasimirOp 1`. -/
theorem operatorZorn_spinHalfCasimir_eq_spinCasimirOp :
    Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinHalfCasimir =
      spinCasimirOp 1 := by
  rw [InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinHalfCasimir_eq_three_quarters,
    spinCasimirOp_eq_scalar 1, map_smul, Matrix.toLin'_one]
  congr 1
  norm_num

/-- Exact Casimir match: `OperatorPauliLubanskiLift.spinHalfCasimir` lifts to `spinCasimirOp 1`. -/
theorem pauliLubanski_spinHalfCasimir_eq_spinCasimirOp :
    Matrix.toLin' InfoGeometry.Bridge.OperatorPauliLubanskiLift.spinHalfCasimir =
      spinCasimirOp 1 := by
  rw [InfoGeometry.Bridge.OperatorPauliLubanskiLift.spinHalfCasimir,
    spinCasimirOp_eq_scalar 1, map_smul, Matrix.toLin'_one]
  congr 1
  norm_num

/-- Exact ket identification: `positiveHelicitySpinor = spinKet 1 0`. -/
theorem positiveHelicitySpinor_eq_spinKet :
    positiveHelicitySpinor = spinKet 1 0 := by
  ext k
  fin_cases k <;> simp [positiveHelicitySpinor, spinKet]

/-- Exact ket identification: `negativeHelicitySpinor = spinKet 1 1`. -/
theorem negativeHelicitySpinor_eq_spinKet :
    negativeHelicitySpinor = spinKet 1 1 := by
  ext k
  fin_cases k <;> simp [negativeHelicitySpinor, spinKet]

/-- Explicit non-commutativity witness on `Mat2C`: `spinRaise * spinLower ≠ spinLower * spinRaise`. -/
theorem operatorZorn_spinRaise_spinLower_noncomm :
    InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinRaise *
        InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinLower ≠
      InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinLower *
        InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinRaise := by
  intro h
  have hsub :
      InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinRaise *
          InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinLower -
        InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinLower *
          InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinRaise = 0 :=
    sub_eq_zero.mpr h
  rw [spinRaise_spinLower_commutator] at hsub
  have h00 := congrFun (congrFun hsub 0) 0
  norm_num [InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinZ,
    InfoGeometry.Quantum.PauliSoldering.σ3] at h00

/-- Explicit non-commutativity witness on `Module.End ℂ (SpinSpace 1)`:
`(spinIrrep 1).J_plus * (spinIrrep 1).J_minus ≠ (spinIrrep 1).J_minus * (spinIrrep 1).J_plus`. -/
theorem spinIrrep_one_J_plus_J_minus_noncomm :
    (spinIrrep 1).J_plus * (spinIrrep 1).J_minus ≠
      (spinIrrep 1).J_minus * (spinIrrep 1).J_plus := by
  rw [spinIrrep_one_eq_spinHalfSU2Rep]
  exact spinHalfSU2Rep_noncomm

/-- Unified spin-1/2 operator-Zorn, Pauli–Lubanski, and `SU2Rep` bridge with explicit eigenvalue
matching on `spinKet 1 0` / `spinKet 1 1` and massless (`W² = 0`) vs massive (`W² = -m² s(s+1)`)
Casimir separation. -/
theorem spin_half_operator_zorn_pauli_lubanski_bridge
    (P : PauliParavector) (E m s : ℝ)
    (J K : InfoGeometry.Bridge.OperatorPauliLubanskiLift.SpatialVector)
    (hm : m ≠ 0) (hs : 0 < s)
    (hJ : InfoGeometry.Physics.ZornMatrixSU3.dotProduct J J = s * (s + 1)) :
    (Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinZ =
      spinHalfSU2Rep.J_zero) ∧
    (Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinRaise =
      spinHalfSU2Rep.J_plus) ∧
    (Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinLower =
      spinHalfSU2Rep.J_minus) ∧
    (Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinHalfCasimir =
      spinCasimirOp 1) ∧
    (circularHelicity = InfoGeometry.Quantum.PauliSoldering.σ3 ∧
      InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinZ = (2 : ℂ)⁻¹ • circularHelicity ∧
      InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinHalfCasimir =
        (3 / 4 : ℂ) • (1 : InfoGeometry.Canonical.OperatorZornSpinCasimirLift.Mat2C) ∧
      (InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinZ * circularPlus =
        (2 : ℂ)⁻¹ • circularPlus ∧
       InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinZ * circularMinus =
        -(2 : ℂ)⁻¹ • circularMinus) ∧
      (zornHelicity * zornHelicity = 1 ∧
       zornSpinPlusProjector * zornSpinPlusProjector = zornSpinPlusProjector ∧
       zornSpinMinusProjector * zornSpinMinusProjector = zornSpinMinusProjector ∧
       zornSpinPlusProjector * zornSpinMinusProjector = 0 ∧
       InfoGeometry.Physics.OperatorZornMatrix.toMatrix zornSpinHalfCasimir =
         (3 / 4 : ℂ) • (1 : InfoGeometry.Canonical.OperatorZornSpinCasimirLift.Mat2C))) ∧
    ((spinIrrep 1).J_zero (spinKet 1 0) = (1 / 2 : ℂ) • spinKet 1 0 ∧
      (spinIrrep 1).J_zero (spinKet 1 1) = (-(1 / 2 : ℂ)) • spinKet 1 1) ∧
    (∀ μ : Fin 4,
      pauliLubanskiLeft (northNullMomentum E) μ *ᵥ spinKet 1 0 =
        ((1 / 2 : ℂ) * momentumComponent (northNullMomentum E) μ) • spinKet 1 0 ∧
      pauliLubanskiRight (northNullMomentum E) μ *ᵥ spinKet 1 1 =
        (-(1 / 2 : ℂ) * momentumComponent (northNullMomentum E) μ) • spinKet 1 1) ∧
    (minkowskiMatrixSq (pauliLubanskiLeft P) =
      -(P.minkowskiNormSq : ℂ) • InfoGeometry.Bridge.OperatorPauliLubanskiLift.spinHalfCasimir ∧
      ((zornPauliLubanskiSq P).n_plus_op = ((-(3 / 4 : ℝ) * P.minkowskiNormSq : ℝ) : ℂ) ∧
       (zornPauliLubanskiSq P).n_minus_op = ((-(3 / 4 : ℝ) * P.minkowskiNormSq : ℝ) : ℂ) ∧
       (zornPauliLubanskiSq P).sigma_plus_op = 0 ∧
       (zornPauliLubanskiSq P).sigma_minus_op = 0)) ∧
    (minkowskiMatrixSq (pauliLubanskiLeft (northNullMomentum E)) = 0 ∧
      minkowskiMatrixSq (pauliLubanskiRight (northNullMomentum E)) = 0) ∧
    (minkowskiPair (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩)
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩) = -m ^ 2 * s * (s + 1) ∧
      minkowskiPair (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩)
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩) ≠ 0) ∧
    (InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinRaise *
        InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinLower ≠
      InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinLower *
        InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinRaise) := by
  have hz : Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinZ =
      spinHalfSU2Rep.J_zero := by
    rw [operatorZorn_spinZ_eq_spinIrrep_J_zero, spinIrrep_one_eq_spinHalfSU2Rep]
  have hp : Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinRaise =
      spinHalfSU2Rep.J_plus := by
    rw [operatorZorn_spinRaise_eq_spinIrrep_J_plus, spinIrrep_one_eq_spinHalfSU2Rep]
  have hmop : Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinLower =
      spinHalfSU2Rep.J_minus := by
    rw [operatorZorn_spinLower_eq_spinIrrep_J_minus, spinIrrep_one_eq_spinHalfSU2Rep]
  have hk0 : (spinIrrep 1).J_zero (spinKet 1 0) = (1 / 2 : ℂ) • spinKet 1 0 := by
    ext i
    fin_cases i <;>
      simp [spinIrrep, InfoGeometry.Physics.NuclearRotationalBand.spinZ, spinMValue, spinKet]
  have hk1 : (spinIrrep 1).J_zero (spinKet 1 1) = (-(1 / 2 : ℂ)) • spinKet 1 1 := by
    ext i
    fin_cases i <;>
      (simp [spinIrrep, InfoGeometry.Physics.NuclearRotationalBand.spinZ, spinMValue, spinKet];
        try ring)
  have hpl : ∀ μ : Fin 4,
      pauliLubanskiLeft (northNullMomentum E) μ *ᵥ spinKet 1 0 =
        ((1 / 2 : ℂ) * momentumComponent (northNullMomentum E) μ) • spinKet 1 0 ∧
      pauliLubanskiRight (northNullMomentum E) μ *ᵥ spinKet 1 1 =
        (-(1 / 2 : ℂ) * momentumComponent (northNullMomentum E) μ) • spinKet 1 1 := by
    intro μ
    constructor
    · rw [← positiveHelicitySpinor_eq_spinKet]
      exact left_null_positive_helicity E μ
    · rw [← negativeHelicitySpinor_eq_spinKet]
      exact right_null_negative_helicity E μ
  have hmass := rest_frame_massive_casimir m s J K hJ
  have hmass_ne :
      minkowskiPair (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩)
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩) ≠ 0 := by
    rw [hmass]
    have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm
    have hpos : 0 < m ^ 2 * s * (s + 1) := mul_pos (mul_pos hm2 hs) (by linarith)
    have hneg : -m ^ 2 * s * (s + 1) < 0 := by linarith
    exact ne_of_lt hneg
  exact ⟨hz, hp, hmop, operatorZorn_spinHalfCasimir_eq_spinCasimirOp,
    ⟨circularHelicity_eq_sigma3, spinZ_eq_half_helicity,
      InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinHalfCasimir_eq_three_quarters,
      spinZ_projection_packet, operatorZorn_spin_half_packet⟩,
    ⟨hk0, hk1⟩, hpl,
    ⟨pauliLubanskiLeft_sq_eq_mass_spin_casimir P, zornPauliLubanski_coordinate_packet P⟩,
    pauliLubanski_null_norm (northNullMomentum E) (northNullMomentum_isNull E),
    ⟨hmass, hmass_ne⟩,
    operatorZorn_spinRaise_spinLower_noncomm⟩

/-! ## Section 3: Continuous `SDiff` Fluid Helicity vs Discrete `twoK` Projection -/

/-- Unconditional sign projection from continuous 3D `SDiff` `totalHelicity : FluidState → ℝ`
to discrete `SpatialParity` (kept strictly distinct from discrete `twoK : ℕ`). -/
def sdiffHelicitySignParity (s : FluidState) : SpatialParity :=
  if 0 ≤ totalHelicity s then .positive else .negative

/-- Non-trivial hypothesis-parameterized bridge (`Type`, NOT `Prop`) assigning a discrete axial
projection `twoK : ℕ` to a continuous `FluidState` via a strictly positive helicity quantum
`helicityScale > 0` and exact magnitude law `|totalHelicity state| = helicityScale * (twoK : ℝ)`. -/
structure QuantizedSDiffHelicityHypothesis where
  state : FluidState
  twoK : ℕ
  parity : SpatialParity
  helicityScale : ℝ
  helicityScale_pos : 0 < helicityScale
  quantization_law : |totalHelicity state| = helicityScale * (twoK : ℝ)

/-- Constructive inhabitant for `QuantizedSDiffHelicityHypothesis` (satisfies Gate 2.5 / T17). -/
def defaultQuantizedSDiffHelicityHypothesis : QuantizedSDiffHelicityHypothesis where
  state := ⟨⟨0, 0, 1⟩, ⟨0, 0, 1⟩⟩
  twoK := 1
  parity := .positive
  helicityScale := 1
  helicityScale_pos := by norm_num
  quantization_law := by
    simp [totalHelicity, helicityDensity, _root_.ChiralVector3.dot]

/-- Constructive unit `LocalSDiffIsometry` witness (satisfies Gate 2.5 / T17). -/
def idLocalSDiffIsometry : LocalSDiffIsometry where
  toFun := id
  h_dot := fun _ _ => rfl

/-- Project a quantized `SDiff` helicity hypothesis to a `RotationalBandhead`. -/
def QuantizedSDiffHelicityHypothesis.toBandhead
    (h : QuantizedSDiffHelicityHypothesis) : RotationalBandhead :=
  ⟨h.twoK, h.parity⟩

/-- Transport a `QuantizedSDiffHelicityHypothesis` along a `LocalSDiffIsometry` coadjoint flow. -/
def QuantizedSDiffHelicityHypothesis.transport
    (h : QuantizedSDiffHelicityHypothesis) (R : LocalSDiffIsometry) :
    QuantizedSDiffHelicityHypothesis where
  state := coadjointFlow R h.state
  twoK := h.twoK
  parity := h.parity
  helicityScale := h.helicityScale
  helicityScale_pos := h.helicityScale_pos
  quantization_law := by
    rw [helicity_is_generalized_casimir R h.state]
    exact h.quantization_law

/-- `SDiff` coadjoint flow preserves `totalHelicity`, `sdiffHelicitySignParity`, Beltrami helicity,
and quantized `twoK` bandheads. -/
theorem sdiff_helicity_coadjoint_and_sign_parity_invariant
    (R : LocalSDiffIsometry) (s : FluidState)
    (h_smul : ∀ (c : ℝ) (v : _root_.ChiralVector3), R.toFun (c • v) = c • R.toFun v)
    (lambda_param : ℝ) (u omega : _root_.ChiralVector3)
    (hq : QuantizedSDiffHelicityHypothesis) :
    IsGeneralizedCasimir totalHelicity coadjointFlow ∧
    (sdiffHelicitySignParity (coadjointFlow R s) = sdiffHelicitySignParity s) ∧
    (helicityDensity (R.toFun u) (R.toFun (lambda_param • u)) =
      helicityDensity u (lambda_param • u)) ∧
    (totalHelicity (coadjointFlow R s) = totalHelicity s ∧
      helicityDensity (R.toFun u) (R.toFun omega) = helicityDensity u omega) ∧
    ((hq.transport R).toBandhead = hq.toBandhead) := by
  refine ⟨helicity_is_generalized_casimir, ?_,
    beltrami_helicity_coadjoint_invariant R h_smul lambda_param u, ?_, rfl⟩
  · unfold sdiffHelicitySignParity
    rw [helicity_is_generalized_casimir R s]
  · have hcert := certified_sdiff_coadjoint_helicity_synthesis R u omega s
    exact ⟨hcert.2.2.2.2, hcert.2.2.2.1⟩

/-- Separation theorem: continuous `totalHelicity : FluidState → ℝ` is strictly finer than
discrete `sdiffHelicitySignParity` — distinct helicity values `1 ≠ 2` share `.positive` parity,
justifying why `QuantizedSDiffHelicityHypothesis` is required to assign `twoK : ℕ`. -/
theorem sdiff_continuous_vs_discrete_twoK_separation :
    ∃ s₁ s₂ : FluidState,
      totalHelicity s₁ = 1 ∧
      totalHelicity s₂ = 2 ∧
      totalHelicity s₁ ≠ totalHelicity s₂ ∧
      sdiffHelicitySignParity s₁ = sdiffHelicitySignParity s₂ := by
  refine ⟨⟨⟨0, 0, 1⟩, ⟨0, 0, 1⟩⟩, ⟨⟨0, 0, 2⟩, ⟨0, 0, 1⟩⟩, ?_, ?_, ?_, ?_⟩
  · norm_num [totalHelicity, helicityDensity, _root_.ChiralVector3.dot]
  · norm_num [totalHelicity, helicityDensity, _root_.ChiralVector3.dot]
  · norm_num [totalHelicity, helicityDensity, _root_.ChiralVector3.dot]
  · unfold sdiffHelicitySignParity
    norm_num [totalHelicity, helicityDensity, _root_.ChiralVector3.dot]

/-! ## Section 4: Composite Seam C Bridge Packet, Four-Parity Factorization, & Multipoles -/

/-- Typed composite bridge packet (`Type`, NOT `Prop`) soldering massless spinor helicity,
spin-1/2 circular helicity, Pauli–Lubanski paravector, quantized `SDiff` helicity, rotational
bandhead, and nuclear taxonomy packet without collapsing distinct carriers. -/
structure HelicityToNuclearKPacket where
  spinHalfBranch : SpinHalfHelicityBranch
  masslessBranch : MasslessHelicityBranch
  momentum : PauliParavector
  sdiffQuantized : QuantizedSDiffHelicityHypothesis
  sdiffIsometry : LocalSDiffIsometry
  bandhead : RotationalBandhead
  sector : SpinParitySector
  qnum : QuantumNumbers
  twoOmega : ℕ
  wmSector : WittenMoebiusSector
  chitureSector : MengChitureSector
  spinPairing : SpinPairingLabel
  isospinPairing : IsospinPairingLabel
  bandhead_twoK_eq : bandhead.twoK = sdiffQuantized.twoK
  bandhead_parity_eq : bandhead.parity = sdiffQuantized.parity

/-- Constructive inhabitant for `HelicityToNuclearKPacket` (satisfies Gate 2.5 / T17). -/
def defaultHelicityToNuclearKPacket : HelicityToNuclearKPacket where
  spinHalfBranch := .plusHalf
  masslessBranch := .plusOne
  momentum := northNullMomentum 1
  sdiffQuantized := defaultQuantizedSDiffHelicityHypothesis
  sdiffIsometry := idLocalSDiffIsometry
  bandhead := ⟨1, .positive⟩
  sector := ⟨1, .positive⟩
  qnum := defaultQuantumNumbers
  twoOmega := 1
  wmSector := .wmEven
  chitureSector := .chiEven
  spinPairing := .spinSinglet
  isospinPairing := .isoTriplet
  bandhead_twoK_eq := rfl
  bandhead_parity_eq := rfl

/-- Project a `HelicityToNuclearKPacket` into `NuclearTaxonomyPacket`. -/
def HelicityToNuclearKPacket.toTaxonomyPacket (p : HelicityToNuclearKPacket) :
    NuclearTaxonomyPacket where
  base := p.qnum
  twoK := p.bandhead.twoK
  twoOmega := p.twoOmega
  spatialParitySign := match p.bandhead.parity with | .positive => 1 | .negative => -1
  spatial_parity_sq := by cases p.bandhead.parity <;> norm_num
  wmSector := p.wmSector
  chitureSector := p.chitureSector
  spinPairing := p.spinPairing
  isospinPairing := p.isospinPairing

/-- Signed `KParitySector` induced by `p.spinHalfBranch` (`twoK = ±1 : ℤ`) and `p.bandhead.parity`. -/
def HelicityToNuclearKPacket.toSignedKParitySector (p : HelicityToNuclearKPacket) :
    KParitySector :=
  ⟨p.spinHalfBranch.signedTwoK, p.bandhead.parity⟩

/-- Unsigned-embedded `KParitySector` from `p.bandhead.toKParitySector`. -/
def HelicityToNuclearKPacket.toBandheadKParitySector (p : HelicityToNuclearKPacket) :
    KParitySector :=
  p.bandhead.toKParitySector

/-- Certifies `NuclearTaxonomyPacket` four-parity compatibility (`piOp`, `fermionOp`, `wmOp`,
`mengParityOp` all distinct, `[k0Op, wmOp] ≠ 0`), rotational band staggering & energy symmetry,
Wigner `6_A` multiplet criterion, and `QuantumNumberSymmetry`/`galoisExtendedAction` preservation. -/
theorem helicity_to_nuclear_taxonomy_and_four_parity
    {G : Type*} [GaloisActionData G]
    (p : HelicityToNuclearKPacket) (b : RotationalBandhead) (hb : b.twoK = 0)
    (s f : SpinParitySector) (hs : bandMemberCompatible b s) (hf : bandMemberCompatible b f)
    (sym : QuantumNumberSymmetry) (g : G)
    (x : ArithmeticNuclearState) (hbar 𝓘 I K : ℝ) :
    (isospinCartan * p.toTaxonomyPacket.base.isospinProjection.projector =
      (p.toTaxonomyPacket.base.twoT3 : ℂ) •
        p.toTaxonomyPacket.base.isospinProjection.projector) ∧
    (piOp * p.toTaxonomyPacket.fourParityProj =
      (p.toTaxonomyPacket.spatialParitySign : ℂ) • p.toTaxonomyPacket.fourParityProj ∧
     fermionOp * p.toTaxonomyPacket.fourParityProj =
      (p.toTaxonomyPacket.base.quasiparticleParity : ℂ) • p.toTaxonomyPacket.fourParityProj ∧
     wmOp * p.toTaxonomyPacket.fourParityProj =
      (p.toTaxonomyPacket.wmSector.sign : ℂ) • p.toTaxonomyPacket.fourParityProj ∧
     mengParityOp * p.toTaxonomyPacket.fourParityProj =
      (p.toTaxonomyPacket.chitureSector.sign : ℂ) • p.toTaxonomyPacket.fourParityProj) ∧
    (p.toTaxonomyPacket.fourParityProj * p.toTaxonomyPacket.fourParityProj =
      p.toTaxonomyPacket.fourParityProj ∧ p.toTaxonomyPacket.fourParityProj ≠ 0) ∧
    (k0Op * wmOp ≠ wmOp * k0Op ∧
      piOp ≠ fermionOp ∧ fermionOp ≠ wmOp ∧ wmOp ≠ mengParityOp) ∧
    (k0AlternatingBandAllowed b s ↔
      NuclearTaxonomyPacket.kZeroStaggeringAllowed s.twoJ
        (b.toTaxonomyPacket p.qnum p.twoOmega).spatialParitySign) ∧
    ((⟨b.twoK, s.parity⟩ : KParitySector) = ⟨b.twoK, f.parity⟩) ∧
    (rotational_energy_K hbar 𝓘 I (-K) = rotational_energy_K hbar 𝓘 I K) ∧
    (p.toTaxonomyPacket.inWigner6AMultiplet ↔
      ((p.toTaxonomyPacket.spinPairing = .spinSinglet) ↔
        (p.toTaxonomyPacket.isospinPairing = .isoTriplet))) ∧
    ((sym p.qnum).twoJ = p.qnum.twoJ ∧
      (sym p.qnum).twoT3 = p.qnum.twoT3 ∧
      (sym p.qnum).occupationNumber = p.qnum.occupationNumber ∧
      (sym p.qnum).quasiparticleParity = p.qnum.quasiparticleParity) ∧
    ((galoisExtendedAction g x).1.twoJ = x.1.twoJ ∧
      (galoisExtendedAction g x).1.twoT3 = x.1.twoT3 ∧
      (galoisExtendedAction g x).1.occupationNumber = x.1.occupationNumber ∧
      (galoisExtendedAction g x).1.quasiparticleParity = x.1.quasiparticleParity) := by
  have hcomp := NuclearTaxonomyPacket.isospin_and_fourParity_compatibility p.toTaxonomyPacket
  have hsep := four_parity_separation_and_compatibility
  refine ⟨hcomp.1, hcomp.2.1, hcomp.2.2.1, ⟨hsep.2.2.1.1, hcomp.2.2.2⟩,
    k0Alternating_iff_packet_staggering b hb s p.qnum p.twoOmega hs.2.2,
    bandMembers_share_KParity b s f hs hf,
    rotational_energy_K_even_in_K hbar 𝓘 I K,
    NuclearTaxonomyPacket.inWigner6AMultiplet_iff_ne p.toTaxonomyPacket,
    sym.preservation_packet p.qnum,
    galoisExtendedAction_preservation_packet g x⟩

/-- Selection rules, $K$-forbiddenness, GDR energy, and `E1`/`M1`/`E2` multipole parity
distinction across `NuclearAngularMomentum`, `NuclearRotationalBand`, `NuclearGiantResonance`,
and `NuclearSymmetrySectors`. -/
theorem helicity_selection_rules_and_gdr_multipole_bridge
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    {rep : SU2Rep K V} {k lam : ℕ} {cPlus cMinus : ℤ → K}
    (T : SphericalTensorOperator rep k cPlus cMinus)
    (Tlam : SphericalTensorOperator rep lam cPlus cMinus)
    (bra : V →ₗ[K] K) (ket : V) (Ki Kf q : ℤ)
    (hket : rep.J_zero ket = (Ki : K) • ket)
    (hbra : ∀ v, bra (rep.J_zero v) = (Kf : K) * bra v)
    (hforb : (k : ℤ) < |Kf - Ki|)
    (twoKi twoKf : ℤ)
    (hket2 : rep.J_zero ket = ((twoKi : K) / 2) • ket)
    (hbra2 : ∀ v, bra (rep.J_zero v) = ((twoKf : K) / 2) * bra v)
    (hforb2 : 2 * (lam : ℤ) < |twoKf - twoKi|)
    (j₁ j₂ J : ℕ) (mass_number : ℕ) (pi_val : K)
    (i_e1 f_e1 i_m1 f_m1 i_e2 f_e2 : SpinParitySector)
    (he1 : MultipoleAllowed .electric 1 i_e1 f_e1)
    (hm1 : MultipoleAllowed .magnetic 1 i_m1 f_m1)
    (he2 : MultipoleAllowed .electric 2 i_e2 f_e2) :
    (bra (T.comp q ket) = 0) ∧
    (∀ q' : ℤ, bra (Tlam.comp q' ket) = 0) ∧
    ((j₁ - j₂ ≤ J ∧ j₂ - j₁ ≤ J ∧ J ≤ j₁ + j₂) ↔
      (j₁ ≤ J + j₂ ∧ j₂ ≤ J + j₁ ∧ J ≤ j₁ + j₂)) ∧
    (gdr_energy (𝒦 := ℝ) mass_number = (518 : ℝ) / (10 : ℝ) / (mass_number : ℝ)) ∧
    (e1_selection_rule j₁ J ↔ m1_selection_rule j₁ J) ∧
    (e1_parity_change pi_val (-pi_val) ∧ m1_parity_preserve pi_val pi_val) ∧
    (f_e1.parity ≠ i_e1.parity ∧ f_e1.parity.sign = -i_e1.parity.sign) ∧
    (f_m1.parity = i_m1.parity) ∧
    (f_e2.parity = i_e2.parity) ∧
    ((⟨1, SpatialParity.positive⟩ : KParitySector) ≠ ⟨1, SpatialParity.negative⟩) := by
  refine ⟨rotational_k_forbidden_vanishes T bra ket Ki Kf q hket hbra hforb,
    k_forbidden_transition_vanishes Tlam bra ket twoKi twoKf hket2 hbra2 hforb2,
    angular_momentum_triangle_iff j₁ j₂ J,
    rfl,
    by rfl,
    ⟨e1_parity_change_holds pi_val, m1_parity_preserve_holds pi_val⟩,
    e1_allowed_flips_parity i_e1 f_e1 he1,
    m1_allowed_same_parity i_m1 f_m1 hm1,
    e2_allowed_same_parity i_e2 f_e2 he2,
    KParitySector_sameK_oppositeParity_distinct⟩

/-- Non-vanishing axial `K`-projection selection rule driven directly by
`OperatorZornSpinCasimirLift.spinZ` acting on `SpinSpace 1` via `spinIrrep 1`. -/
theorem operatorZorn_spinZ_k_projection_selection_rule
    {lam : ℕ} {cPlus cMinus : ℤ → ℂ}
    (T : SphericalTensorOperator (spinIrrep 1) lam cPlus cMinus)
    (q : ℤ) (bra : SpinSpace 1 →ₗ[ℂ] ℂ) (ket : SpinSpace 1) (twoKi twoKf : ℤ)
    (hket : Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinZ ket =
      ((twoKi : ℂ) / 2) • ket)
    (hbra : ∀ v, bra (Matrix.toLin' InfoGeometry.Canonical.OperatorZornSpinCasimirLift.spinZ v) =
      ((twoKf : ℂ) / 2) * bra v)
    (hnonzero : bra (T.comp q ket) ≠ 0) :
    twoKf = twoKi + 2 * q ∧ |q| ≤ (lam : ℤ) ∧ |twoKf - twoKi| ≤ 2 * (lam : ℤ) := by
  rw [operatorZorn_spinZ_eq_spinIrrep_J_zero] at hket
  have hbra' : ∀ v, bra ((spinIrrep 1).J_zero v) = ((twoKf : ℂ) / 2) * bra v := by
    intro v
    rw [← operatorZorn_spinZ_eq_spinIrrep_J_zero]
    exact hbra v
  exact k_projection_selection_rule T q bra ket twoKi twoKf hket hbra' hnonzero

/-- Separation theorem between unsigned `RotationalBandhead.twoK : ℕ` and signed
`KParitySector.twoK : ℤ`: opposite helicities share the same unsigned `twoK` magnitude (`2` or `1`)
while remaining strictly distinct in `KParitySector` (`±2` or `±1`). -/
theorem unsigned_bandhead_vs_signed_KParitySector_separation :
    (MasslessHelicityBranch.plusOne.toBandhead.twoK =
      MasslessHelicityBranch.minusOne.toBandhead.twoK) ∧
    (MasslessHelicityBranch.plusOne.toKParitySector.twoK ≠
      MasslessHelicityBranch.minusOne.toKParitySector.twoK) ∧
    (SpinHalfHelicityBranch.plusHalf.unsignedTwoK =
      SpinHalfHelicityBranch.minusHalf.unsignedTwoK) ∧
    (SpinHalfHelicityBranch.plusHalf.signedTwoK ≠
      SpinHalfHelicityBranch.minusHalf.signedTwoK) ∧
    (⟨1, SpatialParity.positive⟩ : KParitySector) ≠ ⟨1, SpatialParity.negative⟩ := by
  refine ⟨rfl, by decide, rfl, by decide, KParitySector_sameK_oppositeParity_distinct⟩

end InfoGeometry.Synthesis.HelicityNuclearKProjectionSynthesis
