import Mathlib.Tactic
import InfoGeometry.Canonical.HodgeDrazinEnvelope
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge

Direct Cantor-to-Clifford owner lane inspired by the Celik--Kocak
Cantor-address construction.

The primary bridge in this file is not Cuntz `O_2`.  It is:

`Cantor addresses -> tilt/switch operators -> Clifford representation`.

Cuntz/IFS branching remains an optional dynamics layer elsewhere.  This module
records the direct finite and infinite Cantor/Clifford representation interfaces and
then exposes the Drazin--Hodge matter envelope consumed by downstream Fierz--Klein
readouts.

The file proves the algebraic consequences carried by the tilt/switch and
envelope fields.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge

open InfoGeometry.Canonical.HodgeDrazinEnvelope

/--
Abstract tilt/switch system.

`T j` is the sign/tilt operator and `S j` is the bit-switch operator.  The
characteristic law is local anticommutation `T_j S_j = - S_j T_j`; different
slots commute.
-/
structure TiltSwitchSystem
    (Op : Type*) [Ring Op] where
  T : ℕ → Op
  S : ℕ → Op

  T_sq :
    ∀ j, T j * T j = 1

  S_sq :
    ∀ j, S j * S j = 1

  T_comm :
    ∀ i j, T i * T j = T j * T i

  S_comm :
    ∀ i j, S i * S j = S j * S i

  T_S_comm_ne :
    ∀ i j, i ≠ j → T i * S j = S j * T i

  T_S_anticomm :
    ∀ j, T j * S j = - (S j * T j)

namespace TiltSwitchSystem

variable {Op : Type*} [Ring Op]
variable (TS : TiltSwitchSystem Op)

/-- The local tilt generator squares to one. -/
theorem local_tilt_sq (j : ℕ) :
    TS.T j * TS.T j = 1 :=
  TS.T_sq j

/-- The local switch generator squares to one. -/
theorem local_switch_sq (j : ℕ) :
    TS.S j * TS.S j = 1 :=
  TS.S_sq j

/-- Tilt and switch anticommute at the same Cantor address slot. -/
theorem local_tilt_switch_anticomm (j : ℕ) :
    TS.T j * TS.S j + TS.S j * TS.T j = 0 := by
  rw [TS.T_S_anticomm j]
  simp

/-- Tilt and switch commute at different Cantor address slots. -/
theorem tilt_switch_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    TS.T i * TS.S j = TS.S j * TS.T i :=
  TS.T_S_comm_ne i j hij

/-- Split-Majorana `c_j = S_j` from a normalized tilt/switch atom. -/
def localMajoranaC (j : ℕ) : Op :=
  TS.S j

/-- Split-Majorana `d_j = S_j T_j` from a normalized tilt/switch atom. -/
def localMajoranaD (j : ℕ) : Op :=
  TS.S j * TS.T j

/-- Local parity `Π_j = c_j d_j`. -/
def localMajoranaParity (j : ℕ) : Op :=
  TS.localMajoranaC j * TS.localMajoranaD j

/-- `c_j² = 1`. -/
theorem localMajoranaC_sq (j : ℕ) :
    TS.localMajoranaC j * TS.localMajoranaC j = 1 :=
  TS.S_sq j

/-- `d_j² = -1`. -/
theorem localMajoranaD_sq (j : ℕ) :
    TS.localMajoranaD j * TS.localMajoranaD j = -1 := by
  unfold localMajoranaD
  calc
    (TS.S j * TS.T j) * (TS.S j * TS.T j)
        = TS.S j * (TS.T j * TS.S j) * TS.T j := by
            noncomm_ring
    _ = TS.S j * (-(TS.S j * TS.T j)) * TS.T j := by
            rw [TS.T_S_anticomm j]
    _ = -((TS.S j * TS.S j) * (TS.T j * TS.T j)) := by
            noncomm_ring
    _ = -(1 * 1) := by
            rw [TS.S_sq j, TS.T_sq j]
    _ = -1 := by simp

/-- `c_j d_j + d_j c_j = 0`. -/
theorem localMajoranaC_D_anticomm (j : ℕ) :
    TS.localMajoranaC j * TS.localMajoranaD j +
      TS.localMajoranaD j * TS.localMajoranaC j = 0 := by
  unfold localMajoranaC localMajoranaD
  rw [← mul_assoc, TS.S_sq j]
  rw [one_mul]
  rw [mul_assoc]
  rw [TS.T_S_anticomm j]
  rw [mul_neg]
  rw [← mul_assoc, TS.S_sq j]
  simp

/-- `d_j c_j + c_j d_j = 0`. -/
theorem localMajoranaD_C_anticomm (j : ℕ) :
    TS.localMajoranaD j * TS.localMajoranaC j +
      TS.localMajoranaC j * TS.localMajoranaD j = 0 := by
  rw [add_comm]
  exact TS.localMajoranaC_D_anticomm j

theorem localMajoranaC_conjugate_tilt (j : ℕ) :
    TS.localMajoranaC j * TS.T j * TS.localMajoranaC j = -TS.T j := by
  unfold localMajoranaC
  calc
    TS.S j * TS.T j * TS.S j = TS.S j * (TS.T j * TS.S j) := by
      noncomm_ring
    _ = TS.S j * (-(TS.S j * TS.T j)) := by
      rw [TS.T_S_anticomm j]
    _ = -(TS.S j * TS.S j) * TS.T j := by
      noncomm_ring
    _ = -TS.T j := by rw [TS.S_sq j]; simp

theorem localMajoranaC_conjugate_D (j : ℕ) :
    TS.localMajoranaC j * TS.localMajoranaD j * TS.localMajoranaC j =
      -TS.localMajoranaD j := by
  unfold localMajoranaC localMajoranaD
  calc
    TS.S j * (TS.S j * TS.T j) * TS.S j =
        (TS.S j * TS.S j) * TS.T j * TS.S j := by noncomm_ring
    _ = TS.T j * TS.S j := by rw [TS.S_sq j]; simp
    _ = -(TS.S j * TS.T j) := by exact TS.T_S_anticomm j

theorem localMajoranaD_conjugate_C (j : ℕ) :
    TS.localMajoranaD j * TS.localMajoranaC j * TS.localMajoranaD j =
      TS.localMajoranaC j := by
  have hDC :
      TS.localMajoranaD j * TS.localMajoranaC j =
        -(TS.localMajoranaC j * TS.localMajoranaD j) :=
    eq_neg_of_add_eq_zero_right (TS.localMajoranaC_D_anticomm j)
  calc
    TS.localMajoranaD j * TS.localMajoranaC j * TS.localMajoranaD j =
        -(TS.localMajoranaC j * TS.localMajoranaD j) *
          TS.localMajoranaD j := by rw [hDC]
    _ = -(TS.localMajoranaC j *
          (TS.localMajoranaD j * TS.localMajoranaD j)) := by
          noncomm_ring
    _ = TS.localMajoranaC j := by
          rw [TS.localMajoranaD_sq]
          simp

theorem localMajoranaC_C_comm (i j : ℕ) :
    TS.localMajoranaC i * TS.localMajoranaC j =
      TS.localMajoranaC j * TS.localMajoranaC i := by
  unfold localMajoranaC
  exact TS.S_comm i j

theorem localMajoranaD_D_comm_of_ne
    {i j : ℕ} (hij : i ≠ j) :
    TS.localMajoranaD i * TS.localMajoranaD j =
      TS.localMajoranaD j * TS.localMajoranaD i := by
  unfold localMajoranaD
  have hTiSj : TS.T i * TS.S j = TS.S j * TS.T i :=
    TS.T_S_comm_ne i j hij
  have hTjSi : TS.T j * TS.S i = TS.S i * TS.T j :=
    TS.T_S_comm_ne j i (Ne.symm hij)
  have hTiTj : TS.T i * TS.T j = TS.T j * TS.T i :=
    TS.T_comm i j
  have hSiSj : TS.S i * TS.S j = TS.S j * TS.S i :=
    TS.S_comm i j
  calc
    (TS.S i * TS.T i) * (TS.S j * TS.T j) =
        TS.S i * TS.S j * TS.T i * TS.T j := by
      calc
        (TS.S i * TS.T i) * (TS.S j * TS.T j) =
            TS.S i * (TS.T i * TS.S j) * TS.T j := by noncomm_ring
        _ = TS.S i * (TS.S j * TS.T i) * TS.T j := by rw [hTiSj]
        _ = TS.S i * TS.S j * TS.T i * TS.T j := by noncomm_ring
    _ = (TS.S i * TS.S j) * (TS.T i * TS.T j) := by noncomm_ring
    _ = (TS.S j * TS.S i) * (TS.T j * TS.T i) := by
      rw [hSiSj, hTiTj]
    _ = TS.S j * TS.S i * TS.T j * TS.T i := by noncomm_ring
    _ = TS.S j * (TS.S i * TS.T j) * TS.T i := by noncomm_ring
    _ = TS.S j * (TS.T j * TS.S i) * TS.T i := by
      rw [← hTjSi]
    _ = (TS.S j * TS.T j) * (TS.S i * TS.T i) := by noncomm_ring

theorem localMajoranaC_D_comm_of_ne
    {i j : ℕ} (hij : i ≠ j) :
    TS.localMajoranaC i * TS.localMajoranaD j =
      TS.localMajoranaD j * TS.localMajoranaC i := by
  unfold localMajoranaC localMajoranaD
  have hSiTj : TS.S i * TS.T j = TS.T j * TS.S i :=
    (TS.T_S_comm_ne j i (Ne.symm hij)).symm
  have hSiSj : TS.S i * TS.S j = TS.S j * TS.S i :=
    TS.S_comm i j
  calc
    TS.S i * (TS.S j * TS.T j) =
        TS.S i * TS.S j * TS.T j := by noncomm_ring
    _ = TS.S j * TS.S i * TS.T j := by rw [hSiSj]
    _ = TS.S j * (TS.S i * TS.T j) := by noncomm_ring
    _ = TS.S j * (TS.T j * TS.S i) := by rw [← hSiTj]
    _ = (TS.S j * TS.T j) * TS.S i := by noncomm_ring

theorem localMajoranaD_C_comm_of_ne
    {i j : ℕ} (hij : i ≠ j) :
    TS.localMajoranaD i * TS.localMajoranaC j =
      TS.localMajoranaC j * TS.localMajoranaD i := by
  exact (TS.localMajoranaC_D_comm_of_ne (Ne.symm hij)).symm

/-- The local split-Majorana parity is the normalized tilt operator. -/
theorem localMajoranaParity_eq_tilt (j : ℕ) :
    TS.localMajoranaParity j = TS.T j := by
  unfold localMajoranaParity localMajoranaC localMajoranaD
  rw [← mul_assoc, TS.S_sq j]
  simp

section StarReadbacks

variable {OpS : Type*} [Ring OpS] [StarRing OpS]
variable (TSS : TiltSwitchSystem OpS)

/--
If the local switch is star-fixed, then the split-Majorana generator
`c_j = S_j` is self-adjoint.
-/
theorem localMajoranaC_star_eq_self_of_switch_star
    (j : ℕ)
    (hS : star (TSS.S j) = TSS.S j) :
    star (TSS.localMajoranaC j) = TSS.localMajoranaC j := by
  simpa [localMajoranaC] using hS

/--
If the local tilt and switch are star-fixed, then the split-Majorana generator
`d_j = S_j T_j` is skew-adjoint.  This is the honest split-real status before
multiplication by a skew phase axis.
-/
theorem localMajoranaD_star_eq_neg_of_tilt_switch_star
    (j : ℕ)
    (hT : star (TSS.T j) = TSS.T j)
    (hS : star (TSS.S j) = TSS.S j) :
    star (TSS.localMajoranaD j) = -TSS.localMajoranaD j := by
  unfold localMajoranaD
  calc
    star (TSS.S j * TSS.T j)
        = star (TSS.T j) * star (TSS.S j) := by
          rw [star_mul]
    _ = TSS.T j * TSS.S j := by
          rw [hT, hS]
    _ = -(TSS.S j * TSS.T j) := by
          exact TSS.T_S_anticomm j

/--
A skew phase axis times the skew split-Majorana `d_j` is self-adjoint, provided
the phase axis commutes with `d_j`.
-/
theorem phaseAxis_mul_localMajoranaD_star_eq_self_of_tilt_switch_star
    (J : OpS)
    (j : ℕ)
    (hJ : star J = -J)
    (hComm : TSS.localMajoranaD j * J = J * TSS.localMajoranaD j)
    (hT : star (TSS.T j) = TSS.T j)
    (hS : star (TSS.S j) = TSS.S j) :
    star (J * TSS.localMajoranaD j) = J * TSS.localMajoranaD j := by
  calc
    star (J * TSS.localMajoranaD j)
        = star (TSS.localMajoranaD j) * star J := by
          rw [star_mul]
    _ = (-TSS.localMajoranaD j) * (-J) := by
          rw [TSS.localMajoranaD_star_eq_neg_of_tilt_switch_star j hT hS, hJ]
    _ = TSS.localMajoranaD j * J := by
          simp
    _ = J * TSS.localMajoranaD j := hComm

end StarReadbacks

/-- Twice the CAR creation/nilpotent generator: `2 ε_j = c_j + d_j`. -/
def localCARCreationTwice (j : ℕ) : Op :=
  TS.localMajoranaC j + TS.localMajoranaD j

/-- Twice the CAR annihilation/nilpotent generator: `2 ι_j = c_j - d_j`. -/
def localCARAnnihilationTwice (j : ℕ) : Op :=
  TS.localMajoranaC j - TS.localMajoranaD j

/--
The reconstructed creation generator is square-zero, up to the harmless factor
`2`: `(2 ε_j)^2 = 0`.
-/
theorem localCARCreationTwice_sq (j : ℕ) :
    TS.localCARCreationTwice j * TS.localCARCreationTwice j = 0 := by
  let c : Op := TS.localMajoranaC j
  let d : Op := TS.localMajoranaD j
  have hc : c * c = 1 := by
    dsimp [c]
    exact TS.localMajoranaC_sq j
  have hd : d * d = -1 := by
    dsimp [d]
    exact TS.localMajoranaD_sq j
  have hcd : c * d + d * c = 0 := by
    dsimp [c, d]
    exact TS.localMajoranaC_D_anticomm j
  change (c + d) * (c + d) = 0
  calc
    (c + d) * (c + d)
        = c * c + (c * d + d * c) + d * d := by
            noncomm_ring
    _ = 1 + 0 + (-1 : Op) := by
            rw [hc, hcd, hd]
    _ = 0 := by
            simp

/--
The reconstructed annihilation generator is square-zero, up to the harmless
factor `2`: `(2 ι_j)^2 = 0`.
-/
theorem localCARAnnihilationTwice_sq (j : ℕ) :
    TS.localCARAnnihilationTwice j * TS.localCARAnnihilationTwice j = 0 := by
  let c : Op := TS.localMajoranaC j
  let d : Op := TS.localMajoranaD j
  have hc : c * c = 1 := by
    dsimp [c]
    exact TS.localMajoranaC_sq j
  have hd : d * d = -1 := by
    dsimp [d]
    exact TS.localMajoranaD_sq j
  have hcd : c * d + d * c = 0 := by
    dsimp [c, d]
    exact TS.localMajoranaC_D_anticomm j
  change (c - d) * (c - d) = 0
  calc
    (c - d) * (c - d)
        = c * c - (c * d + d * c) + d * d := by
            noncomm_ring
    _ = 1 - 0 + (-1 : Op) := by
            rw [hc, hcd, hd]
    _ = 0 := by
            simp

/--
The unnormalized CAR anticommutator:

`(2ι_j)(2ε_j) + (2ε_j)(2ι_j) = 4`.

After adjoining `1/2`, this is exactly `{ι_j, ε_j} = 1`.
-/
theorem localCARTwice_anticomm (j : ℕ) :
    TS.localCARAnnihilationTwice j * TS.localCARCreationTwice j +
      TS.localCARCreationTwice j * TS.localCARAnnihilationTwice j =
        (4 : Op) := by
  let c : Op := TS.localMajoranaC j
  let d : Op := TS.localMajoranaD j
  have hc : c * c = 1 := by
    dsimp [c]
    exact TS.localMajoranaC_sq j
  have hd : d * d = -1 := by
    dsimp [d]
    exact TS.localMajoranaD_sq j
  change (c - d) * (c + d) + (c + d) * (c - d) = (4 : Op)
  calc
    (c - d) * (c + d) + (c + d) * (c - d)
        = (c * c - d * d) + (c * c - d * d) := by
            noncomm_ring
    _ = (1 - (-1 : Op)) + (1 - (-1 : Op)) := by
            rw [hc, hd]
    _ = (4 : Op) := by
            norm_num

/-- Raw exterior-creation nilpotent: `ε_raw = c + d`. -/
def localExteriorCreateRaw (j : ℕ) : Op :=
  TS.localCARCreationTwice j

/-- Raw exterior-contraction nilpotent: `ι_raw = c - d`. -/
def localExteriorContractRaw (j : ℕ) : Op :=
  TS.localCARAnnihilationTwice j

/-- The raw exterior-creation operator squares to zero. -/
theorem localExteriorCreateRaw_sq_zero (j : ℕ) :
    TS.localExteriorCreateRaw j * TS.localExteriorCreateRaw j = 0 := by
  simpa [localExteriorCreateRaw] using TS.localCARCreationTwice_sq j

/-- The raw exterior-contraction operator squares to zero. -/
theorem localExteriorContractRaw_sq_zero (j : ℕ) :
    TS.localExteriorContractRaw j * TS.localExteriorContractRaw j = 0 := by
  simpa [localExteriorContractRaw] using TS.localCARAnnihilationTwice_sq j

/-- Raw CAR normalization: `(c - d)(c + d) + (c + d)(c - d) = 4`. -/
theorem localExteriorContractRaw_mul_createRaw_add_createRaw_mul_contractRaw
    (j : ℕ) :
    TS.localExteriorContractRaw j * TS.localExteriorCreateRaw j +
      TS.localExteriorCreateRaw j * TS.localExteriorContractRaw j = 4 := by
  simpa [localExteriorContractRaw, localExteriorCreateRaw] using TS.localCARTwice_anticomm j

/-- Raw product `ε_raw ι_raw = 2 - 2Π`. -/
theorem localExteriorCreateRaw_mul_contractRaw_eq_two_sub_two_parity
    (j : ℕ) :
    TS.localExteriorCreateRaw j * TS.localExteriorContractRaw j =
      2 - 2 * TS.localMajoranaParity j := by
  unfold localExteriorCreateRaw localExteriorContractRaw
  unfold localCARCreationTwice localCARAnnihilationTwice localMajoranaParity
  calc
    (TS.localMajoranaC j + TS.localMajoranaD j) *
        (TS.localMajoranaC j - TS.localMajoranaD j)
        = TS.localMajoranaC j * TS.localMajoranaC j -
            (TS.localMajoranaC j * TS.localMajoranaD j) +
            TS.localMajoranaD j * TS.localMajoranaC j -
            TS.localMajoranaD j * TS.localMajoranaD j := by
          noncomm_ring
    _ = 1 - TS.localMajoranaC j * TS.localMajoranaD j +
            TS.localMajoranaD j * TS.localMajoranaC j - (-1) := by
          rw [TS.localMajoranaC_sq j, TS.localMajoranaD_sq j]
    _ = 2 - 2 * (TS.localMajoranaC j * TS.localMajoranaD j) := by
          have hdc : TS.localMajoranaD j * TS.localMajoranaC j =
              -(TS.localMajoranaC j * TS.localMajoranaD j) := by
            have hanti := TS.localMajoranaC_D_anticomm j
            have h := congrArg (fun x => x - TS.localMajoranaC j * TS.localMajoranaD j) hanti
            simpa using h
          rw [hdc]
          calc
            1 - TS.localMajoranaC j * TS.localMajoranaD j +
                (-(TS.localMajoranaC j * TS.localMajoranaD j)) - (-1 : Op)
                = (1 + 1 : Op) -
                    (TS.localMajoranaC j * TS.localMajoranaD j +
                      TS.localMajoranaC j * TS.localMajoranaD j) := by
                    abel_nf
            _ = 2 - 2 * (TS.localMajoranaC j * TS.localMajoranaD j) := by
                    rw [← two_mul (TS.localMajoranaC j * TS.localMajoranaD j)]
                    norm_num

/-- Raw product `ι_raw ε_raw = 2 + 2Π`. -/
theorem localExteriorContractRaw_mul_createRaw_eq_two_add_two_parity
    (j : ℕ) :
    TS.localExteriorContractRaw j * TS.localExteriorCreateRaw j =
      2 + 2 * TS.localMajoranaParity j := by
  have hsum := TS.localExteriorContractRaw_mul_createRaw_add_createRaw_mul_contractRaw j
  have hcreate := TS.localExteriorCreateRaw_mul_contractRaw_eq_two_sub_two_parity j
  calc
    TS.localExteriorContractRaw j * TS.localExteriorCreateRaw j
        = 4 - TS.localExteriorCreateRaw j * TS.localExteriorContractRaw j := by
          have h := congrArg
            (fun x => x - TS.localExteriorCreateRaw j * TS.localExteriorContractRaw j) hsum
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    _ = 4 - (2 - 2 * TS.localMajoranaParity j) := by rw [hcreate]
    _ = 2 + 2 * TS.localMajoranaParity j := by
          calc
            4 - (2 - 2 * TS.localMajoranaParity j)
                = (4 - 2) + 2 * TS.localMajoranaParity j := by
                    abel_nf
            _ = 2 + 2 * TS.localMajoranaParity j := by
                    norm_num

/-- Normalized exterior creation with an explicitly supplied half scalar. -/
def localExteriorCreateWith (half : Op) (j : ℕ) : Op :=
  half * TS.localExteriorCreateRaw j

/-- Normalized exterior contraction with an explicitly supplied half scalar. -/
def localExteriorContractWith (half : Op) (j : ℕ) : Op :=
  half * TS.localExteriorContractRaw j

/-- If `half` commutes with `ε_raw`, then normalized creation is square-zero. -/
theorem localExteriorCreateWith_sq_zero
    (half : Op) (j : ℕ)
    (hcomm : TS.localExteriorCreateRaw j * half = half * TS.localExteriorCreateRaw j) :
    TS.localExteriorCreateWith half j * TS.localExteriorCreateWith half j = 0 := by
  unfold localExteriorCreateWith
  calc
    (half * TS.localExteriorCreateRaw j) *
        (half * TS.localExteriorCreateRaw j)
        = half * (TS.localExteriorCreateRaw j * half) * TS.localExteriorCreateRaw j := by
          noncomm_ring
    _ = half * (half * TS.localExteriorCreateRaw j) * TS.localExteriorCreateRaw j := by
          rw [hcomm]
    _ = half * half *
          (TS.localExteriorCreateRaw j * TS.localExteriorCreateRaw j) := by
          noncomm_ring
    _ = half * half * 0 := by rw [TS.localExteriorCreateRaw_sq_zero j]
    _ = 0 := by simp

/-- If `half` commutes with `ι_raw`, then normalized contraction is square-zero. -/
theorem localExteriorContractWith_sq_zero
    (half : Op) (j : ℕ)
    (hcomm : TS.localExteriorContractRaw j * half = half * TS.localExteriorContractRaw j) :
    TS.localExteriorContractWith half j * TS.localExteriorContractWith half j = 0 := by
  unfold localExteriorContractWith
  calc
    (half * TS.localExteriorContractRaw j) *
        (half * TS.localExteriorContractRaw j)
        = half * (TS.localExteriorContractRaw j * half) * TS.localExteriorContractRaw j := by
          noncomm_ring
    _ = half * (half * TS.localExteriorContractRaw j) * TS.localExteriorContractRaw j := by
          rw [hcomm]
    _ = half * half *
          (TS.localExteriorContractRaw j * TS.localExteriorContractRaw j) := by
          noncomm_ring
    _ = half * half * 0 := by rw [TS.localExteriorContractRaw_sq_zero j]
    _ = 0 := by simp

/-- Normalized CAR from an explicit half scalar: `ι ε + ε ι = 1`. -/
theorem localExteriorContractWith_mul_createWith_add_createWith_mul_contractWith
    (half : Op) (j : ℕ)
    (hcommCreate : TS.localExteriorCreateRaw j * half = half * TS.localExteriorCreateRaw j)
    (hcommContract : TS.localExteriorContractRaw j * half = half * TS.localExteriorContractRaw j)
    (hhalf : half * half * 4 = 1) :
    TS.localExteriorContractWith half j * TS.localExteriorCreateWith half j +
      TS.localExteriorCreateWith half j * TS.localExteriorContractWith half j = 1 := by
  unfold localExteriorCreateWith localExteriorContractWith
  calc
    (half * TS.localExteriorContractRaw j) *
          (half * TS.localExteriorCreateRaw j) +
        (half * TS.localExteriorCreateRaw j) *
          (half * TS.localExteriorContractRaw j)
        = half * (TS.localExteriorContractRaw j * half) * TS.localExteriorCreateRaw j +
          half * (TS.localExteriorCreateRaw j * half) * TS.localExteriorContractRaw j := by
          noncomm_ring
    _ = half * (half * TS.localExteriorContractRaw j) * TS.localExteriorCreateRaw j +
          half * (half * TS.localExteriorCreateRaw j) * TS.localExteriorContractRaw j := by
          rw [hcommContract, hcommCreate]
    _ = half * half *
          (TS.localExteriorContractRaw j * TS.localExteriorCreateRaw j +
            TS.localExteriorCreateRaw j * TS.localExteriorContractRaw j) := by
          noncomm_ring
    _ = half * half * 4 := by
          rw [TS.localExteriorContractRaw_mul_createRaw_add_createRaw_mul_contractRaw j]
    _ = 1 := by exact hhalf

/--
Explicit normalized CAR corollary with local names `ε, ι`:
`ι * ε + ε * ι = 1`.
-/
theorem localExteriorWith_anticomm_eq_one
    (half : Op) (j : ℕ)
    (hcommCreate : TS.localExteriorCreateRaw j * half = half * TS.localExteriorCreateRaw j)
    (hcommContract : TS.localExteriorContractRaw j * half = half * TS.localExteriorContractRaw j)
    (hhalf : half * half * 4 = 1) :
    let ε := TS.localExteriorCreateWith half j
    let ι := TS.localExteriorContractWith half j
    ι * ε + ε * ι = 1 := by
  simpa using
    (TS.localExteriorContractWith_mul_createWith_add_createWith_mul_contractWith
      half j hcommCreate hcommContract hhalf)

/-- Explicit local split-Majorana product readout: `c_j d_j = T_j`. -/
theorem localMajoranaC_mul_D_eq_tilt (j : ℕ) :
    TS.localMajoranaC j * TS.localMajoranaD j = TS.T j := by
  simpa [localMajoranaParity] using TS.localMajoranaParity_eq_tilt j

/-- Local parity squares to one. -/
theorem localMajoranaParity_sq (j : ℕ) :
    TS.localMajoranaParity j * TS.localMajoranaParity j = 1 := by
  rw [TS.localMajoranaParity_eq_tilt]
  exact TS.T_sq j

/--
Unscaled exterior creation operator recovered from the local split-Majorana
generators:

`ε̃_j = c_j + d_j`.

The normalized CAR creation is `(1/2) ε̃_j` when `2` is invertible.
-/
def localCreationUnscaled (j : ℕ) : Op :=
  TS.localMajoranaC j + TS.localMajoranaD j

/--
Unscaled contraction/annihilation operator recovered from the local split-Majorana
generators:

`ι̃_j = c_j - d_j`.

The normalized CAR contraction is `(1/2) ι̃_j` when `2` is invertible.
-/
def localAnnihilationUnscaled (j : ℕ) : Op :=
  TS.localMajoranaC j - TS.localMajoranaD j

theorem localCreationUnscaled_eq_localExteriorCreateRaw (j : ℕ) :
    TS.localCreationUnscaled j = TS.localExteriorCreateRaw j := by
  rfl

theorem localAnnihilationUnscaled_eq_localExteriorContractRaw (j : ℕ) :
    TS.localAnnihilationUnscaled j = TS.localExteriorContractRaw j := by
  rfl

/-- The recovered unscaled creation operator squares to zero. -/
theorem localCreationUnscaled_sq_zero (j : ℕ) :
    TS.localCreationUnscaled j * TS.localCreationUnscaled j = 0 := by
  unfold localCreationUnscaled
  calc
    (TS.localMajoranaC j + TS.localMajoranaD j) *
        (TS.localMajoranaC j + TS.localMajoranaD j)
        =
      TS.localMajoranaC j * TS.localMajoranaC j
        + (TS.localMajoranaC j * TS.localMajoranaD j
            + TS.localMajoranaD j * TS.localMajoranaC j)
        + TS.localMajoranaD j * TS.localMajoranaD j := by
          noncomm_ring
    _ = 1 + 0 + (-1 : Op) := by
          rw [TS.localMajoranaC_sq j,
            TS.localMajoranaC_D_anticomm j,
            TS.localMajoranaD_sq j]
    _ = 0 := by
          simp

/-- The recovered unscaled annihilation/contraction operator squares to zero. -/
theorem localAnnihilationUnscaled_sq_zero (j : ℕ) :
    TS.localAnnihilationUnscaled j * TS.localAnnihilationUnscaled j = 0 := by
  unfold localAnnihilationUnscaled
  calc
    (TS.localMajoranaC j - TS.localMajoranaD j) *
        (TS.localMajoranaC j - TS.localMajoranaD j)
        =
      TS.localMajoranaC j * TS.localMajoranaC j
        - (TS.localMajoranaC j * TS.localMajoranaD j
            + TS.localMajoranaD j * TS.localMajoranaC j)
        + TS.localMajoranaD j * TS.localMajoranaD j := by
          noncomm_ring
    _ = 1 - 0 + (-1 : Op) := by
          rw [TS.localMajoranaC_sq j,
            TS.localMajoranaC_D_anticomm j,
            TS.localMajoranaD_sq j]
    _ = 0 := by
          simp

/--
The unscaled CAR anticommutator is `4`.

After normalization by `1/2`, this becomes `{ι_j, ε_j} = 1`.
-/
theorem localAnnihilation_creation_anticomm_unscaled (j : ℕ) :
    TS.localAnnihilationUnscaled j * TS.localCreationUnscaled j
      + TS.localCreationUnscaled j * TS.localAnnihilationUnscaled j
        = (4 : Op) := by
  unfold localAnnihilationUnscaled localCreationUnscaled
  calc
    (TS.localMajoranaC j - TS.localMajoranaD j) *
        (TS.localMajoranaC j + TS.localMajoranaD j)
      + (TS.localMajoranaC j + TS.localMajoranaD j) *
        (TS.localMajoranaC j - TS.localMajoranaD j)
        =
      (TS.localMajoranaC j * TS.localMajoranaC j
        + TS.localMajoranaC j * TS.localMajoranaC j)
        - (TS.localMajoranaD j * TS.localMajoranaD j
        + TS.localMajoranaD j * TS.localMajoranaD j) := by
          noncomm_ring
    _ = (1 + 1 : Op) - ((-1 : Op) + (-1 : Op)) := by
          rw [TS.localMajoranaC_sq j, TS.localMajoranaD_sq j]
    _ = (4 : Op) := by
          norm_num

section CommCARReconstruction

variable {OpC : Type*} [CommRing OpC]
variable (TSC : TiltSwitchSystem OpC)

/-- CAR reconstruction: `ε_j = (c_j + d_j)/2`. -/
def localEpsilon [Invertible (2 : OpC)] (j : ℕ) : OpC :=
  ⅟ (2 : OpC) * (TSC.localMajoranaC j + TSC.localMajoranaD j)

/-- CAR reconstruction: `ι_j = (c_j - d_j)/2`. -/
def localIota [Invertible (2 : OpC)] (j : ℕ) : OpC :=
  ⅟ (2 : OpC) * (TSC.localMajoranaC j - TSC.localMajoranaD j)

/-- Reconstructed CAR creator is square-zero. -/
theorem localEpsilon_sq [Invertible (2 : OpC)] (j : ℕ) :
    TSC.localEpsilon j * TSC.localEpsilon j = 0 := by
  unfold localEpsilon
  have hsum_sq : (TSC.localMajoranaC j + TSC.localMajoranaD j) ^ 2 = 0 := by
    calc
      (TSC.localMajoranaC j + TSC.localMajoranaD j) ^ 2
          = TSC.localMajoranaC j * TSC.localMajoranaC j +
              (TSC.localMajoranaC j * TSC.localMajoranaD j +
                TSC.localMajoranaD j * TSC.localMajoranaC j) +
              TSC.localMajoranaD j * TSC.localMajoranaD j := by ring
      _ = 1 + 0 + (-1) := by
            simp [TSC.localMajoranaC_sq j, TSC.localMajoranaC_D_anticomm j, TSC.localMajoranaD_sq j]
      _ = 0 := by ring
  calc
    (⅟ (2 : OpC) * (TSC.localMajoranaC j + TSC.localMajoranaD j)) *
      (⅟ (2 : OpC) * (TSC.localMajoranaC j + TSC.localMajoranaD j))
        = (⅟ (2 : OpC)) ^ 2 * (TSC.localMajoranaC j + TSC.localMajoranaD j) ^ 2 := by ring
    _ = 0 := by simp [hsum_sq]

/-- Reconstructed CAR annihilator is square-zero. -/
theorem localIota_sq [Invertible (2 : OpC)] (j : ℕ) :
    TSC.localIota j * TSC.localIota j = 0 := by
  unfold localIota
  have hdiff_sq : (TSC.localMajoranaC j - TSC.localMajoranaD j) ^ 2 = 0 := by
    calc
      (TSC.localMajoranaC j - TSC.localMajoranaD j) ^ 2
          = TSC.localMajoranaC j * TSC.localMajoranaC j -
              (TSC.localMajoranaC j * TSC.localMajoranaD j +
                TSC.localMajoranaD j * TSC.localMajoranaC j) +
              TSC.localMajoranaD j * TSC.localMajoranaD j := by ring
      _ = 1 - 0 + (-1) := by
            simp [TSC.localMajoranaC_sq j, TSC.localMajoranaC_D_anticomm j, TSC.localMajoranaD_sq j]
      _ = 0 := by ring
  calc
    (⅟ (2 : OpC) * (TSC.localMajoranaC j - TSC.localMajoranaD j)) *
      (⅟ (2 : OpC) * (TSC.localMajoranaC j - TSC.localMajoranaD j))
        = (⅟ (2 : OpC)) ^ 2 * (TSC.localMajoranaC j - TSC.localMajoranaD j) ^ 2 := by ring
    _ = 0 := by simp [hdiff_sq]

/-- Reconstructed CAR anticommutator: `ι_j ε_j + ε_j ι_j = 1`. -/
theorem localIota_localEpsilon_anticomm [Invertible (2 : OpC)] (j : ℕ) :
    TSC.localIota j * TSC.localEpsilon j + TSC.localEpsilon j * TSC.localIota j = 1 := by
  unfold localIota localEpsilon
  have hmix :
      (TSC.localMajoranaC j - TSC.localMajoranaD j) * (TSC.localMajoranaC j + TSC.localMajoranaD j) +
        (TSC.localMajoranaC j + TSC.localMajoranaD j) * (TSC.localMajoranaC j - TSC.localMajoranaD j) = 4 := by
    calc
      (TSC.localMajoranaC j - TSC.localMajoranaD j) * (TSC.localMajoranaC j + TSC.localMajoranaD j) +
          (TSC.localMajoranaC j + TSC.localMajoranaD j) * (TSC.localMajoranaC j - TSC.localMajoranaD j)
          = 2 * (TSC.localMajoranaC j * TSC.localMajoranaC j) -
              2 * (TSC.localMajoranaD j * TSC.localMajoranaD j) := by ring
      _ = 2 * 1 - 2 * (-1) := by simp [TSC.localMajoranaC_sq j, TSC.localMajoranaD_sq j]
      _ = 4 := by ring
  have hfac :
      (⅟ (2 : OpC) * (TSC.localMajoranaC j - TSC.localMajoranaD j)) *
          (⅟ (2 : OpC) * (TSC.localMajoranaC j + TSC.localMajoranaD j)) +
        (⅟ (2 : OpC) * (TSC.localMajoranaC j + TSC.localMajoranaD j)) *
          (⅟ (2 : OpC) * (TSC.localMajoranaC j - TSC.localMajoranaD j)) =
      (⅟ (2 : OpC)) ^ 2 *
        ((TSC.localMajoranaC j - TSC.localMajoranaD j) * (TSC.localMajoranaC j + TSC.localMajoranaD j) +
          (TSC.localMajoranaC j + TSC.localMajoranaD j) * (TSC.localMajoranaC j - TSC.localMajoranaD j)) := by
    ring
  have hhalf : (⅟ (2 : OpC)) * (2 : OpC) = 1 := by
    exact invOf_mul_self (2 : OpC)
  calc
    (⅟ (2 : OpC) * (TSC.localMajoranaC j - TSC.localMajoranaD j)) *
        (⅟ (2 : OpC) * (TSC.localMajoranaC j + TSC.localMajoranaD j)) +
      (⅟ (2 : OpC) * (TSC.localMajoranaC j + TSC.localMajoranaD j)) *
        (⅟ (2 : OpC) * (TSC.localMajoranaC j - TSC.localMajoranaD j))
        = (⅟ (2 : OpC)) ^ 2 * 4 := by
            rw [hfac, hmix]
    _ = 1 := by
          calc
            (⅟ (2 : OpC)) ^ 2 * 4 = ((⅟ (2 : OpC)) * (2 : OpC)) * ((⅟ (2 : OpC)) * (2 : OpC)) := by
              ring
            _ = 1 := by
              simp [hhalf]

/-- CAR number operator reconstructed from `ε_j, ι_j`. -/
def localNumber [Invertible (2 : OpC)] (j : ℕ) : OpC :=
  TSC.localEpsilon j * TSC.localIota j

/-- CAR parity reconstructed from `ε_j, ι_j`: `1 - 2N_j`. -/
def localParityFromCAR [Invertible (2 : OpC)] (j : ℕ) : OpC :=
  1 - (2 : OpC) * TSC.localNumber j

/--
Commutative reconstruction consequence:
the CAR parity readout `1 - 2(ε_j ι_j)` vanishes.
-/
theorem localParityFromCAR_eq_zero [Invertible (2 : OpC)] (j : ℕ) :
    TSC.localParityFromCAR j = 0 := by
  have hcar : TSC.localIota j * TSC.localEpsilon j + TSC.localEpsilon j * TSC.localIota j = 1 :=
    TSC.localIota_localEpsilon_anticomm j
  have hcomm : TSC.localIota j * TSC.localEpsilon j = TSC.localEpsilon j * TSC.localIota j := by
    simp [mul_comm]
  have htwoN : (2 : OpC) * TSC.localNumber j = 1 := by
    unfold localNumber
    calc
      (2 : OpC) * (TSC.localEpsilon j * TSC.localIota j)
          = TSC.localEpsilon j * TSC.localIota j + TSC.localEpsilon j * TSC.localIota j := by ring
      _ = TSC.localIota j * TSC.localEpsilon j + TSC.localEpsilon j * TSC.localIota j := by
            rw [hcomm]
      _ = 1 := hcar
  unfold localParityFromCAR
  rw [htwoN]
  ring

end CommCARReconstruction

end TiltSwitchSystem

/--
A Clifford representation produced from a Cantor tilt/switch system.

`gamma i` is the image of the `i`-th Clifford generator.
-/
structure CantorCliffordRepresentation
    (Op : Type*) [Ring Op] where
  gamma : ℕ → Op

  gamma_sq :
    ∀ i, gamma i * gamma i = 1

  gamma_anticomm :
    ∀ i j, i ≠ j → gamma i * gamma j = - (gamma j * gamma i)

namespace CantorCliffordRepresentation

variable {Op : Type*} [Ring Op]
variable (R : CantorCliffordRepresentation Op)

end CantorCliffordRepresentation

/--
Finite Cantor-Pauli bridge.

For the endpoint set `V_n`, the representation of `Cl_{2n}` on functions
`V_n -> ℂ` is represented by Pauli tensor-product matrices.
-/
def IsFiniteCantorPauliRepresentation
    (n : ℕ)
    (Mat : Type*) [Ring Mat]
    (psiGamma : Fin (2 * n) → Mat) : Prop :=
  (∀ i, psiGamma i * psiGamma i = 1) ∧
    (∀ i j, i ≠ j → psiGamma i * psiGamma j =
      - (psiGamma j * psiGamma i))

theorem finiteCantorPauli_generator_sq
    {n : ℕ} {Mat : Type*} [Ring Mat]
    {psiGamma : Fin (2 * n) → Mat}
    (h : IsFiniteCantorPauliRepresentation n Mat psiGamma)
    (i : Fin (2 * n)) :
    psiGamma i * psiGamma i = 1 :=
  h.1 i

theorem finiteCantorPauli_generator_anticomm
    {n : ℕ} {Mat : Type*} [Ring Mat]
    {psiGamma : Fin (2 * n) → Mat}
    (h : IsFiniteCantorPauliRepresentation n Mat psiGamma)
    {i j : Fin (2 * n)} (hij : i ≠ j) :
    psiGamma i * psiGamma j = -(psiGamma j * psiGamma i) :=
  h.2 i j hij

/-- Drazin support of a signal operator `A`: `p_A = A A^D`. -/
abbrev DrazinHorizon
    (Op : Type*) [Ring Op] [Star Op] :=
  SignalDrazinSupport Op

/-- Drazin-Green harmonic data for a frequency/Laplacian-like operator. -/
abbrev DrazinGreenHarmonic
    (Op : Type*) [Ring Op] [Star Op] :=
  FrequencyDrazinGreen Op

/--
Physical matter envelope:

`x_phys = H_L * (p_A * x * p_A) * H_L`.
-/
def cantorCliffordMatterEnvelope
    {Op : Type*} [Ring Op] [Star Op]
    (D : DrazinHorizon Op)
    (G : DrazinGreenHarmonic Op)
    (x : Op) : Op :=
  G.P_harm * (D.p * x * D.p) * G.P_harm

theorem cantorCliffordMatterEnvelope_zero
    {Op : Type*} [Ring Op] [Star Op]
    (D : DrazinHorizon Op)
    (G : DrazinGreenHarmonic Op) :
    cantorCliffordMatterEnvelope D G 0 = 0 := by
  simp [cantorCliffordMatterEnvelope]

theorem cantorCliffordMatterEnvelope_add
    {Op : Type*} [Ring Op] [Star Op]
    (D : DrazinHorizon Op)
    (G : DrazinGreenHarmonic Op)
    (x y : Op) :
    cantorCliffordMatterEnvelope D G (x + y) =
      cantorCliffordMatterEnvelope D G x +
        cantorCliffordMatterEnvelope D G y := by
  simp [cantorCliffordMatterEnvelope, mul_add, add_mul]

/-- The matter envelope is the existing Hodge-Drazin physical envelope. -/
theorem cantorCliffordMatterEnvelope_eq_physicalEnvelope
    {Op : Type*} [Ring Op] [Star Op]
    (D : DrazinHorizon Op)
    (G : DrazinGreenHarmonic Op)
    (x : Op) :
    cantorCliffordMatterEnvelope D G x =
      HodgeDrazinEnvelope.physicalEnvelope
        { signal := D, frequency := G, x_raw := x } := by
  rfl

/-- Fierz readout happens after Drazin-Hodge envelope extraction. -/
def envelopeFierzCoordinate
    {Op : Type*} [Ring Op] [Star Op]
    (D : DrazinHorizon Op)
    (G : DrazinGreenHarmonic Op)
    (channel : Op → ℝ)
    (x : Op) : ℝ :=
  channel (cantorCliffordMatterEnvelope D G x)

theorem two_generator_sum_sq
    {Op : Type*} [Ring Op]
    (R : CantorCliffordRepresentation Op)
    {i j : ℕ} (hij : i ≠ j) :
    (R.gamma i + R.gamma j) * (R.gamma i + R.gamma j) = 2 := by
  calc
    (R.gamma i + R.gamma j) * (R.gamma i + R.gamma j) =
        R.gamma i * R.gamma i +
          (R.gamma i * R.gamma j + R.gamma j * R.gamma i) +
            R.gamma j * R.gamma j := by
              noncomm_ring
    _ = 2 := by
      rw [R.gamma_sq i, R.gamma_sq j, R.gamma_anticomm i j hij]
      simp
      exact one_add_one_eq_two

end InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
