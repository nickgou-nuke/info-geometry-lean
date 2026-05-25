import Mathlib
import InfoGeometry.Canonical.HodgeDrazinEnvelope
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge

Direct Cantor-to-Clifford owner lane inspired by the Celik--Kocak
Cantor-address construction.

The primary bridge in this file is not Cuntz `O_2`.  It is:

`Cantor addresses -> tilt/switch operators -> Clifford representation`.

Cuntz/IFS branching remains an optional dynamics layer elsewhere.  This module
records the direct finite and infinite Cantor/Clifford representation sockets and
then exposes the Drazin--Hodge matter envelope consumed by downstream Fierz--Klein
readouts.

The file proves the algebraic consequences carried by the tilt/switch and
envelope fields.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge

open InfoGeometry.Canonical.HodgeDrazinEnvelope

/-- Symbolic Cantor space: infinite binary streams. -/
abbrev CantorSpace := ℕ → Bool

/-- Finite binary Cantor address of length `n`. -/
abbrev CantorAddress (n : ℕ) := Fin n → Bool

/-- Function space over the finite Cantor endpoint set `V_n`. -/
abbrev FiniteCantorFunctionSpace (n : ℕ) :=
  CantorAddress n → ℂ

/--
Abstract tilt/switch system.

`T j` is the sign/tilt operator and `S j` is the bit-switch operator.  The
characteristic law is local anticommutation `T_j S_j = - S_j T_j`; different
slots commute.
-/
@[rep_depth operator]
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
@[rep_depth operator]
theorem local_tilt_sq (j : ℕ) :
    TS.T j * TS.T j = 1 :=
  TS.T_sq j

/-- The local switch generator squares to one. -/
@[rep_depth operator]
theorem local_switch_sq (j : ℕ) :
    TS.S j * TS.S j = 1 :=
  TS.S_sq j

/-- Tilt and switch anticommute at the same Cantor address slot. -/
@[rep_depth operator]
theorem local_tilt_switch_anticomm (j : ℕ) :
    TS.T j * TS.S j + TS.S j * TS.T j = 0 := by
  rw [TS.T_S_anticomm j]
  simp

/-- Tilt and switch commute at different Cantor address slots. -/
@[rep_depth operator]
theorem tilt_switch_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    TS.T i * TS.S j = TS.S j * TS.T i :=
  TS.T_S_comm_ne i j hij

/-- Split-Majorana `c_j = S_j` from a normalized tilt/switch atom. -/
@[rep_depth operator]
def localMajoranaC (j : ℕ) : Op :=
  TS.S j

/-- Split-Majorana `d_j = S_j T_j` from a normalized tilt/switch atom. -/
@[rep_depth operator]
def localMajoranaD (j : ℕ) : Op :=
  TS.S j * TS.T j

/-- Local parity `Π_j = c_j d_j`. -/
@[rep_depth operator]
def localMajoranaParity (j : ℕ) : Op :=
  TS.localMajoranaC j * TS.localMajoranaD j

/-- `c_j² = 1`. -/
@[rep_depth operator]
theorem localMajoranaC_sq (j : ℕ) :
    TS.localMajoranaC j * TS.localMajoranaC j = 1 :=
  TS.S_sq j

/-- `d_j² = -1`. -/
@[rep_depth operator]
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
@[rep_depth operator]
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
@[rep_depth operator]
theorem localMajoranaD_C_anticomm (j : ℕ) :
    TS.localMajoranaD j * TS.localMajoranaC j +
      TS.localMajoranaC j * TS.localMajoranaD j = 0 := by
  rw [add_comm]
  exact TS.localMajoranaC_D_anticomm j

/-- The local split-Majorana parity is the normalized tilt operator. -/
@[rep_depth operator]
theorem localMajoranaParity_eq_tilt (j : ℕ) :
    TS.localMajoranaParity j = TS.T j := by
  unfold localMajoranaParity localMajoranaC localMajoranaD
  rw [← mul_assoc, TS.S_sq j]
  simp

/-- Twice the CAR creation/nilpotent generator: `2 ε_j = c_j + d_j`. -/
@[rep_depth operator]
def localCARCreationTwice (j : ℕ) : Op :=
  TS.localMajoranaC j + TS.localMajoranaD j

/-- Twice the CAR annihilation/nilpotent generator: `2 ι_j = c_j - d_j`. -/
@[rep_depth operator]
def localCARAnnihilationTwice (j : ℕ) : Op :=
  TS.localMajoranaC j - TS.localMajoranaD j

/--
The reconstructed creation generator is square-zero, up to the harmless factor
`2`: `(2 ε_j)^2 = 0`.
-/
@[rep_depth operator]
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
@[rep_depth operator]
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
@[rep_depth operator]
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
@[rep_depth operator]
def localExteriorCreateRaw (j : ℕ) : Op :=
  TS.localCARCreationTwice j

/-- Raw exterior-contraction nilpotent: `ι_raw = c - d`. -/
@[rep_depth operator]
def localExteriorContractRaw (j : ℕ) : Op :=
  TS.localCARAnnihilationTwice j

/-- The raw exterior-creation operator squares to zero. -/
@[rep_depth operator]
theorem localExteriorCreateRaw_sq_zero (j : ℕ) :
    TS.localExteriorCreateRaw j * TS.localExteriorCreateRaw j = 0 := by
  simpa [localExteriorCreateRaw] using TS.localCARCreationTwice_sq j

/-- The raw exterior-contraction operator squares to zero. -/
@[rep_depth operator]
theorem localExteriorContractRaw_sq_zero (j : ℕ) :
    TS.localExteriorContractRaw j * TS.localExteriorContractRaw j = 0 := by
  simpa [localExteriorContractRaw] using TS.localCARAnnihilationTwice_sq j

/-- Raw CAR normalization: `(c - d)(c + d) + (c + d)(c - d) = 4`. -/
@[rep_depth operator]
theorem localExteriorContractRaw_mul_createRaw_add_createRaw_mul_contractRaw
    (j : ℕ) :
    TS.localExteriorContractRaw j * TS.localExteriorCreateRaw j +
      TS.localExteriorCreateRaw j * TS.localExteriorContractRaw j = 4 := by
  simpa [localExteriorContractRaw, localExteriorCreateRaw] using TS.localCARTwice_anticomm j

/-- Raw product `ε_raw ι_raw = 2 - 2Π`. -/
@[rep_depth operator]
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
@[rep_depth operator]
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
@[rep_depth operator]
def localExteriorCreateWith (half : Op) (j : ℕ) : Op :=
  half * TS.localExteriorCreateRaw j

/-- Normalized exterior contraction with an explicitly supplied half scalar. -/
@[rep_depth operator]
def localExteriorContractWith (half : Op) (j : ℕ) : Op :=
  half * TS.localExteriorContractRaw j

/-- If `half` commutes with `ε_raw`, then normalized creation is square-zero. -/
@[rep_depth operator]
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
@[rep_depth operator]
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
@[rep_depth operator]
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

/-- Explicit local split-Majorana product readout: `c_j d_j = T_j`. -/
@[rep_depth operator]
theorem localMajoranaC_mul_D_eq_tilt (j : ℕ) :
    TS.localMajoranaC j * TS.localMajoranaD j = TS.T j := by
  simpa [localMajoranaParity] using TS.localMajoranaParity_eq_tilt j

/-- Local parity squares to one. -/
@[rep_depth operator]
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
@[rep_depth operator]
def localCreationUnscaled (j : ℕ) : Op :=
  TS.localMajoranaC j + TS.localMajoranaD j

/--
Unscaled contraction/annihilation operator recovered from the local split-Majorana
generators:

`ι̃_j = c_j - d_j`.

The normalized CAR contraction is `(1/2) ι̃_j` when `2` is invertible.
-/
@[rep_depth operator]
def localAnnihilationUnscaled (j : ℕ) : Op :=
  TS.localMajoranaC j - TS.localMajoranaD j

/-- The recovered unscaled creation operator squares to zero. -/
@[rep_depth operator]
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
@[rep_depth operator]
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
@[rep_depth operator]
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
@[rep_depth operator]
def localEpsilon [Invertible (2 : OpC)] (j : ℕ) : OpC :=
  ⅟ (2 : OpC) * (TSC.localMajoranaC j + TSC.localMajoranaD j)

/-- CAR reconstruction: `ι_j = (c_j - d_j)/2`. -/
@[rep_depth operator]
def localIota [Invertible (2 : OpC)] (j : ℕ) : OpC :=
  ⅟ (2 : OpC) * (TSC.localMajoranaC j - TSC.localMajoranaD j)

/-- Reconstructed CAR creator is square-zero. -/
@[rep_depth operator]
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
@[rep_depth operator]
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
@[rep_depth operator]
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
    simpa using (invOf_mul_self (2 : OpC))
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
@[rep_depth operator]
def localNumber [Invertible (2 : OpC)] (j : ℕ) : OpC :=
  TSC.localEpsilon j * TSC.localIota j

/-- CAR parity reconstructed from `ε_j, ι_j`: `1 - 2N_j`. -/
@[rep_depth operator]
def localParityFromCAR [Invertible (2 : OpC)] (j : ℕ) : OpC :=
  1 - (2 : OpC) * TSC.localNumber j

/--
Commutative reconstruction consequence:
the CAR parity readout `1 - 2(ε_j ι_j)` vanishes.
-/
@[rep_depth operator]
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
@[rep_depth operator]
structure CantorCliffordRepresentation
    (Op : Type*) [Ring Op] where
  tiltSwitch : TiltSwitchSystem Op

  gamma : ℕ → Op

  gamma_sq :
    ∀ i, gamma i * gamma i = 1

  gamma_anticomm :
    ∀ i j, i ≠ j → gamma i * gamma j = - (gamma j * gamma i)

namespace CantorCliffordRepresentation

variable {Op : Type*} [Ring Op]
variable (R : CantorCliffordRepresentation Op)

/-- Re-export of the Clifford square law. -/
@[rep_depth operator]
theorem generator_sq (i : ℕ) :
    R.gamma i * R.gamma i = 1 :=
  R.gamma_sq i

/-- Re-export of the Clifford anticommutation law. -/
@[rep_depth operator]
theorem generator_anticomm {i j : ℕ} (hij : i ≠ j) :
    R.gamma i * R.gamma j + R.gamma j * R.gamma i = 0 := by
  rw [R.gamma_anticomm i j hij]
  simp

end CantorCliffordRepresentation

/--
Finite Cantor-Pauli bridge.

For the endpoint set `V_n`, the representation of `Cl_{2n}` on functions
`V_n -> ℂ` is represented by Pauli tensor-product matrices.
-/
@[rep_depth operator]
structure FiniteCantorPauliBridge
    (n : ℕ)
    (Mat : Type*) [Ring Mat] where
  psiGamma : Fin (2 * n) → Mat

  clifford_sq :
    ∀ i, psiGamma i * psiGamma i = 1

  clifford_anticomm :
    ∀ i j, i ≠ j → psiGamma i * psiGamma j = - (psiGamma j * psiGamma i)

namespace FiniteCantorPauliBridge

variable {n : ℕ} {Mat : Type*} [Ring Mat]
variable (B : FiniteCantorPauliBridge n Mat)

/-- Re-export of the finite Pauli square law. -/
@[rep_depth operator]
theorem gamma_sq (i : Fin (2 * n)) :
    B.psiGamma i * B.psiGamma i = 1 :=
  B.clifford_sq i

/-- Re-export of the finite Pauli anticommutation law. -/
@[rep_depth operator]
theorem gamma_anticomm {i j : Fin (2 * n)} (hij : i ≠ j) :
    B.psiGamma i * B.psiGamma j + B.psiGamma j * B.psiGamma i = 0 := by
  rw [B.clifford_anticomm i j hij]
  simp

end FiniteCantorPauliBridge

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
@[rep_depth operator]
def cantorCliffordMatterEnvelope
    {Op : Type*} [Ring Op] [Star Op]
    (D : DrazinHorizon Op)
    (G : DrazinGreenHarmonic Op)
    (x : Op) : Op :=
  G.P_harm * (D.p * x * D.p) * G.P_harm

/-- The matter envelope is the existing Hodge-Drazin physical envelope. -/
@[rep_depth operator]
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
@[rep_depth operator]
def envelopeFierzCoordinate
    {Op : Type*} [Ring Op] [Star Op]
    (D : DrazinHorizon Op)
    (G : DrazinGreenHarmonic Op)
    (channel : Op → ℝ)
    (x : Op) : ℝ :=
  channel (cantorCliffordMatterEnvelope D G x)

/--
Full direct Cantor tilt/switch -> Clifford -> envelope -> readout socket.

This is the primary owner route supplied by the Cantor/Clifford papers.  It does
not pass through Cuntz, and it does not assert a Fierz/Klein law without a
separate admissibility witness.
-/
@[socket_debt_tag, rep_depth operator]
structure CantorTiltSwitchMatterReadoutSocket
    (Op : Type*) [Ring Op] [Star Op] where
  clifford : CantorCliffordRepresentation Op
  horizon : DrazinHorizon Op
  harmonic : DrazinGreenHarmonic Op
  channel : Op → ℝ
  fierzAdmissibilityPredicate : Op → Prop
  fierzAdmissible : ∀ x : Op, fierzAdmissibilityPredicate x

namespace CantorTiltSwitchMatterReadoutSocket

variable {Op : Type*} [Ring Op] [Star Op]
variable (S : CantorTiltSwitchMatterReadoutSocket Op)

/-- The socket evaluates channels on the Drazin-Hodge envelope, not raw operators. -/
@[rep_depth operator]
def coordinate (x : Op) : ℝ :=
  envelopeFierzCoordinate S.horizon S.harmonic S.channel x

end CantorTiltSwitchMatterReadoutSocket

/-- Packaged owner target for the direct Cantor tilt/switch Clifford bridge. -/
@[rep_depth operator]
structure CantorTiltSwitchCliffordOwner where
  Op : Type
  instRing : Ring Op
  representation : @CantorCliffordRepresentation Op instRing

/-- Owner target for the direct Cantor tilt/switch Clifford bridge. -/
def CantorTiltSwitchCliffordBridgeTarget : Prop :=
  Nonempty CantorTiltSwitchCliffordOwner

/-- Constructor for the direct Cantor tilt/switch Clifford owner target. -/
@[rep_depth operator]
theorem constructCantorTiltSwitchCliffordBridgeTarget
    {Op : Type} [Ring Op]
    (R : CantorCliffordRepresentation Op) :
    CantorTiltSwitchCliffordBridgeTarget := by
  exact ⟨{ Op := Op, instRing := inferInstance, representation := R }⟩

end InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
