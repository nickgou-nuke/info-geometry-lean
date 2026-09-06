import InfoGeometry.Clifford.JordanWignerBridge
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Canonical.CelikKocakCl11ConcretePacket
import InfoGeometry.Canonical.CelikKocakPaperFormalism
import InfoGeometry.Canonical.SplitCliffordSourceWickBase
import InfoGeometry.Canonical.SplitCliffordJordanWigner

/-!
# InfoGeometry.Canonical.JordanWignerCelikKocakBridge

Finite adapter between the concrete Jordan-Wigner matrix seed and the existing
Çelik--Koçak `n = 1` Cantor/Cl(1,1) owner packet.

This file does not introduce a new CAR carrier, tensor colimit, or infinite
Fock representation.  It only proves:

* the local Jordan-Wigner nilpotent matrices are the Wick nilpotents already
  owned by `SplitCliffordSourceWickBase`;
* the same nilpotents are recovered from the canonical Çelik--Koçak Pauli pair
  by the usual split idempotent formulas;
* the depth-one Çelik--Koçak tilt/switch system yields the raw finite CAR
  identities on endpoint functions.
-/

noncomputable section

namespace InfoGeometry.Canonical.JordanWignerCelikKocakBridge

open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.CelikKocakPaperFormalism.FunctionSpace

namespace JW

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

abbrev createBase : Mat2R :=
  InfoGeometry.Clifford.JordanWignerBridge.a_dagger_base

abbrev annihilateBase : Mat2R :=
  InfoGeometry.Clifford.JordanWignerBridge.a_base

abbrev ckGamma0 : Mat2R :=
  InfoGeometry.Canonical.CelikKocakCl11ConcretePacket.canonicalPauliGamma
    ⟨0, by decide⟩

abbrev ckGamma1 : Mat2R :=
  InfoGeometry.Canonical.CelikKocakCl11ConcretePacket.canonicalPauliGamma
    ⟨1, by decide⟩

/-- The Jordan-Wigner upper nilpotent is the repo-owned Wick annihilation atom. -/
theorem createBase_eq_wick_annihilation :
    createBase = InfoGeometry.Canonical.SplitCliffordSourceWickBase.a := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [createBase, InfoGeometry.Clifford.JordanWignerBridge.a_dagger_base,
      InfoGeometry.Canonical.SplitCliffordSourceWickBase.a,
      InfoGeometry.Canonical.SplitCliffordSourceWickBase.N]

/-- The Jordan-Wigner lower nilpotent is the repo-owned Wick creation atom. -/
theorem annihilateBase_eq_wick_creation :
    annihilateBase = InfoGeometry.Canonical.SplitCliffordSourceWickBase.aDag := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [annihilateBase, InfoGeometry.Clifford.JordanWignerBridge.a_base,
      InfoGeometry.Canonical.SplitCliffordSourceWickBase.aDag]

/-- The two local Jordan-Wigner nilpotents satisfy the existing one-mode CAR law. -/
theorem base_nilpotent_car :
    createBase * annihilateBase + annihilateBase * createBase = (1 : Mat2R) := by
  rw [createBase_eq_wick_annihilation, annihilateBase_eq_wick_creation]
  exact InfoGeometry.Canonical.SplitCliffordSourceWickBase.local_car_identity

/-- Matrix-side readback of the first canonical Çelik--Koçak Pauli generator. -/
theorem ckGamma0_eq_Eplus :
    ckGamma0 = InfoGeometry.Clifford.Cl11Matrix.Eplus :=
  InfoGeometry.Canonical.CelikKocakCl11ConcretePacket.canonical_psiGamma_zero

/-- Matrix-side readback of the second canonical Çelik--Koçak Pauli generator. -/
theorem ckGamma1_eq_J1 :
    ckGamma1 = InfoGeometry.Clifford.Cl11Matrix.J1 :=
  InfoGeometry.Canonical.CelikKocakCl11ConcretePacket.canonical_psiGamma_one

/-- The Jordan-Wigner parity matrix is the first canonical Çelik--Koçak generator. -/
theorem parity_eq_ckGamma0 :
    InfoGeometry.Canonical.SplitCliffordJordanWigner.P = ckGamma0 := by
  rw [ckGamma0_eq_Eplus]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Canonical.SplitCliffordJordanWigner.P,
      InfoGeometry.Canonical.SplitCliffordSourceWickBase.a,
      InfoGeometry.Canonical.SplitCliffordSourceWickBase.aDag,
      InfoGeometry.Canonical.SplitCliffordSourceWickBase.N,
      InfoGeometry.Clifford.Cl11Matrix.Eplus,
      Matrix.mul_apply, Fin.sum_univ_two]

/--
The upper Jordan-Wigner nilpotent is recovered from the canonical
Çelik--Koçak `Cl(1,1)` Pauli pair by the split formula
`(gamma_1 + gamma_0 gamma_1) / 2`.
-/
theorem createBase_eq_half_ckGamma1_add_ckGamma0_mul_ckGamma1 :
    createBase = (1 / 2 : ℝ) • (ckGamma1 + ckGamma0 * ckGamma1) := by
  rw [ckGamma0_eq_Eplus, ckGamma1_eq_J1]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [createBase, InfoGeometry.Clifford.JordanWignerBridge.a_dagger_base,
      InfoGeometry.Clifford.Cl11Matrix.Eplus, InfoGeometry.Clifford.Cl11Matrix.J1,
      Matrix.mul_apply, Fin.sum_univ_two]

/--
The lower Jordan-Wigner nilpotent is recovered from the canonical
Çelik--Koçak `Cl(1,1)` Pauli pair by the split formula
`(gamma_1 - gamma_0 gamma_1) / 2`.
-/
theorem annihilateBase_eq_half_ckGamma1_sub_ckGamma0_mul_ckGamma1 :
    annihilateBase = (1 / 2 : ℝ) • (ckGamma1 - ckGamma0 * ckGamma1) := by
  rw [ckGamma0_eq_Eplus, ckGamma1_eq_J1]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [annihilateBase, InfoGeometry.Clifford.JordanWignerBridge.a_base,
      InfoGeometry.Clifford.Cl11Matrix.Eplus, InfoGeometry.Clifford.Cl11Matrix.J1,
      Matrix.mul_apply, Fin.sum_univ_two]

/--
The finite Jordan-Wigner seed factors through the canonical depth-one
Çelik--Koçak packet.

This is only a forwarding/readback theorem: it packages the existing
Jordan-Wigner matrix seed, the repo-owned `Cl(1,1)` packet, and the
depth-one Cantor tilt/switch packet in one place.
-/
theorem canonical_depth_one_wire :
    createBase = InfoGeometry.Canonical.SplitCliffordSourceWickBase.a ∧
    annihilateBase = InfoGeometry.Canonical.SplitCliffordSourceWickBase.aDag ∧
    InfoGeometry.Canonical.SplitCliffordJordanWigner.P = ckGamma0 ∧
    ckGamma1 = InfoGeometry.Clifford.Cl11Matrix.J1 ∧
    createBase = (1 / 2 : ℝ) • (ckGamma1 + ckGamma0 * ckGamma1) ∧
    annihilateBase = (1 / 2 : ℝ) • (ckGamma1 - ckGamma0 * ckGamma1) := by
  refine ⟨createBase_eq_wick_annihilation, annihilateBase_eq_wick_creation, ?_, ?_, ?_, ?_⟩
  · exact parity_eq_ckGamma0
  · exact ckGamma1_eq_J1
  · exact createBase_eq_half_ckGamma1_add_ckGamma0_mul_ckGamma1
  · exact annihilateBase_eq_half_ckGamma1_sub_ckGamma0_mul_ckGamma1

/--
Recursive finite-stage wire packet.

This is a forwarding packet only: it packages the stage-preservation law on the
tensor-tower Jordan--Wigner strings together with the existing recursive
prefix law on the Çelik--Koçak Cantor operators.
-/
theorem canonical_recursive_wire_packet (n : ℕ) :
    (∀ k : Fin n,
      matStageEmbed n (jwCreation n k) = jwCreation (n + 1) k.castSucc) ∧
    (∀ k : Fin n,
      matStageEmbed n (jwAnnihilation n k) = jwAnnihilation (n + 1) k.castSucc) ∧
    (∀ m : ℕ,
      pairPrefix (n := n) (m + 1) = pairPrefix (n := n) m * pairTerm (n := n) m) := by
  constructor
  · intro k
    exact matStageEmbed_jwCreation (n := n) k
  · constructor
    · intro k
      exact matStageEmbed_jwAnnihilation (n := n) k
    · intro m
      exact pairPrefix_succ (n := n) m

end JW

namespace OneSlotTiltSwitch

variable {Op : Type*} [Ring Op]
variable {T S : Op}

private theorem D_sq
    (hT : T * T = 1)
    (hS : S * S = 1)
    (hTS : T * S = -(S * T)) :
    (S * T) * (S * T) = -1 := by
  calc
    (S * T) * (S * T)
        = S * (T * S) * T := by noncomm_ring
    _ = S * (-(S * T)) * T := by rw [hTS]
    _ = -((S * S) * (T * T)) := by noncomm_ring
    _ = -(1 * 1 : Op) := by rw [hS, hT]
    _ = -1 := by simp

private theorem C_D_anticomm
    (hS : S * S = 1)
    (hTS : T * S = -(S * T)) :
    S * (S * T) + (S * T) * S = 0 := by
  calc
    S * (S * T) + (S * T) * S
        = (S * S) * T + S * (T * S) := by noncomm_ring
    _ = 1 * T + S * (-(S * T)) := by rw [hS, hTS]
    _ = T + -(S * (S * T)) := by simp
    _ = T - S * (S * T) := by rw [sub_eq_add_neg]
    _ = T - (S * S) * T := by noncomm_ring
    _ = T - 1 * T := by rw [hS]
    _ = 0 := by simp

private theorem create_sq_zero
    (hT : T * T = 1)
    (hS : S * S = 1)
    (hTS : T * S = -(S * T)) :
    (S + S * T) * (S + S * T) = 0 := by
  have hD : (S * T) * (S * T) = -1 := D_sq (T := T) (S := S) hT hS hTS
  have hCD : S * (S * T) + (S * T) * S = 0 :=
    C_D_anticomm (T := T) (S := S) hS hTS
  calc
    (S + S * T) * (S + S * T)
        = S * S + (S * (S * T) + (S * T) * S) + (S * T) * (S * T) := by
            noncomm_ring
    _ = 1 + 0 + (-1 : Op) := by rw [hS, hCD, hD]
    _ = 0 := by simp

private theorem annihilate_sq_zero
    (hT : T * T = 1)
    (hS : S * S = 1)
    (hTS : T * S = -(S * T)) :
    (S - S * T) * (S - S * T) = 0 := by
  have hD : (S * T) * (S * T) = -1 := D_sq (T := T) (S := S) hT hS hTS
  have hCD : S * (S * T) + (S * T) * S = 0 :=
    C_D_anticomm (T := T) (S := S) hS hTS
  calc
    (S - S * T) * (S - S * T)
        = S * S - (S * (S * T) + (S * T) * S) + (S * T) * (S * T) := by
            noncomm_ring
    _ = 1 - 0 + (-1 : Op) := by rw [hS, hCD, hD]
    _ = 0 := by simp

private theorem raw_anticomm
    (hS : S * S = 1)
    (hD : (S * T) * (S * T) = -1) :
    (S - S * T) * (S + S * T) + (S + S * T) * (S - S * T) = 4 := by
  calc
    (S - S * T) * (S + S * T) + (S + S * T) * (S - S * T)
        = (S * S + S * S) - ((S * T) * (S * T) + (S * T) * (S * T)) := by
            noncomm_ring
    _ = (1 + 1 : Op) - ((-1 : Op) + (-1 : Op)) := by rw [hS, hD]
    _ = 4 := by norm_num

end OneSlotTiltSwitch

namespace CelikDepthOne

abbrev F1 :=
  (((Fin 1) → Bool) → ℂ)

abbrev Op1 :=
  F1 →ₗ[ℂ] F1

abbrev slot0 : Fin 1 :=
  ⟨0, by decide⟩

abbrev T0 : Op1 :=
  InfoGeometry.Canonical.CelikKocakCl11ConcretePacket.canonicalTiltSwitch.T slot0

abbrev S0 : Op1 :=
  InfoGeometry.Canonical.CelikKocakCl11ConcretePacket.canonicalTiltSwitch.S slot0

def majoranaC : Op1 :=
  S0

def majoranaD : Op1 :=
  S0 * T0

def creationRaw : Op1 :=
  majoranaC + majoranaD

def annihilationRaw : Op1 :=
  majoranaC - majoranaD

theorem T0_sq :
    T0 * T0 = (1 : Op1) :=
  InfoGeometry.Canonical.CelikKocakCl11ConcretePacket.canonical_tilt_sq

theorem S0_sq :
    S0 * S0 = (1 : Op1) :=
  InfoGeometry.Canonical.CelikKocakCl11ConcretePacket.canonical_switch_sq

theorem T0_S0_anticomm :
    T0 * S0 = - (S0 * T0) :=
  InfoGeometry.Canonical.CelikKocakCl11ConcretePacket.canonical_tilt_switch_anticomm

theorem majoranaC_sq :
    majoranaC * majoranaC = (1 : Op1) := by
  simpa [majoranaC] using S0_sq

theorem majoranaD_sq :
    majoranaD * majoranaD = -(1 : Op1) := by
  simpa [majoranaD] using
    (OneSlotTiltSwitch.D_sq (T := T0) (S := S0) T0_sq S0_sq T0_S0_anticomm)

theorem majoranaC_D_anticomm :
    majoranaC * majoranaD + majoranaD * majoranaC = (0 : Op1) := by
  simpa [majoranaC, majoranaD] using
    (OneSlotTiltSwitch.C_D_anticomm (T := T0) (S := S0) S0_sq T0_S0_anticomm)

/-- Depth-one Çelik--Koçak raw creation squares to zero. -/
theorem creationRaw_sq_zero :
    creationRaw * creationRaw = (0 : Op1) := by
  simpa [creationRaw, majoranaC, majoranaD] using
    (OneSlotTiltSwitch.create_sq_zero (T := T0) (S := S0) T0_sq S0_sq T0_S0_anticomm)

/-- Depth-one Çelik--Koçak raw annihilation squares to zero. -/
theorem annihilationRaw_sq_zero :
    annihilationRaw * annihilationRaw = (0 : Op1) := by
  simpa [annihilationRaw, majoranaC, majoranaD] using
    (OneSlotTiltSwitch.annihilate_sq_zero (T := T0) (S := S0) T0_sq S0_sq T0_S0_anticomm)

/--
Depth-one Çelik--Koçak raw CAR identity.  Normalizing both raw generators by
`1/2` gives the usual local CAR anticommutator.
-/
theorem annihilation_creation_anticomm_raw :
    annihilationRaw * creationRaw + creationRaw * annihilationRaw = (4 : Op1) := by
  simpa [annihilationRaw, creationRaw, majoranaC, majoranaD] using
    (OneSlotTiltSwitch.raw_anticomm (T := T0) (S := S0) S0_sq majoranaD_sq)

/-- The depth-one raw Cantor/Jordan-Wigner pair satisfies the CAR axioms. -/
theorem depthOneCAR_propertys :
    annihilationRaw * annihilationRaw = (0 : Op1) ∧
    creationRaw * creationRaw = (0 : Op1) ∧
    annihilationRaw * creationRaw + creationRaw * annihilationRaw = (4 : Op1) := by
  exact ⟨annihilationRaw_sq_zero, creationRaw_sq_zero,
    annihilation_creation_anticomm_raw⟩

end CelikDepthOne

end InfoGeometry.Canonical.JordanWignerCelikKocakBridge
