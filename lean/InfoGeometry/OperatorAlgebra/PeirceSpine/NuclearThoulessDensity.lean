/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradingPerturbation

/-!
# Thouless particle-hole transport on the Peirce operator carrier

The causal order here is: Peirce nilpotence → an invertible shear → conjugate
transport of an idempotent → its even Peirce occupation readout.  These are
finite algebraic statements in an associative ring; no analytic density or
spectral interpretation is assumed.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The two-sided Thouless shear built from the opposite Peirce corners. -/
def thoulessShear (P A C : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C)

/-- The inverse shear, with the inverse factors in reverse order. -/
def thoulessShearInv (P A C : B) : B :=
  (1 + coneMinus P C) * (1 - conePlus P A)

/-- The transported idempotent under the Thouless shear. -/
def thoulessIdempotent (P A C : B) : B :=
  thoulessShear P A C * P * thoulessShearInv P A C

/-- The even Peirce occupation readout of the transported idempotent. -/
def thoulessOccupation (P A C : B) : B :=
  P * (1 - qgtPlus P A C) + (1 - P) * qgtMinus P A C

/-- Vacancy readout on the complementary Peirce sectors. -/
def thoulessVacancy (P A C : B) : B :=
  (1 - P) * (1 - qgtMinus P A C) + P * qgtPlus P A C

/-- The grading-perturbed generator used for the KSB commutator. -/
def ksbGenerator (P A C : B) : B := invS P + genPhi P A C

/-- A polynomial density commuting with the KSB generator. -/
def ksbStationaryDensity (P A C : B) : B :=
  1 + invS P + genPhi P A C + genV P A C +
    genV P A C * genPhi P A C + genSig P A C

/-- Opposite Peirce shears are mutual inverses. -/
theorem thoulessShear_mul_inv {P : B} (hP : P * P = P) (A C : B) :
    thoulessShear P A C * thoulessShearInv P A C = 1 := by
  dsimp [thoulessShear, thoulessShearInv]
  peirce_nf hP

/-- A shear conjugate of an idempotent remains idempotent. -/
theorem thoulessIdempotent_idempotent {P : B} (hP : P * P = P) (A C : B) :
    thoulessIdempotent P A C * thoulessIdempotent P A C =
      thoulessIdempotent P A C := by
  have hInv := thoulessShear_mul_inv hP A C
  have hInv' : thoulessShearInv P A C * thoulessShear P A C = 1 := by
    dsimp [thoulessShear, thoulessShearInv]
    peirce_nf hP
  unfold thoulessIdempotent
  calc
    (thoulessShear P A C * P * thoulessShearInv P A C) *
        (thoulessShear P A C * P * thoulessShearInv P A C) =
      thoulessShear P A C * P * (thoulessShearInv P A C *
        thoulessShear P A C) * P * thoulessShearInv P A C := by noncomm_ring
    _ = thoulessShear P A C * P * thoulessShearInv P A C := by
      rw [hInv', mul_one]
      calc
        thoulessShear P A C * P * P * thoulessShearInv P A C =
            thoulessShear P A C * (P * P) * thoulessShearInv P A C := by noncomm_ring
        _ = thoulessShear P A C * P * thoulessShearInv P A C := by rw [hP]

/-- The even Peirce component of the transported idempotent is the
occupation operator `P(1-Q₊) + (1-P)Q₋`. -/
theorem evenGrade_thoulessIdempotent {P : B} (hP : P * P = P) (A C : B) :
    evenGrade P (thoulessIdempotent P A C) = thoulessOccupation P A C := by
  dsimp [evenGrade, thoulessIdempotent, thoulessShear, thoulessShearInv,
    thoulessOccupation, qgtPlus, qgtMinus]
  peirce_nf hP

/-- The occupation shift from the reference idempotent is the negative
Peirce commutator `Q₊ - Q₋`. -/
theorem thoulessOccupation_sub_reference {P : B} (hP : P * P = P) (A C : B) :
    thoulessOccupation P A C - P = -genSig P A C := by
  dsimp [thoulessOccupation, genSig, comm, qgtPlus, qgtMinus]
  peirce_nf hP

/-- Occupation and vacancy, defined on the two complementary Peirce corners,
resolve the identity. -/
theorem thoulessOccupation_add_vacancy {P : B} (hP : P * P = P) (A C : B) :
    thoulessOccupation P A C + thoulessVacancy P A C = 1 := by
  dsimp [thoulessOccupation, thoulessVacancy, qgtPlus, qgtMinus]
  peirce_nf hP

/-- The occupation-vacancy product is the negative idempotency defect of the
Peirce metric. This is an algebraic pairing fluctuation identity; no positivity
or analytic density interpretation is included. -/
theorem thoulessOccupation_pairing_defect {P : B} (hP : P * P = P) (A C : B) :
    thoulessOccupation P A C * thoulessVacancy P A C =
      -(genV P A C * genV P A C - genV P A C) := by
  dsimp [thoulessVacancy, thoulessOccupation, qgtPlus, qgtMinus,
    genV, anticomm]
  peirce_nf hP

/-- The KSB generator has square `1 + V` in the Peirce operator algebra. -/
theorem ksbGenerator_sq {P : B} (hP : P * P = P) (A C : B) :
    ksbGenerator P A C * ksbGenerator P A C = 1 + genV P A C := by
  simpa [ksbGenerator, zetaPlusFactor] using grading_add_phi_sq hP A C

/-- The stationary density is the polynomial factorization
`(1 + H_KSB)(1 + V)`. -/
theorem ksbStationaryDensity_factorization {P : B}
    (hP : P * P = P) (A C : B) :
    ksbStationaryDensity P A C =
      (1 + ksbGenerator P A C) * (1 + genV P A C) := by
  dsimp [ksbStationaryDensity, ksbGenerator]
  peirce_nf hP

/-- The KSB generator commutes with the displayed stationary density for every
Peirce transition pair. -/
theorem ksbGenerator_comm_stationaryDensity {P : B} (hP : P * P = P) (A C : B) :
    comm (ksbGenerator P A C) (ksbStationaryDensity P A C) = 0 := by
  dsimp [ksbGenerator, ksbStationaryDensity, comm]
  peirce_nf hP

/-- The two orthogonal isospin sectors form the charge operator. -/
def isospinCharge (Pp Pn : B) : B := Pp - Pn

/-- Raising transition from the negative sector to the positive sector. -/
def isospinRaise (Pp Pn W : B) : B := Pp * W * Pn

/-- Lowering transition from the positive sector to the negative sector. -/
def isospinLower (Pp Pn M : B) : B := Pn * M * Pp

/-- Orthogonal idempotent sectors give a tripotent charge operator. -/
theorem isospinCharge_tripotent {Pp Pn : B}
    (hpp : Pp * Pp = Pp) (hpn : Pn * Pn = Pn)
    (horth₁ : Pp * Pn = 0) (horth₂ : Pn * Pp = 0) :
    isospinCharge Pp Pn * isospinCharge Pp Pn = Pp + Pn ∧
    isospinCharge Pp Pn * isospinCharge Pp Pn * isospinCharge Pp Pn =
      isospinCharge Pp Pn := by
  have hSq : isospinCharge Pp Pn * isospinCharge Pp Pn = Pp + Pn := by
    dsimp [isospinCharge]
    noncomm_ring [hpp, hpn, horth₁, horth₂]
  constructor
  · exact hSq
  · rw [hSq]
    dsimp [isospinCharge]
    noncomm_ring [hpp, hpn, horth₁, horth₂]

/-- The raising corner has charge weight `+2`. -/
theorem isospinCharge_comm_raise {Pp Pn W : B}
    (hpp : Pp * Pp = Pp) (hpn : Pn * Pn = Pn)
    (horth₂ : Pn * Pp = 0) :
    comm (isospinCharge Pp Pn) (isospinRaise Pp Pn W) =
      (2 : ℤ) • isospinRaise Pp Pn W := by
  have hleft : Pp * (Pp * W * Pn) = Pp * W * Pn := by
    calc
      Pp * (Pp * W * Pn) = ((Pp * Pp) * W) * Pn := by noncomm_ring
      _ = Pp * W * Pn := by rw [hpp]
  have hcross : Pn * (Pp * W * Pn) = 0 := by
    calc
      Pn * (Pp * W * Pn) = ((Pn * Pp) * W) * Pn := by noncomm_ring
      _ = 0 := by rw [horth₂]; simp
  have hright₁ : (Pp * W * Pn) * Pp = 0 := by
    calc
      (Pp * W * Pn) * Pp = (Pp * W) * (Pn * Pp) := by noncomm_ring
      _ = 0 := by rw [horth₂]; simp
  have hright₂ : (Pp * W * Pn) * Pn = Pp * W * Pn := by
    calc
      (Pp * W * Pn) * Pn = (Pp * W) * (Pn * Pn) := by noncomm_ring
      _ = Pp * W * Pn := by rw [hpn]
  unfold comm isospinCharge isospinRaise
  rw [sub_mul, mul_sub, hleft, hcross, hright₁, hright₂]
  simp only [sub_zero, zero_sub]
  abel

/-- The lowering corner has charge weight `-2`. -/
theorem isospinCharge_comm_lower {Pp Pn M : B}
    (hpp : Pp * Pp = Pp) (hpn : Pn * Pn = Pn)
    (horth₁ : Pp * Pn = 0) :
    comm (isospinCharge Pp Pn) (isospinLower Pp Pn M) =
      -((2 : ℤ) • isospinLower Pp Pn M) := by
  have hleft₁ : Pp * (Pn * M * Pp) = 0 := by
    calc
      Pp * (Pn * M * Pp) = ((Pp * Pn) * M) * Pp := by noncomm_ring
      _ = 0 := by rw [horth₁]; simp
  have hleft₂ : Pn * (Pn * M * Pp) = Pn * M * Pp := by
    calc
      Pn * (Pn * M * Pp) = ((Pn * Pn) * M) * Pp := by noncomm_ring
      _ = Pn * M * Pp := by rw [hpn]
  have hright₁ : (Pn * M * Pp) * Pp = Pn * M * Pp := by
    calc
      (Pn * M * Pp) * Pp = (Pn * M) * (Pp * Pp) := by noncomm_ring
      _ = Pn * M * Pp := by rw [hpp]
  have hright₂ : (Pn * M * Pp) * Pn = 0 := by
    calc
      (Pn * M * Pp) * Pn = (Pn * M) * (Pp * Pn) := by noncomm_ring
      _ = 0 := by rw [horth₁]; simp
  unfold comm isospinCharge isospinLower
  rw [sub_mul, mul_sub, hleft₁, hleft₂, hright₁, hright₂]
  simp only [sub_zero, zero_sub]
  abel

end InfoGeometry.OperatorAlgebra.PeirceSpine
