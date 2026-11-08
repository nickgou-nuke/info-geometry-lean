/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.NuclearThoulessDensity
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import Mathlib.Tactic.NoncommRing

/-!
# Finite Kohn–Sham / HFB identities in the Peirce operator algebra

The constructions below reuse the noncommutative Peirce corners.  The five
dependency stages are: unipotent particle–hole conjugation; its even density
and defect; the self-consistent operator polynomial; isospin corner weights;
and the joint particle–hole/isospin selection rule.  No matrix coordinates or
commutativity assumptions are introduced.

These are algebraic finite-ring identities; the names do not assert analytic
or empirical DFT results.
-/

namespace InfoGeometry.Physics.NuclearKohnShamPeirceBridge

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-! ## Stage DF₁: Thouless conjugation and the even occupation corner -/

abbrev thoulessTransform (P A C : B) : B := thoulessShear P A C

abbrev thoulessTransformInv (P A C : B) : B := thoulessShearInv P A C

abbrev thoulessDensity (P A C : B) : B := thoulessIdempotent P A C

abbrev occupationDensity (P A C : B) : B := thoulessOccupation P A C

abbrev vacancyDensity (P A C : B) : B :=
  thoulessVacancy P A C

/-- Idempotency defect of an operator. -/
def operatorDefect (X : B) : B := X * X - X

theorem thouless_transform_two_sided_inverse
    {P : B} (hP : P * P = P) (A C : B) :
    thoulessTransform P A C * thoulessTransformInv P A C = 1 ∧
      thoulessTransformInv P A C * thoulessTransform P A C = 1 := by
  exact ⟨thoulessShear_mul_inv hP A C,
    by
      dsimp [thoulessTransform, thoulessTransformInv]
      simp only [thoulessShear, thoulessShearInv]
      peirce_nf hP⟩

theorem thouless_density_idempotent
    {P : B} (hP : P * P = P) (A C : B) :
    thoulessDensity P A C * thoulessDensity P A C = thoulessDensity P A C := by
  exact thoulessIdempotent_idempotent hP A C

theorem thouless_even_density_eq_occupation
    {P : B} (hP : P * P = P) (A C : B) :
    evenGrade P (thoulessDensity P A C) = occupationDensity P A C := by
  exact evenGrade_thoulessIdempotent hP A C

theorem occupation_shift_is_negative_chiral_commutator
    {P : B} (hP : P * P = P) (A C : B) :
    occupationDensity P A C - P = -genSig P A C := by
  exact thoulessOccupation_sub_reference hP A C

/-! ## Stage DF₂: Complementary density and the Peirce defect identity -/

theorem occupation_vacancy_partition
    {P : B} (hP : P * P = P) (A C : B) :
    occupationDensity P A C + vacancyDensity P A C = 1 := by
  exact thoulessOccupation_add_vacancy hP A C

theorem occupation_vacancy_product
    {P : B} (hP : P * P = P) (A C : B) :
    occupationDensity P A C * vacancyDensity P A C =
    -operatorDefect (genV P A C) := by
  exact thoulessOccupation_pairing_defect hP A C

theorem hfb_quadratic_and_dispersion
    {P : B} (hP : P * P = P) (A C : B) :
    operatorDefect (P + genPhi P A C) = genV P A C ∧
    (invS P + genPhi P A C) * (invS P + genPhi P A C) = 1 + genV P A C := by
  exact ⟨by
      change (P + genPhi P A C) * (P + genPhi P A C) -
        (P + genPhi P A C) = genV P A C
      peirce_nf hP,
    ksbGenerator_sq hP A C⟩

/-! ## Stage DF₃: The stationary self-consistent operator polynomial -/

def meanFieldOperator (P H₀ H₁ A C : B) : B :=
  P * H₀ * P + (1 - P) * H₁ * (1 - P) + genPhi P A C

abbrev bogoliubovOperator (P A C : B) : B := ksbGenerator P A C

abbrev selfConsistentDensity (P A C : B) : B := ksbStationaryDensity P A C

theorem mean_field_brillouin_commutator
    {P : B} (hP : P * P = P) (H₀ H₁ A C : B) :
    comm (meanFieldOperator P H₀ H₁ A C) P = -genJ P A C := by
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    (P * H₀ * P + (1 - P) * H₁ * (1 - P) + genPhi P A C) P = -genJ P A C
  dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
    genPhi, genJ, conePlus, coneMinus]
  peirce_nf hP

theorem bogoliubov_hamiltonian_commutes_with_self_consistent_density
    {P : B} (hP : P * P = P) (A C : B) :
    comm (bogoliubovOperator P A C) (selfConsistentDensity P A C) = 0 := by
  exact ksbGenerator_comm_stationaryDensity hP A C

/-! ## Stage DF₄: Orthogonal isospin sectors and charge-weighted transitions -/

abbrev isospinCharge (Pp Pn : B) : B :=
  InfoGeometry.OperatorAlgebra.PeirceSpine.isospinCharge Pp Pn

abbrev chargePlus (Pp Pn W : B) : B :=
  InfoGeometry.OperatorAlgebra.PeirceSpine.isospinRaise Pp Pn W

abbrev chargeMinus (Pp Pn W : B) : B :=
  InfoGeometry.OperatorAlgebra.PeirceSpine.isospinLower Pp Pn W

def isospinPairing (Pp Pn W M : B) : B :=
  anticomm (chargePlus Pp Pn W) (chargeMinus Pp Pn M)

theorem isospin_charge_selection_rules
    {Pp Pn : B}
    (hpp : Pp * Pp = Pp) (hnn : Pn * Pn = Pn)
    (hpn : Pp * Pn = 0) (hnp : Pn * Pp = 0) (W M : B) :
    isospinCharge Pp Pn * isospinCharge Pp Pn = Pp + Pn ∧
    comm (isospinCharge Pp Pn) (chargePlus Pp Pn W) =
      (2 : ℤ) • chargePlus Pp Pn W ∧
    comm (isospinCharge Pp Pn) (chargeMinus Pp Pn M) =
      -(2 : ℤ) • chargeMinus Pp Pn M ∧
    comm (isospinCharge Pp Pn) (isospinPairing Pp Pn W M) = 0 := by
  rcases InfoGeometry.OperatorAlgebra.PeirceSpine.isospinCharge_tripotent
      hpp hnn hpn hnp with ⟨hSq, _⟩
  have hp : comm (isospinCharge Pp Pn) (chargePlus Pp Pn W) =
      (2 : ℤ) • chargePlus Pp Pn W := by
    change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.OperatorAlgebra.PeirceSpine.isospinCharge Pp Pn)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.isospinRaise Pp Pn W) = _
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.isospinCharge_comm_raise
      hpp hnn hnp
  have hm : comm (isospinCharge Pp Pn) (chargeMinus Pp Pn M) =
      -(2 : ℤ) • chargeMinus Pp Pn M := by
    change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.OperatorAlgebra.PeirceSpine.isospinCharge Pp Pn)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.isospinLower Pp Pn M) = _
    simpa [chargeMinus] using
      InfoGeometry.OperatorAlgebra.PeirceSpine.isospinCharge_comm_lower
        hpp hnn hpn
  exact ⟨hSq,
    hp, hm,
    by
      change InfoGeometry.OperatorAlgebra.PeirceSpine.comm (isospinCharge Pp Pn)
        (chargePlus Pp Pn W * chargeMinus Pp Pn M +
          chargeMinus Pp Pn M * chargePlus Pp Pn W) = 0
      have hmul : ∀ X Y : B,
          comm (isospinCharge Pp Pn) (X * Y) =
            comm (isospinCharge Pp Pn) X * Y + X * comm (isospinCharge Pp Pn) Y := by
        intro X Y
        unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        noncomm_ring
      have hadd : ∀ X Y : B,
          comm (isospinCharge Pp Pn) (X + Y) =
            comm (isospinCharge Pp Pn) X + comm (isospinCharge Pp Pn) Y := by
        intro X Y
        unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        noncomm_ring
      have hp' : comm (isospinCharge Pp Pn) (chargePlus Pp Pn W) =
          chargePlus Pp Pn W + chargePlus Pp Pn W := by
        simpa only [two_zsmul] using hp
      have hm' : comm (isospinCharge Pp Pn) (chargeMinus Pp Pn M) =
          -(chargeMinus Pp Pn M + chargeMinus Pp Pn M) := by
        simpa only [two_zsmul, neg_zsmul] using hm
      rw [hadd, hmul, hmul, hp', hm']
      simp only [add_mul, mul_add, neg_mul, mul_neg, neg_add]
      abel_nf
  ⟩

/-! ## Stage DF₅: Joint particle–hole and isospin selection -/

def gamowTeller (Pocc Pp Pn W : B) : B :=
  Pp * (1 - Pocc) * W * Pn * Pocc

/-- Joint proton/neutron and hole/particle sectors.  Products are kept in the
displayed order; the commuting hypotheses below are what make them projectors. -/
def protonHoleSector (Pocc Pp : B) : B := Pp * Pocc
def protonParticleSector (Pocc Pp : B) : B := Pp * (1 - Pocc)
def neutronHoleSector (Pocc Pn : B) : B := Pn * Pocc
def neutronParticleSector (Pocc Pn : B) : B := Pn * (1 - Pocc)

/-- A commuting occupation projection refines orthogonal proton and neutron
projections into four idempotents whose sum is the represented nucleon carrier
`Pp + Pn`. Pairwise orthogonality is stated separately below. -/
theorem proton_neutron_particle_hole_four_sector_resolution
    {Pocc Pp Pn : B}
    (hOcc : Pocc * Pocc = Pocc)
    (hpp : Pp * Pp = Pp) (hnn : Pn * Pn = Pn)
    (hppOcc : Pp * Pocc = Pocc * Pp)
    (hnnOcc : Pn * Pocc = Pocc * Pn) :
    protonHoleSector Pocc Pp * protonHoleSector Pocc Pp =
      protonHoleSector Pocc Pp ∧
    protonParticleSector Pocc Pp * protonParticleSector Pocc Pp =
      protonParticleSector Pocc Pp ∧
    neutronHoleSector Pocc Pn * neutronHoleSector Pocc Pn =
      neutronHoleSector Pocc Pn ∧
    neutronParticleSector Pocc Pn * neutronParticleSector Pocc Pn =
      neutronParticleSector Pocc Pn ∧
    protonHoleSector Pocc Pp + protonParticleSector Pocc Pp +
      neutronHoleSector Pocc Pn + neutronParticleSector Pocc Pn = Pp + Pn := by
  have hOccComp : (1 - Pocc) * (1 - Pocc) = 1 - Pocc := by
    noncomm_ring [hOcc]
  have hPcommComp : Pp * (1 - Pocc) = (1 - Pocc) * Pp := by
    noncomm_ring [hppOcc]
  have hNcommComp : Pn * (1 - Pocc) = (1 - Pocc) * Pn := by
    noncomm_ring [hnnOcc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [protonHoleSector]
    calc
      Pp * Pocc * (Pp * Pocc) = Pp * (Pocc * Pp) * Pocc := by noncomm_ring
      _ = Pp * (Pp * Pocc) * Pocc := by rw [← hppOcc]
      _ = (Pp * Pp) * (Pocc * Pocc) := by noncomm_ring
      _ = Pp * Pocc := by rw [hpp, hOcc]
  · dsimp [protonParticleSector]
    calc
      Pp * (1 - Pocc) * (Pp * (1 - Pocc)) =
          Pp * ((1 - Pocc) * Pp) * (1 - Pocc) := by noncomm_ring
      _ = Pp * (Pp * (1 - Pocc)) * (1 - Pocc) := by rw [← hPcommComp]
      _ = (Pp * Pp) * ((1 - Pocc) * (1 - Pocc)) := by noncomm_ring
      _ = Pp * (1 - Pocc) := by rw [hpp, hOccComp]
  · dsimp [neutronHoleSector]
    calc
      Pn * Pocc * (Pn * Pocc) = Pn * (Pocc * Pn) * Pocc := by noncomm_ring
      _ = Pn * (Pn * Pocc) * Pocc := by rw [← hnnOcc]
      _ = (Pn * Pn) * (Pocc * Pocc) := by noncomm_ring
      _ = Pn * Pocc := by rw [hnn, hOcc]
  · dsimp [neutronParticleSector]
    calc
      Pn * (1 - Pocc) * (Pn * (1 - Pocc)) =
          Pn * ((1 - Pocc) * Pn) * (1 - Pocc) := by noncomm_ring
      _ = Pn * (Pn * (1 - Pocc)) * (1 - Pocc) := by rw [← hNcommComp]
      _ = (Pn * Pn) * ((1 - Pocc) * (1 - Pocc)) := by noncomm_ring
      _ = Pn * (1 - Pocc) := by rw [hnn, hOccComp]
  · dsimp [protonHoleSector, protonParticleSector,
      neutronHoleSector, neutronParticleSector]
    noncomm_ring

/-- If an intermediate factor commutes with the right idempotent, orthogonal
left idempotents annihilate the corresponding four-factor product. -/
private theorem orthogonalLeftFactor_product
    {B : Type*} [Ring B] (P Q e f : B)
    (hPQ : P * Q = 0) (heQ : e * Q = Q * e) :
    P * e * Q * f = 0 := by
  calc
    P * e * Q * f = P * (e * Q) * f := by noncomm_ring
    _ = P * (Q * e) * f := by rw [heQ]
    _ = P * Q * e * f := by noncomm_ring
    _ = 0 := by rw [hPQ, zero_mul, zero_mul]

/-- The reverse-order version of `orthogonalLeftFactor_product`. -/
private theorem orthogonalRightFactor_product
    {B : Type*} [Ring B] (P Q e f : B)
    (hQP : Q * P = 0) (heP : e * P = P * e) :
    Q * e * P * f = 0 := by
  calc
    Q * e * P * f = Q * (e * P) * f := by noncomm_ring
    _ = Q * (P * e) * f := by rw [heP]
    _ = Q * P * e * f := by noncomm_ring
    _ = 0 := by rw [hQP, zero_mul, zero_mul]

/-- The four occupation-refined proton/neutron sectors are mutually
orthogonal in both product orders when the occupation projection commutes with
both charge projections. -/
theorem proton_neutron_particle_hole_sectors_pairwise_orthogonal
    {Pocc Pp Pn : B}
    (hOcc : Pocc * Pocc = Pocc)
    (hpp : Pp * Pp = Pp) (hnn : Pn * Pn = Pn)
    (hpn : Pp * Pn = 0) (hnp : Pn * Pp = 0)
    (hppOcc : Pp * Pocc = Pocc * Pp)
    (hnnOcc : Pn * Pocc = Pocc * Pn) :
    protonHoleSector Pocc Pp * protonParticleSector Pocc Pp = 0 ∧
    protonParticleSector Pocc Pp * protonHoleSector Pocc Pp = 0 ∧
    neutronHoleSector Pocc Pn * neutronParticleSector Pocc Pn = 0 ∧
    neutronParticleSector Pocc Pn * neutronHoleSector Pocc Pn = 0 ∧
    protonHoleSector Pocc Pp * neutronHoleSector Pocc Pn = 0 ∧
    neutronHoleSector Pocc Pn * protonHoleSector Pocc Pp = 0 ∧
    protonHoleSector Pocc Pp * neutronParticleSector Pocc Pn = 0 ∧
    neutronParticleSector Pocc Pn * protonHoleSector Pocc Pp = 0 ∧
    protonParticleSector Pocc Pp * neutronHoleSector Pocc Pn = 0 ∧
    neutronHoleSector Pocc Pn * protonParticleSector Pocc Pp = 0 ∧
    protonParticleSector Pocc Pp * neutronParticleSector Pocc Pn = 0 ∧
    neutronParticleSector Pocc Pn * protonParticleSector Pocc Pp = 0 := by
  have hPcommComp : Pp * (1 - Pocc) = (1 - Pocc) * Pp := by
    noncomm_ring [hppOcc]
  have hNcommComp : Pn * (1 - Pocc) = (1 - Pocc) * Pn := by
    noncomm_ring [hnnOcc]
  have hOccCompLeft : Pocc * (1 - Pocc) = 0 := by
    noncomm_ring [hOcc]
  have hOccCompRight : (1 - Pocc) * Pocc = 0 := by
    noncomm_ring [hOcc]
  have hPleft : Pp * Pocc * Pp * (1 - Pocc) = 0 := by
    calc
      Pp * Pocc * Pp * (1 - Pocc) = Pp * (Pocc * Pp) * (1 - Pocc) := by
        noncomm_ring
      _ = Pp * (Pp * Pocc) * (1 - Pocc) := by rw [← hppOcc]
      _ = Pp * Pp * Pocc * (1 - Pocc) := by noncomm_ring
      _ = 0 := by rw [hpp, mul_assoc, hOccCompLeft, mul_zero]
  have hPright : Pp * (1 - Pocc) * Pp * Pocc = 0 := by
    calc
      Pp * (1 - Pocc) * Pp * Pocc = Pp * ((1 - Pocc) * Pp) * Pocc := by
        noncomm_ring
      _ = Pp * (Pp * (1 - Pocc)) * Pocc := by rw [← hPcommComp]
      _ = Pp * Pp * (1 - Pocc) * Pocc := by noncomm_ring
      _ = 0 := by rw [hpp, mul_assoc, hOccCompRight, mul_zero]
  have hNleft : Pn * Pocc * Pn * (1 - Pocc) = 0 := by
    calc
      Pn * Pocc * Pn * (1 - Pocc) = Pn * (Pocc * Pn) * (1 - Pocc) := by
        noncomm_ring
      _ = Pn * (Pn * Pocc) * (1 - Pocc) := by rw [← hnnOcc]
      _ = Pn * Pn * Pocc * (1 - Pocc) := by noncomm_ring
      _ = 0 := by rw [hnn, mul_assoc, hOccCompLeft, mul_zero]
  have hNright : Pn * (1 - Pocc) * Pn * Pocc = 0 := by
    calc
      Pn * (1 - Pocc) * Pn * Pocc = Pn * ((1 - Pocc) * Pn) * Pocc := by
        noncomm_ring
      _ = Pn * (Pn * (1 - Pocc)) * Pocc := by rw [← hNcommComp]
      _ = Pn * Pn * (1 - Pocc) * Pocc := by noncomm_ring
      _ = 0 := by rw [hnn, mul_assoc, hOccCompRight, mul_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [protonHoleSector, protonParticleSector, mul_assoc] using hPleft
  · simpa [protonParticleSector, protonHoleSector, mul_assoc] using hPright
  · simpa [neutronHoleSector, neutronParticleSector, mul_assoc] using hNleft
  · simpa [neutronParticleSector, neutronHoleSector, mul_assoc] using hNright
  · simpa [protonHoleSector, neutronHoleSector, mul_assoc] using
      orthogonalLeftFactor_product Pp Pn Pocc Pocc hpn hnnOcc.symm
  · simpa [neutronHoleSector, protonHoleSector, mul_assoc] using
      orthogonalRightFactor_product Pp Pn Pocc Pocc hnp hppOcc.symm
  · simpa [protonHoleSector, neutronParticleSector, mul_assoc] using
      orthogonalLeftFactor_product Pp Pn Pocc (1 - Pocc) hpn hnnOcc.symm
  · simpa [neutronParticleSector, protonHoleSector, mul_assoc] using
      orthogonalRightFactor_product Pp Pn (1 - Pocc) Pocc hnp hPcommComp.symm
  · simpa [protonParticleSector, neutronHoleSector, mul_assoc] using
      orthogonalLeftFactor_product Pp Pn (1 - Pocc) Pocc hpn hNcommComp.symm
  · simpa [neutronHoleSector, protonParticleSector, mul_assoc] using
      orthogonalRightFactor_product Pp Pn Pocc (1 - Pocc) hnp hppOcc.symm
  · simpa [protonParticleSector, neutronParticleSector, mul_assoc] using
      orthogonalLeftFactor_product Pp Pn (1 - Pocc) (1 - Pocc) hpn hNcommComp.symm
  · simpa [neutronParticleSector, protonParticleSector, mul_assoc] using
      orthogonalRightFactor_product Pp Pn (1 - Pocc) (1 - Pocc) hnp hPcommComp.symm

theorem gamow_teller_selection_rules
    {Pocc Pp Pn : B}
    (hOcc : Pocc * Pocc = Pocc)
    (hpp : Pp * Pp = Pp) (hnn : Pn * Pn = Pn)
    (hnp : Pn * Pp = 0)
    (hppOcc : Pp * Pocc = Pocc * Pp)
    (hnnOcc : Pn * Pocc = Pocc * Pn) (W : B) :
    gamowTeller Pocc Pp Pn W * gamowTeller Pocc Pp Pn W = 0 ∧
    comm (isospinCharge Pp Pn) (gamowTeller Pocc Pp Pn W) =
      (2 : ℤ) • gamowTeller Pocc Pp Pn W ∧
    comm Pocc (gamowTeller Pocc Pp Pn W) = -gamowTeller Pocc Pp Pn W := by
  have hEleft : Pocc * (1 - Pocc) = 0 := by
    rw [mul_sub, hOcc, mul_one, sub_self]
  have hPleft : Pp * gamowTeller Pocc Pp Pn W =
      gamowTeller Pocc Pp Pn W := by
    unfold gamowTeller
    calc
      Pp * (Pp * (1 - Pocc) * W * Pn * Pocc) =
          (((Pp * Pp) * (1 - Pocc)) * W) * Pn * Pocc := by noncomm_ring
      _ = Pp * (1 - Pocc) * W * Pn * Pocc := by rw [hpp]
  have hNleft : Pn * gamowTeller Pocc Pp Pn W = 0 := by
    unfold gamowTeller
    calc
      Pn * (Pp * (1 - Pocc) * W * Pn * Pocc) =
          (((Pn * Pp) * (1 - Pocc)) * W) * Pn * Pocc := by noncomm_ring
      _ = 0 := by rw [hnp]; simp
  have hPright : gamowTeller Pocc Pp Pn W * Pp = 0 := by
    unfold gamowTeller
    calc
      Pp * (1 - Pocc) * W * Pn * Pocc * Pp =
          Pp * (1 - Pocc) * W * Pn * (Pocc * Pp) := by noncomm_ring
      _ = Pp * (1 - Pocc) * W * Pn * (Pp * Pocc) := by rw [← hppOcc]
      _ = Pp * (1 - Pocc) * W * (Pn * Pp) * Pocc := by noncomm_ring
      _ = 0 := by rw [hnp]; simp
  have hNright : gamowTeller Pocc Pp Pn W * Pn =
      gamowTeller Pocc Pp Pn W := by
    unfold gamowTeller
    calc
      Pp * (1 - Pocc) * W * Pn * Pocc * Pn =
          Pp * (1 - Pocc) * W * Pn * (Pocc * Pn) := by noncomm_ring
      _ = Pp * (1 - Pocc) * W * Pn * (Pn * Pocc) := by rw [← hnnOcc]
      _ = Pp * (1 - Pocc) * W * (Pn * Pn) * Pocc := by noncomm_ring
      _ = Pp * (1 - Pocc) * W * Pn * Pocc := by rw [hnn]
  have hSq : gamowTeller Pocc Pp Pn W * gamowTeller Pocc Pp Pn W = 0 := by
    unfold gamowTeller
    have hMid : Pocc * Pp * (1 - Pocc) = 0 := by
      calc
        Pocc * Pp * (1 - Pocc) = Pp * Pocc * (1 - Pocc) := by rw [← hppOcc]
        _ = Pp * (Pocc * (1 - Pocc)) := by noncomm_ring
        _ = 0 := by rw [hEleft]; simp
    calc
      Pp * (1 - Pocc) * W * Pn * Pocc *
          (Pp * (1 - Pocc) * W * Pn * Pocc) =
        Pp * (1 - Pocc) * W * Pn * (Pocc * Pp * (1 - Pocc)) *
          W * Pn * Pocc := by noncomm_ring
      _ = 0 := by rw [hMid]; simp
  have hTau : InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (isospinCharge Pp Pn) (gamowTeller Pocc Pp Pn W) =
      (2 : ℤ) • gamowTeller Pocc Pp Pn W := by
    change (Pp - Pn) * gamowTeller Pocc Pp Pn W -
      gamowTeller Pocc Pp Pn W * (Pp - Pn) =
      (2 : ℤ) • gamowTeller Pocc Pp Pn W
    rw [sub_mul, mul_sub, hPleft, hNleft, hPright, hNright]
    simp only [sub_zero, zero_sub, sub_neg_eq_add]
    rw [two_zsmul]
  have hOccComm : InfoGeometry.OperatorAlgebra.PeirceSpine.comm Pocc
      (gamowTeller Pocc Pp Pn W) = -gamowTeller Pocc Pp Pn W := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm gamowTeller
    have hleft : Pocc * (Pp * (1 - Pocc) * W * Pn * Pocc) = 0 := by
      calc
        Pocc * (Pp * (1 - Pocc) * W * Pn * Pocc) =
            (Pocc * Pp) * (1 - Pocc) * W * Pn * Pocc := by noncomm_ring
        _ = (Pp * Pocc) * (1 - Pocc) * W * Pn * Pocc := by rw [← hppOcc]
        _ = 0 := by
          calc
            Pp * Pocc * (1 - Pocc) * W * Pn * Pocc =
                Pp * (Pocc * (1 - Pocc)) * W * Pn * Pocc := by noncomm_ring
            _ = 0 := by rw [hEleft]; simp
    have hright : (Pp * (1 - Pocc) * W * Pn * Pocc) * Pocc =
        Pp * (1 - Pocc) * W * Pn * Pocc := by
      rw [mul_assoc, hOcc]
    rw [hleft, hright, zero_sub]
  exact ⟨hSq, hTau, hOccComm⟩

/-! ## Stage DF₁ → DF₅: Algebraic synthesis -/

/-- The finite Peirce identities used by the Thouless, KSB, isospin, and
Gamow–Teller constructions hold together under their stated corner hypotheses. -/
theorem stageDF43_operator_synthesis
    {P Pocc Pp Pn A C W M : B}
    (hP : P * P = P) (hOcc : Pocc * Pocc = Pocc)
    (hpp : Pp * Pp = Pp) (hnn : Pn * Pn = Pn)
    (hpn : Pp * Pn = 0) (hnp : Pn * Pp = 0)
    (hppOcc : Pp * Pocc = Pocc * Pp)
    (hnnOcc : Pn * Pocc = Pocc * Pn) :
    thoulessDensity P A C * thoulessDensity P A C = thoulessDensity P A C ∧
    evenGrade P (thoulessDensity P A C) = occupationDensity P A C ∧
    occupationDensity P A C - P = -genSig P A C ∧
    occupationDensity P A C * vacancyDensity P A C =
      -operatorDefect (genV P A C) ∧
    comm (bogoliubovOperator P A C) (selfConsistentDensity P A C) = 0 ∧
    isospinCharge Pp Pn * isospinCharge Pp Pn = Pp + Pn ∧
    comm (isospinCharge Pp Pn) (chargePlus Pp Pn W) =
      (2 : ℤ) • chargePlus Pp Pn W ∧
    comm (isospinCharge Pp Pn) (chargeMinus Pp Pn M) =
      -(2 : ℤ) • chargeMinus Pp Pn M ∧
    comm (isospinCharge Pp Pn) (isospinPairing Pp Pn W M) = 0 ∧
    gamowTeller Pocc Pp Pn W * gamowTeller Pocc Pp Pn W = 0 ∧
    comm (isospinCharge Pp Pn) (gamowTeller Pocc Pp Pn W) =
      (2 : ℤ) • gamowTeller Pocc Pp Pn W ∧
    comm Pocc (gamowTeller Pocc Pp Pn W) =
      -gamowTeller Pocc Pp Pn W := by
  rcases thouless_density_idempotent hP A C with hIdem
  rcases thouless_even_density_eq_occupation hP A C with hEven
  rcases occupation_shift_is_negative_chiral_commutator hP A C with hShift
  rcases occupation_vacancy_product hP A C with hVariance
  rcases bogoliubov_hamiltonian_commutes_with_self_consistent_density hP A C with hStationary
  rcases isospin_charge_selection_rules hpp hnn hpn hnp W M with
    ⟨hTauSq, hRaise, hLower, hPair⟩
  rcases gamow_teller_selection_rules hOcc hpp hnn hnp hppOcc hnnOcc W with
    ⟨hGTsq, hGTisospin, hGTparticleHole⟩
  exact ⟨hIdem, hEven, hShift, hVariance, hStationary, hTauSq, hRaise,
    hLower, hPair, hGTsq, hGTisospin, hGTparticleHole⟩

end InfoGeometry.Physics.NuclearKohnShamPeirceBridge
