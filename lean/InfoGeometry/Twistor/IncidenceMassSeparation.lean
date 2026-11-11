/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwistorConstituentKinematics

/-!
# Hermitian incidence pairing and the independent pair-mass determinant

The existing Witt form and infinity twistor are different pairings on the
same native carrier. Common Hermitian incidence makes the Witt pairing zero,
while a nonzero lower-spinor minor gives positive pair mass squared. Conversely,
two individually Witt-null twistors with nonzero lower spinors can have a
nonzero mutual Witt pairing and zero pair mass squared.

`pairMassSq` retains the owner's determinant normalization. The paper's mass
squared has the separate factor two already recorded by `paper_pair_mass`.
No optical twist or spatial screw-pitch invariant is introduced here.
-/

noncomputable section

namespace InfoGeometry.Twistor.IncidenceMassSeparation

open PenroseIncidence PerjesConventions InfinityTwistor TwistorConstituentKinematics
open scoped Matrix

/-- The infinity bracket ignores both upper-spinor incidence coordinates. -/
theorem infinityTwistor_paperIncidence (X Y : ComplexSpacetime) (pi rho : Spinor2) :
    infinityTwistor (paperIncidence X pi) (paperIncidence Y rho) =
      spinorMinor pi rho := rfl

/-- The same unrestricted identity for the actual constituent mass square. -/
theorem pairMassSq_paperIncidence (X Y : ComplexSpacetime) (pi rho : Spinor2) :
    pairMassSq (paperIncidence X pi) (paperIncidence Y rho) =
      Complex.normSq (spinorMinor pi rho) := rfl

/-- Mutual Witt orthogonality at a real incident point is compatible with
positive pair mass squared, exactly when the lower-spinor minor is nonzero. -/
theorem common_incidence_mass_pos_iff (X : ComplexSpacetime) (hX : Xᴴ = X)
    (pi rho : Spinor2) :
    (wittPair (paperIncidence X pi) (paperIncidence X rho) = 0 ∧
      0 < pairMassSq (paperIncidence X pi) (paperIncidence X rho)) ↔
        spinorMinor pi rho ≠ 0 := by
  constructor
  · rintro ⟨_, hmass⟩
    rw [pairMassSq_paperIncidence] at hmass
    exact Complex.normSq_pos.mp hmass
  · intro hminor
    refine ⟨paperIncidence_witt_isotropic X hX pi rho, ?_⟩
    rw [pairMassSq_paperIncidence]
    exact Complex.normSq_pos.mpr hminor

/-- The unit lower-spinor frame supplies a massive orthogonal pair at every
Hermitian spacetime point, reusing the existing massive-pair witness. -/
theorem common_incidence_basis_mass (X : ComplexSpacetime) (hX : Xᴴ = X) :
    wittPair (paperIncidence X ![1, 0]) (paperIncidence X ![0, 1]) = 0 ∧
      pairMassSq (paperIncidence X ![1, 0]) (paperIncidence X ![0, 1]) = 1 := by
  refine ⟨paperIncidence_witt_isotropic X hX _ _, ?_⟩
  exact massive_pair_witness

/-- First constituent of the opposite, nonorthogonal massless example. -/
def nullFirst : Twistor4 := ((0 : Spinor2), ![1, 0])

/-- An imaginary upper component changes the mutual pairing without changing
the common lower spinor or destroying self-nullity. -/
def nullSecond : Twistor4 := (![Complex.I, 0], ![1, 0])

theorem nullFirst_lower_ne_zero : nullFirst.2 ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num [nullFirst] at h0

theorem nullSecond_lower_ne_zero : nullSecond.2 ≠ 0 :=
  nullFirst_lower_ne_zero

theorem nullFirst_witt_self : wittPair nullFirst nullFirst = 0 := by
  simp [nullFirst, wittPair]

theorem nullSecond_witt_self : wittPair nullSecond nullSecond = 0 := by
  simp [nullSecond, wittPair, Fin.sum_univ_two]

/-- The first argument is conjugate-linear in the existing Witt convention. -/
theorem nullPair_witt : wittPair nullFirst nullSecond = Complex.I := by
  simp [nullFirst, nullSecond, wittPair, Fin.sum_univ_two]

theorem nullPair_witt_ne_zero : wittPair nullFirst nullSecond ≠ 0 := by
  rw [nullPair_witt]
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

theorem nullPair_infinity : infinityTwistor nullFirst nullSecond = 0 := by
  simp [nullFirst, nullSecond, infinityTwistor_apply]

theorem nullPair_massSq : pairMassSq nullFirst nullSecond = 0 :=
  (pairMassSq_zero_iff_infinityTwistor_pairing_zero nullFirst nullSecond).2
    nullPair_infinity

end InfoGeometry.Twistor.IncidenceMassSeparation
