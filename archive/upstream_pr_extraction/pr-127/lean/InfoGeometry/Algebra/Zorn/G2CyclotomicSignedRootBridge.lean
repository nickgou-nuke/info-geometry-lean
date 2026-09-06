/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
import InfoGeometry.Algebra.Zorn.G2CyclotomicWeylBridge

/-!
# Cyclotomic coordinates for the signed coordinate-root carrier

The first coordinate records the short/long orbit.  The `ZMod 6` coordinate
is calibrated against the concrete coordinate reflections; it is not an
independent enumeration of the six positive roots.
-/

namespace InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl
open InfoGeometry.Algebra.Zorn.G2Roots

def signedCyclotomic : Bool × G2PositiveRoot → Bool × ZMod 6
  | (false, .alpha) => (false, 0)
  | (false, .beta) => (true, 0)
  | (false, .alpha_add_beta) => (false, 2)
  | (false, .two_alpha_beta) => (false, 1)
  | (false, .three_alpha_beta) => (true, 2)
  | (false, .three_alpha_two_beta) => (true, 1)
  | (true, .alpha) => (false, 3)
  | (true, .beta) => (true, 3)
  | (true, .alpha_add_beta) => (false, 5)
  | (true, .two_alpha_beta) => (false, 4)
  | (true, .three_alpha_beta) => (true, 5)
  | (true, .three_alpha_two_beta) => (true, 4)

theorem signedCyclotomic_bijective :
    Function.Bijective signedCyclotomic := by
  classical
  decide

noncomputable def signedRootCyclotomicEquiv :
    G2CoordinateRoot ≃ Root :=
  signedRootCoordinateEquiv.symm.trans
    (Equiv.ofBijective signedCyclotomic signedCyclotomic_bijective)

@[simp] theorem signedRootCyclotomicEquiv_apply
    (r : Bool × G2PositiveRoot) :
    signedRootCyclotomicEquiv (signedRootCoordinate r) = signedCyclotomic r := by
  have h := signedRootCoordinateEquiv.symm_apply_apply r
  rw [signedRootCoordinateEquiv_apply] at h
  exact congrArg signedCyclotomic h

/-! The two sectors have different reflection axes.  This is why the old
single-offset `DihedralGroup` action is not the concrete `G₂` action. -/

def cyclotomicS1Fun : Root → Root
  | (false, k) => (false, 3 - k)
  | (true, k) => (true, 2 - k)

def cyclotomicS2Fun : Root → Root
  | (false, k) => (false, 2 - k)
  | (true, k) => (true, 3 - k)

theorem cyclotomicS1Fun_bijective : Function.Bijective cyclotomicS1Fun := by
  classical
  decide

theorem cyclotomicS2Fun_bijective : Function.Bijective cyclotomicS2Fun := by
  classical
  decide

noncomputable def cyclotomicS1Perm : Equiv.Perm Root :=
  Equiv.ofBijective cyclotomicS1Fun cyclotomicS1Fun_bijective

noncomputable def cyclotomicS2Perm : Equiv.Perm Root :=
  Equiv.ofBijective cyclotomicS2Fun cyclotomicS2Fun_bijective

def s1Signed : Bool × G2PositiveRoot → Bool × G2PositiveRoot
  | (b, .alpha) => (!b, .alpha)
  | (b, .beta) => (b, .three_alpha_beta)
  | (b, .alpha_add_beta) => (b, .two_alpha_beta)
  | (b, .two_alpha_beta) => (b, .alpha_add_beta)
  | (b, .three_alpha_beta) => (b, .beta)
  | (b, .three_alpha_two_beta) => (b, .three_alpha_two_beta)

def s2Signed : Bool × G2PositiveRoot → Bool × G2PositiveRoot
  | (b, .alpha) => (b, .alpha_add_beta)
  | (b, .beta) => (!b, .beta)
  | (b, .alpha_add_beta) => (b, .alpha)
  | (b, .two_alpha_beta) => (b, .two_alpha_beta)
  | (b, .three_alpha_beta) => (b, .three_alpha_two_beta)
  | (b, .three_alpha_two_beta) => (b, .three_alpha_beta)

theorem s1Root_signedRootCoordinate (r : Bool × G2PositiveRoot) :
    s1Root (signedRootCoordinate r) = signedRootCoordinate (s1Signed r) := by
  rcases r with ⟨b, α⟩
  cases b <;> cases α <;> apply Subtype.ext <;> decide

theorem s2Root_signedRootCoordinate (r : Bool × G2PositiveRoot) :
    s2Root (signedRootCoordinate r) = signedRootCoordinate (s2Signed r) := by
  rcases r with ⟨b, α⟩
  cases b <;> cases α <;> apply Subtype.ext <;> decide

theorem signedRootCyclotomicEquiv_s1 (r : G2CoordinateRoot) :
    signedRootCyclotomicEquiv (s1Root r) =
      cyclotomicS1Perm (signedRootCyclotomicEquiv r) := by
  obtain ⟨r, rfl⟩ := signedRootCoordinateEquiv.surjective r
  rcases r with ⟨b, α⟩
  rw [signedRootCoordinateEquiv_apply, s1Root_signedRootCoordinate,
    signedRootCyclotomicEquiv_apply]
  cases b <;> cases α <;>
    simp [cyclotomicS1Perm, cyclotomicS1Fun, signedCyclotomic, s1Signed] <;>
      decide

theorem signedRootCyclotomicEquiv_s2 (r : G2CoordinateRoot) :
    signedRootCyclotomicEquiv (s2Root r) =
      cyclotomicS2Perm (signedRootCyclotomicEquiv r) := by
  obtain ⟨r, rfl⟩ := signedRootCoordinateEquiv.surjective r
  rcases r with ⟨b, α⟩
  rw [signedRootCoordinateEquiv_apply, s2Root_signedRootCoordinate,
    signedRootCyclotomicEquiv_apply]
  cases b <;> cases α <;>
    simp [cyclotomicS2Perm, cyclotomicS2Fun, signedCyclotomic, s2Signed] <;>
      decide

theorem cyclotomicS1Perm_sq : cyclotomicS1Perm ^ 2 = 1 := by
  apply Equiv.ext
  intro r
  change cyclotomicS1Fun (cyclotomicS1Fun r) = r
  rcases r with ⟨b, k⟩
  cases b <;> simp [cyclotomicS1Fun]

theorem cyclotomicS2Perm_sq : cyclotomicS2Perm ^ 2 = 1 := by
  apply Equiv.ext
  intro r
  change cyclotomicS2Fun (cyclotomicS2Fun r) = r
  rcases r with ⟨b, k⟩
  cases b <;> simp [cyclotomicS2Fun]

theorem cyclotomicS1Perm_ne_cyclotomicS2Perm :
    cyclotomicS1Perm ≠ cyclotomicS2Perm := by
  intro h
  have hx := congrArg (fun p : Equiv.Perm Root => p (false, (0 : ZMod 6))) h
  change (false, (3 : ZMod 6)) = (false, (2 : ZMod 6)) at hx
  exact (by decide : ¬ ((3 : ZMod 6) = 2)) (congrArg Prod.snd hx)

theorem cyclotomicS1Perm_ne_one : cyclotomicS1Perm ≠ 1 := by
  intro h
  have hx := congrArg (fun p : Equiv.Perm Root => p (false, (0 : ZMod 6))) h
  change (false, (3 : ZMod 6)) = (false, (0 : ZMod 6)) at hx
  exact (by decide : ¬ ((3 : ZMod 6) = 0)) (congrArg Prod.snd hx)

theorem cyclotomicS2Perm_ne_one : cyclotomicS2Perm ≠ 1 := by
  intro h
  have hx := congrArg (fun p : Equiv.Perm Root => p (false, (0 : ZMod 6))) h
  change (false, (2 : ZMod 6)) = (false, (0 : ZMod 6)) at hx
  exact (by decide : ¬ ((2 : ZMod 6) = 0)) (congrArg Prod.snd hx)

theorem cyclotomicS1Perm_mul_S2Perm_pow_six :
    (cyclotomicS1Perm * cyclotomicS2Perm) ^ 6 = 1 := by
  apply Equiv.ext
  intro r
  rcases r with ⟨b, k⟩
  cases b <;>
    simp [cyclotomicS1Perm, cyclotomicS2Perm, cyclotomicS1Fun,
      cyclotomicS2Fun, Equiv.Perm.mul_apply, pow_succ] <;>
    ring_nf <;>
      rw [show (6 : ZMod 6) = 0 by decide] <;>
      simp

theorem cyclotomicS2Perm_mul_S1Perm_pow_six :
    (cyclotomicS2Perm * cyclotomicS1Perm) ^ 6 = 1 := by
  apply Equiv.ext
  intro r
  rcases r with ⟨b, k⟩
  cases b <;>
    simp [cyclotomicS1Perm, cyclotomicS2Perm, cyclotomicS1Fun,
      cyclotomicS2Fun, Equiv.Perm.mul_apply, pow_succ] <;>
    ring_nf <;>
      rw [show (6 : ZMod 6) = 0 by decide] <;>
      simp

theorem cyclotomicS1Perm_mul_S2Perm_mul_S1Perm_mul_S2Perm_mul_S1Perm_mul_S2Perm_eq_reverse :
    cyclotomicS1Perm * cyclotomicS2Perm * cyclotomicS1Perm * cyclotomicS2Perm *
        cyclotomicS1Perm * cyclotomicS2Perm =
      cyclotomicS2Perm * cyclotomicS1Perm * cyclotomicS2Perm * cyclotomicS1Perm *
        cyclotomicS2Perm * cyclotomicS1Perm := by
  apply Equiv.ext
  intro r
  rcases r with ⟨b, k⟩
  cases b <;>
    simp [cyclotomicS1Perm, cyclotomicS2Perm, cyclotomicS1Fun,
      cyclotomicS2Fun, Equiv.Perm.mul_apply] <;>
    ring_nf
  all_goals
    have hz : (3 : ZMod 6) = -3 := by decide
    first
    | simpa using congrArg (fun z : ZMod 6 => z + k) hz
    | simpa using congrArg (fun z : ZMod 6 => z + k) hz.symm

def cyclotomicCoxeterFun : Root → Root
  | (false, k) => (false, k - 1)
  | (true, k) => (true, k + 1)

theorem cyclotomicCoxeterFun_bijective :
    Function.Bijective cyclotomicCoxeterFun := by
  classical
  decide

noncomputable def cyclotomicCoxeterPerm : Equiv.Perm Root :=
  Equiv.ofBijective cyclotomicCoxeterFun cyclotomicCoxeterFun_bijective

theorem signedRootCyclotomicEquiv_cRoot (r : G2CoordinateRoot) :
    signedRootCyclotomicEquiv (cRoot r) =
      cyclotomicCoxeterPerm (signedRootCyclotomicEquiv r) := by
  obtain ⟨r, rfl⟩ := signedRootCoordinateEquiv.surjective r
  rcases r with ⟨b, α⟩
  rw [signedRootCoordinateEquiv_apply, cRoot_apply,
    s1Root_signedRootCoordinate,
    s2Root_signedRootCoordinate, signedRootCyclotomicEquiv_apply,
    signedRootCyclotomicEquiv_apply]
  cases b <;> cases α <;>
    simp [cyclotomicCoxeterPerm, cyclotomicCoxeterFun, signedCyclotomic,
      s1Signed, s2Signed] <;> decide

theorem cyclotomicCoxeterPerm_pow_six :
    cyclotomicCoxeterPerm ^ 6 = 1 := by
  apply Equiv.ext
  intro r
  rcases r with ⟨b, k⟩
  cases b <;>
    simp [cyclotomicCoxeterPerm, cyclotomicCoxeterFun, pow_succ]
  all_goals
    have hz : (6 : ZMod 6) = 0 := ZMod.natCast_self 6
    ring_nf
    rw [hz]
    ring

end InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
