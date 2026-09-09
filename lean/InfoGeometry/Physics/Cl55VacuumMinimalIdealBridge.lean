import Mathlib.Tactic
import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.Physics.Cl55SpinorCartanFock

noncomputable section
namespace InfoGeometry.Physics.Cl55VacuumMinimalIdealBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Physics.Cl55SpinorCartanFock

abbrev Mat32 := MatStage 5

def occupationProjector (i : Fin 5) : Mat32 := creation i * annihilation i
def vacancyProjector (i : Fin 5) : Mat32 := annihilation i * creation i

theorem occupation_add_vacancy (i : Fin 5) :
    occupationProjector i + vacancyProjector i = 1 := by
  simpa [occupationProjector, vacancyProjector] using creation_annihilation_same_site i

theorem occupationProjector_sq (i : Fin 5) :
    occupationProjector i * occupationProjector i = occupationProjector i := by
  have h := creation_annihilation_same_site i
  have hs := eq_sub_of_add_eq' h
  rw [occupationProjector, show creation i * annihilation i * (creation i * annihilation i) =
    creation i * (annihilation i * creation i) * annihilation i by simp [mul_assoc], hs]
  rw [mul_sub, sub_mul]
  simp only [mul_assoc, mul_one]
  rw [annihilation_same_site_sq]
  simp

theorem vacancyProjector_sq (i : Fin 5) :
    vacancyProjector i * vacancyProjector i = vacancyProjector i := by
  have h := creation_annihilation_same_site i
  have hs := eq_sub_of_add_eq h
  rw [vacancyProjector, show annihilation i * creation i * (annihilation i * creation i) =
    annihilation i * (creation i * annihilation i) * creation i by simp [mul_assoc], hs]
  rw [mul_sub, sub_mul]
  simp [mul_assoc, creation_same_site_sq, mul_one, mul_zero]

theorem mul_idempotent_of_commute {p q : Mat32}
    (hp : p * p = p) (hq : q * q = q) (hpq : p * q = q * p) :
    (p * q) * (p * q) = p * q := by
  calc
    (p * q) * (p * q) = p * (q * p) * q := by simp [mul_assoc]
    _ = p * (p * q) * q := by rw [hpq]
    _ = (p * p) * (q * q) := by simp [mul_assoc]
    _ = p * q := by rw [hp, hq]

def vacuumProjector : Mat32 :=
  (((vacancyProjector 0 * vacancyProjector 1) * vacancyProjector 2) *
    vacancyProjector 3) * vacancyProjector 4

end InfoGeometry.Physics.Cl55VacuumMinimalIdealBridge
