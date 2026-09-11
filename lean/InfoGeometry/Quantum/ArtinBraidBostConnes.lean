import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.ArtinBraidBostConnes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {A : Type*} [CommRing A]
variable {R : Type*} [Ring R] [Algebra A R]

def BraidRelation (s1 s2 : R) : Prop :=
  s1 * s2 * s1 = s2 * s1 * s2

def HeckeRelation (s : R) (q : A) : Prop :=
  s * s = algebraMap A R (q - 1) * s + algebraMap A R q

theorem braid_inverse (s : R) (q q_inv : A)
    (hq : q_inv * q = 1)
    (h_hecke : HeckeRelation s q) :
    s * (algebraMap A R q_inv * s - algebraMap A R (q_inv * (q - 1))) = 1 := by
  unfold HeckeRelation at h_hecke
  rw [mul_sub]
  have h1 : s * (algebraMap A R q_inv * s) = algebraMap A R q_inv * (s * s) := by
    calc
      s * (algebraMap A R q_inv * s) = (s * algebraMap A R q_inv) * s := by rw [mul_assoc]
      _ = (algebraMap A R q_inv * s) * s := by rw [Algebra.commutes q_inv s]
      _ = algebraMap A R q_inv * (s * s) := by rw [mul_assoc]
  rw [h1, h_hecke]
  have h2 : algebraMap A R q_inv * (algebraMap A R (q - 1) * s + algebraMap A R q) =
            algebraMap A R (q_inv * (q - 1)) * s + algebraMap A R (q_inv * q) := by
    rw [mul_add]
    have h_left : algebraMap A R q_inv * (algebraMap A R (q - 1) * s) = algebraMap A R (q_inv * (q - 1)) * s := by
      rw [← mul_assoc, ← map_mul]
    have h_right : algebraMap A R q_inv * algebraMap A R q = algebraMap A R (q_inv * q) := by
      rw [← map_mul]
    rw [h_left, h_right]
  rw [h2, hq, map_one]
  have h3 : s * algebraMap A R (q_inv * (q - 1)) = algebraMap A R (q_inv * (q - 1)) * s := by
    rw [Algebra.commutes]
  rw [h3]
  abel

theorem galois_hecke_shift (s : R) (q : A) (g : A →+* A)
    (h_hecke : HeckeRelation s q) :
    s * s = algebraMap A R (g q - 1) * s + algebraMap A R (g q)
            - algebraMap A R (g q - q) * (s + 1) := by
  rw [h_hecke]
  rw [map_sub, map_sub, map_one]
  have h1 : (algebraMap A R (g q) - 1) * s = algebraMap A R (g q) * s - s := by
    rw [sub_mul, one_mul]
  have h2 : (algebraMap A R (g q) - algebraMap A R q) * (s + 1) =
            algebraMap A R (g q) * s - algebraMap A R q * s + algebraMap A R (g q) - algebraMap A R q := by
    rw [mul_add, sub_mul, mul_one]
    abel
  have h3 : (algebraMap A R q - 1) * s = algebraMap A R q * s - s := by
    rw [sub_mul, one_mul]
  rw [h1, h3, map_sub, h2]
  abel


end InfoGeometry.Quantum.ArtinBraidBostConnes
