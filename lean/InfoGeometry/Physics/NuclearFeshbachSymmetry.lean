/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearFeshbachReduction
import Mathlib.Algebra.Star.Module

/-!
# Conserved symmetries and adjoints under exact elimination

Commutation with both the Hamiltonian and the model projector propagates to
the complementary inverse, wave map, and effective Hamiltonian. Self-adjoint
data give a self-adjoint effective Hamiltonian when the scalar energy is
self-adjoint. The star structure is explicit; no adjoint on the countable
algebraic nuclear carrier is supplied here.
-/

namespace InfoGeometry.Physics.NuclearFeshbachSymmetry

open InfoGeometry.Physics.NuclearFeshbachReduction

section Ring

variable {A : Type*} [Ring A]

/-- Uniqueness of an inverse with a corner identity in place of the unit. -/
theorem cornerInverse_unique (Q D R S : A)
    (hRQ : R * Q = R) (hQS : Q * S = S)
    (hRD : R * D = Q) (hDS : D * S = Q) : R = S := by
  calc
    R = R * Q := hRQ.symm
    _ = R * (D * S) := by rw [hDS]
    _ = (R * D) * S := (mul_assoc _ _ _).symm
    _ = S := by rw [hRD, hQS]

/-- A symmetry commuting with the corner and its denominator commutes with
the two-sided supported inverse. -/
theorem cornerInverse_commutes (Q D R S : A)
    (hSQ : Commute S Q) (hSD : Commute S D)
    (hQR : Q * R = R) (hRQ : R * Q = R)
    (hRD : R * D = Q) (hDR : D * R = Q) : Commute S R := by
  change S * R = R * S
  calc
    S * R = S * (Q * R) := by rw [hQR]
    _ = (Q * S) * R := by rw [← mul_assoc, hSQ.eq]
    _ = ((R * D) * S) * R := by rw [hRD]
    _ = (R * S) * (D * R) := by
      calc
        _ = R * (D * S) * R := by noncomm_ring
        _ = R * (S * D) * R := by rw [hSD.eq]
        _ = _ := by noncomm_ring
    _ = (R * S) * Q := by rw [hDR]
    _ = (R * Q) * S := by rw [mul_assoc, hSQ.eq, ← mul_assoc]
    _ = R * S := by rw [hRQ]

variable [StarRing A]

/-- A supported right inverse of a self-adjoint corner denominator is itself
self-adjoint; uniqueness derives the matching left inverse. -/
theorem cornerInverse_star (Q D R : A) (hQ : star Q = Q) (hD : star D = D)
    (hQR : Q * R = R) (hDR : D * R = Q) : star R = R := by
  apply cornerInverse_unique Q D (star R) R
  · simpa only [star_mul, hQ] using congrArg star hQR
  · exact hQR
  · simpa only [star_mul, hD, hQ] using congrArg star hDR
  · exact hDR

end Ring

section Operators

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem commute_denominator (P H S : Module.End K V) (E : K)
    (hSP : Commute S P) (hSH : Commute S H) : Commute S (denominator P H E) := by
  have hSQ : Commute S (1 - P) := (Commute.one_right S).sub_right hSP
  exact (hSQ.smul_right E).sub_right ((hSQ.mul_right hSH).mul_right hSQ)

/-- Every supplied conserved symmetry of H and P remains conserved after
eliminating the complementary configurations. -/
theorem commute_resolvent (P H R S : Module.End K V) (E : K)
    (hSP : Commute S P) (hSH : Commute S H)
    (hQR : (1 - P) * R = R) (hRQ : R * (1 - P) = R)
    (hRD : R * denominator P H E = 1 - P)
    (hDR : denominator P H E * R = 1 - P) : Commute S R :=
  cornerInverse_commutes (1 - P) (denominator P H E) R S
    ((Commute.one_right S).sub_right hSP) (commute_denominator P H S E hSP hSH)
    hQR hRQ hRD hDR

theorem commute_waveOperator (P H R S : Module.End K V)
    (hSP : Commute S P) (hSH : Commute S H) (hSR : Commute S R) :
    Commute S (waveOperator P H R) :=
  hSP.add_right ((hSR.mul_right hSH).mul_right hSP)

theorem commute_effectiveHamiltonian (P H R S : Module.End K V)
    (hSP : Commute S P) (hSH : Commute S H) (hSR : Commute S R) :
    Commute S (effectiveHamiltonian P H R) :=
  ((hSP.mul_right hSH).mul_right hSP).add_right
    ((((hSP.mul_right hSH).mul_right hSR).mul_right hSH).mul_right hSP)

variable [StarRing K] [StarRing (Module.End K V)] [StarModule K (Module.End K V)]

theorem denominator_star (P H : Module.End K V) (E : K)
    (hP : star P = P) (hH : star H = H) (hE : star E = E) :
    star (denominator P H E) = denominator P H E := by
  simp only [denominator, star_sub, star_smul, star_one, star_mul, hP, hH, hE]
  noncomm_ring

/-- Self-adjoint P, H, and spectral parameter give a self-adjoint effective
operator when the supported complementary inverse exists. -/
theorem effectiveHamiltonian_star (P H R : Module.End K V) (E : K)
    (hP : star P = P) (hH : star H = H) (hE : star E = E)
    (hQR : (1 - P) * R = R) (hDR : denominator P H E * R = 1 - P) :
    star (effectiveHamiltonian P H R) = effectiveHamiltonian P H R := by
  have hR : star R = R := cornerInverse_star (1 - P) (denominator P H E) R
    (by simp only [star_sub, star_one, hP]) (denominator_star P H E hP hH hE) hQR hDR
  simp only [effectiveHamiltonian, star_add, star_mul, hP, hH, hR]
  noncomm_ring

end Operators

end InfoGeometry.Physics.NuclearFeshbachSymmetry
