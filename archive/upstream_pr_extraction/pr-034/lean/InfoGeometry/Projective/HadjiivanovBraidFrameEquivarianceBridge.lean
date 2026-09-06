import InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameEquivariance
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# Hadjiivanov monodromy transported by a finite braid frame

The concrete boundary braid representation acts on an eight-dimensional
carrier, whereas the native Hadjiivanov block is two-dimensional.  This file
therefore records the smallest honest common-carrier contract: a square-zero
family of logarithmic directions in a complex algebra, together with an
explicit conjugation-equivariance law.  It proves naturality of the unipotent
and phase-decorated Hadjiivanov constructions from that contract.

No embedding of the rank-two LCFT block into the Jones carrier, topological
fundamental-group realization, or physical anyon interpretation is asserted.
-/

namespace InfoGeometry.Projective.HadjiivanovBraidFrameEquivarianceBridge

open InfoGeometry.Canonical.BoundaryBraidRepresentation
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance
open InfoGeometry.Physics.B3PresentedGroup

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℂ A]

def conjugate (u : Aˣ) (x : A) : A :=
  (u : A) * x * ((u⁻¹ : Aˣ) : A)

structure NilpotentBraidFrame where
  representation :
    InfoGeometry.Canonical.BoundaryBraidRepresentation.BoundaryBraidGroup →* Aˣ
  direction : Fin 3 → A
  direction_sq : ∀ a, direction a * direction a = 0
  direction_equivariant : ∀ g a,
    conjugate (representation g) (direction a) =
      direction (braidPermutation g a)

def unipotentShear (N : A) (p : ℂ) : A :=
  1 - p • N

def frameMonodromy (F : NilpotentBraidFrame (A := A))
    (a : Fin 3) (h : ℂ) (n : ℕ) : A :=
  (lcftPhase h ^ n) •
    unipotentShear (F.direction a) (-((n : ℂ) * logShearBase))

omit [Algebra ℂ A] in theorem nilpotent_direction
    (F : NilpotentBraidFrame (A := A)) (a : Fin 3) :
    F.direction a * F.direction a = 0 :=
  F.direction_sq a

omit [Algebra ℂ A] in theorem direction_conjugation_equivariant
    (F : NilpotentBraidFrame (A := A))
    (g : InfoGeometry.Canonical.BoundaryBraidRepresentation.BoundaryBraidGroup)
    (a : Fin 3) :
    conjugate (F.representation g) (F.direction a) =
      F.direction (braidPermutation g a) :=
  F.direction_equivariant g a

theorem conjugate_unipotentShear
    (u : Aˣ) (N : A) (p : ℂ) :
    conjugate u (unipotentShear N p) =
      unipotentShear (conjugate u N) p := by
  rw [unipotentShear, unipotentShear]
  simp only [conjugate, mul_sub, sub_mul, mul_one]
  have hu : (u : A) * ((u⁻¹ : Aˣ) : A) = 1 := u.val_inv
  rw [hu]
  congr 1
  rw [Algebra.smul_def, Algebra.smul_def]
  calc
    (u : A) * (algebraMap ℂ A p * N) * ((u⁻¹ : Aˣ) : A) =
        ((u : A) * algebraMap ℂ A p) * N * ((u⁻¹ : Aˣ) : A) := by
          rw [← mul_assoc]
    _ = (algebraMap ℂ A p * (u : A)) * N * ((u⁻¹ : Aˣ) : A) := by
          rw [← Algebra.commutes p (u : A)]
    _ = algebraMap ℂ A p * ((u : A) * N * ((u⁻¹ : Aˣ) : A)) := by
          simp only [mul_assoc]

theorem unipotentShear_equivariant
    (F : NilpotentBraidFrame (A := A))
    (g : InfoGeometry.Canonical.BoundaryBraidRepresentation.BoundaryBraidGroup)
    (a : Fin 3) (p : ℂ) :
    conjugate (F.representation g) (unipotentShear (F.direction a) p) =
      unipotentShear (F.direction (braidPermutation g a)) p := by
  rw [conjugate_unipotentShear, F.direction_equivariant]

theorem conjugate_smul
    (u : Aˣ) (c : ℂ) (x : A) :
    conjugate u (c • x) = c • conjugate u x := by
  simp only [conjugate, Algebra.smul_def]
  have hc : algebraMap ℂ A c * (u : A) = (u : A) * algebraMap ℂ A c :=
    Algebra.commutes c (u : A)
  calc
    (u : A) * (algebraMap ℂ A c * x) * ((u⁻¹ : Aˣ) : A) =
        ((u : A) * algebraMap ℂ A c) * x * ((u⁻¹ : Aˣ) : A) := by
          rw [← mul_assoc]
    _ = (algebraMap ℂ A c * (u : A)) * x * ((u⁻¹ : Aˣ) : A) := by
          rw [hc]
    _ = algebraMap ℂ A c * ((u : A) * x * ((u⁻¹ : Aˣ) : A)) := by
          simp only [mul_assoc]

theorem frameMonodromy_equivariant
    (F : NilpotentBraidFrame (A := A))
    (g : InfoGeometry.Canonical.BoundaryBraidRepresentation.BoundaryBraidGroup)
    (a : Fin 3) (h : ℂ) (n : ℕ) :
    conjugate (F.representation g) (frameMonodromy F a h n) =
      frameMonodromy F (braidPermutation g a) h n := by
  rw [frameMonodromy, conjugate_smul, unipotentShear_equivariant]
  rfl

theorem unipotentShear_neg_mul
    (N : A) (hN : N * N = 0) (p : ℂ) :
    unipotentShear N (-p) * unipotentShear N p = 1 := by
  rw [unipotentShear, unipotentShear]
  rw [neg_smul, sub_neg_eq_add]
  have hsq : (p • N) * (p • N) = 0 := by
    simp only [Algebra.smul_def]
    calc
      (algebraMap ℂ A p * N) * (algebraMap ℂ A p * N) =
          algebraMap ℂ A p * (N * algebraMap ℂ A p) * N := by
            simp only [mul_assoc]
      _ = algebraMap ℂ A p * (algebraMap ℂ A p * N) * N := by
            rw [Algebra.commutes p N]
      _ = (algebraMap ℂ A p * algebraMap ℂ A p) * (N * N) := by
            simp only [mul_assoc]
      _ = 0 := by rw [hN, mul_zero]
  rw [Algebra.smul_def]
  have hsq' :
      (algebraMap ℂ A p * N) * (algebraMap ℂ A p * N) = 0 := by
    simpa [Algebra.smul_def] using hsq
  calc
    (1 + algebraMap ℂ A p * N) * (1 - algebraMap ℂ A p * N) =
        1 - (algebraMap ℂ A p * N) * (algebraMap ℂ A p * N) := by
      noncomm_ring
    _ = 1 := by rw [hsq', sub_zero]

theorem artin_conjugation_transport
    (x : Matrix (Fin 8) (Fin 8) ℂ) :
    conjugate
        (boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig0) *
          boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig1) *
          boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig0)) x =
      conjugate
        (boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig1) *
          boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig0) *
          boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig1)) x := by
  rw [boundaryBraidRepresentation_artin]

end

end InfoGeometry.Projective.HadjiivanovBraidFrameEquivarianceBridge
