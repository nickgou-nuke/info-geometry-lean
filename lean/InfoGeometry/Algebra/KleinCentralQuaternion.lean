/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.KleinPresentedGroup

/-!
# A native central quadratic model of the Klein inversion relation

The carrier is Mathlib's `QuaternionAlgebra R (-1) s t`. Its generators
satisfy `i² = s*i - 1`, `j² = t`, and `j*i = (s-i)*j`. The first generator
is a unit with inverse `s-i`; the second is a unit when `t` is a unit.

The native star is quaternion conjugation, fixing the coefficient ring.
It is not asserted to be a C*-adjoint. The trace, norm, and quadratic
identity below are algebraic. No generic division property, Azumaya
property, or isomorphism with a group algebra is asserted.
-/

namespace InfoGeometry.Algebra.KleinCentralQuaternion

variable {R : Type*} [CommRing R]

/-- The transverse generator, with inverse given by its central trace minus itself. -/
def transverseUnit (s t : R) : (QuaternionAlgebra R (-1) s t)ˣ where
  val := ⟨0, 1, 0, 0⟩
  inv := algebraMap R (QuaternionAlgebra R (-1) s t) s - ⟨0, 1, 0, 0⟩
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

@[simp] theorem transverseUnit_val (s t : R) :
    (transverseUnit s t : QuaternionAlgebra R (-1) s t) = ⟨0, 1, 0, 0⟩ := rfl

theorem transverseUnit_inv_val (s t : R) :
    (↑((transverseUnit s t)⁻¹) : QuaternionAlgebra R (-1) s t) =
      algebraMap R _ s - (transverseUnit s t : QuaternionAlgebra R (-1) s t) := rfl

/-- The glide generator is invertible when its central square is invertible. -/
def glideUnit (s : R) (t : Rˣ) : (QuaternionAlgebra R (-1) s (t : R))ˣ where
  val := ⟨0, 0, 1, 0⟩
  inv := (↑(t⁻¹) : R) • (⟨0, 0, 1, 0⟩ : QuaternionAlgebra R (-1) s (t : R))
  val_inv := by ext <;> simp [mul_comm]
  inv_val := by ext <;> simp [mul_comm]

@[simp] theorem glideUnit_val (s : R) (t : Rˣ) :
    (glideUnit s t : QuaternionAlgebra R (-1) s (t : R)) = ⟨0, 0, 1, 0⟩ := rfl

theorem glideUnit_inv_val (s : R) (t : Rˣ) :
    (↑((glideUnit s t)⁻¹) : QuaternionAlgebra R (-1) s (t : R)) =
      (↑(t⁻¹) : R) • (glideUnit s t : QuaternionAlgebra R (-1) s (t : R)) := rfl

theorem glideUnit_square (s : R) (t : Rˣ) :
    (glideUnit s t : QuaternionAlgebra R (-1) s (t : R)) ^ 2 =
      algebraMap R _ (t : R) := by
  ext <;> simp [pow_two, glideUnit]

theorem transverseUnit_trace (s t : R) :
    (transverseUnit s t : QuaternionAlgebra R (-1) s t) +
      (↑((transverseUnit s t)⁻¹) : QuaternionAlgebra R (-1) s t) =
      algebraMap R _ s := by
  rw [transverseUnit_inv_val]
  abel

/-- Ordered multiplication implements inversion of the transverse unit. -/
theorem glide_mul_transverse (s : R) (t : Rˣ) :
    glideUnit s t * transverseUnit s (t : R) =
      (transverseUnit s (t : R))⁻¹ * glideUnit s t := by
  apply Units.ext
  ext <;> simp [glideUnit, transverseUnit]

theorem glide_conjugates_transverse (s : R) (t : Rˣ) :
    glideUnit s t * transverseUnit s (t : R) * (glideUnit s t)⁻¹ =
      (transverseUnit s (t : R))⁻¹ := by
  rw [glide_mul_transverse]
  simp [mul_assoc]

/-- The native generators do not commute when two is nonzero in the coefficient ring. -/
theorem transverse_glide_noncommute (s : R) (t : Rˣ) (h2 : (2 : R) ≠ 0) :
    (transverseUnit s (t : R) : QuaternionAlgebra R (-1) s (t : R)) * glideUnit s t ≠
      (glideUnit s t : QuaternionAlgebra R (-1) s (t : R)) * transverseUnit s (t : R) := by
  intro h
  have hk : (1 : R) = -1 := by
    simpa [transverseUnit, glideUnit] using congrArg QuaternionAlgebra.imK h
  apply h2
  calc
    (2 : R) = 1 + 1 := by ring
    _ = -1 + 1 := congrArg (fun z : R => z + 1) hk
    _ = 0 := neg_add_cancel 1

/-- A concrete integral transverse generator in the native algebra. -/
def integerTransverse : QuaternionAlgebra ℤ (-1) 0 1 :=
  ↑(transverseUnit (R := ℤ) 0 1)

/-- A concrete integral glide generator with square one. -/
def integerGlide : QuaternionAlgebra ℤ (-1) 0 1 := glideUnit 0 (1 : ℤˣ)

/-- The integral model supplies a closed noncommutativity witness. -/
theorem integer_generators_noncommute :
    integerTransverse * integerGlide ≠ integerGlide * integerTransverse :=
  transverse_glide_noncommute (R := ℤ) 0 (1 : ℤˣ) (by decide)

/-- The existing presented Klein group acts through the constructed units. -/
def kleinRepresentation (s : R) (t : Rˣ) :
    InfoGeometry.Canonical.KleinPresentedGroup.KleinGroup →*
      (QuaternionAlgebra R (-1) s (t : R))ˣ :=
  InfoGeometry.Canonical.KleinPresentedGroup.kleinRep
    (glideUnit s t) (transverseUnit s (t : R)) (glide_conjugates_transverse s t)

theorem kleinRepresentation_generators (s : R) (t : Rˣ) :
    let a := InfoGeometry.Canonical.KleinPresentedGroup.toKlein
      InfoGeometry.Canonical.KleinPresentedGroup.genA
    let b := InfoGeometry.Canonical.KleinPresentedGroup.toKlein
      InfoGeometry.Canonical.KleinPresentedGroup.genB
    kleinRepresentation s t a = glideUnit s t ∧
      kleinRepresentation s t b = transverseUnit s (t : R) :=
  InfoGeometry.Canonical.KleinPresentedGroup.kleinRep_relator_relation
    (glideUnit s t) (transverseUnit s (t : R)) (glide_conjugates_transverse s t)

section TraceNorm

variable {s t : R}

/-- The central coefficient of the linear term in the quaternion quadratic identity. -/
def reducedTrace (q : QuaternionAlgebra R (-1) s t) : R :=
  2 * q.re + s * q.imI

/-- The central quaternion norm for the parameters `(-1,s,t)`. -/
def reducedNorm (q : QuaternionAlgebra R (-1) s t) : R :=
  q.re ^ 2 + s * q.re * q.imI + q.imI ^ 2 -
    t * (q.imJ ^ 2 + s * q.imJ * q.imK + q.imK ^ 2)

theorem add_conjugate (q : QuaternionAlgebra R (-1) s t) :
    q + star q = algebraMap R _ (reducedTrace q) := by
  exact QuaternionAlgebra.self_add_star' q

theorem conjugate_eq (q : QuaternionAlgebra R (-1) s t) :
    star q = algebraMap R _ (reducedTrace q) - q := by
  exact QuaternionAlgebra.star_eq_two_re_sub q

theorem mul_conjugate (q : QuaternionAlgebra R (-1) s t) :
    q * star q = algebraMap R _ (reducedNorm q) := by
  ext <;> simp [reducedNorm, pow_two] <;> ring

theorem conjugate_mul (q : QuaternionAlgebra R (-1) s t) :
    star q * q = algebraMap R _ (reducedNorm q) := by
  ext <;> simp [reducedNorm, pow_two] <;> ring

theorem reducedTrace_conjugate (q : QuaternionAlgebra R (-1) s t) :
    reducedTrace (star q) = reducedTrace q := by
  simp [reducedTrace]
  ring

theorem reducedNorm_conjugate (q : QuaternionAlgebra R (-1) s t) :
    reducedNorm (star q) = reducedNorm q := by
  simp [reducedNorm]
  ring

/-- A central quadratic identity, without division, separability, or a field assumption. -/
theorem reduced_quadratic (q : QuaternionAlgebra R (-1) s t) :
    q * q - algebraMap R _ (reducedTrace q) * q +
      algebraMap R _ (reducedNorm q) = 0 := by
  rw [← add_conjugate q, ← conjugate_mul q]
  noncomm_ring

/-- The same identity is evaluated by Mathlib's native algebra homomorphism. -/
theorem aeval_reduced_quadratic (q : QuaternionAlgebra R (-1) s t) :
    Polynomial.aeval q
      (Polynomial.X ^ 2 - Polynomial.C (reducedTrace q) * Polynomial.X +
        Polynomial.C (reducedNorm q)) = 0 := by
  simpa only [map_add, map_sub, map_mul, map_pow,
    Polynomial.aeval_X, Polynomial.aeval_C, pow_two] using reduced_quadratic q

end TraceNorm

section UniversalMap

variable {A : Type*} [Ring A] [Algebra R A]

/-- Actual units and their equations define the native quaternion basis datum. -/
def representationBasis (s t : R) (u g : Aˣ)
    (hKlein : g * u * g⁻¹ = u⁻¹)
    (hTrace : (u : A) + (↑(u⁻¹) : A) = algebraMap R A s)
    (hSquare : (g : A) * (g : A) = algebraMap R A t) :
    QuaternionAlgebra.Basis A (-1 : R) s t where
  i := u
  j := g
  k := (u : A) * (g : A)
  i_mul_i := by
    have hi : (u : A) * (u : A) + 1 = algebraMap R A s * (u : A) := by
      simpa only [add_mul, Units.inv_mul] using
        congrArg (fun a : A => a * (u : A)) hTrace
    calc
      (u : A) * (u : A) = algebraMap R A s * (u : A) - 1 :=
        (eq_sub_iff_add_eq).2 hi
      _ = (-1 : R) • (1 : A) + s • (u : A) := by
        simp [Algebra.smul_def, sub_eq_add_neg, add_comm]
  j_mul_j := by simpa only [Algebra.smul_def, mul_one] using hSquare
  i_mul_j := rfl
  j_mul_i := by
    have hcrossUnits : g * u = u⁻¹ * g := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using
        congrArg (fun x : Aˣ => x * g) hKlein
    have hcross : (g : A) * (u : A) = (↑(u⁻¹) : A) * (g : A) :=
      congrArg (fun x : Aˣ => (x : A)) hcrossUnits
    have hi : (↑(u⁻¹) : A) = algebraMap R A s - (u : A) := by
      apply (eq_sub_iff_add_eq).2
      simpa only [add_comm] using hTrace
    calc
      (g : A) * (u : A) = (↑(u⁻¹) : A) * (g : A) := hcross
      _ = (algebraMap R A s - (u : A)) * (g : A) := by rw [hi]
      _ = s • (g : A) - (u : A) * (g : A) := by rw [sub_mul, Algebra.smul_def]

/-- The universal map is the native quaternion `Basis.liftHom`. -/
def representationHom (s t : R) (u g : Aˣ)
    (hKlein : g * u * g⁻¹ = u⁻¹)
    (hTrace : (u : A) + (↑(u⁻¹) : A) = algebraMap R A s)
    (hSquare : (g : A) * (g : A) = algebraMap R A t) :
    QuaternionAlgebra R (-1) s t →ₐ[R] A :=
  (representationBasis s t u g hKlein hTrace hSquare).liftHom

variable (s t : R) (u g : Aˣ)
  (hKlein : g * u * g⁻¹ = u⁻¹)
  (hTrace : (u : A) + (↑(u⁻¹) : A) = algebraMap R A s)
  (hSquare : (g : A) * (g : A) = algebraMap R A t)

@[simp] theorem representationHom_transverse :
    representationHom s t u g hKlein hTrace hSquare ⟨0, 1, 0, 0⟩ = (u : A) := by
  simp [representationHom, representationBasis, QuaternionAlgebra.Basis.liftHom_apply,
    QuaternionAlgebra.Basis.lift]

@[simp] theorem representationHom_glide :
    representationHom s t u g hKlein hTrace hSquare ⟨0, 0, 1, 0⟩ = (g : A) := by
  simp [representationHom, representationBasis, QuaternionAlgebra.Basis.liftHom_apply,
    QuaternionAlgebra.Basis.lift]

/-- The image is precisely the generated algebra, with no faithfulness assumption. -/
theorem representationHom_range :
    (representationHom s t u g hKlein hTrace hSquare).range =
      Algebra.adjoin R ({(u : A), (g : A)} : Set A) := by
  rw [representationHom, QuaternionAlgebra.Basis.range_liftHom]
  change Algebra.adjoin R ({(u : A), (g : A), (u : A) * (g : A)} : Set A) = _
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro x (rfl | rfl | rfl)
    · exact Algebra.subset_adjoin (by simp)
    · exact Algebra.subset_adjoin (by simp)
    · exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (by simp))
        (Algebra.subset_adjoin (by simp))
  · apply Algebra.adjoin_mono
    rintro x (rfl | rfl) <;> simp

/-- The two generator images determine the algebra homomorphism uniquely. -/
theorem representationHom_unique
    (f : QuaternionAlgebra R (-1) s t →ₐ[R] A)
    (hi : f ⟨0, 1, 0, 0⟩ = (u : A))
    (hj : f ⟨0, 0, 1, 0⟩ = (g : A)) :
    f = representationHom s t u g hKlein hTrace hSquare := by
  apply QuaternionAlgebra.hom_ext
  · exact hi.trans (representationHom_transverse s t u g hKlein hTrace hSquare).symm
  · exact hj.trans (representationHom_glide s t u g hKlein hTrace hSquare).symm

end UniversalMap

end InfoGeometry.Algebra.KleinCentralQuaternion
