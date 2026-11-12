/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCompressionCStar
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-!
# Unitary evolution followed by a corner compression

The ambient evolution is Mathlib's native unitary star-algebra automorphism.
Compression has an exact transferred-observable Gram defect and an independent
composition defect. The algebraic and C-star statements have no dimension
restriction. Native finite matrix positivity supplies strict trace detection.

The full-algebra map sends `1` to the corner identity. Its restriction to the
corner need not preserve that identity or compose as a semigroup. Neither a
partial trace nor a Markov generator is constructed here.
-/

namespace InfoGeometry.OperatorAlgebra.UnitaryCornerCompression

open InfoGeometry.Core.PeirceCompressionDefect

section Algebra

variable {A : Type*} [Ring A] [StarRing A]

/-- Observe a native unitary conjugation in the `p` corner. -/
def compress (p : A) (u : unitary A) (x : A) : A :=
  p * Unitary.conjStarAlgAut ℤ A u x * p

/-- The relevant transfer is that of the conjugated observable, not only `u`. -/
def transfer (p : A) (u : unitary A) (x : A) : A :=
  (1 - p) * Unitary.conjStarAlgAut ℤ A u x * p

@[simp] theorem compress_zero (p : A) (u : unitary A) :
    compress p u 0 = 0 := by
  simp [compress]

@[simp] theorem compress_one (p : A) (u : unitary A)
    (hp : IsIdempotentElem p) : compress p u 1 = p := by
  simpa only [compress, map_one, mul_one] using hp

@[simp] theorem compress_identity (p x : A) :
    compress p (1 : unitary A) x = p * x * p := by
  simp [compress]

/-- Self-adjoint cuts preserve the star operation on the full source algebra. -/
theorem compress_star (p : A) (u : unitary A) (x : A)
    (hp : IsSelfAdjoint p) :
    compress p u (star x) = star (compress p u x) := by
  simp only [compress, map_star, star_mul, hp.star_eq, mul_assoc]

/-- The existing polarized Peirce identity applied to native unitary evolution. -/
theorem schwarz_defect (p : A) (u : unitary A) (x y : A)
    (hp : IsStarProjection p) :
    compress p u (star x * y) - star (compress p u x) * compress p u y =
      star (transfer p u x) * transfer p u y := by
  rw [← compress_star p u x hp.isSelfAdjoint]
  simpa only [compress, transfer, map_mul, map_star] using
    compression_adjoint_mul_defect p (Unitary.conjStarAlgAut ℤ A u x)
      (Unitary.conjStarAlgAut ℤ A u y) hp.isIdempotentElem hp.isSelfAdjoint.star_eq

/-- A compressed ambient projection has the same actual transfer criterion. -/
theorem projection_defect_eq_gram (p q : A) (u : unitary A)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    compress p u q - (compress p u q) ^ 2 =
      star (transfer p u q) * transfer p u q := by
  have hstar : star (compress p u q) = compress p u q := by
    rw [← compress_star p u q hp.isSelfAdjoint, hq.isSelfAdjoint.star_eq]
  simpa only [hq.isSelfAdjoint.star_eq, hq.isIdempotentElem, hstar, pow_two] using
    schwarz_defect p u q q hp

/-- The defect of preserving the *corner* identity uses the reverse unitary
transfer. This is distinct from the full-domain identity law above. -/
theorem corner_unit_defect (p : A) (u : unitary A)
    (hp : IsStarProjection p) :
    p - compress p u p =
      star ((1 - p) * star (u : A) * p) * ((1 - p) * star (u : A) * p) := by
  have hc := hp.one_sub.isIdempotentElem
  have hgram :
      star ((1 - p) * star (u : A) * p) * ((1 - p) * star (u : A) * p) =
        p * (u : A) * (1 - p) * star (u : A) * p := by
    simp only [star_mul, star_sub, star_one, hp.isSelfAdjoint.star_eq, star_star]
    calc
      _ = p * (u : A) * ((1 - p) * (1 - p)) * star (u : A) * p := by
        simp only [mul_assoc]
      _ = _ := by rw [hc]
  rw [hgram]
  unfold compress
  rw [Unitary.conjStarAlgAut_apply]
  calc
    p - p * ((u : A) * p * star (u : A)) * p =
        p * ((u : A) * star (u : A)) * p -
          p * (u : A) * p * star (u : A) * p := by
      rw [Unitary.coe_mul_star_self]
      simp only [mul_one, hp.isIdempotentElem, mul_assoc]
    _ = _ := by noncomm_ring

/-- Composition loses all three omitted Peirce blocks of the intermediate
observable, with their original multiplication order retained. -/
theorem composition_defect (p : A) (u v : unitary A) (x : A) :
    compress p (u * v) x - compress p u (compress p v x) =
      p * Unitary.conjStarAlgAut ℤ A u
        (p * Unitary.conjStarAlgAut ℤ A v x * (1 - p) +
          (1 - p) * Unitary.conjStarAlgAut ℤ A v x * p +
          (1 - p) * Unitary.conjStarAlgAut ℤ A v x * (1 - p)) * p := by
  have hsplit (y : A) :
      y - p * y * p =
        p * y * (1 - p) + (1 - p) * y * p + (1 - p) * y * (1 - p) := by
    noncomm_ring
  rw [← hsplit]
  simp only [compress, Unitary.conjStarAlgAut_mul_apply, map_sub, mul_sub, sub_mul]

private theorem conjugate_cut (p : A) (u : unitary A)
    (hu : Commute (u : A) p) : Unitary.conjStarAlgAut ℤ A u p = p := by
  rw [Unitary.conjStarAlgAut_apply, hu.eq, mul_assoc,
    Unitary.coe_mul_star_self, mul_one]

/-- A unitary commuting with the cut cannot leak through that cut. -/
theorem unitary_transfer_zero_of_commute (p : A) (u : unitary A)
    (hp : IsIdempotentElem p) (hu : Commute (u : A) p) :
    (1 - p) * (u : A) * p = 0 := by
  rw [mul_assoc, hu.eq, ← mul_assoc]
  simp only [sub_mul, one_mul, hp, sub_self, zero_mul]

/-- On a preserved corner the observed map is the actual ambient automorphism. -/
theorem compress_eq_conjugate_of_supported (p x : A) (u : unitary A)
    (hu : Commute (u : A) p) (hx : p * x * p = x) :
    compress p u x = Unitary.conjStarAlgAut ℤ A u x := by
  have h := congrArg (Unitary.conjStarAlgAut ℤ A u) hx
  simpa only [compress, map_mul, conjugate_cut p u hu] using h

/-- Preserving the observation cut repairs the composition law. No condition
is imposed on the intermediate unitary `v`. -/
theorem composition_of_commute (p : A) (u v : unitary A) (x : A)
    (hp : IsIdempotentElem p) (hu : Commute (u : A) p) :
    compress p (u * v) x = compress p u (compress p v x) := by
  simp only [compress, Unitary.conjStarAlgAut_mul_apply, map_mul,
    conjugate_cut p u hu]
  have hpp (y : A) : p * (p * y * p) * p = p * y * p := by
    calc
      _ = (p * p) * y * (p * p) := by simp only [mul_assoc]
      _ = _ := by rw [hp]
  exact (hpp _).symm

end Algebra

section CStar

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- Native C-star properness identifies exactly which evolved observables
have a zero Schwarz defect. Raw transfer of `u` is not this criterion. -/
theorem schwarz_defect_eq_zero_iff (p : A) (u : unitary A) (x : A)
    (hp : IsStarProjection p) :
    compress p u (star x * x) - star (compress p u x) * compress p u x = 0 ↔
      transfer p u x = 0 := by
  rw [schwarz_defect p u x x hp]
  exact CStarRing.star_mul_self_eq_zero_iff _

/-- The transferred observable measures the exact defect in any C-star ring. -/
theorem norm_schwarz_defect (p : A) (u : unitary A) (x : A)
    (hp : IsStarProjection p) :
    ‖compress p u (star x * x) - star (compress p u x) * compress p u x‖ =
      ‖transfer p u x‖ ^ 2 := by
  rw [schwarz_defect p u x x hp, CStarRing.norm_star_mul_self, pow_two]

/-- Corner unitality is equivalent to reverse transfer vanishing. -/
theorem corner_unital_iff (p : A) (u : unitary A) (hp : IsStarProjection p) :
    compress p u p = p ↔ (1 - p) * star (u : A) * p = 0 := by
  rw [eq_comm, ← sub_eq_zero, corner_unit_defect p u hp]
  exact CStarRing.star_mul_self_eq_zero_iff _

end CStar

section Matrix

open Matrix
open scoped ComplexOrder

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The actual Schwarz defect is native matrix positive semidefinite. -/
theorem schwarz_defect_posSemidef (p x : Matrix n n 𝕜)
    (u : unitary (Matrix n n 𝕜)) (hp : IsStarProjection p) :
    (compress p u (star x * x) - star (compress p u x) * compress p u x).PosSemidef := by
  rw [schwarz_defect p u x x hp]
  exact Matrix.posSemidef_conjTranspose_mul_self (transfer p u x)

/-- Strict finite trace deficit is exactly nonzero observable transfer.
This asserts no trace-preservation or entropy-production law. -/
theorem projection_trace_deficit_pos_iff (p q : Matrix n n 𝕜)
    (u : unitary (Matrix n n 𝕜)) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    0 < trace (compress p u q) - trace ((compress p u q) ^ 2) ↔
      transfer p u q ≠ 0 := by
  rw [← trace_sub]
  have hpos : (compress p u q - (compress p u q) ^ 2).PosSemidef := by
    rw [projection_defect_eq_gram p q u hp hq]
    exact Matrix.posSemidef_conjTranspose_mul_self (transfer p u q)
  have hz : trace (compress p u q - (compress p u q) ^ 2) = 0 ↔
      transfer p u q = 0 := by
    rw [hpos.trace_eq_zero_iff, projection_defect_eq_gram p q u hp hq]
    exact Matrix.conjTranspose_mul_self_eq_zero
  constructor
  · intro ht hzero
    exact ht.ne' (hz.mpr hzero)
  · intro hnonzero
    apply lt_of_le_of_ne hpos.trace_nonneg
    intro ht
    exact hnonzero (hz.mp ht.symm)

end Matrix

end InfoGeometry.OperatorAlgebra.UnitaryCornerCompression
