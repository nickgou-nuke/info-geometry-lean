/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.PeirceLieJordanResolution
import InfoGeometry.Algebra.PeirceDeWittChiralSplit
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Peirce trace pairings and the distinction between bilinear and Hermitian forms

The weighted bilinear form is generally not symmetric. Its asymmetry is
measured exactly by a commutator. A different, sesquilinear form is Hermitian
for a self-adjoint idempotent. No DeWitt, BKM, Berry or Fubini--Study
identification is asserted by these finite matrix identities.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

open Matrix
open InfoGeometry.Algebra.PeirceDeWittChiralSplit
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- Cyclicity reduces a product of opposing corners without commuting matrices. -/
theorem trace_sandwich_pair {E F : Matrix n n R}
    (hE : E * E = E) (hF : F * F = F) (X Y : Matrix n n R) :
    trace ((E * X * F) * (F * Y * E)) = trace (E * X * F * Y) := by
  calc
    trace ((E * X * F) * (F * Y * E)) =
        trace ((E * X * (F * F) * Y) * E) := by
      congr 1
      noncomm_ring
    _ = trace (E * (E * X * (F * F) * Y)) := trace_mul_comm _ _
    _ = trace ((E * E) * X * (F * F) * Y) := by
      congr 1
      noncomm_ring
    _ = _ := by rw [hE, hF]

/-- The four nonzero block pairings in the bilinear trace form. -/
theorem trace_four_corners {P : Matrix n n R} (hP : IsIdempotent P)
    (X Y : Matrix n n R) :
    trace (X * Y) = trace (peirce11 P X * peirce11 P Y) +
      trace (peirce00 P X * peirce00 P Y) +
      trace (peirce10 P X * peirce01 P Y) +
      trace (peirce01 P X * peirce10 P Y) := by
  have hQ : compIdempotent P * compIdempotent P = compIdempotent P :=
    compIdempotent_isIdempotent hP
  simp only [peirce11, peirce00, peirce10, peirce01]
  rw [trace_sandwich_pair hP hP, trace_sandwich_pair hQ hQ,
    trace_sandwich_pair hP hQ, trace_sandwich_pair hQ hP]
  rw [← trace_add, ← trace_add, ← trace_add]
  congr 1
  simp only [compIdempotent]
  noncomm_ring

/-- An ordered bilinear trace form. It is not a symmetric metric in general. -/
def weightedTrace (P X Y : Matrix n n R) : R := trace (grading P * X * Y)

/-- Diagonal and opposing off-diagonal terms have their exact ordered signs. -/
theorem weightedTrace_four_corners {P : Matrix n n R} (hP : IsIdempotent P)
    (X Y : Matrix n n R) :
    weightedTrace P X Y = trace (peirce11 P X * peirce11 P Y) -
      trace (peirce00 P X * peirce00 P Y) +
      trace (peirce10 P X * peirce01 P Y) -
      trace (peirce01 P X * peirce10 P Y) := by
  have hQ : compIdempotent P * compIdempotent P = compIdempotent P :=
    compIdempotent_isIdempotent hP
  simp only [weightedTrace, peirce11, peirce00, peirce10, peirce01]
  rw [trace_sandwich_pair hP hP, trace_sandwich_pair hQ hQ,
    trace_sandwich_pair hP hQ, trace_sandwich_pair hQ hP]
  rw [← trace_sub, ← trace_add, ← trace_sub]
  congr 1
  simp only [grading, compIdempotent]
  noncomm_ring

/-- The precise obstruction to symmetry of the weighted bilinear form. -/
theorem weightedTrace_asymmetry (P X Y : Matrix n n R) :
    weightedTrace P X Y - weightedTrace P Y X =
      trace ((grading P * X - X * grading P) * Y) := by
  unfold weightedTrace
  rw [sub_mul, trace_sub]
  have hcyc : trace (grading P * Y * X) = trace (X * grading P * Y) :=
    trace_mul_cycle _ _ _
  rw [hcyc]

/-- The symmetric part is the anticommutator with the grading element. -/
theorem weightedTrace_symmetric_part (P X Y : Matrix n n R) :
    weightedTrace P X Y + weightedTrace P Y X =
      trace ((grading P * X + X * grading P) * Y) := by
  unfold weightedTrace
  rw [add_mul, trace_add]
  have hcyc : trace (grading P * Y * X) = trace (X * grading P * Y) :=
    trace_mul_cycle _ _ _
  rw [hcyc]

/-- Symmetry on the actual even Peirce sector. -/
theorem weightedTrace_even_symmetric {P : Matrix n n R} (hP : IsIdempotent P)
    (X Y : Matrix n n R) :
    weightedTrace P (evenPart P X) Y = weightedTrace P Y (evenPart P X) := by
  apply sub_eq_zero.mp
  rw [weightedTrace_asymmetry, grading_commutes_evenPart P hP X, sub_self]
  simp

/-- Skew symmetry on the actual odd Peirce sector. -/
theorem weightedTrace_odd_skew {P : Matrix n n R} (hP : IsIdempotent P)
    (X Y : Matrix n n R) :
    weightedTrace P (oddPart P X) Y + weightedTrace P Y (oddPart P X) = 0 := by
  rw [weightedTrace_symmetric_part, grading_anticommutes_oddPart P hP X]
  simp

section Star

variable [StarRing R]

/-- A separate sesquilinear form on full matrices. -/
def kreinTrace (P X Y : Matrix n n R) : R := trace (Xᴴ * grading P * Y)

theorem grading_conjTranspose {P : Matrix n n R} (hP : Pᴴ = P) :
    (grading P)ᴴ = grading P := by
  simp only [grading, compIdempotent, conjTranspose_sub, conjTranspose_one, hP]

/-- Hermitian symmetry requires the actual self-adjointness hypothesis. -/
theorem kreinTrace_hermitian {P : Matrix n n R} (hP : Pᴴ = P)
    (X Y : Matrix n n R) :
    star (kreinTrace P Y X) = kreinTrace P X Y := by
  unfold kreinTrace
  rw [← trace_conjTranspose]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose,
    grading_conjTranspose hP, mul_assoc]

/-- Evaluation of a projected square, with no diagonalization. -/
theorem trace_projected_square {E : Matrix n n R}
    (hE : E * E = E) (hE' : Eᴴ = E) (X : Matrix n n R) :
    trace ((E * X)ᴴ * (E * X)) = trace (Xᴴ * E * X) := by
  rw [conjTranspose_mul, hE']
  calc
    trace (Xᴴ * E * (E * X)) = trace (Xᴴ * (E * E) * X) := by
      congr 1
      noncomm_ring
    _ = _ := by rw [hE]

/-- The Hermitian form is the difference of two genuine projected square forms. -/
theorem kreinTrace_square_split {P : Matrix n n R}
    (hP : IsIdempotent P) (hP' : Pᴴ = P) (X : Matrix n n R) :
    kreinTrace P X X = trace ((P * X)ᴴ * (P * X)) -
      trace ((compIdempotent P * X)ᴴ * (compIdempotent P * X)) := by
  have hQ : compIdempotent P * compIdempotent P = compIdempotent P :=
    compIdempotent_isIdempotent hP
  have hQ' : (compIdempotent P)ᴴ = compIdempotent P := by
    simp [compIdempotent, hP']
  rw [trace_projected_square hP hP', trace_projected_square hQ hQ']
  simp only [kreinTrace, grading, mul_sub, sub_mul, trace_sub]

/-- Nondegeneracy is inherited from the full matrix trace pairing and `grading²=1`. -/
theorem kreinTrace_left_nondegenerate {P X : Matrix n n R}
    (hP : IsIdempotent P) (h : ∀ Y, kreinTrace P X Y = 0) : X = 0 := by
  have hz : Xᴴ * grading P = 0 := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro Y
    simpa only [kreinTrace, zero_mul, trace_zero] using h Y
  have hX : Xᴴ = 0 := by
    have hm := congrArg (fun M : Matrix n n R => M * grading P) hz
    simpa only [mul_assoc, grading_sq P hP, mul_one, zero_mul] using hm
  have := congrArg Matrix.conjTranspose hX
  simpa only [conjTranspose_conjTranspose, conjTranspose_zero] using this

end Star
end InfoGeometry.OperatorAlgebra.LieJordan
