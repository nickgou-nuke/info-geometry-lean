import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Lie.RealSplitOctonionG2Classification

/-!
# Concrete `sl₃` stabilizer carrier

This file records the part of the split-`G₂` stabilizer statement that is
independent of any octonion realization: trace-zero `3 × 3` matrices are
closed under the commutator, and that commutator satisfies Jacobi.  The file
does not identify this carrier with a split-octonion derivation algebra.
-/

namespace InfoGeometry.Physics.SplitG2SL3Concrete

abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℝ

/-- The concrete trace-zero carrier for `sl₃(ℝ)`. -/
def SL3 := {M : Matrix3 // Matrix.trace M = 0}

instance : Zero SL3 := ⟨⟨0, by simp⟩⟩
@[simp] theorem zero_val : (0 : SL3).1 = 0 := rfl

instance : Add SL3 where
  add X Y := ⟨X.1 + Y.1, by simp [X.2, Y.2]⟩
@[simp] theorem add_val (X Y : SL3) : (X + Y).1 = X.1 + Y.1 := rfl

instance : Neg SL3 where
  neg X := ⟨-X.1, by simp [X.2]⟩
@[simp] theorem neg_val (X : SL3) : (-X).1 = -X.1 := rfl

instance : SMul ℝ SL3 where
  smul r X := ⟨r • X.1, by simp [X.2]⟩
@[simp] theorem smul_val (r : ℝ) (X : SL3) : (r • X).1 = r • X.1 := rfl

/-- The commutator bracket on the trace-zero carrier. -/
def commutator (X Y : SL3) : SL3 :=
  ⟨X.1 * Y.1 - Y.1 * X.1, by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm]
    exact sub_self _⟩

@[simp] theorem commutator_val (X Y : SL3) :
    (commutator X Y).1 = X.1 * Y.1 - Y.1 * X.1 := rfl

theorem commutator_trace_zero (X Y : SL3) :
    Matrix.trace (X.1 * Y.1 - Y.1 * X.1) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm]
  exact sub_self _

theorem commutator_add_left (X Y Z : SL3) :
    commutator (X + Y) Z = commutator X Z + commutator Y Z := by
  apply Subtype.ext
  change
    (X.1 + Y.1) * Z.1 - Z.1 * (X.1 + Y.1) =
      (X.1 * Z.1 - Z.1 * X.1) + (Y.1 * Z.1 - Z.1 * Y.1)
  noncomm_ring

theorem commutator_add_right (X Y Z : SL3) :
    commutator X (Y + Z) = commutator X Y + commutator X Z := by
  apply Subtype.ext
  change
    X.1 * (Y.1 + Z.1) - (Y.1 + Z.1) * X.1 =
      (X.1 * Y.1 - Y.1 * X.1) + (X.1 * Z.1 - Z.1 * X.1)
  noncomm_ring

theorem commutator_skew (X Y : SL3) :
    commutator X Y = -commutator Y X := by
  apply Subtype.ext
  change
    X.1 * Y.1 - Y.1 * X.1 =
      -(Y.1 * X.1 - X.1 * Y.1)
  noncomm_ring

theorem commutator_smul_left (r : ℝ) (X Y : SL3) :
    commutator (r • X) Y = r • commutator X Y := by
  apply Subtype.ext
  change
    (r • X.1) * Y.1 - Y.1 * (r • X.1) =
      r • (X.1 * Y.1 - Y.1 * X.1)
  simp only [smul_mul_assoc, mul_smul_comm, smul_sub]

theorem commutator_smul_right (r : ℝ) (X Y : SL3) :
    commutator X (r • Y) = r • commutator X Y := by
  apply Subtype.ext
  change
    X.1 * (r • Y.1) - (r • Y.1) * X.1 =
      r • (X.1 * Y.1 - Y.1 * X.1)
  simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

theorem commutator_jacobi (X Y Z : SL3) :
    commutator X (commutator Y Z) +
        commutator Y (commutator Z X) +
        commutator Z (commutator X Y) = 0 := by
  apply Subtype.ext
  change
    (X.1 * (Y.1 * Z.1 - Z.1 * Y.1) -
        (Y.1 * Z.1 - Z.1 * Y.1) * X.1) +
      (Y.1 * (Z.1 * X.1 - X.1 * Z.1) -
        (Z.1 * X.1 - X.1 * Z.1) * Y.1) +
      (Z.1 * (X.1 * Y.1 - Y.1 * X.1) -
        (X.1 * Y.1 - Y.1 * X.1) * Z.1) = 0
  noncomm_ring

/-!
The existing canonical Zorn owner supplies the genuine fourteen-dimensional
derivation space.  The following theorem records only the numerical
compatibility with the intended `8 + 3 + 3` grading; it does not assert an
unproved linear equivalence between the carriers.
-/

theorem canonical_derivation_finrank_matches_grade_sum :
    Module.finrank ℝ
        InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations =
      8 + 3 + 3 := by
  rw [InfoGeometry.Lie.RealSplitOctonionG2Classification.canonical_split_octonion_derivation_finrank]

end InfoGeometry.Physics.SplitG2SL3Concrete
