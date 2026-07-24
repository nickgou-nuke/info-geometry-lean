import Mathlib
import InfoGeometry.Canonical.MoorePenrose

/-!
# Smith block-circulant Moore-Penrose certificates

Finite exact-rational formalization for Ronald L. Smith,
"Moore-Penrose Inverses of Block Circulant and Block k-Circulant Matrices",
Linear Algebra and Its Applications 16 (1977), 237--245.

Smith's structural result is that, for `|k| = 1`, the Moore-Penrose inverse of
a block `k`-circulant matrix is again block `k`-circulant.  This file records
the kernel-checked algebraic core used by the external CAS lanes:

* a `3 × 3` block-circulant commutation law against the cyclic shift;
* a concrete `3`-block, `2 × 2`-block exact rational witness;
* its Moore-Penrose inverse, checked by the four Penrose equations;
* preservation of the same block-circulant shift commutation by the inverse.

The generic finite Fourier diagonalization and the analytic uniqueness theorem
remain represented by the stated Smith certificate interface below; the closed
matrix witness is the exact rational certificate consumed by the Sage/GAP/M2/
SymPy/Clifford lanes.
-/

namespace InfoGeometry.Canonical.SmithBlockCirculantMoorePenrose

open InfoGeometry.Canonical

noncomputable section

abbrev Mat3 (R : Type*) := Matrix (Fin 3) (Fin 3) R
abbrev Mat6 (R : Type*) := Matrix (Fin 6) (Fin 6) R

/-- The `3 × 3` block-circulant layout with scalar/block entries in any ring. -/
def blockCirculant3 {R : Type*} [Ring R] (A0 A1 A2 : R) : Mat3 R :=
  !![A0, A1, A2;
     A2, A0, A1;
     A1, A2, A0]

/-- The cyclic block shift used in Smith's commutant characterization. -/
def cyclicShift3 {R : Type*} [Semiring R] : Mat3 R :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

/-- Every `3`-block circulant commutes with the cyclic shift. -/
theorem blockCirculant3_commutes_cyclicShift
    {R : Type*} [Ring R] (A0 A1 A2 : R) :
    blockCirculant3 A0 A1 A2 * cyclicShift3 =
      cyclicShift3 * blockCirculant3 A0 A1 A2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockCirculant3, cyclicShift3, Matrix.mul_apply, Fin.sum_univ_three]

/--
Certificate shape for Smith's block `k`-circulant Moore-Penrose theorem.

The theorem is parameterized by the shift commutant (`isBlockKCirculant`), the
unit-modulus hypothesis on `k`, and a Moore-Penrose operation.
-/
structure BlockKCirculantMPCertificate (α : Type*) [Ring α] [StarRing α] where
  isBlockKCirculant : α → Prop
  unitModulusK : Prop
  mp : α → α
  mp_law : ∀ A : α, isBlockKCirculant A → unitModulusK →
    MoorePenrose.IsMoorePenroseInverse A (mp A)
  mp_preserves : ∀ A : α, isBlockKCirculant A → unitModulusK →
    isBlockKCirculant (mp A)

namespace BlockKCirculantMPCertificate

variable {α : Type*} [Ring α] [StarRing α]
variable (C : BlockKCirculantMPCertificate α)

/-- Smith preservation readout: the Moore-Penrose inverse stays block `k`-circulant. -/
theorem mp_isBlockKCirculant {A : α} (hA : C.isBlockKCirculant A) (hk : C.unitModulusK) :
    C.isBlockKCirculant (C.mp A) :=
  C.mp_preserves A hA hk

/-- Smith Penrose readout: the supplied inverse satisfies the four MP laws. -/
theorem mp_isMoorePenrose {A : α} (hA : C.isBlockKCirculant A) (hk : C.unitModulusK) :
    MoorePenrose.IsMoorePenroseInverse A (C.mp A) :=
  C.mp_law A hA hk

end BlockKCirculantMPCertificate

/-- The `6 × 6` cyclic shift `Q ⊗ I₂`. -/
def smithShift6 : Mat6 ℚ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0]

/--
A concrete block-circulant matrix with diagonal `2 × 2` blocks
`A₀ = diag(1,2)`, `A₁ = diag(1,0)`, `A₂ = diag(0,1)`.
-/
def smithA : Mat6 ℚ :=
  !![1, 0, 1, 0, 0, 0;
     0, 2, 0, 0, 0, 1;
     0, 0, 1, 0, 1, 0;
     0, 1, 0, 2, 0, 0;
     1, 0, 0, 0, 1, 0;
     0, 0, 0, 1, 0, 2]

/-- Exact rational inverse, hence the Moore-Penrose inverse for `smithA`. -/
def smithAMP : Mat6 ℚ :=
  !![(1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0;
     0, (4 / 9 : ℚ), 0, (1 / 9 : ℚ), 0, (-2 / 9 : ℚ);
     (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0;
     0, (-2 / 9 : ℚ), 0, (4 / 9 : ℚ), 0, (1 / 9 : ℚ);
     (-1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0;
     0, (1 / 9 : ℚ), 0, (-2 / 9 : ℚ), 0, (4 / 9 : ℚ)]

/-- The witness is block-circulant, expressed as commutation with `Q ⊗ I₂`. -/
theorem smithA_commutes_shift :
    smithA * smithShift6 = smithShift6 * smithA := by
  native_decide

/-- Smith's conclusion in the concrete rational witness: the MP inverse commutes too. -/
theorem smithAMP_commutes_shift :
    smithAMP * smithShift6 = smithShift6 * smithAMP := by
  native_decide

/-- Exact left inverse certificate. -/
theorem smithAMP_mul_smithA :
    smithAMP * smithA = 1 := by
  native_decide

/-- Exact right inverse certificate. -/
theorem smithA_mul_smithAMP :
    smithA * smithAMP = 1 := by
  native_decide

/-- Determinant sanity check for the exact rational witness. -/
theorem smithA_det_eq :
    Matrix.det smithA = (18 : ℚ) := by
  native_decide

/-- The exact inverse is the Moore-Penrose inverse in the existing repo predicate. -/
theorem smithAMP_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse smithA smithAMP := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · native_decide

end

end InfoGeometry.Canonical.SmithBlockCirculantMoorePenrose
