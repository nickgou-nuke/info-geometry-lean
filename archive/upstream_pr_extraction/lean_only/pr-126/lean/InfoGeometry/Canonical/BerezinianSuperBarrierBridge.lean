import Mathlib
import InfoGeometry.NCG.BerezinianSuperdeterminant
import InfoGeometry.External.Auto.LogDetSuperKahlerBarrier

/-!
# Berezinian super-barrier bridge

Finite theorem-honest bridge from the repository's determinant/log-barrier lane
to its block-diagonal Berezinian owner.

For real even/odd blocks `A,D` with nonzero determinants, the canonical
block-diagonal Berezinian is

  Ber(A,D) = det(A) / det(D),

and the graded logarithmic barrier satisfies

  -log Ber(A,D) = -log det(A) + log det(D).

Thus the odd block enters with the opposite logarithmic sign.  Equal even/odd
determinants give exact cancellation `Ber = 1` and zero super-barrier.

The file also records the elementary odd-coordinate reflection sign
`Ber(diag(1,-1)) = -1` on a `1|1` block carrier.

This finite owner does not construct a supermanifold, a super-vielbein,
coordinate-invariant integration measure, Pin^- structure, path integral,
Kasteleyn theorem, or anomaly-cancellation theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.BerezinianSuperBarrierBridge

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Block := Matrix ι ι ℝ

/-- Canonical block-diagonal Berezinian using the actual determinant inverse. -/
def canonicalBerezinian (A D : Block) : ℝ :=
  Matrix.det A / Matrix.det D

/-- The canonical ratio is exactly the existing NCG block-diagonal Berezinian
when its inverse-determinant slot is instantiated by `(det D)⁻¹`. -/
theorem canonicalBerezinian_eq_owner (A D : Block) :
    canonicalBerezinian A D =
      InfoGeometry.NCG.berezinianBlockDiag A D (Matrix.det D)⁻¹ := by
  simp [canonicalBerezinian, InfoGeometry.NCG.berezinianBlockDiag, div_eq_mul_inv]

/-- Positivity of the graded volume ratio on positive determinant blocks. -/
theorem canonicalBerezinian_pos {A D : Block}
    (hA : 0 < Matrix.det A) (hD : 0 < Matrix.det D) :
    0 < canonicalBerezinian A D := by
  exact div_pos hA hD

/-- Multiplicativity of the canonical block-diagonal Berezinian. -/
theorem canonicalBerezinian_mul
    (A₁ A₂ D₁ D₂ : Block)
    (hD₁ : Matrix.det D₁ ≠ 0) (hD₂ : Matrix.det D₂ ≠ 0) :
    canonicalBerezinian (A₁ * A₂) (D₁ * D₂) =
      canonicalBerezinian A₁ D₁ * canonicalBerezinian A₂ D₂ := by
  simp only [canonicalBerezinian, Matrix.det_mul]
  field_simp [hD₁, hD₂]
  ring

/-- Ordinary bosonic log-determinant barrier. -/
def bosonicDetBarrier (A : Block) : ℝ :=
  -Real.log (Matrix.det A)

/-- Graded log-volume barrier `-log Ber`. -/
def superBerezinianBarrier (A D : Block) : ℝ :=
  -Real.log (canonicalBerezinian A D)

/-- Exact boson/fermion sign split of the graded barrier. -/
theorem superBerezinianBarrier_split
    (A D : Block)
    (hA : Matrix.det A ≠ 0) (hD : Matrix.det D ≠ 0) :
    superBerezinianBarrier A D =
      -Real.log (Matrix.det A) + Real.log (Matrix.det D) := by
  rw [superBerezinianBarrier, canonicalBerezinian,
    Real.log_div hA hD]
  ring

/-- Equivalent formulation: the super-barrier is the bosonic barrier of the
even block minus the bosonic barrier of the odd block. -/
theorem superBerezinianBarrier_eq_bosonic_sub_fermionic
    (A D : Block)
    (hA : Matrix.det A ≠ 0) (hD : Matrix.det D ≠ 0) :
    superBerezinianBarrier A D =
      bosonicDetBarrier A - bosonicDetBarrier D := by
  rw [superBerezinianBarrier_split A D hA hD]
  simp [bosonicDetBarrier]
  ring

/-- A balanced even/odd determinant gives unit Berezinian. -/
theorem canonicalBerezinian_eq_one_of_det_eq
    (A D : Block) (hdet : Matrix.det A = Matrix.det D)
    (hD : Matrix.det D ≠ 0) :
    canonicalBerezinian A D = 1 := by
  rw [canonicalBerezinian, hdet]
  exact div_self hD

/-- Exact finite supersymmetric cancellation at equal determinant weight:
`Ber = 1` implies the graded logarithmic barrier is zero. -/
theorem superBerezinianBarrier_zero_of_det_eq
    (A D : Block) (hdet : Matrix.det A = Matrix.det D)
    (hD : Matrix.det D ≠ 0) :
    superBerezinianBarrier A D = 0 := by
  rw [superBerezinianBarrier,
    canonicalBerezinian_eq_one_of_det_eq A D hdet hD]
  simp

/-- Additivity of the graded barrier under block-diagonal multiplication. -/
theorem superBerezinianBarrier_mul
    (A₁ A₂ D₁ D₂ : Block)
    (hA₁ : Matrix.det A₁ ≠ 0) (hA₂ : Matrix.det A₂ ≠ 0)
    (hD₁ : Matrix.det D₁ ≠ 0) (hD₂ : Matrix.det D₂ ≠ 0) :
    superBerezinianBarrier (A₁ * A₂) (D₁ * D₂) =
      superBerezinianBarrier A₁ D₁ + superBerezinianBarrier A₂ D₂ := by
  rw [superBerezinianBarrier_split (A₁ * A₂) (D₁ * D₂)
      (by simpa [Matrix.det_mul] using mul_ne_zero hA₁ hA₂)
      (by simpa [Matrix.det_mul] using mul_ne_zero hD₁ hD₂)]
  rw [Matrix.det_mul, Matrix.det_mul,
    Real.log_mul hA₁ hA₂, Real.log_mul hD₁ hD₂]
  rw [superBerezinianBarrier_split A₁ D₁ hA₁ hD₁,
    superBerezinianBarrier_split A₂ D₂ hA₂ hD₂]
  ring

/-! ## The elementary odd-reflection sign on a 1|1 carrier -/

abbrev OneBlock := Matrix (Fin 1) (Fin 1) ℝ

/-- Identity transformation on the even coordinate. -/
def oddReflectionEven : OneBlock := 1

/-- Sign reversal of the odd coordinate. -/
def oddReflectionOdd : OneBlock := -1

@[simp] theorem oddReflectionEven_det : Matrix.det oddReflectionEven = 1 := by
  simp [oddReflectionEven]

@[simp] theorem oddReflectionOdd_det : Matrix.det oddReflectionOdd = -1 := by
  rw [Matrix.det_fin_one]
  simp [oddReflectionOdd]

/-- Berezinian detects the odd reflection with sign `-1`. -/
theorem oddReflection_berezinian :
    canonicalBerezinian oddReflectionEven oddReflectionOdd = -1 := by
  rw [canonicalBerezinian, oddReflectionEven_det, oddReflectionOdd_det]
  norm_num

/-- Compact finite packet exposing the mathematically certified graded-volume
content without importing stronger geometric interpretations. -/
theorem berezinian_super_barrier_packet
    (A D : Block)
    (hA : Matrix.det A ≠ 0) (hD : Matrix.det D ≠ 0) :
    canonicalBerezinian A D =
        InfoGeometry.NCG.berezinianBlockDiag A D (Matrix.det D)⁻¹ ∧
    superBerezinianBarrier A D =
        -Real.log (Matrix.det A) + Real.log (Matrix.det D) ∧
    oddReflection_berezinian = (-1 : ℝ) := by
  exact ⟨canonicalBerezinian_eq_owner A D,
    superBerezinianBarrier_split A D hA hD,
    oddReflection_berezinian⟩

end InfoGeometry.Canonical.BerezinianSuperBarrierBridge
