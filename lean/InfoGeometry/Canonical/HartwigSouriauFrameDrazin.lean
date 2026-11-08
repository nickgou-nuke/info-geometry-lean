/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Drazin

/-!
# Hartwig 1976: Souriau--Frame coefficients and the Drazin inverse

Source digest:

R. E. Hartwig, "More on the Souriau--Frame Algorithm and the Drazin Inverse",
SIAM Journal on Applied Mathematics 31(1), 42--46, 1976.

The paper uses the Souriau--Frame coefficient matrices from
`adj (lambda I - A)` to obtain formulas for the Drazin inverse and the
principal idempotent.  The Lean-native part formalized here is the strict
algebraic core:

* Hartwig's group inverse laws are exactly the index-one Drazin laws.
* The principal idempotent `1 - A A#` is idempotent and annihilates `A`.
* The group inverse laws are stable under invertible conjugation.
* A rational Souriau--Frame coefficient packet realizes the paper's formula
  `(I - A_0 / a_k) (-A_k / a_k)` for a rank-defective matrix with one zero
  root.

This file intentionally does not formalize the numerical Souriau--Frame
recurrence, field-dependent rank-basis extraction, or floating-point algorithmic
stability.  Those are represented by exact external certificates in `tools/`.
-/

noncomputable section

namespace InfoGeometry.Canonical.HartwigSouriauFrameDrazin

open InfoGeometry.Canonical

abbrev Mat3 (R : Type*) := Matrix (Fin 3) (Fin 3) R

section GroupInverse

variable {R : Type*} [Ring R]

/-- Hartwig/semigroup group inverse laws. -/
def IsGroupInverse (a x : R) : Prop :=
  a * x * a = a ∧ x * a * x = x ∧ a * x = x * a

/-- The regular idempotent attached to a group inverse. -/
def regularIdempotent (a x : R) : R :=
  a * x

/-- Hartwig's principal idempotent for the zero spectral part: `Z = 1 - A A#`. -/
def principalIdempotent (a x : R) : R :=
  1 - regularIdempotent a x

/--
The group inverse equations are equivalent to the repository's Drazin laws at
index one.
-/
theorem groupInverse_iff_drazin_index_one {a x : R} :
    IsGroupInverse a x ↔ InfoGeometry.Canonical.Drazin.IsDrazinInverse a x 1 := by
  constructor
  · intro h
    rcases h with ⟨haxa, hxax, hcomm⟩
    refine InfoGeometry.Canonical.Drazin.IsDrazinInverse.mk hcomm hxax ?_
    calc
      a ^ (1 + 1) * x = a * a * x := by simp [pow_two]
      _ = a * (a * x) := by rw [mul_assoc]
      _ = a * (x * a) := by rw [hcomm]
      _ = a * x * a := by rw [mul_assoc]
      _ = a ^ 1 := by simpa using haxa
  · intro h
    constructor
    · calc
        a * x * a = a * (x * a) := by rw [mul_assoc]
        _ = a * (a * x) := by rw [InfoGeometry.Canonical.Drazin.IsDrazinInverse.comm h]
        _ = a * a * x := by rw [mul_assoc]
        _ = a ^ (1 + 1) * x := by simp [pow_two]
        _ = a := by simpa using InfoGeometry.Canonical.Drazin.IsDrazinInverse.power h
    constructor
    · exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.idempotent h
    · exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.comm h

/-- A group inverse gives an index-one Drazin inverse. -/
theorem IsGroupInverse.toDrazin {a x : R} (h : IsGroupInverse a x) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse a x 1 :=
  groupInverse_iff_drazin_index_one.mp h

/-- An index-one Drazin inverse is a Hartwig group inverse. -/
theorem IsGroupInverse.ofDrazin {a x : R}
    (h : InfoGeometry.Canonical.Drazin.IsDrazinInverse a x 1) :
    IsGroupInverse a x :=
  groupInverse_iff_drazin_index_one.mpr h

/-- The group inverse is unique: the three group-inverse equations are exactly
the repository's index-one Drazin equations, whose inverse is unique. -/
theorem IsGroupInverse.unique {a x y : R}
    (hx : IsGroupInverse a x) (hy : IsGroupInverse a y) : x = y :=
  InfoGeometry.Canonical.Drazin.IsDrazinInverse.unique
    (IsGroupInverse.toDrazin hx) (IsGroupInverse.toDrazin hy)

/-- The regular support `A A#` is idempotent. -/
theorem regularIdempotent_idempotent {a x : R} (h : IsGroupInverse a x) :
    regularIdempotent a x * regularIdempotent a x = regularIdempotent a x := by
  exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_is_idempotent
    (IsGroupInverse.toDrazin h)

/-- Hartwig's principal idempotent `Z = 1 - A A#` is idempotent. -/
theorem principalIdempotent_idempotent {a x : R} (h : IsGroupInverse a x) :
    principalIdempotent a x * principalIdempotent a x = principalIdempotent a x := by
  exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_is_idempotent
    (IsGroupInverse.toDrazin h)

/-- The principal idempotent is the Drazin complementary projector. -/
theorem principalIdempotent_eq_drazin_complement {a x : R} :
    principalIdempotent a x =
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a x :=
  rfl

/-- `A` kills the zero-root principal idempotent on the left. -/
theorem mul_principalIdempotent_eq_zero {a x : R} (h : IsGroupInverse a x) :
    a * principalIdempotent a x = 0 := by
  rcases h with ⟨haxa, _, hcomm⟩
  have hpow : a * a * x = a := by
    calc
      a * a * x = a * (a * x) := by rw [mul_assoc]
      _ = a * (x * a) := by rw [hcomm]
      _ = a * x * a := by rw [mul_assoc]
      _ = a := haxa
  calc
    a * principalIdempotent a x = a * (1 - a * x) := rfl
    _ = a - a * (a * x) := by rw [mul_sub, mul_one]
    _ = a - a * a * x := by rw [mul_assoc]
    _ = 0 := by rw [hpow, sub_self]

/-- The zero-root principal idempotent kills `A` on the right. -/
theorem principalIdempotent_mul_eq_zero {a x : R} (h : IsGroupInverse a x) :
    principalIdempotent a x * a = 0 := by
  rcases h with ⟨haxa, _, _⟩
  calc
    principalIdempotent a x * a = (1 - a * x) * a := rfl
    _ = a - a * x * a := by rw [sub_mul, one_mul]
    _ = 0 := by rw [haxa, sub_self]

/-- The group-inverse shift obtained by adding its zero-root projector. -/
def groupInverseShift (a x : R) : R :=
  x + principalIdempotent a x

/-- The inverse candidate, formed from the original operator and the same projector. -/
def groupInverseShiftInverse (a x : R) : R :=
  a + principalIdempotent a x

private theorem groupInverse_mul_principalIdempotent_eq_zero {a x : R}
    (h : IsGroupInverse a x) : x * principalIdempotent a x = 0 := by
  rcases h with ⟨_, hxax, _⟩
  change x * (1 - a * x) = 0
  rw [mul_sub, mul_one, ← mul_assoc, hxax, sub_self]

private theorem principalIdempotent_mul_groupInverse_eq_zero {a x : R}
    (h : IsGroupInverse a x) : principalIdempotent a x * x = 0 := by
  rcases h with ⟨_, hxax, hcomm⟩
  change (1 - a * x) * x = 0
  rw [sub_mul, one_mul]
  have hax2 : a * x * x = x := by
    calc
      a * x * x = x * a * x := by rw [← hcomm]
      _ = x := hxax
  rw [hax2, sub_self]

/-- The shifted group inverse `x + (1 - a*x)` has right inverse `a + (1 - a*x)`.

This is a purely algebraic identity and makes no Markov-chain claim. -/
theorem groupInverseShift_mul_inverse {a x : R}
    (h : IsGroupInverse a x) :
    groupInverseShift a x * groupInverseShiftInverse a x = 1 := by
  have hE2 := principalIdempotent_idempotent h
  have hsum : a * x + principalIdempotent a x = 1 := by
    change a * x + (1 - a * x) = 1
    noncomm_ring
  unfold groupInverseShift groupInverseShiftInverse
  calc
    (x + principalIdempotent a x) * (a + principalIdempotent a x)
        = x * a + x * principalIdempotent a x +
          (principalIdempotent a x * a +
            principalIdempotent a x * principalIdempotent a x) := by
              noncomm_ring
    _ = x * a + principalIdempotent a x := by
          rw [groupInverse_mul_principalIdempotent_eq_zero h,
            principalIdempotent_mul_eq_zero h, hE2]
          simp
    _ = a * x + principalIdempotent a x := by
          rw [(h.2.2).symm]
    _ = 1 := hsum

/-- The shifted group inverse `x + (1 - a*x)` has left inverse `a + (1 - a*x)`. -/
theorem groupInverseShift_inverse_mul {a x : R}
    (h : IsGroupInverse a x) :
    groupInverseShiftInverse a x * groupInverseShift a x = 1 := by
  have hE2 := principalIdempotent_idempotent h
  have hsum : a * x + principalIdempotent a x = 1 := by
    change a * x + (1 - a * x) = 1
    noncomm_ring
  unfold groupInverseShift groupInverseShiftInverse
  calc
    (a + principalIdempotent a x) * (x + principalIdempotent a x)
        = a * x + a * principalIdempotent a x +
          (principalIdempotent a x * x +
            principalIdempotent a x * principalIdempotent a x) := by
              noncomm_ring
    _ = a * x + principalIdempotent a x := by
          rw [mul_principalIdempotent_eq_zero h,
            principalIdempotent_mul_groupInverse_eq_zero h, hE2]
          simp
    _ = 1 := hsum

/-- Invertible conjugation action. -/
def unitConj {R : Type*} [Monoid R] (u : Rˣ) (a : R) : R :=
  (u : R) * a * ((u⁻¹ : Rˣ) : R)

/-- Hartwig group inverse witnesses are stable under unit conjugation. -/
theorem groupInverse_unitConj {a x : R} (h : IsGroupInverse a x) (u : Rˣ) :
    IsGroupInverse (unitConj u a) (unitConj u x) := by
  rcases h with ⟨haxa, hxax, hcomm⟩
  constructor
  · calc
      unitConj u a * unitConj u x * unitConj u a
          = (u : R) * (a * x * a) * ((u⁻¹ : Rˣ) : R) := by
              simp [unitConj, mul_assoc]
      _ = unitConj u a := by simp [unitConj, haxa]
  constructor
  · calc
      unitConj u x * unitConj u a * unitConj u x
          = (u : R) * (x * a * x) * ((u⁻¹ : Rˣ) : R) := by
              simp [unitConj, mul_assoc]
      _ = unitConj u x := by simp [unitConj, hxax]
  · calc
      unitConj u a * unitConj u x
          = (u : R) * (a * x) * ((u⁻¹ : Rˣ) : R) := by
              simp [unitConj, mul_assoc]
      _ = (u : R) * (x * a) * ((u⁻¹ : Rˣ) : R) := by rw [hcomm]
      _ = unitConj u x * unitConj u a := by
              simp [unitConj, mul_assoc]

end GroupInverse

section RationalSouriauFramePacket

/-! ## Exact rational readout of Hartwig's formula (13) -/

/-- Two matrix units used to make the noncommutative `Mat3 ℚ` carrier explicit. -/
def matrixUnit01 : Mat3 ℚ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

/-- The transposed matrix unit to `matrixUnit01`. -/
def matrixUnit10 : Mat3 ℚ := !![0, 0, 0; 1, 0, 0; 0, 0, 0]

/-- These matrix units do not commute: their products are distinct diagonal units. -/
theorem mat3_noncommutativity_witness :
    matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01 := by
  intro h
  have h00 := congrArg (fun M : Mat3 ℚ => M 0 0) h
  norm_num [matrixUnit01, matrixUnit10, Matrix.mul_apply, Fin.sum_univ_succ] at h00

/-- A simple singular matrix with one zero root and regular eigenvalues `2,3`. -/
def hartwigA : Mat3 ℚ :=
  !![0, 0, 0;
     0, 2, 0;
     0, 0, 3]

/-- Constant coefficient matrix `A₀` in `adj(lambda I - A)`. -/
def hartwigAdjCoeff0 : Mat3 ℚ :=
  !![6, 0, 0;
     0, 0, 0;
     0, 0, 0]

/-- Linear coefficient matrix `A₁` in `adj(lambda I - A)`. -/
def hartwigAdjCoeff1 : Mat3 ℚ :=
  !![-5, 0, 0;
     0, -3, 0;
     0, 0, -2]

/-- Hartwig formula `(I - A₀/aₖ)(-Aₖ/aₖ)` for `aₖ = 6`. -/
def hartwigFormulaCandidate : Mat3 ℚ :=
  (1 - ((1 / 6 : ℚ) • hartwigAdjCoeff0)) *
    ((-1 / 6 : ℚ) • hartwigAdjCoeff1)

/-- Expected group inverse: zero on the nilpotent block, ordinary inverse on the regular block. -/
def hartwigExpectedGroupInverse : Mat3 ℚ :=
  !![0, 0, 0;
     0, 1 / 2, 0;
     0, 0, 1 / 3]

/-- The finite Souriau--Frame coefficient formula produces the expected group inverse. -/
theorem hartwig_formula_candidate_eq_expected :
    hartwigFormulaCandidate = hartwigExpectedGroupInverse := by
  native_decide

/-- Hartwig's formula satisfies the group inverse equations for the packet. -/
theorem hartwig_formula_candidate_isGroupInverse :
    IsGroupInverse hartwigA hartwigFormulaCandidate := by
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide

/-- Therefore the same formula is the index-one Drazin inverse. -/
theorem hartwig_formula_candidate_isDrazinInverse :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse hartwigA hartwigFormulaCandidate 1 :=
  IsGroupInverse.toDrazin hartwig_formula_candidate_isGroupInverse

/-- The regular idempotent `A A#` selects the regular `2,3` eigenspaces. -/
theorem hartwig_regular_idempotent_readout :
    regularIdempotent hartwigA hartwigFormulaCandidate =
      !![0, 0, 0;
         0, 1, 0;
         0, 0, 1] := by
  native_decide

/-- The principal idempotent `Z = I - A A#` selects the zero-root lane. -/
theorem hartwig_principal_idempotent_readout :
    principalIdempotent hartwigA hartwigFormulaCandidate =
      !![1, 0, 0;
         0, 0, 0;
         0, 0, 0] := by
  native_decide

/-- The zero-root principal idempotent is killed by `A` on the left. -/
theorem hartwig_mul_principal_idempotent_eq_zero :
    hartwigA * principalIdempotent hartwigA hartwigFormulaCandidate = 0 := by
  native_decide

/-- The zero-root principal idempotent is killed by `A` on the right. -/
theorem hartwig_principal_idempotent_mul_eq_zero :
    principalIdempotent hartwigA hartwigFormulaCandidate * hartwigA = 0 := by
  native_decide

end RationalSouriauFramePacket

end InfoGeometry.Canonical.HartwigSouriauFrameDrazin
