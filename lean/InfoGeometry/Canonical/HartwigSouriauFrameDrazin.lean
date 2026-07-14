import Mathlib
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

namespace HartwigSouriauFrameDrazin

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
    IsGroupInverse a x ↔ Drazin.IsDrazinInverse a x 1 := by
  constructor
  · intro h
    rcases h with ⟨haxa, hxax, hcomm⟩
    refine Drazin.IsDrazinInverse.mk hcomm hxax ?_
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
        _ = a * (a * x) := by rw [h.comm]
        _ = a * a * x := by rw [mul_assoc]
        _ = a ^ (1 + 1) * x := by simp [pow_two]
        _ = a := by simpa using h.power
    constructor
    · exact h.idempotent
    · exact h.comm

/-- A group inverse gives an index-one Drazin inverse. -/
theorem IsGroupInverse.toDrazin {a x : R} (h : IsGroupInverse a x) :
    Drazin.IsDrazinInverse a x 1 :=
  groupInverse_iff_drazin_index_one.mp h

/-- An index-one Drazin inverse is a Hartwig group inverse. -/
theorem IsGroupInverse.ofDrazin {a x : R}
    (h : Drazin.IsDrazinInverse a x 1) :
    IsGroupInverse a x :=
  groupInverse_iff_drazin_index_one.mpr h

/-- The regular support `A A#` is idempotent. -/
theorem regularIdempotent_idempotent {a x : R} (h : IsGroupInverse a x) :
    regularIdempotent a x * regularIdempotent a x = regularIdempotent a x := by
  exact Drazin.IsDrazinInverse.projection_is_idempotent h.toDrazin

/-- Hartwig's principal idempotent `Z = 1 - A A#` is idempotent. -/
theorem principalIdempotent_idempotent {a x : R} (h : IsGroupInverse a x) :
    principalIdempotent a x * principalIdempotent a x = principalIdempotent a x := by
  exact Drazin.IsDrazinInverse.complementaryProjection_is_idempotent h.toDrazin

/-- The principal idempotent is the Drazin complementary projector. -/
theorem principalIdempotent_eq_drazin_complement {a x : R} :
    principalIdempotent a x =
      Drazin.IsDrazinInverse.complementaryProjection a x :=
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
    Drazin.IsDrazinInverse hartwigA hartwigFormulaCandidate 1 :=
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

end HartwigSouriauFrameDrazin
