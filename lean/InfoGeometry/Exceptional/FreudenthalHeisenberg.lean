import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Exceptional.Freudenthal

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

open FreudenthalCharge

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- The positive (or negative) Heisenberg sector attached to a concrete
Freudenthal symplectic datum.  The second component is the central grade `±2`
direction. -/
abbrev FreudenthalHeisenberg (D : CubicJordanDatum J) :=
  FreudenthalCharge J × ℝ

/-- The Heisenberg bracket determined by the Freudenthal alternating form:
`[(X,a),(Y,b)] = (0, Ω(X,Y))`. -/
def heisenbergBracket (D : CubicJordanDatum J)
    (P Q : FreudenthalHeisenberg D) : FreudenthalHeisenberg D :=
  (0, symplecticForm D P.1 Q.1)

instance (D : CubicJordanDatum J) :
    Bracket (FreudenthalHeisenberg D) (FreudenthalHeisenberg D) where
  bracket := heisenbergBracket D

@[simp] theorem heisenbergBracket_apply
    (D : CubicJordanDatum J) (P Q : FreudenthalHeisenberg D) :
    ⁅P, Q⁆ = (0, symplecticForm D P.1 Q.1) :=
  rfl

@[simp] theorem heisenbergBracket_charge
    (D : CubicJordanDatum J) (P Q : FreudenthalHeisenberg D) :
    (⁅P, Q⁆ : FreudenthalHeisenberg D).1 = 0 :=
  rfl

@[simp] theorem heisenbergBracket_center
    (D : CubicJordanDatum J) (P Q : FreudenthalHeisenberg D) :
    (⁅P, Q⁆ : FreudenthalHeisenberg D).2 = symplecticForm D P.1 Q.1 :=
  rfl

/-- The central grade direction. -/
def heisenbergCenter (D : CubicJordanDatum J) (r : ℝ) :
    FreudenthalHeisenberg D :=
  (0, r)

@[simp] theorem heisenbergCenter_bracket_left
    (D : CubicJordanDatum J) (r : ℝ) (P : FreudenthalHeisenberg D) :
    ⁅heisenbergCenter D r, P⁆ = 0 := by
  ext <;> simp [heisenbergCenter, heisenbergBracket_apply, symplecticForm]

@[simp] theorem heisenbergCenter_bracket_right
    (D : CubicJordanDatum J) (r : ℝ) (P : FreudenthalHeisenberg D) :
    ⁅P, heisenbergCenter D r⁆ = 0 := by
  ext <;> simp [heisenbergCenter, heisenbergBracket_apply, symplecticForm]

/-- The Freudenthal Heisenberg central extension is a genuine Lie ring. -/
instance (D : CubicJordanDatum J) : LieRing (FreudenthalHeisenberg D) where
  add_lie P Q S := by
    ext
    · rfl
    · change symplecticForm D (P.1 + Q.1) S.1 =
        symplecticForm D P.1 S.1 + symplecticForm D Q.1 S.1
      exact LinearMap.add_apply (symplecticFormLinear D) P.1 Q.1 S.1
  lie_add P Q S := by
    ext
    · rfl
    · change symplecticForm D P.1 (Q.1 + S.1) =
        symplecticForm D P.1 Q.1 + symplecticForm D P.1 S.1
      exact (symplecticFormLinear D P.1).map_add Q.1 S.1
  lie_self P := by
    ext
    · rfl
    · exact symplectic_form_alternating D P.1
  leibniz_lie P Q S := by
    ext
    · rfl
    · simp [heisenbergBracket_apply, symplecticForm]

/-- The central extension bracket is real bilinear, hence a genuine real Lie
algebra. -/
instance (D : CubicJordanDatum J) : LieAlgebra ℝ (FreudenthalHeisenberg D) where
  lie_smul r P Q := by
    ext
    · rfl
    · change symplecticForm D (r • P.1) Q.1 =
        r • symplecticForm D P.1 Q.1
      exact congrArg (fun f : FreudenthalCharge J →ₗ[ℝ] ℝ => f Q.1)
        ((symplecticFormLinear D).map_smul r P.1)

/-- The grade-`±1` bracket lands exactly in the one-dimensional central
`±2` direction. -/
theorem bracket_eq_center
    (D : CubicJordanDatum J) (P Q : FreudenthalHeisenberg D) :
    ⁅P, Q⁆ = heisenbergCenter D (symplecticForm D P.1 Q.1) :=
  rfl

/-- The Heisenberg algebra is two-step nilpotent: every iterated bracket of
length three vanishes. -/
theorem heisenberg_two_step_nilpotent
    (D : CubicJordanDatum J) (P Q S : FreudenthalHeisenberg D) :
    ⁅P, ⁅Q, S⁆⁆ = 0 := by
  rw [bracket_eq_center]
  exact heisenbergCenter_bracket_right D _ P

end InfoGeometry.Exceptional.Freudenthal
