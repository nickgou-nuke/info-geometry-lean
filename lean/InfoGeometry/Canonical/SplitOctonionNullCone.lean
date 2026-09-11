import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ZornMatrixSU3.ZornMatrixCore
import InfoGeometry.OperatorAlgebra.KreinIsotropicCone

/-!
# The split-octonion null cone in Zorn coordinates

This owner records the finite algebraic part of the null-cone story.  It uses
the existing real Zorn matrix carrier and its multiplicative split norm; no
claim about projectivisation, `G₂` or physical particle representations is
made here.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Physics.ZornMatrixSU3
open InfoGeometry.OperatorAlgebra.KreinIsotropicCone

abbrev SplitZornMatrix := ZornMatrix

def splitZornNullCone : Set SplitZornMatrix :=
  {X | norm X = 0}

theorem mem_splitZornNullCone_iff (X : SplitZornMatrix) :
    X ∈ splitZornNullCone ↔ X.a * X.b =
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct X.x X.y := by
  simp [splitZornNullCone, InfoGeometry.Physics.ZornMatrixSU3.norm,
    sub_eq_zero]

theorem splitZornNullCone_closed_under_mul_left
    {X Y : SplitZornMatrix} (hX : X ∈ splitZornNullCone) :
    norm (X * Y) = 0 := by
  rw [InfoGeometry.Physics.ZornMatrixSU3.norm_mul, hX]
  simp

theorem splitZornNullCone_closed_under_mul_right
    {X Y : SplitZornMatrix} (hY : Y ∈ splitZornNullCone) :
    norm (X * Y) = 0 := by
  rw [InfoGeometry.Physics.ZornMatrixSU3.norm_mul, hY]
  simp

/-- The split-octonion null cone is closed under real scalar multiplication. -/
theorem splitZornNullCone_smul
    (r : ℝ) (X : SplitZornMatrix)
    (hX : X ∈ splitZornNullCone) :
    r • X ∈ splitZornNullCone := by
  have hX' : X.a * X.b =
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct X.x X.y := by
    simpa [splitZornNullCone, InfoGeometry.Physics.ZornMatrixSU3.norm, sub_eq_zero]
      using hX
  rw [mem_splitZornNullCone_iff]
  calc
    (r • X).a * (r • X).b = (r * r) * (X.a * X.b) := by
      simp [mul_left_comm, mul_comm]
    _ = (r * r) * InfoGeometry.Physics.ZornMatrixSU3.dotProduct X.x X.y := by
      rw [hX']
    _ = InfoGeometry.Physics.ZornMatrixSU3.dotProduct (r • X).x (r • X).y := by
      rw [show (r • X).x = r • X.x by rfl, show (r • X).y = r • X.y by rfl]
      rw [InfoGeometry.Physics.ZornMatrixSU3.dotProduct_smul_left,
        InfoGeometry.Physics.ZornMatrixSU3.dotProduct_smul_right]
      ring

/--
A representative on the same projective ray as a null split-octonion
remains null.
-/
theorem splitZornNullCone_of_sameProjectiveRay
    {X Y : SplitZornMatrix}
    (hXY : SameProjectiveRay X Y)
    (hX : X ∈ splitZornNullCone) :
    Y ∈ splitZornNullCone := by
  rcases hXY with ⟨r, hr, rfl⟩
  exact splitZornNullCone_smul r X hX

def upperNull (u : Fin 3 → ℝ) : SplitZornMatrix :=
  { a := 0, b := 0, x := u, y := 0 }

def lowerNull (v : Fin 3 → ℝ) : SplitZornMatrix :=
  { a := 0, b := 0, x := 0, y := v }

@[simp] theorem upperNull_mem (u : Fin 3 → ℝ) :
    upperNull u ∈ splitZornNullCone := by
  change (0 : ℝ) * 0 -
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct u (fun _ => 0) = 0
  rw [InfoGeometry.Physics.ZornMatrixSU3.dotProduct_zero_right]
  norm_num

@[simp] theorem lowerNull_mem (v : Fin 3 → ℝ) :
    lowerNull v ∈ splitZornNullCone := by
  change (0 : ℝ) * 0 -
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct (fun _ => 0) v = 0
  rw [InfoGeometry.Physics.ZornMatrixSU3.dotProduct_zero_left]
  norm_num

@[simp] theorem upperNull_sq (u : Fin 3 → ℝ) :
    upperNull u * upperNull u = 0 := by
  apply InfoGeometry.Physics.ZornMatrixSU3.ext
  · change (0 : ℝ) * 0 +
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct u (fun _ => 0) = 0
    rw [InfoGeometry.Physics.ZornMatrixSU3.dotProduct_zero_right]
    norm_num
  · change (0 : ℝ) * 0 +
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct (fun _ => 0) u = 0
    rw [InfoGeometry.Physics.ZornMatrixSU3.dotProduct_zero_left]
    norm_num
  · simp [upperNull]
  · simp [upperNull]

@[simp] theorem lowerNull_sq (v : Fin 3 → ℝ) :
    lowerNull v * lowerNull v = 0 := by
  apply InfoGeometry.Physics.ZornMatrixSU3.ext
  · change (0 : ℝ) * 0 +
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct (fun _ => 0) v = 0
    rw [InfoGeometry.Physics.ZornMatrixSU3.dotProduct_zero_left]
    norm_num
  · change (0 : ℝ) * 0 +
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct v (fun _ => 0) = 0
    rw [InfoGeometry.Physics.ZornMatrixSU3.dotProduct_zero_right]
    norm_num
  · simp [lowerNull]
  · simp [lowerNull]

theorem upperNull_ne_zero {u : Fin 3 → ℝ} (hu : u ≠ 0) :
    upperNull u ≠ 0 := by
  intro h
  apply hu
  funext i
  have hi := congrArg (fun Z : SplitZornMatrix => Z.x i) h
  simpa [upperNull] using hi

theorem lowerNull_ne_zero {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    lowerNull v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi := congrArg (fun Z : SplitZornMatrix => Z.y i) h
  simpa [lowerNull] using hi

def standardColourVector : Fin 3 → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 0

theorem standardColourVector_ne_zero :
    standardColourVector ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [standardColourVector] at h0

theorem standardUpperNull_ne_zero :
    upperNull standardColourVector ≠ 0 :=
  upperNull_ne_zero standardColourVector_ne_zero

end InfoGeometry.Canonical
