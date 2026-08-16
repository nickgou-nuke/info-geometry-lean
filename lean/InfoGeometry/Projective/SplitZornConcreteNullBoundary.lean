import InfoGeometry.Projective.NullBoundary
import InfoGeometry.Canonical.SplitZornNullBoundary

/-!
# Concrete split-Zorn projective null boundary

This is a carrier-specific adapter from the native seven-coordinate Zorn cell
owner to the generic projective-null quotient.  It does not introduce a new
Zorn product or identify this carrier with the other Zorn-cell owners.

The canonical top-right square-zero cell is promoted to an actual nonzero
projective null representative and hence to a projective null boundary point.
-/

open scoped Classical

namespace InfoGeometry.Projective.SplitZornConcreteNullBoundary

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
open InfoGeometry.Canonical.SplitZornNullBoundary
open InfoGeometry.Projective.ProjectiveNullBoundaryDatum

abbrev Cell := ZornCell ℝ

def scaleCell (u : ℝˣ) (X : Cell) : Cell where
  r := (u : ℝ) * X.r
  s := (u : ℝ) * X.s
  x1 := (u : ℝ) * X.x1
  x2 := (u : ℝ) * X.x2
  x3 := (u : ℝ) * X.x3
  y1 := (u : ℝ) * X.y1
  y2 := (u : ℝ) * X.y2
  y3 := (u : ℝ) * X.y3

@[simp] theorem scaleCell_one (X : Cell) :
    scaleCell 1 X = X := by
  cases X <;> simp [scaleCell]

theorem scaleCell_mul (u v : ℝˣ) (X : Cell) :
    scaleCell (u * v) X = scaleCell u (scaleCell v X) := by
  cases X <;> simp [scaleCell, mul_assoc]

theorem detZ_scaleCell (u : ℝˣ) (X : Cell) :
    detZ (scaleCell u X) = (u : ℝ) * (u : ℝ) * detZ X := by
  cases X <;> simp [scaleCell, detZ, mul_add, sub_eq_add_neg]
  ring

theorem detZ_scaleCell_zero (u : ℝˣ) (X : Cell) :
    detZ (scaleCell u X) = 0 ↔ detZ X = 0 := by
  rw [detZ_scaleCell]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact False.elim ((Units.ne_zero u) h)
      · exact False.elim ((Units.ne_zero u) h)
    · exact h
  · intro h
    rw [h]
    simp

theorem scaleCell_ne_zero (u : ℝˣ) (X : Cell) :
    X ≠ (zornZero : Cell) → scaleCell u X ≠ (zornZero : Cell) := by
  intro hX hscaled
  apply hX
  cases X with
  | mk r s x1 x2 x3 y1 y2 y3 =>
      have hr : (u : ℝ) * r = 0 := by
        simpa [scaleCell, zornZero] using congrArg ZornCell.r hscaled
      have hs : (u : ℝ) * s = 0 := by
        simpa [scaleCell, zornZero] using congrArg ZornCell.s hscaled
      have hx1 : (u : ℝ) * x1 = 0 := by
        simpa [scaleCell, zornZero] using congrArg ZornCell.x1 hscaled
      have hx2 : (u : ℝ) * x2 = 0 := by
        simpa [scaleCell, zornZero] using congrArg ZornCell.x2 hscaled
      have hx3 : (u : ℝ) * x3 = 0 := by
        simpa [scaleCell, zornZero] using congrArg ZornCell.x3 hscaled
      have hy1 : (u : ℝ) * y1 = 0 := by
        simpa [scaleCell, zornZero] using congrArg ZornCell.y1 hscaled
      have hy2 : (u : ℝ) * y2 = 0 := by
        simpa [scaleCell, zornZero] using congrArg ZornCell.y2 hscaled
      have hy3 : (u : ℝ) * y3 = 0 := by
        simpa [scaleCell, zornZero] using congrArg ZornCell.y3 hscaled
      have hr0 : r = 0 := (mul_eq_zero.mp hr).resolve_left (Units.ne_zero u)
      have hs0 : s = 0 := (mul_eq_zero.mp hs).resolve_left (Units.ne_zero u)
      have hx10 : x1 = 0 := (mul_eq_zero.mp hx1).resolve_left (Units.ne_zero u)
      have hx20 : x2 = 0 := (mul_eq_zero.mp hx2).resolve_left (Units.ne_zero u)
      have hx30 : x3 = 0 := (mul_eq_zero.mp hx3).resolve_left (Units.ne_zero u)
      have hy10 : y1 = 0 := (mul_eq_zero.mp hy1).resolve_left (Units.ne_zero u)
      have hy20 : y2 = 0 := (mul_eq_zero.mp hy2).resolve_left (Units.ne_zero u)
      have hy30 : y3 = 0 := (mul_eq_zero.mp hy3).resolve_left (Units.ne_zero u)
      rw [ZornCell.mk.injEq]
      exact ⟨hr0, hs0, hx10, hx20, hx30, hy10, hy20, hy30⟩

def datum : ProjectiveNullBoundaryDatum ℝ ℝ Cell where
  q := detZ
  zero := (zornZero : Cell)
  scale := scaleCell
  scale_one := scaleCell_one
  scale_mul := scaleCell_mul
  null_scale := detZ_scaleCell_zero
  scale_ne_zero := scaleCell_ne_zero

abbrev NullRep := ProjectiveNullBoundaryDatum.NullRep datum
abbrev Boundary := ProjectiveNullBoundaryDatum.ProjectiveNullBoundary datum

def topRightNullRep : NullRep where
  Z := zornTopRightNull
  null := zornTopRightNull_detZ
  nonzero := zornTopRightNull_ne_zero

def topRightNullPoint : Boundary :=
  ProjectiveNullBoundaryDatum.nullMk datum topRightNullRep

theorem topRightNullPoint_scale_invariant (u : ℝˣ) :
    topRightNullPoint =
      ProjectiveNullBoundaryDatum.nullMk datum
        (ProjectiveNullBoundaryDatum.scaleNull datum u topRightNullRep) :=
  ProjectiveNullBoundaryDatum.nullMk_scaleNull datum u topRightNullRep

theorem topRightNull_has_square_zero_and_projective_point :
    zornTopRightNull * zornTopRightNull = zornZero ∧
      topRightNullPoint =
        ProjectiveNullBoundaryDatum.nullMk datum topRightNullRep := by
  exact ⟨zornTopRightNull_sq_zero, rfl⟩

theorem projective_boundary_nonempty : Nonempty Boundary :=
  ⟨topRightNullPoint⟩

end InfoGeometry.Projective.SplitZornConcreteNullBoundary
