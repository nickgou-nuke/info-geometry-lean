import InfoGeometry.Algebra.Zorn.ConcreteComposition

/-!
# InfoGeometry.Algebra.Zorn.Decomposition

Sector-explicit decomposition for the concrete Zorn cell multiplication.

This file records a two-part algebraic split of `mulZ`:

* `assocMul`: the purely associative-like seed obtained by dropping cross-term
  corrections;
* `teleportMul`: the off-diagonal correction carrying the nonassociative defect.

The central identity is

`X * Y = assocMul X Y + teleportMul X Y`

with `+` realized componentwise via `addZ`.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.ConcreteComposition
namespace ZornCell

variable {R : Type*} [CommRing R]

/-
Elementwise constructor extensionality for concrete Zorn cells.
-/
@[simp] theorem ext_fields {R : Type*} {X Y : ZornCell R}
    (hr : X.r = Y.r)
    (hs : X.s = Y.s)
    (hx1 : X.x1 = Y.x1)
    (hx2 : X.x2 = Y.x2)
    (hx3 : X.x3 = Y.x3)
    (hy1 : X.y1 = Y.y1)
    (hy2 : X.y2 = Y.y2)
    (hy3 : X.y3 = Y.y3) :
    X = Y := by
  cases X
  cases Y
  simp_all

/--
`assocMul` keeps only the diagonal-sector coupling and bilinear scalar actions.
-/
def assocMul (X Y : ZornCell R) : ZornCell R where
  r := X.r * Y.r + (X.x1 * Y.y1 + X.x2 * Y.y2 + X.x3 * Y.y3)
  s := X.s * Y.s + (X.y1 * Y.x1 + X.y2 * Y.x2 + X.y3 * Y.x3)
  x1 := X.r * Y.x1 + Y.s * X.x1
  x2 := X.r * Y.x2 + Y.s * X.x2
  x3 := X.r * Y.x3 + Y.s * X.x3
  y1 := Y.r * X.y1 + X.s * Y.y1
  y2 := Y.r * X.y2 + X.s * Y.y2
  y3 := Y.r * X.y3 + X.s * Y.y3

/--
`teleportMul` is the explicit nonassociative correction term carried by the
vector cross blocks.
-/
def teleportMul (X Y : ZornCell R) : ZornCell R where
  r := 0
  s := 0
  x1 := -(X.y2 * Y.y3 - X.y3 * Y.y2)
  x2 := -(X.y3 * Y.y1 - X.y1 * Y.y3)
  x3 := -(X.y1 * Y.y2 - X.y2 * Y.y1)
  y1 := X.x2 * Y.x3 - X.x3 * Y.x2
  y2 := X.x3 * Y.x1 - X.x1 * Y.x3
  y3 := X.x1 * Y.x2 - X.x2 * Y.x1

/--`X * Y` splits as associative seed plus teleport correction, componentwise.-/
theorem mul_eq_assoc_plus_teleport (X Y : ZornCell R) :
    X * Y = addZ (assocMul X Y) (teleportMul X Y) := by
  change mulZ X Y = addZ (assocMul X Y) (teleportMul X Y)
  refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [mulZ, assocMul, teleportMul, addZ, sub_eq_add_neg, add_assoc]
  ·
    simp [mulZ, assocMul, teleportMul, addZ, sub_eq_add_neg]
    ring
  · simp [mulZ, assocMul, teleportMul, addZ, sub_eq_add_neg, add_assoc]
  · simp [mulZ, assocMul, teleportMul, addZ, sub_eq_add_neg, add_assoc]
  · simp [mulZ, assocMul, teleportMul, addZ, sub_eq_add_neg, add_assoc]
  · simp [mulZ, assocMul, teleportMul, addZ, sub_eq_add_neg, add_assoc]
  · simp [mulZ, assocMul, teleportMul, addZ, sub_eq_add_neg, add_assoc]
  · simp [mulZ, assocMul, teleportMul, addZ, sub_eq_add_neg, add_assoc]

/--
Diagonal sector extraction: drop off-diagonal coordinates.
-/
def diagSector (X : ZornCell R) : ZornCell R where
  r := X.r
  s := X.s
  x1 := 0
  x2 := 0
  x3 := 0
  y1 := 0
  y2 := 0
  y3 := 0

/-- Off-diagonal sector extraction: drop diagonal coordinates.-/
def offDiagSector (X : ZornCell R) : ZornCell R where
  r := 0
  s := 0
  x1 := X.x1
  x2 := X.x2
  x3 := X.x3
  y1 := X.y1
  y2 := X.y2
  y3 := X.y3

/-- Sector decomposition `X = D + N` with componentwise `addZ`.-/
theorem cell_sector_decomposition (X : ZornCell R) :
    X = addZ (diagSector X) (offDiagSector X) := by
  refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [diagSector, offDiagSector, addZ]
  · simp [diagSector, offDiagSector, addZ]
  · simp [diagSector, offDiagSector, addZ]
  · simp [diagSector, offDiagSector, addZ]
  · simp [diagSector, offDiagSector, addZ]
  · simp [diagSector, offDiagSector, addZ]
  · simp [diagSector, offDiagSector, addZ]
  · simp [diagSector, offDiagSector, addZ]

end ZornCell


end InfoGeometry.Algebra.Zorn.ConcreteComposition
