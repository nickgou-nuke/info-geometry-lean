import InfoGeometry.Tessellation.Incidence

/-!
# Tessellation Wilson loops

This file contains the minimal supported-holonomy Wilson loop layer.

It deliberately does not implement path calculus, composability of arrows,
cyclic cohomology, current algebras, or `H^3` gluing.  A later typed path
calculus can be built over a quiver/indexed-arrow API.
-/

namespace InfoGeometry.Tessellation

/--
A Wilson loop at a base idempotent sector.

The holonomy is supported on the base sector on both sides.  This is the
minimal loop readout used before any typed path calculus is introduced.
-/
structure WilsonLoop (A : Type*) [Semiring A] (base : Diamond A) where
  /-- Loop holonomy at the base sector. -/
  holonomy : A
  /-- Left support at the base sector. -/
  left_support : base.P * holonomy = holonomy
  /-- Right support at the base sector. -/
  right_support : holonomy * base.P = holonomy

/-- The Wilson loop defect: holonomy minus the base idempotent. -/
def WilsonLoop.defect {A : Type*} [Ring A] {base : Diamond A}
    (L : WilsonLoop A base) : A :=
  L.holonomy - base.P

/-- A Wilson loop is flat when its holonomy is the base idempotent. -/
def WilsonLoop.Flat {A : Type*} [Semiring A] {base : Diamond A}
    (L : WilsonLoop A base) : Prop :=
  L.holonomy = base.P

/-- Vanishing defect is equivalent to flatness. -/
theorem WilsonLoop.defect_eq_zero_iff_flat
    {A : Type*} [Ring A] {base : Diamond A}
    (L : WilsonLoop A base) :
    WilsonLoop.defect L = 0 ↔ WilsonLoop.Flat L := by
  simp [WilsonLoop.defect, WilsonLoop.Flat, sub_eq_zero]

/-- Flat loops have zero defect. -/
theorem WilsonLoop.defect_eq_zero_of_flat
    {A : Type*} [Ring A] {base : Diamond A}
    {L : WilsonLoop A base} (hL : L.Flat) :
    WilsonLoop.defect L = 0 :=
  (L.defect_eq_zero_iff_flat).2 hL

/-- A zero-defect loop is flat. -/
theorem WilsonLoop.flat_of_defect_eq_zero
    {A : Type*} [Ring A] {base : Diamond A}
    {L : WilsonLoop A base} (hL : WilsonLoop.defect L = 0) :
    L.Flat :=
  (L.defect_eq_zero_iff_flat).1 hL

end InfoGeometry.Tessellation
