/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorContentNetwork.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Combinatorics.Quiver.Path

/-!
# Ordered operator transport on native quiver paths

Edges carry arbitrary real square matrices. Path transport multiplies their
labels in path order. Vertex units act by endpoint changes of frame, so a
parallel-path defect transforms by the same two-sided action. No commutation
of edge labels or vertex units is assumed.
Products follow the left-to-right word convention, or equivalently row action.

This is a theorem layer for arbitrary quivers and their native `Quiver.Path`;
it does not identify compiler information trees with a newly defined carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorContentNetwork

abbrev EdgeLabelling (V n : Type*) [Quiver V] :=
  ∀ {a b : V}, (a ⟶ b) → Operator n

variable {V n : Type*} [Quiver V] [Fintype n] [DecidableEq n]

/-- The ordered product of edge operators, with the identity on an empty path. -/
def pathTransport (L : EdgeLabelling V n) {a : V} :
    ∀ {b : V}, Quiver.Path a b → Operator n
  | _, .nil => 1
  | _, .cons p e => pathTransport L p * L e

@[simp] theorem pathTransport_nil (L : EdgeLabelling V n) (a : V) :
    pathTransport L (.nil : Quiver.Path a a) = 1 := rfl

@[simp] theorem pathTransport_cons (L : EdgeLabelling V n) {a b c : V}
    (p : Quiver.Path a b) (e : b ⟶ c) :
    pathTransport L (p.cons e) = pathTransport L p * L e := rfl

@[simp] theorem pathTransport_single (L : EdgeLabelling V n) {a b : V}
    (e : a ⟶ b) : pathTransport L e.toPath = L e := by
  simp [Quiver.Hom.toPath, pathTransport]

theorem pathTransport_comp (L : EdgeLabelling V n) {a b c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    pathTransport L (p.comp q) = pathTransport L p * pathTransport L q := by
  induction q with
  | nil => simp
  | cons q e ih =>
    simp only [Quiver.Path.comp_cons, pathTransport_cons, ih, mul_assoc]

/-- A change of frame at each vertex, with its inverse at the target vertex. -/
def gaugeLabel (G : V → (Operator n)ˣ) (L : EdgeLabelling V n) : EdgeLabelling V n :=
  fun {a b} e => (G a : Operator n) * L e * ↑((G b)⁻¹)

@[simp] theorem gaugeLabel_one (L : EdgeLabelling V n) :
    (gaugeLabel (fun _ => 1) L : EdgeLabelling V n) = (L : EdgeLabelling V n) := by
  funext a b e
  simp [gaugeLabel]

/-- Changes of frame compose in the same ordered unit group as the matrices. -/
theorem gaugeLabel_comp (G H : V → (Operator n)ˣ) (L : EdgeLabelling V n) :
    (gaugeLabel H (gaugeLabel G L) : EdgeLabelling V n) =
      (gaugeLabel (fun a => H a * G a) L : EdgeLabelling V n) := by
  funext a b e
  simp [gaugeLabel, mul_inv_rev, mul_assoc]

@[simp] theorem gaugeLabel_inverse (G : V → (Operator n)ˣ) (L : EdgeLabelling V n) :
    (gaugeLabel (fun a => (G a)⁻¹) (gaugeLabel G L) : EdgeLabelling V n) =
      (L : EdgeLabelling V n) := by
  rw [gaugeLabel_comp]
  simp

/-- All internal changes of frame cancel, leaving only the path endpoints. -/
theorem pathTransport_gaugeLabel (G : V → (Operator n)ˣ) (L : EdgeLabelling V n)
    {a b : V} (p : Quiver.Path a b) :
    pathTransport (gaugeLabel G L) p =
      (G a : Operator n) * pathTransport L p * ↑((G b)⁻¹) := by
  induction p with
  | nil => simp only [pathTransport_nil, mul_one, Units.mul_inv]
  | cons p e ih =>
    simp only [pathTransport_cons, ih, gaugeLabel, mul_assoc, Units.inv_mul_cancel_left]

/-- The obstruction to two parallel paths having the same operator transport. -/
def pathDefect (L : EdgeLabelling V n) {a b : V} (p q : Quiver.Path a b) : Operator n :=
  pathTransport L p - pathTransport L q

@[simp] theorem pathDefect_self (L : EdgeLabelling V n) {a b : V}
    (p : Quiver.Path a b) : pathDefect L p p = 0 := by
  simp [pathDefect]

theorem pathDefect_gaugeLabel (G : V → (Operator n)ˣ) (L : EdgeLabelling V n)
    {a b : V} (p q : Quiver.Path a b) :
    pathDefect (gaugeLabel G L) p q =
      (G a : Operator n) * pathDefect L p q * ↑((G b)⁻¹) := by
  simp only [pathDefect, pathTransport_gaugeLabel, mul_sub, sub_mul]

theorem pathTransport_gauge_eq_iff (G : V → (Operator n)ˣ) (L : EdgeLabelling V n)
    {a b : V} (p q : Quiver.Path a b) :
    pathTransport (gaugeLabel G L) p = pathTransport (gaugeLabel G L) q ↔
      pathTransport L p = pathTransport L q := by
  rw [pathTransport_gaugeLabel, pathTransport_gaugeLabel,
    Units.mul_left_inj, Units.mul_right_inj]

theorem pathDefect_gauge_eq_zero_iff (G : V → (Operator n)ˣ) (L : EdgeLabelling V n)
    {a b : V} (p q : Quiver.Path a b) :
    pathDefect (gaugeLabel G L) p q = 0 ↔ pathDefect L p q = 0 := by
  simp only [pathDefect, sub_eq_zero, pathTransport_gauge_eq_iff]

theorem pathDefect_gauge_ne_zero_iff (G : V → (Operator n)ˣ) (L : EdgeLabelling V n)
    {a b : V} (p q : Quiver.Path a b) :
    pathDefect (gaugeLabel G L) p q ≠ 0 ↔ pathDefect L p q ≠ 0 :=
  not_congr (pathDefect_gauge_eq_zero_iff G L p q)

/-- Edge labels induced by a single unit-valued potential on the vertices. -/
def potentialLabel (G : V → (Operator n)ˣ) : EdgeLabelling V n :=
  fun {a b} _ => (↑((G a)⁻¹) : Operator n) * G b

/-- Transport of a potential labelling depends only on its endpoints. -/
theorem pathTransport_potentialLabel (G : V → (Operator n)ˣ) {a b : V}
    (p : Quiver.Path a b) :
    pathTransport (potentialLabel G) p = (↑((G a)⁻¹) : Operator n) * G b := by
  induction p with
  | nil => simp only [pathTransport_nil, Units.inv_mul]
  | cons p e ih =>
    simp only [pathTransport_cons, ih, potentialLabel, mul_assoc, Units.mul_inv_cancel_left]

theorem potentialLabel_path_independent (G : V → (Operator n)ˣ) {a b : V}
    (p q : Quiver.Path a b) :
    pathTransport (potentialLabel G) p = pathTransport (potentialLabel G) q := by
  rw [pathTransport_potentialLabel, pathTransport_potentialLabel]

@[simp] theorem pathDefect_potentialLabel (G : V → (Operator n)ˣ) {a b : V}
    (p q : Quiver.Path a b) : pathDefect (potentialLabel G) p q = 0 := by
  rw [pathDefect, potentialLabel_path_independent G p q, sub_self]

@[simp] theorem potentialLabel_loop (G : V → (Operator n)ˣ) {a : V}
    (p : Quiver.Path a a) : pathTransport (potentialLabel G) p = 1 := by
  rw [pathTransport_potentialLabel, Units.inv_mul]

/-- A change of frame preserves the class of potential-induced edge labellings. -/
theorem gaugeLabel_potentialLabel (G H : V → (Operator n)ˣ) :
    (gaugeLabel H (potentialLabel G) : EdgeLabelling V n) =
      (potentialLabel (fun a => G a * (H a)⁻¹) : EdgeLabelling V n) := by
  funext a b e
  simp [gaugeLabel, potentialLabel, mul_inv_rev, mul_assoc]

end InfoGeometry.Canonical.OperatorContentNetwork
