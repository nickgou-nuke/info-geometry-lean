/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Real minitwistors: oriented affine lines and perpendicular representatives

The Euclidean minitwistor carrier is the quotient of a unit direction and a
base point by translation along that direction. The quotient is explicitly
equivalent to unit directions equipped with perpendicular offsets. In real
three-space this is the set-level tangent-sphere description of oriented
lines. Opposite directions remain distinct. No complex coordinates, smooth
tangent-bundle equivalence, holomorphic `O(2)` structure or monopole transform
is asserted by these algebraic and inner-product theorems.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace InfoGeometry.Twistor.RealMiniTwistor

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

abbrev Direction := {u : V // ⟪u, u⟫ = 1}

/-- A direction and the perpendicular, hence canonical, base point. -/
structure PerpendicularLine where
  direction : Direction V
  offset : V
  perpendicular : ⟪direction.val, offset⟫ = 0

variable {V}

@[ext] theorem PerpendicularLine.ext {a b : PerpendicularLine V}
    (hd : a.direction = b.direction) (ho : a.offset = b.offset) : a = b := by
  cases a
  cases b
  cases hd
  cases ho
  rfl

/-- Native orthogonal projection off the chosen unit direction. -/
def perpendicularProjection (u : Direction V) : V →ₗ[ℝ] V where
  toFun x := x - ⟪u.val, x⟫ • u.val
  map_add' x y := by simp [inner_add_right, add_smul]; abel
  map_smul' r x := by simp [real_inner_smul_right, smul_sub, smul_smul]

@[simp] theorem perpendicularProjection_apply (u : Direction V) (x : V) :
    perpendicularProjection u x = x - ⟪u.val, x⟫ • u.val := rfl

@[simp] theorem inner_perpendicularProjection (u : Direction V) (x : V) :
    ⟪u.val, perpendicularProjection u x⟫ = 0 := by
  simp only [perpendicularProjection_apply, inner_sub_right,
    real_inner_smul_right, u.property, mul_one, sub_self]

theorem perpendicularProjection_eq_self (u : Direction V) (x : V)
    (h : ⟪u.val, x⟫ = 0) : perpendicularProjection u x = x := by
  simp [perpendicularProjection, h]

@[simp] theorem perpendicularProjection_idempotent (u : Direction V) (x : V) :
    perpendicularProjection u (perpendicularProjection u x) =
      perpendicularProjection u x := by
  exact perpendicularProjection_eq_self _ _ (inner_perpendicularProjection _ _)

@[simp] theorem perpendicularProjection_add_direction (u : Direction V)
    (x : V) (t : ℝ) :
    perpendicularProjection u (x + t • u.val) = perpendicularProjection u x := by
  simp only [perpendicularProjection_apply, inner_add_right,
    real_inner_smul_right, u.property, mul_one, add_smul]
  abel

/-- Equal perpendicular representatives are exactly changes of base point
along the same oriented line. -/
theorem perpendicularProjection_eq_iff (u : Direction V) (x y : V) :
    perpendicularProjection u x = perpendicularProjection u y ↔
      ∃ t : ℝ, y = x + t • u.val := by
  constructor
  · intro h
    refine ⟨⟪u.val, y⟫ - ⟪u.val, x⟫, ?_⟩
    calc
      y = perpendicularProjection u y + ⟪u.val, y⟫ • u.val := by
        simp [perpendicularProjection]
      _ = perpendicularProjection u x + ⟪u.val, y⟫ • u.val := by rw [h]
      _ = x + (⟪u.val, y⟫ - ⟪u.val, x⟫) • u.val := by
        simp only [perpendicularProjection_apply, sub_smul]
        abel
  · rintro ⟨t, rfl⟩
    exact (perpendicularProjection_add_direction u x t).symm

variable (V)

/-- Translation is quotiented only at a fixed unit direction. -/
def orientedLineSetoid : Setoid (Direction V × V) where
  r p q := p.1 = q.1 ∧
    perpendicularProjection p.1 p.2 = perpendicularProjection q.1 q.2
  iseqv := ⟨fun _ => ⟨rfl, rfl⟩,
    fun h => ⟨h.1.symm, h.2.symm⟩,
    fun h k => ⟨h.1.trans k.1, h.2.trans k.2⟩⟩

abbrev OrientedLine := Quotient (orientedLineSetoid V)

variable {V}

theorem same_line_iff (u v : Direction V) (x y : V) :
    (orientedLineSetoid V).r (u, x) (v, y) ↔
      u = v ∧ ∃ t : ℝ, y = x + t • u.val := by
  change (u = v ∧ perpendicularProjection u x = perpendicularProjection v y) ↔ _
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, (perpendicularProjection_eq_iff _ _ _).mp h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, (perpendicularProjection_eq_iff _ _ _).mpr h⟩

def perpendicularRepresentative (l : OrientedLine V) : PerpendicularLine V :=
  Quotient.lift (fun p : Direction V × V =>
    (⟨p.1, perpendicularProjection p.1 p.2,
      inner_perpendicularProjection p.1 p.2⟩ : PerpendicularLine V))
    (fun _ _ (h : (orientedLineSetoid V).r _ _) => PerpendicularLine.ext h.1 h.2) l

def lineOfPerpendicular (l : PerpendicularLine V) : OrientedLine V :=
  Quotient.mk _ (l.direction, l.offset)

/-- The actual quotient correspondence, with explicit inverse. -/
def orientedLineEquiv : OrientedLine V ≃ PerpendicularLine V where
  toFun := perpendicularRepresentative
  invFun := lineOfPerpendicular
  left_inv l := by
    refine Quotient.inductionOn l ?_
    intro p
    apply Quotient.sound
    exact ⟨rfl, perpendicularProjection_idempotent p.1 p.2⟩
  right_inv l := by
    change (⟨l.direction, perpendicularProjection l.direction l.offset,
      inner_perpendicularProjection _ _⟩ : PerpendicularLine V) = l
    apply PerpendicularLine.ext
    · rfl
    · exact perpendicularProjection_eq_self _ _ l.perpendicular

/-- Euclidean three-dimensional real minitwistors. -/
abbrev MiniTwistor := OrientedLine (EuclideanSpace ℝ (Fin 3))

def Incident (l : PerpendicularLine V) (x : V) : Prop :=
  perpendicularProjection l.direction x = l.offset

theorem incident_iff (l : PerpendicularLine V) (x : V) :
    Incident l x ↔ ∃ t : ℝ, x = l.offset + t • l.direction.val := by
  have h := perpendicularProjection_eq_iff l.direction l.offset x
  rw [perpendicularProjection_eq_self _ _ l.perpendicular] at h
  exact eq_comm.trans h

theorem parameter_readout (l : PerpendicularLine V) (t : ℝ) :
    ⟪l.direction.val, l.offset + t • l.direction.val⟫ = t := by
  simp only [inner_add_right, real_inner_smul_right, l.perpendicular,
    l.direction.property, mul_one, zero_add]

theorem parameter_unique (l : PerpendicularLine V) {s t : ℝ}
    (h : l.offset + s • l.direction.val = l.offset + t • l.direction.val) : s = t := by
  simpa only [parameter_readout] using congrArg (fun x => ⟪l.direction.val, x⟫) h

/-- A concrete real three-dimensional direction, ensuring nonvacuity. -/
def coordinateDirection : Direction (EuclideanSpace ℝ (Fin 3)) :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

def coordinateLine : PerpendicularLine (EuclideanSpace ℝ (Fin 3)) :=
  ⟨coordinateDirection, 0, by simp⟩

theorem coordinateLine_incident (t : ℝ) :
    Incident coordinateLine (t • coordinateDirection.val) := by
  rw [incident_iff]
  exact ⟨t, by simp [coordinateLine]⟩

end InfoGeometry.Twistor.RealMiniTwistor
