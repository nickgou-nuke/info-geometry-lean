import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Coordinate-Free Connection Channels

This file formalizes the finite algebraic core of the "one connection, many
representations" statement.

The owner object is not a coordinate chart and not a matrix basis.  It is a
noncommutative ring element expression, transported through representation
channels modeled as ring homomorphisms.

The results here prove that any multiplicative/additive channel preserves:

* commutators;
* two-slot curvature expressions `d_xy - d_yx + [A_x,A_y]`;
* curvature antisymmetry under swapping the slots;
* cyclic Bianchi sums;
* the trifactor law `T^3 = T`.

Concrete vector/spinor/quaternion matrix models are instances of these channel
laws, not replacements for them.
-/

set_option autoImplicit false

namespace CoordinateFreeConnectionChannels

universe u v w x

section Basic

variable {A : Type u} [Ring A]

/-- Associative-ring commutator, used as the coordinate-free Lie bracket. -/
def commutator (X Y : A) : A :=
  X * Y - Y * X

/--
Two-slot curvature expression.

This is the finite algebraic shadow of `F_A = dA + A ∧ A`: the derivative part
is represented by `dXY - dYX`, and the connection product part by the
commutator `[AX, AY]`.
-/
def twoSlotCurvature (dXY dYX AX AY : A) : A :=
  dXY - dYX + commutator AX AY

/--
Two-slot torsion expression (left action).

This is the finite algebraic shadow of `T = dE + \Omega \wedge E`: the derivative part
is represented by `dEXY - dEYX`, and the connection action by `OX * EY - OY * EX`.
-/
def twoSlotTorsionLeft (dEXY dEYX OX EY OY EX : A) : A :=
  dEXY - dEYX + OX * EY - OY * EX

/--
Two-slot torsion expression (commutator action).

This is the shadow of `T = dE + [\Omega, E]_\wedge`.
-/
def twoSlotTorsionComm (dEXY dEYX OX EY OY EX : A) : A :=
  dEXY - dEYX + commutator OX EY - commutator OY EX

/-- Cyclic sum used by the algebraic Bianchi readout. -/
def cyclicSum (X Y Z : A) : A :=
  X + Y + Z

/-- Curvature is antisymmetric in its two slots. -/
theorem twoSlotCurvature_swap (dXY dYX AX AY : A) :
    twoSlotCurvature dYX dXY AY AX = -twoSlotCurvature dXY dYX AX AY := by
  unfold twoSlotCurvature commutator
  noncomm_ring

/-- Additive form of the curvature antisymmetry. -/
theorem twoSlotCurvature_add_swap (dXY dYX AX AY : A) :
    twoSlotCurvature dXY dYX AX AY + twoSlotCurvature dYX dXY AY AX = 0 := by
  rw [twoSlotCurvature_swap]
  simp

/-- Torsion is antisymmetric in its two slots (left action). -/
theorem twoSlotTorsionLeft_swap (dEXY dEYX OX EY OY EX : A) :
    twoSlotTorsionLeft dEYX dEXY OY EX OX EY = -twoSlotTorsionLeft dEXY dEYX OX EY OY EX := by
  unfold twoSlotTorsionLeft
  noncomm_ring

/-- Torsion is antisymmetric in its two slots (commutator action). -/
theorem twoSlotTorsionComm_swap (dEXY dEYX OX EY OY EX : A) :
    twoSlotTorsionComm dEYX dEXY OY EX OX EY = -twoSlotTorsionComm dEXY dEYX OX EY OY EX := by
  unfold twoSlotTorsionComm commutator
  noncomm_ring

end Basic

section Channel

variable {A : Type u} {B : Type v} [Ring A] [Ring B]

/--
A representation channel from one associative algebra to another.

For the intended geometry, the source is the coordinate-free connection algebra
and targets are the vector, spinor, or quaternion readout algebras.
-/
structure ConnectionChannel where
  map : A →+* B

namespace ConnectionChannel

/-- A channel preserves commutators. -/
theorem map_commutator (ρ : ConnectionChannel (A := A) (B := B)) (X Y : A) :
    ρ.map (commutator X Y) = commutator (ρ.map X) (ρ.map Y) := by
  simp [commutator]

/-- A channel preserves the two-slot curvature expression. -/
theorem map_twoSlotCurvature
    (ρ : ConnectionChannel (A := A) (B := B)) (dXY dYX AX AY : A) :
    ρ.map (twoSlotCurvature dXY dYX AX AY) =
      twoSlotCurvature (ρ.map dXY) (ρ.map dYX) (ρ.map AX) (ρ.map AY) := by
  simp [twoSlotCurvature, commutator]

/-- A channel preserves the two-slot torsion expression (left action). -/
theorem map_twoSlotTorsionLeft
    (ρ : ConnectionChannel (A := A) (B := B)) (dEXY dEYX OX EY OY EX : A) :
    ρ.map (twoSlotTorsionLeft dEXY dEYX OX EY OY EX) =
      twoSlotTorsionLeft (ρ.map dEXY) (ρ.map dEYX) (ρ.map OX) (ρ.map EY) (ρ.map OY) (ρ.map EX) := by
  simp [twoSlotTorsionLeft]

/-- A channel preserves the two-slot torsion expression (commutator action). -/
theorem map_twoSlotTorsionComm
    (ρ : ConnectionChannel (A := A) (B := B)) (dEXY dEYX OX EY OY EX : A) :
    ρ.map (twoSlotTorsionComm dEXY dEYX OX EY OY EX) =
      twoSlotTorsionComm (ρ.map dEXY) (ρ.map dEYX) (ρ.map OX) (ρ.map EY) (ρ.map OY) (ρ.map EX) := by
  simp [twoSlotTorsionComm, commutator]

/-- A channel preserves zero cyclic Bianchi sums. -/
theorem map_cyclicSum_of_zero
    (ρ : ConnectionChannel (A := A) (B := B)) (X Y Z : A)
    (h : cyclicSum X Y Z = 0) :
    cyclicSum (ρ.map X) (ρ.map Y) (ρ.map Z) = 0 := by
  unfold cyclicSum at h ⊢
  calc
    ρ.map X + ρ.map Y + ρ.map Z = ρ.map (X + Y + Z) := by simp
    _ = ρ.map 0 := by rw [h]
    _ = 0 := by simp

/-- A channel preserves the trifactor operator law `T^3 = T`. -/
theorem map_trifactor_law
    (ρ : ConnectionChannel (A := A) (B := B)) (T : A) (hT : T ^ 3 = T) :
    ρ.map T ^ 3 = ρ.map T := by
  calc
    ρ.map T ^ 3 = ρ.map (T ^ 3) := by simp
    _ = ρ.map T := by rw [hT]

/--
The image curvature remains antisymmetric because the target ring is itself a
coordinate-free associative algebra.
-/
theorem mapped_curvature_swap
    (ρ : ConnectionChannel (A := A) (B := B)) (dXY dYX AX AY : A) :
    twoSlotCurvature (ρ.map dYX) (ρ.map dXY) (ρ.map AY) (ρ.map AX) =
      -twoSlotCurvature (ρ.map dXY) (ρ.map dYX) (ρ.map AX) (ρ.map AY) :=
  twoSlotCurvature_swap (A := B) (ρ.map dXY) (ρ.map dYX) (ρ.map AX) (ρ.map AY)

end ConnectionChannel

end Channel

section ThreeChannels

variable {A : Type u} {V : Type v} {S : Type w} {Q : Type x}
variable [Ring A] [Ring V] [Ring S] [Ring Q]

/--
Three representation channels of one coordinate-free connection algebra.

The names are geometric readouts only:
* `vector` is the Christoffel/vector channel;
* `spinor` is the spinorial channel;
* `quaternion` is the quaternion/gauge channel.
-/
structure ThreeConnectionChannels where
  vector : ConnectionChannel (A := A) (B := V)
  spinor : ConnectionChannel (A := A) (B := S)
  quaternion : ConnectionChannel (A := A) (B := Q)

namespace ThreeConnectionChannels

/-- One curvature object transported into the vector, spinor, and quaternion channels. -/
theorem map_twoSlotCurvature_all
    (C : ThreeConnectionChannels (A := A) (V := V) (S := S) (Q := Q))
    (dXY dYX AX AY : A) :
    C.vector.map (twoSlotCurvature dXY dYX AX AY) =
        twoSlotCurvature (C.vector.map dXY) (C.vector.map dYX)
          (C.vector.map AX) (C.vector.map AY)
      ∧ C.spinor.map (twoSlotCurvature dXY dYX AX AY) =
        twoSlotCurvature (C.spinor.map dXY) (C.spinor.map dYX)
          (C.spinor.map AX) (C.spinor.map AY)
      ∧ C.quaternion.map (twoSlotCurvature dXY dYX AX AY) =
        twoSlotCurvature (C.quaternion.map dXY) (C.quaternion.map dYX)
          (C.quaternion.map AX) (C.quaternion.map AY) := by
  exact ⟨C.vector.map_twoSlotCurvature dXY dYX AX AY,
    C.spinor.map_twoSlotCurvature dXY dYX AX AY,
    C.quaternion.map_twoSlotCurvature dXY dYX AX AY⟩

/-- One torsion object transported into the vector, spinor, and quaternion channels (left action). -/
theorem map_twoSlotTorsionLeft_all
    (C : ThreeConnectionChannels (A := A) (V := V) (S := S) (Q := Q))
    (dEXY dEYX OX EY OY EX : A) :
    C.vector.map (twoSlotTorsionLeft dEXY dEYX OX EY OY EX) =
        twoSlotTorsionLeft (C.vector.map dEXY) (C.vector.map dEYX)
          (C.vector.map OX) (C.vector.map EY) (C.vector.map OY) (C.vector.map EX)
      ∧ C.spinor.map (twoSlotTorsionLeft dEXY dEYX OX EY OY EX) =
        twoSlotTorsionLeft (C.spinor.map dEXY) (C.spinor.map dEYX)
          (C.spinor.map OX) (C.spinor.map EY) (C.spinor.map OY) (C.spinor.map EX)
      ∧ C.quaternion.map (twoSlotTorsionLeft dEXY dEYX OX EY OY EX) =
        twoSlotTorsionLeft (C.quaternion.map dEXY) (C.quaternion.map dEYX)
          (C.quaternion.map OX) (C.quaternion.map EY) (C.quaternion.map OY) (C.quaternion.map EX) := by
  exact ⟨C.vector.map_twoSlotTorsionLeft dEXY dEYX OX EY OY EX,
    C.spinor.map_twoSlotTorsionLeft dEXY dEYX OX EY OY EX,
    C.quaternion.map_twoSlotTorsionLeft dEXY dEYX OX EY OY EX⟩

/-- One torsion object transported into the vector, spinor, and quaternion channels (commutator action). -/
theorem map_twoSlotTorsionComm_all
    (C : ThreeConnectionChannels (A := A) (V := V) (S := S) (Q := Q))
    (dEXY dEYX OX EY OY EX : A) :
    C.vector.map (twoSlotTorsionComm dEXY dEYX OX EY OY EX) =
        twoSlotTorsionComm (C.vector.map dEXY) (C.vector.map dEYX)
          (C.vector.map OX) (C.vector.map EY) (C.vector.map OY) (C.vector.map EX)
      ∧ C.spinor.map (twoSlotTorsionComm dEXY dEYX OX EY OY EX) =
        twoSlotTorsionComm (C.spinor.map dEXY) (C.spinor.map dEYX)
          (C.spinor.map OX) (C.spinor.map EY) (C.spinor.map OY) (C.spinor.map EX)
      ∧ C.quaternion.map (twoSlotTorsionComm dEXY dEYX OX EY OY EX) =
        twoSlotTorsionComm (C.quaternion.map dEXY) (C.quaternion.map dEYX)
          (C.quaternion.map OX) (C.quaternion.map EY) (C.quaternion.map OY) (C.quaternion.map EX) := by
  exact ⟨C.vector.map_twoSlotTorsionComm dEXY dEYX OX EY OY EX,
    C.spinor.map_twoSlotTorsionComm dEXY dEYX OX EY OY EX,
    C.quaternion.map_twoSlotTorsionComm dEXY dEYX OX EY OY EX⟩

/-- A zero Bianchi cyclic sum transports to all three representation channels. -/
theorem map_bianchi_zero_all
    (C : ThreeConnectionChannels (A := A) (V := V) (S := S) (Q := Q))
    (X Y Z : A) (h : cyclicSum X Y Z = 0) :
    cyclicSum (C.vector.map X) (C.vector.map Y) (C.vector.map Z) = 0
      ∧ cyclicSum (C.spinor.map X) (C.spinor.map Y) (C.spinor.map Z) = 0
      ∧ cyclicSum (C.quaternion.map X) (C.quaternion.map Y) (C.quaternion.map Z) = 0 := by
  exact ⟨C.vector.map_cyclicSum_of_zero X Y Z h,
    C.spinor.map_cyclicSum_of_zero X Y Z h,
    C.quaternion.map_cyclicSum_of_zero X Y Z h⟩

/-- The trifactor law transports to all three representation channels. -/
theorem map_trifactor_law_all
    (C : ThreeConnectionChannels (A := A) (V := V) (S := S) (Q := Q))
    (T : A) (hT : T ^ 3 = T) :
    C.vector.map T ^ 3 = C.vector.map T
      ∧ C.spinor.map T ^ 3 = C.spinor.map T
      ∧ C.quaternion.map T ^ 3 = C.quaternion.map T := by
  exact ⟨C.vector.map_trifactor_law T hT,
    C.spinor.map_trifactor_law T hT,
    C.quaternion.map_trifactor_law T hT⟩

end ThreeConnectionChannels

end ThreeChannels

end CoordinateFreeConnectionChannels
