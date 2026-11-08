import Mathlib.Algebra.Group.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Abel
import InfoGeometry.Categorical.ModularDoubledRealHopfFibration

/-!
# InfoGeometry.Categorical.ModularDoubledRealHopfTransport

Transport and soldering data for modular doubled-real fibration shadows.

The module name keeps the historical `Hopf` label for compatibility.  The
projective two-qubit map `CP^3 -> S^4` should be read as a twistor/projection
shadow; the quaternionic Hopf map lives one level up at `S^7 -> S^4`.

This file connects the fibration skeleton to the algebraic structures that
should later instantiate vector, spinor, and quaternion channels:

* one-form/connection coefficients as additive 1-cocycles;
* soldering maps as additive maps between transport channels;
* V4-style pairs of commuting involutive gradings;
* a finite `Bool x Bool` Cl(1,1)/Varlamov shadow for the three nontrivial
  trifactor gradings.

It is categorical infrastructure.  Matrix/quaternion formulas instantiate this
surface; they do not replace it.
-/

universe u v wV wS wQ

namespace InfoGeometry.Categorical.ModularDoubledRealHopfTransport

open ModularDoubledRealHopfFibration

/-! ## 1-cocycle transport -/

/--
An additive transport 1-cocycle on an object space.

`transport x y` is the abstract connection/one-form integral from `x` to `y`.
The cocycle law says transport along `x -> y -> z` composes additively.
-/
structure TransportCocycle (X : Type u) (Ω : Type v) [AddCommGroup Ω] where
  transport : X → X → Ω
  zero_diag : ∀ x : X, transport x x = 0
  cocycle : ∀ x y z : X, transport x y + transport y z = transport x z

namespace TransportCocycle

variable {X : Type u} {Ω : Type v} [AddCommGroup Ω]

/-- Reversing transport negates a transport cocycle. -/
theorem reverse (C : TransportCocycle X Ω) (x y : X) :
    C.transport y x = -C.transport x y := by
  have hsum : C.transport x y + C.transport y x = 0 := by
    simpa [C.zero_diag x] using C.cocycle x y x
  have h := congrArg (fun t : Ω => -C.transport x y + t) hsum
  simpa [add_assoc] using h

/-- Transport through four points collapses to direct transport. -/
theorem cocycle_four (C : TransportCocycle X Ω) (w x y z : X) :
    C.transport w x + C.transport x y + C.transport y z = C.transport w z := by
  calc
    C.transport w x + C.transport x y + C.transport y z =
        C.transport w y + C.transport y z := by rw [C.cocycle w x y]
    _ = C.transport w z := C.cocycle w y z

end TransportCocycle

/-! ## Soldered vector/spinor/quaternion transport channels -/

open ModularDoubledRealHopfFibration

/--
Three soldered transport channels over one modular doubled-real fibration.

The vector channel is the source channel.  The spinor and quaternion channels
are obtained from it by additive soldering maps.  This captures the common
connection-one-form spine without choosing matrix coordinates.
-/
structure SolderedTransport
    (F : ModularDoubledRealHopf.{u, v})
    (ΩV : Type wV) (ΩS : Type wS) (ΩQ : Type wQ)
    [AddCommGroup ΩV] [AddCommGroup ΩS] [AddCommGroup ΩQ] where
  vector : TransportCocycle F.Total ΩV
  spinor : TransportCocycle F.Total ΩS
  quaternion : TransportCocycle F.Total ΩQ
  vectorToSpinor : ΩV →+ ΩS
  vectorToQuaternion : ΩV →+ ΩQ
  spinor_soldered : ∀ x y : F.Total,
    vectorToSpinor (vector.transport x y) = spinor.transport x y
  quaternion_soldered : ∀ x y : F.Total,
    vectorToQuaternion (vector.transport x y) = quaternion.transport x y

namespace SolderedTransport

variable {F : ModularDoubledRealHopf.{u, v}}
variable {ΩV : Type wV} {ΩS : Type wS} {ΩQ : Type wQ}
variable [AddCommGroup ΩV] [AddCommGroup ΩS] [AddCommGroup ΩQ]

/-- The spinor cocycle is transported from the vector cocycle by soldering. -/
theorem spinor_cocycle_from_vector
    (S : SolderedTransport F ΩV ΩS ΩQ) (x y z : F.Total) :
    S.spinor.transport x y + S.spinor.transport y z =
      S.spinor.transport x z := by
  calc
    S.spinor.transport x y + S.spinor.transport y z =
        S.vectorToSpinor (S.vector.transport x y) +
          S.vectorToSpinor (S.vector.transport y z) := by
            rw [← S.spinor_soldered x y, ← S.spinor_soldered y z]
    _ = S.vectorToSpinor (S.vector.transport x y + S.vector.transport y z) := by
          rw [map_add]
    _ = S.vectorToSpinor (S.vector.transport x z) := by
          rw [S.vector.cocycle x y z]
    _ = S.spinor.transport x z := S.spinor_soldered x z

/-- The quaternion cocycle is transported from the vector cocycle by soldering. -/
theorem quaternion_cocycle_from_vector
    (S : SolderedTransport F ΩV ΩS ΩQ) (x y z : F.Total) :
    S.quaternion.transport x y + S.quaternion.transport y z =
      S.quaternion.transport x z := by
  calc
    S.quaternion.transport x y + S.quaternion.transport y z =
        S.vectorToQuaternion (S.vector.transport x y) +
          S.vectorToQuaternion (S.vector.transport y z) := by
            rw [← S.quaternion_soldered x y, ← S.quaternion_soldered y z]
    _ = S.vectorToQuaternion (S.vector.transport x y + S.vector.transport y z) := by
          rw [map_add]
    _ = S.vectorToQuaternion (S.vector.transport x z) := by
          rw [S.vector.cocycle x y z]
    _ = S.quaternion.transport x z := S.quaternion_soldered x z

end SolderedTransport

/-! ## V4 / multifactor involutive gradings -/

/--
Two commuting involutive gradings on one carrier.

The third nontrivial V4 grading is their composite.  This is the categorical
version of "not a single grading": vector/spinor/quaternion/trifactor transport
can carry the full V4 of involutive grade reflections.
-/
structure V4Grading (X : Type u) where
  gradeA : X → X
  gradeB : X → X
  gradeA_involutive : Function.Involutive gradeA
  gradeB_involutive : Function.Involutive gradeB
  commute : ∀ x : X, gradeA (gradeB x) = gradeB (gradeA x)

namespace V4Grading

variable {X : Type u}

/-- The third nontrivial V4 grading, the composite of the two generators. -/
def gradeAB (G : V4Grading X) : X → X :=
  fun x => G.gradeA (G.gradeB x)

/-- The composite grading is also involutive. -/
theorem gradeAB_involutive (G : V4Grading X) :
    Function.Involutive G.gradeAB := by
  intro x
  unfold gradeAB
  calc
    G.gradeA (G.gradeB (G.gradeA (G.gradeB x))) =
        G.gradeA (G.gradeA (G.gradeB (G.gradeB x))) := by
          rw [← G.commute (G.gradeB x)]
    _ = G.gradeA (G.gradeA x) := by rw [G.gradeB_involutive x]
    _ = x := G.gradeA_involutive x

/-- `gradeA` commutes with the composite grading. -/
theorem gradeA_commutes_gradeAB (G : V4Grading X) (x : X) :
    G.gradeA (G.gradeAB x) = G.gradeAB (G.gradeA x) := by
  unfold gradeAB
  calc
    G.gradeA (G.gradeA (G.gradeB x)) = G.gradeB x :=
      G.gradeA_involutive (G.gradeB x)
    _ = G.gradeA (G.gradeB (G.gradeA x)) := by
      rw [← G.commute x]
      exact (G.gradeA_involutive (G.gradeB x)).symm

/-- `gradeB` commutes with the composite grading. -/
theorem gradeB_commutes_gradeAB (G : V4Grading X) (x : X) :
    G.gradeB (G.gradeAB x) = G.gradeAB (G.gradeB x) := by
  unfold gradeAB
  calc
    G.gradeB (G.gradeA (G.gradeB x)) = G.gradeA (G.gradeB (G.gradeB x)) :=
      (G.commute (G.gradeB x)).symm
    _ = G.gradeA x := by rw [G.gradeB_involutive x]
    _ = G.gradeA (G.gradeB (G.gradeB x)) := by rw [G.gradeB_involutive x]

end V4Grading

/--
A modular doubled-real fibration equipped with V4 gradings on total and base,
compatible with projection.
-/
structure V4GradedFibration (F : ModularDoubledRealHopf.{u, v}) where
  totalGrading : V4Grading F.Total
  baseGrading : V4Grading F.Base
  projection_gradeA : ∀ x : F.Total,
    F.projection (totalGrading.gradeA x) = baseGrading.gradeA (F.projection x)
  projection_gradeB : ∀ x : F.Total,
    F.projection (totalGrading.gradeB x) = baseGrading.gradeB (F.projection x)

namespace V4GradedFibration

variable {F : ModularDoubledRealHopf.{u, v}}

/-- Projection is compatible with the third V4 grading. -/
theorem projection_gradeAB (G : V4GradedFibration F) (x : F.Total) :
    F.projection (G.totalGrading.gradeAB x) =
      G.baseGrading.gradeAB (F.projection x) := by
  unfold V4Grading.gradeAB
  rw [G.projection_gradeA, G.projection_gradeB]

end V4GradedFibration

/-! ## Finite Cl(1,1) / Varlamov V4 shadow -/

/-- First Boolean grading flip. -/
def flipFirst : Bool × Bool → Bool × Bool :=
  fun x => (!x.1, x.2)

/-- Second Boolean grading flip. -/
def flipSecond : Bool × Bool → Bool × Bool :=
  fun x => (x.1, !x.2)

theorem flipFirst_involutive : Function.Involutive flipFirst := by
  intro x
  cases x with
  | mk a b =>
    cases a <;> cases b <;> rfl

theorem flipSecond_involutive : Function.Involutive flipSecond := by
  intro x
  cases x with
  | mk a b =>
    cases a <;> cases b <;> rfl

theorem flipFirst_flipSecond_commute (x : Bool × Bool) :
    flipFirst (flipSecond x) = flipSecond (flipFirst x) := by
  cases x with
  | mk a b =>
    cases a <;> cases b <;> rfl

/--
Finite V4 shadow of the two commuting Cl(1,1)-style involutive gradings.
The third nontrivial grading is the composite `flipFirst ∘ flipSecond`.
-/
def cl11V4Shadow : V4Grading (Bool × Bool) where
  gradeA := flipFirst
  gradeB := flipSecond
  gradeA_involutive := flipFirst_involutive
  gradeB_involutive := flipSecond_involutive
  commute := flipFirst_flipSecond_commute

theorem cl11V4Shadow_composite_involutive :
    Function.Involutive cl11V4Shadow.gradeAB :=
  cl11V4Shadow.gradeAB_involutive

end InfoGeometry.Categorical.ModularDoubledRealHopfTransport
