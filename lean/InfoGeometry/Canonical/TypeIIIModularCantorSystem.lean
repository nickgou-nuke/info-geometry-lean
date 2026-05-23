import InfoGeometry.Canonical.StandardFormCore
import InfoGeometry.Meta.Architecture
import Mathlib

open scoped InnerProductSpace BigOperators

/-!
# InfoGeometry.Canonical.TypeIIIModularCantorSystem

Theorem-safe modular-Cartan Cantor interface for type-III-style operator
geometry.

This file does not assert a trace, determinant, Lebesgue volume, finite
symmetric cone, or global self-concordant barrier for a type III factor. It
records the replacement dictionary used by the modular layer:

* finite determinant-volume analogies are replaced by modular weight,
  Connes-cocycle, and Araki-entropy data;
* symmetric cone       ↦  standard-form natural positive cone;
* Cartan involution    ↦  Tomita modular conjugation / mirror equivalence;
* left/right twins     ↦  an algebra and its modular commutant mirror;
* Cantor splitting     ↦  a dyadic projection tree and its reflected tree.

The formal content is intentionally bounded and algebraic. The unbounded
relative modular logarithm is represented only as an explicit proof/readout
packet, not constructed by functional calculus in this file.
-/

namespace InfoGeometry.Canonical.TypeIIIModularCantorSystem

open InfoGeometry.Canonical.StandardFormCore

universe u v w

/-- Finite binary words indexing cylinder projections. -/
abbrev BinaryWord : Type := List Bool

namespace BinaryWord

/-- Append one binary branch to a finite word. -/
def child (w : BinaryWord) (b : Bool) : BinaryWord :=
  w ++ [b]

@[simp] theorem child_nil (b : Bool) : child [] b = [b] := rfl

/-- Finite closed cylinder of all finite words extending `w`. -/
def closedCylinder (w : BinaryWord) : Set BinaryWord :=
  {u | ∃ t : BinaryWord, u = w ++ t}

/-- Every word lies in its own closed cylinder. -/
@[rep_depth projective]
theorem mem_closedCylinder_self (w : BinaryWord) :
    w ∈ closedCylinder w := by
  exact ⟨[], by simp⟩

/--
Closed finite binary cylinders split into the root word and the two one-step
child cylinders.

This is a concrete Cantor-combinatorics law proved from mathlib list/set
case analysis, not a projection-tree witness field.
-/
@[rep_depth projective]
theorem closedCylinder_split (w : BinaryWord) :
    closedCylinder w =
      ({w} : Set BinaryWord)
        ∪ closedCylinder (child w false)
        ∪ closedCylinder (child w true) := by
  ext u
  constructor
  · intro hu
    rcases hu with ⟨t, rfl⟩
    cases t with
    | nil =>
        simp [closedCylinder]
    | cons b t =>
        cases b <;> simp [closedCylinder, child, List.append_assoc]
  · intro hu
    rcases hu with hRootOrFalse | hTrue
    · rcases hRootOrFalse with hRoot | hFalse
      · rcases hRoot with rfl
        exact ⟨[], by simp⟩
      · rcases hFalse with ⟨t, rfl⟩
        exact ⟨false :: t, by simp [child, List.append_assoc]⟩
    · rcases hTrue with ⟨t, rfl⟩
      exact ⟨true :: t, by simp [child, List.append_assoc]⟩

end BinaryWord

/-! ## Modular mirror / Cartan twin split -/

/--
A theorem-safe abstraction of the Tomita mirror between a left real
self-adjoint observable space and its modular commutant twin.

In an actual standard form this is induced by `A ↦ J A J` on self-adjoint
observables; here it is kept as a real-linear equivalence so that we can prove
the Cartan/twin algebra without constructing a von Neumann algebra in mathlib.
-/
@[rep_depth operator]
structure ModularMirror
    (Left Right : Type*)
    [AddCommGroup Left] [Module ℝ Left]
    [AddCommGroup Right] [Module ℝ Right] where
  /-- The Tomita mirror, read as a real-linear equivalence. -/
  mirror : Left ≃ₗ[ℝ] Right

namespace ModularMirror

variable {Left : Type u} {Right : Type v}
variable [AddCommGroup Left] [Module ℝ Left]
variable [AddCommGroup Right] [Module ℝ Right]
variable (T : ModularMirror Left Right)

/-- Doubled left/right real observable space. -/
abbrev Doubled (_T : ModularMirror Left Right) : Type (max u v) := Left × Right

/-- Cartan/Tomita twin involution: `(A,B) ↦ (J B J, J A J)`. -/
def theta (z : T.Doubled) : T.Doubled :=
  (T.mirror.symm z.2, T.mirror z.1)

@[simp] theorem theta_fst (z : T.Doubled) :
    (T.theta z).1 = T.mirror.symm z.2 := rfl

@[simp] theorem theta_snd (z : T.Doubled) :
    (T.theta z).2 = T.mirror z.1 := rfl

/-- The twin reflection is involutive. -/
@[rep_depth operator, simp]
theorem theta_sq (z : T.Doubled) :
    T.theta (T.theta z) = z := by
  rcases z with ⟨A, B⟩
  simp [theta]

/-- Self-dual doubled sector, the diagonal modular horizon surface. -/
def IsSelfDual (z : T.Doubled) : Prop :=
  T.theta z = z

/-- Anti-self-dual doubled sector, the normal direction to the modular mirror. -/
def IsAntiSelfDual (z : T.Doubled) : Prop :=
  T.theta z = -z

/-- The self-dual diagonal pair `(A, JAJ)`. -/
def diagonal (A : Left) : T.Doubled :=
  (A, T.mirror A)

/-- The anti-self-dual normal pair `(A, -JAJ)`. -/
def antiDiagonal (A : Left) : T.Doubled :=
  (A, -T.mirror A)

@[rep_depth operator, simp]
theorem diagonal_selfDual (A : Left) :
    T.IsSelfDual (T.diagonal A) := by
  simp [IsSelfDual, diagonal, theta]

@[rep_depth operator, simp]
theorem antiDiagonal_antiSelfDual (A : Left) :
    T.IsAntiSelfDual (T.antiDiagonal A) := by
  simp [IsAntiSelfDual, antiDiagonal, theta]

/-- Pull a right observable back to the left algebraic representative. -/
def rightAsLeft (B : Right) : Left :=
  T.mirror.symm B

/-- Push a left observable to its modular right twin. -/
def leftAsRight (A : Left) : Right :=
  T.mirror A

@[simp] theorem rightAsLeft_leftAsRight (A : Left) :
    T.rightAsLeft (T.leftAsRight A) = A := by
  simp [rightAsLeft, leftAsRight]

@[simp] theorem leftAsRight_rightAsLeft (B : Right) :
    T.leftAsRight (T.rightAsLeft B) = B := by
  simp [rightAsLeft, leftAsRight]

end ModularMirror

/-! ## Proof-only modular twins for concrete cylinder maps -/

section TwinCylinders

variable {Left : Type u} {Right : Type v}
variable [AddCommGroup Left] [Module ℝ Left]
variable [AddCommGroup Right] [Module ℝ Right]
variable (T : ModularMirror Left Right)

/-- Right/reflected cylinder obtained by applying a real-linear mirror. -/
def rightCylinder (cylinder : BinaryWord → Left) (w : BinaryWord) : Right :=
  T.mirror (cylinder w)

/-- Self-dual doubled cylinder `(p_w,p_w^R)`. -/
def selfDualCylinder (cylinder : BinaryWord → Left) (w : BinaryWord) : T.Doubled :=
  T.diagonal (cylinder w)

/-- Anti-self-dual doubled cylinder `(p_w,-p_w^R)`. -/
def antiSelfDualCylinder (cylinder : BinaryWord → Left) (w : BinaryWord) : T.Doubled :=
  T.antiDiagonal (cylinder w)

@[rep_depth operator, simp]
theorem selfDualCylinder_selfDual (cylinder : BinaryWord → Left) (w : BinaryWord) :
    T.IsSelfDual (selfDualCylinder T cylinder w) := by
  simp [selfDualCylinder]

@[rep_depth operator, simp]
theorem antiSelfDualCylinder_antiSelfDual (cylinder : BinaryWord → Left) (w : BinaryWord) :
    T.IsAntiSelfDual (antiSelfDualCylinder T cylinder w) := by
  simp [antiSelfDualCylinder]

/--
The reflected cylinders inherit any supplied equality by `LinearMap.map_add`.

The equality hypothesis is local to this theorem; it is not stored as a packet
law.
-/
@[rep_depth operator]
theorem rightCylinder_split_of_eq
    (cylinder : BinaryWord → Left)
    (w : BinaryWord)
    (h :
      cylinder w =
        cylinder (BinaryWord.child w false) + cylinder (BinaryWord.child w true)) :
    rightCylinder T cylinder w =
      rightCylinder T cylinder (BinaryWord.child w false)
        + rightCylinder T cylinder (BinaryWord.child w true) := by
  unfold rightCylinder
  rw [h]
  exact map_add T.mirror _ _

end TwinCylinders

/-! ## Cylinder weights and logarithmic branch potentials -/

section CylinderWeights

/-- Negative logarithmic cylinder potential `-log μ([w])`. -/
@[rep_depth thermo]
noncomputable def cylinderPotential (weight : BinaryWord → ℝ) (w : BinaryWord) : ℝ :=
  -Real.log (weight w)

/-- Local branch cost `-log( μ([wi]) / μ([w]) )`. -/
@[rep_depth thermo]
noncomputable def branchIncrement (weight : BinaryWord → ℝ) (w : BinaryWord) (b : Bool) : ℝ :=
  -Real.log (weight (BinaryWord.child w b) / weight w)

/-- Logarithmic chain rule along one dyadic branch. -/
@[rep_depth thermo]
theorem cylinderPotential_child
    (weight : BinaryWord → ℝ)
    (hpos : ∀ w, 0 < weight w)
    (w : BinaryWord) (b : Bool) :
    cylinderPotential weight (BinaryWord.child w b)
      = cylinderPotential weight w + branchIncrement weight w b := by
  have hchild : weight (BinaryWord.child w b) ≠ 0 :=
    ne_of_gt (hpos (BinaryWord.child w b))
  have hparent : weight w ≠ 0 :=
    ne_of_gt (hpos w)
  unfold cylinderPotential branchIncrement
  rw [Real.log_div hchild hparent]
  ring

/-- Finite-level determinant-barrier shadow on a supplied finite cylinder set. -/
@[rep_depth thermo]
noncomputable def finiteBarrierOn (weight : BinaryWord → ℝ) (s : Finset BinaryWord) : ℝ :=
  -(Finset.sum s (fun w => Real.log (weight w)))

/-- Finite-depth KL/relative-entropy readout on a supplied cylinder set. -/
@[rep_depth thermo]
noncomputable def relativeEntropyOn
    (targetWeight referenceWeight : BinaryWord → ℝ)
    (s : Finset BinaryWord) : ℝ :=
  Finset.sum s
    (fun w => targetWeight w * Real.log (targetWeight w / referenceWeight w))

end CylinderWeights

end InfoGeometry.Canonical.TypeIIIModularCantorSystem
