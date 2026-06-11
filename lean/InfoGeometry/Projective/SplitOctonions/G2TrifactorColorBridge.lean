import InfoGeometry.Algebra.Zorn.G2TrifactorSU3
import InfoGeometry.Projective.SplitOctonions.SplitOctonionsColorStabilizer

noncomputable section

namespace InfoGeometry.Projective.SplitOctonions.G2TrifactorColorBridge

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Projective.SplitOctonions.SplitOctonionsColorStabilizer
open InfoGeometry.Projective.SplitOctonions.SplitOctonionsColorStabilizer.BektasMatrix
open Quaternion

/-!
# Trifactor Color Stabilizer Bridge

This module connects the finite Zorn-matrix `OP` projector lane to the concrete
quaternion-block color-action lane.

#### BUCKET 1: CLOSED FINITE THEOREMS
The `colorAct` operation on Bektaş quaternion blocks preserves the
longitudinal block, preserves the split norm, and therefore preserves the
split-norm null shell. The identity color element is a stabilizer, and the
product of color elements composes their actions.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None in this file.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not identify `ColorStabilizerElement` with a concrete
special-unitary color group, does not construct the exceptional automorphism
group, and does not prove an exceptional-to-color breaking theorem. It only
records the finite block invariants that such a later bridge would need.
-/

variable {R : Type*} [CommRing R]

/-- Embed a Zorn `R^3` color slot as a purely imaginary quaternion. -/
def vecToQuaternion (v : Fin 3 → R) : Quaternion R :=
  { re := 0
    imI := v 0
    imJ := v 1
    imK := v 2 }

/-- The Bektaş block obtained from the upper-right Zorn color slot. -/
def colorPartToBektas (X : ZMat R) : BektasMatrix R :=
  { q1 := 0
    q2 := vecToQuaternion X.x }

/-- The Bektaş block obtained from the lower-left Zorn anticolor slot. -/
def anticolorPartToBektas (X : ZMat R) : BektasMatrix R :=
  { q1 := 0
    q2 := vecToQuaternion X.y }

/-- 
The generic action of an `OP`-stabilizer (an action that fixes the macroscopic 
Cl(1,1) base) mapped into the Bektaş quaternion-block representation.
It is defined as any transformation `f` on `BektasMatrix R` that 
acts solely on the transverse `q2` block, leaving the longitudinal `q1` fixed.
-/
def IsBektasStabilizer (f : BektasMatrix R → BektasMatrix R) : Prop :=
  ∀ X, (f X).q1 = X.q1

/-- 
The concrete `colorAct` defined by a unit-norm quaternion fixes the
longitudinal block.
-/
theorem colorAct_is_stabilizer (g : ColorStabilizerElement R) :
    IsBektasStabilizer (colorAct g) := by
  intro X
  exact longitudinal_invariant g X

/-- The identity color element is a Bektaş stabilizer. -/
theorem stabilizerOne_is_stabilizer :
    IsBektasStabilizer (colorAct (stabilizerOne (R := R))) := by
  exact colorAct_is_stabilizer (stabilizerOne (R := R))

/-- Products of color elements are Bektaş stabilizers. -/
theorem stabilizerMul_is_stabilizer
    (g h : ColorStabilizerElement R) :
    IsBektasStabilizer (colorAct (stabilizerMul g h)) := by
  exact colorAct_is_stabilizer (stabilizerMul g h)

/-- The identity color element acts as the identity transformation. -/
theorem colorAct_stabilizer_action_one (X : BektasMatrix R) :
    colorAct (stabilizerOne (R := R)) X = X :=
  colorAct_one X

/-- Multiplying color elements composes their transformations. -/
theorem colorAct_stabilizer_action_mul
    (g h : ColorStabilizerElement R) (X : BektasMatrix R) :
    colorAct (stabilizerMul g h) X = colorAct g (colorAct h X) :=
  colorAct_comp g h X

/--
The `colorAct` preserves the split norm of the quaternion-block state.
-/
theorem colorAct_preserves_splitNorm (g : ColorStabilizerElement R) (X : BektasMatrix R) :
    splitNorm (colorAct g X) = splitNorm X := by
  exact splitNorm_invariant g X

/-- The `colorAct` preserves the split-norm null shell. -/
theorem colorAct_preserves_splitNorm_null
    (g : ColorStabilizerElement R) (X : BektasMatrix R)
    (hX : splitNorm X = 0) :
    splitNorm (colorAct g X) = 0 := by
  rw [colorAct_preserves_splitNorm g X, hX]

/-- The Zorn color-slot embedding has zero Bektaş longitudinal block. -/
@[simp] theorem colorPartToBektas_q1 (X : ZMat R) :
    (colorPartToBektas X).q1 = 0 :=
  rfl

/-- The Zorn anticolor-slot embedding has zero Bektaş longitudinal block. -/
@[simp] theorem anticolorPartToBektas_q1 (X : ZMat R) :
    (anticolorPartToBektas X).q1 = 0 :=
  rfl

/-- The Zorn color-slot embedding records the upper-right vector in quaternion form. -/
@[simp] theorem colorPartToBektas_q2 (X : ZMat R) :
    (colorPartToBektas X).q2 = vecToQuaternion X.x :=
  rfl

/-- The Zorn anticolor-slot embedding records the lower-left vector in quaternion form. -/
@[simp] theorem anticolorPartToBektas_q2 (X : ZMat R) :
    (anticolorPartToBektas X).q2 = vecToQuaternion X.y :=
  rfl

/-- The OP-sandwiched color part embeds to the same Bektaş cell as the raw upper-right vector. -/
theorem colorPartToBektas_of_colorPart (X : ZMat R) :
    colorPartToBektas (colorPart X) = colorPartToBektas X := by
  ext <;>
    simp [colorPartToBektas, vecToQuaternion, colorPart_shape]

/--
The OP-sandwiched anticolor part embeds to the same Bektaş cell as the raw lower-left vector.
-/
theorem anticolorPartToBektas_of_anticolorPart (X : ZMat R) :
    anticolorPartToBektas (anticolorPart X) = anticolorPartToBektas X := by
  ext <;>
    simp [anticolorPartToBektas, vecToQuaternion, anticolorPart_shape]

/--
Any `OP`-stabilizing composition map preserves the embedded Bektaş color lane after OP-sandwiching.
-/
theorem op_stabilizer_preserves_colorPartToBektas
    (f : ZMat R → ZMat R)
    (hf : IsOPStabilizingCompositionMap f)
    (X : ZMat R) :
    colorPartToBektas (f (colorPart X)) = colorPartToBektas (colorPart (f X)) := by
  rw [op_stabilizer_preserves_colorPart f hf X]

/--
Any `OP`-stabilizing composition map preserves the embedded Bektaş anticolor lane after OP-sandwiching.
-/
theorem op_stabilizer_preserves_anticolorPartToBektas
    (f : ZMat R → ZMat R)
    (hf : IsOPStabilizingCompositionMap f)
    (X : ZMat R) :
    anticolorPartToBektas (f (anticolorPart X)) = anticolorPartToBektas (anticolorPart (f X)) := by
  rw [op_stabilizer_preserves_anticolorPart f hf X]

end InfoGeometry.Projective.SplitOctonions.G2TrifactorColorBridge
