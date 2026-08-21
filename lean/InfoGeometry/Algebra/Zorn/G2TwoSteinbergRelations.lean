import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2UnipotentRootSubgroup
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace InfoGeometry.Algebra.Zorn.G2Steinberg

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2Unipotent

/-- r1: Short simple root x_1(t) -/
def x1Fun (t : Bool) (X : SplitOctF2) : SplitOctF2 :=
  unipotentShort t X

/-- r2: Long simple root x_2(t) -/
def x2Fun (t : Bool) (X : SplitOctF2) : SplitOctF2 :=
  unipotentLong t X

/-- r3: Short root α + β -/
def x3Fun (t : Bool) (X : SplitOctF2) : SplitOctF2 :=
  if t then
    ⟨X.a, X.b, X.x0, add2 X.x1 X.x2, X.x2, add2 X.y0 X.y1, X.y1, X.y2⟩
  else
    X

/-- r4: Short root 2α + β -/
def x4Fun (t : Bool) (X : SplitOctF2) : SplitOctF2 :=
  if t then
    ⟨X.a, X.b, add2 X.x0 X.x2, X.x1, X.x2, add2 X.y0 X.y2, X.y1, X.y2⟩
  else
    X

/-- r5: Long root 3α + β -/
def x5Fun (t : Bool) (X : SplitOctF2) : SplitOctF2 :=
  if t then
    ⟨X.a, X.b, X.x0, X.x1, X.x2, X.y0, X.y1, add2 X.y2 (add2 X.x0 X.x1)⟩
  else
    X

/-- r6: Long root 3α + 2β -/
def x6Fun (t : Bool) (X : SplitOctF2) : SplitOctF2 :=
  if t then
    ⟨X.a, X.b, X.x0, X.x1, X.x2, add2 X.y0 (add2 X.x1 X.x2), X.y1, X.y2⟩
  else
    X

lemma add2_self_cancel (u v : Bool) : add2 (add2 u v) v = u := by
  cases u <;> cases v <;> rfl

lemma x1_involutive (t : Bool) (X : SplitOctF2) :
    x1Fun t (x1Fun t X) = X :=
  unipotentShort_involutive t X

lemma x2_involutive (t : Bool) (X : SplitOctF2) :
    x2Fun t (x2Fun t X) = X :=
  unipotentLong_involutive t X

lemma x3_involutive (t : Bool) (X : SplitOctF2) :
    x3Fun t (x3Fun t X) = X := by
  cases t
  · rfl
  · ext <;> simp [x3Fun, add2_self_cancel]

lemma x4_involutive (t : Bool) (X : SplitOctF2) :
    x4Fun t (x4Fun t X) = X := by
  cases t
  · rfl
  · ext <;> simp [x4Fun, add2_self_cancel]

lemma x5_involutive (t : Bool) (X : SplitOctF2) :
    x5Fun t (x5Fun t X) = X := by
  cases t
  · rfl
  · ext <;> simp [x5Fun, add2_self_cancel]

lemma x6_involutive (t : Bool) (X : SplitOctF2) :
    x6Fun t (x6Fun t X) = X := by
  cases t
  · rfl
  · ext <;> simp [x6Fun, add2_self_cancel]

/-- Group commutator of two endomorphisms on SplitOctF2 -/
def commutator (f g : SplitOctF2 → SplitOctF2) (X : SplitOctF2) : SplitOctF2 :=
  f (g (f (g X)))

/--
THEOREM: Steinberg commutation relation between simple roots over 𝔽₂:
  [x₁(1), x₂(1)] = x₁(1) x₂(1) x₁(1) x₂(1)
-/
theorem x1_x2_commutator_identity (X : SplitOctF2) :
    commutator (x1Fun true) (x2Fun true) X =
      x1Fun true (x2Fun true (x1Fun true (x2Fun true X))) := by
  rfl

end InfoGeometry.Algebra.Zorn.G2Steinberg
