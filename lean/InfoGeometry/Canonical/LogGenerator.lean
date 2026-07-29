import InfoGeometry.Canonical.MultiplicativeToAdditiveBridge
import InfoGeometry.Canonical.SpineAttributes
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace InfoGeometry.Canonical

/-!
# Log Generator

High-level naming layer for the canonical relative-geometry spine.

This file introduces the abstract stages

`RelativeWeight -> LogGenerator`

while keeping the exact, defective, and operator-level branches separate via
small wrapper structures around the more detailed bridge objects.
-/

/-- Relative multiplicative datum attached to a pair of states/objects. -/
abbrev RelativeWeight (X W : Type*) := X → X → W

/-- Additive logarithmic generator extracted from a relative weight. -/
abbrev LogGenerator (W G : Type*) := W → G

attribute [spine_object] RelativeWeight LogGenerator

namespace LogGenerator

variable {W G : Type*}

/-- Evaluate the additive generator. -/
def apply (L : LogGenerator W G) (w : W) : G :=
  L w

end LogGenerator

/-- Canonical logarithmic linearization on real units. -/
noncomputable def logAbsUnitsLinearization : AdditiveLinearization ℝˣ ℝ where
  linearize u := Real.log |(u : ℝ)|
  map_mul x y := by
    rw [Units.val_mul, abs_mul, Real.log_mul]
    · exact abs_ne_zero.mpr (Units.ne_zero _)
    · exact abs_ne_zero.mpr (Units.ne_zero _)

/--
Exact descent branch: a multiplicative source descends to a commutative
invariant and then linearizes additively.
-/
abbrev ExactDescentLogGenerator (M S A : Type*)
    [Monoid M] [CommMonoid S] [AddCommMonoid A] :=
  ExactMultiplicativeToAdditiveBridge M S A

namespace ExactDescentLogGenerator

variable {M S A : Type*} [Monoid M] [CommMonoid S] [AddCommMonoid A]

/-- Promote an exact bridge to the high-level exact log-generator layer. -/
def ofBridge (B : ExactMultiplicativeToAdditiveBridge M S A) :
    ExactDescentLogGenerator M S A := B

/-- The additive generator induced on the source type. -/
abbrev additiveInvariant (L : ExactDescentLogGenerator M S A) : M → A :=
  ExactMultiplicativeToAdditiveBridge.additiveInvariant L

/-- Forget the exact branch to the common log-generator interface. -/
def toLogGenerator (L : ExactDescentLogGenerator M S A) : LogGenerator M A :=
  ExactMultiplicativeToAdditiveBridge.additiveInvariant L

/-- Exact descent yields an additive law on the source. -/
theorem map_mul (L : ExactDescentLogGenerator M S A) (x y : M) :
    L.additiveInvariant (x * y) = L.additiveInvariant x + L.additiveInvariant y :=
  ExactMultiplicativeToAdditiveBridge.additiveInvariant_mul L x y

attribute [spine_morphism, spine_functor, spine_functor_constructor]
  ExactDescentLogGenerator.toLogGenerator

end ExactDescentLogGenerator

/--
Defective descent branch: multiplicative descent carries an anomaly term that
survives as an additive defect after linearization.
-/
abbrev DefectiveDescentLogGenerator (M S A : Type*)
    [Monoid M] [CommMonoid S] [AddCommMonoid A] :=
  DefectiveMultiplicativeToAdditiveBridge M S A

namespace DefectiveDescentLogGenerator

variable {M S A : Type*} [Monoid M] [CommMonoid S] [AddCommMonoid A]

/-- Promote a defective bridge to the high-level defective log-generator layer. -/
def ofBridge (B : DefectiveMultiplicativeToAdditiveBridge M S A) :
    DefectiveDescentLogGenerator M S A := B

/-- The additive generator induced on the source type. -/
abbrev additiveInvariant (L : DefectiveDescentLogGenerator M S A) : M → A :=
  DefectiveMultiplicativeToAdditiveBridge.additiveInvariant L

/-- The additive anomaly term induced by defective descent. -/
abbrev additiveDefect (L : DefectiveDescentLogGenerator M S A) : M → M → A :=
  DefectiveMultiplicativeToAdditiveBridge.additiveDefect L

/-- Forget the defective branch to the common log-generator interface. -/
def toLogGenerator (L : DefectiveDescentLogGenerator M S A) : LogGenerator M A :=
  DefectiveMultiplicativeToAdditiveBridge.additiveInvariant L

/-- Defective descent yields an additive law with an anomaly term. -/
theorem map_mul_defect (L : DefectiveDescentLogGenerator M S A) (x y : M) :
    L.additiveInvariant (x * y) =
      L.additiveDefect x y + (L.additiveInvariant x + L.additiveInvariant y) :=
  DefectiveMultiplicativeToAdditiveBridge.additiveInvariant_mul L x y

attribute [spine_morphism, spine_functor, spine_functor_constructor]
  DefectiveDescentLogGenerator.toLogGenerator

end DefectiveDescentLogGenerator

/--
Operator-level branch: functional-calculus linearization happens before full
commutative descent.
-/
abbrev OperatorLogGenerator (O A : Type*)
    [Monoid O] [AddCommMonoid A] :=
  FunctionalCalculusLinearization O A

namespace OperatorLogGenerator

variable {O A : Type*} [Monoid O] [AddCommMonoid A]

/-- Promote a functional-calculus linearization to the operator log-generator layer. -/
def ofLinearization (L : FunctionalCalculusLinearization O A) :
    OperatorLogGenerator O A := L

/-- The operator-level logarithmic generator. -/
abbrev linearize (L : OperatorLogGenerator O A) : O → A :=
  FunctionalCalculusLinearization.linearize L

/-- Forget the operator branch to the common log-generator interface. -/
def toLogGenerator (L : OperatorLogGenerator O A) : LogGenerator O A :=
  FunctionalCalculusLinearization.linearize L

/-- Functional-calculus linearization is additive on commuting products. -/
theorem map_mul_of_commute (L : OperatorLogGenerator O A) {x y : O}
    (hxy : Commute x y) :
    L.linearize (x * y) = L.linearize x + L.linearize y :=
  FunctionalCalculusLinearization.map_mul_of_commute_apply L hxy

attribute [spine_morphism, spine_functor, spine_functor_constructor]
  OperatorLogGenerator.toLogGenerator

end OperatorLogGenerator

end InfoGeometry.Canonical
