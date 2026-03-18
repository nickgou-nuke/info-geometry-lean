import InfoGeometry.Canonical.MultiplicativeToAdditiveBridge
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
structure RelativeWeight (X W : Type*) where
  weight : X → X → W

/-- Additive logarithmic generator extracted from a relative weight. -/
structure LogGenerator (W G : Type*) where
  logGen : W → G

namespace LogGenerator

variable {W G : Type*}

/-- Evaluate the additive generator. -/
def apply (L : LogGenerator W G) (w : W) : G :=
  L.logGen w

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
structure ExactDescentLogGenerator (M S A : Type*)
    [Monoid M] [CommMonoid S] [AddCommMonoid A] where
  toBridge : ExactMultiplicativeToAdditiveBridge M S A

namespace ExactDescentLogGenerator

variable {M S A : Type*} [Monoid M] [CommMonoid S] [AddCommMonoid A]

/-- Promote an exact bridge to the high-level exact log-generator layer. -/
def ofBridge (B : ExactMultiplicativeToAdditiveBridge M S A) :
    ExactDescentLogGenerator M S A :=
  ⟨B⟩

/-- The additive generator induced on the source type. -/
def additiveInvariant (L : ExactDescentLogGenerator M S A) : M → A :=
  L.toBridge.additiveInvariant

/-- Forget the exact branch to the common log-generator interface. -/
def toLogGenerator (L : ExactDescentLogGenerator M S A) : LogGenerator M A where
  logGen := L.additiveInvariant

/-- Exact descent yields an additive law on the source. -/
theorem map_mul (L : ExactDescentLogGenerator M S A) (x y : M) :
    L.additiveInvariant (x * y) = L.additiveInvariant x + L.additiveInvariant y :=
  ExactMultiplicativeToAdditiveBridge.additiveInvariant_mul L.toBridge x y

end ExactDescentLogGenerator

/--
Defective descent branch: multiplicative descent carries an anomaly term that
survives as an additive defect after linearization.
-/
structure DefectiveDescentLogGenerator (M S A : Type*)
    [Monoid M] [CommMonoid S] [AddCommMonoid A] where
  toBridge : DefectiveMultiplicativeToAdditiveBridge M S A

namespace DefectiveDescentLogGenerator

variable {M S A : Type*} [Monoid M] [CommMonoid S] [AddCommMonoid A]

/-- Promote a defective bridge to the high-level defective log-generator layer. -/
def ofBridge (B : DefectiveMultiplicativeToAdditiveBridge M S A) :
    DefectiveDescentLogGenerator M S A :=
  ⟨B⟩

/-- The additive generator induced on the source type. -/
def additiveInvariant (L : DefectiveDescentLogGenerator M S A) : M → A :=
  L.toBridge.additiveInvariant

/-- The additive anomaly term induced by defective descent. -/
def additiveDefect (L : DefectiveDescentLogGenerator M S A) : M → M → A :=
  L.toBridge.additiveDefect

/-- Forget the defective branch to the common log-generator interface. -/
def toLogGenerator (L : DefectiveDescentLogGenerator M S A) : LogGenerator M A where
  logGen := L.additiveInvariant

/-- Defective descent yields an additive law with an anomaly term. -/
theorem map_mul_defect (L : DefectiveDescentLogGenerator M S A) (x y : M) :
    L.additiveInvariant (x * y) =
      L.additiveDefect x y + (L.additiveInvariant x + L.additiveInvariant y) :=
  DefectiveMultiplicativeToAdditiveBridge.additiveInvariant_mul L.toBridge x y

end DefectiveDescentLogGenerator

/--
Operator-level branch: functional-calculus linearization happens before full
commutative descent.
-/
structure OperatorLogGenerator (O A : Type*)
    [Monoid O] [AddCommMonoid A] where
  toLinearization : FunctionalCalculusLinearization O A

namespace OperatorLogGenerator

variable {O A : Type*} [Monoid O] [AddCommMonoid A]

/-- Promote a functional-calculus linearization to the operator log-generator layer. -/
def ofLinearization (L : FunctionalCalculusLinearization O A) :
    OperatorLogGenerator O A :=
  ⟨L⟩

/-- The operator-level logarithmic generator. -/
def linearize (L : OperatorLogGenerator O A) : O → A :=
  L.toLinearization.linearize

/-- Forget the operator branch to the common log-generator interface. -/
def toLogGenerator (L : OperatorLogGenerator O A) : LogGenerator O A where
  logGen := L.linearize

/-- Functional-calculus linearization is additive on commuting products. -/
theorem map_mul_of_commute (L : OperatorLogGenerator O A) {x y : O}
    (hxy : Commute x y) :
    L.linearize (x * y) = L.linearize x + L.linearize y :=
  FunctionalCalculusLinearization.map_mul_of_commute_apply L.toLinearization hxy

end OperatorLogGenerator

end InfoGeometry.Canonical
