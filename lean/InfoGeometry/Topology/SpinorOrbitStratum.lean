import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Physics.Pin55Formal

/-!
# Quadratic-form zero/null/generic strata

This module provides a theorem-safe trichotomy for any module equipped with a
quadratic form:

* zero: `x = 0`;
* null: `x ≠ 0` and `Q x = 0`;
* generic: `Q x ≠ 0`.

It also specializes the trichotomy to the concrete split `(5,5)` form `q55`
from `Physics/Pin55Formal.lean`.

The module gives the predicate and case-split layer used by the `(5,5)` orbit
stratum files.
-/

namespace InfoGeometry.Topology.SpinorOrbitStratum

open InfoGeometry.Physics.Pin55Formal

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Zero/null/generic stratum of a vector with respect to a quadratic form. -/
inductive OrbitStratum (Q : QuadraticForm R M) (x : M) : Prop where
  | isZero : x = 0 → OrbitStratum Q x
  | isNull : x ≠ 0 → Q x = 0 → OrbitStratum Q x
  | isGeneric : Q x ≠ 0 → OrbitStratum Q x

/-- The proposition-level trichotomy induced by equality to zero and the value of `Q`. -/
theorem orbit_classify_trichotomy [DecidableEq R] [DecidableEq M]
    (Q : QuadraticForm R M) (x : M) :
    (x = 0) ∨ (x ≠ 0 ∧ Q x = 0) ∨ (Q x ≠ 0) := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    by_cases hQ : Q x = 0
    · exact Or.inl ⟨hx, hQ⟩
    · exact Or.inr hQ

/-- Constructive stratum property for any vector. -/
def classifyOrbit [DecidableEq R] [DecidableEq M]
    (Q : QuadraticForm R M) (x : M) : OrbitStratum Q x := by
  by_cases hx : x = 0
  · exact OrbitStratum.isZero hx
  · by_cases hQ : Q x = 0
    · exact OrbitStratum.isNull hx hQ
    · exact OrbitStratum.isGeneric hQ

/-- The zero and null predicates are incompatible. -/
theorem zero_not_null {Q : QuadraticForm R M} {x : M}
    (hzero : x = 0) : ¬ (x ≠ 0 ∧ Q x = 0) := by
  intro h
  exact h.1 hzero

/-- The zero and generic predicates are incompatible. -/
theorem zero_not_generic {Q : QuadraticForm R M} {x : M}
    (hzero : x = 0) : ¬ Q x ≠ 0 := by
  intro hQ
  subst x
  simp at hQ

/-- The null and generic predicates are incompatible. -/
theorem null_not_generic {Q : QuadraticForm R M} {x : M}
    (hnull : x ≠ 0 ∧ Q x = 0) : ¬ Q x ≠ 0 := by
  intro hgeneric
  exact hgeneric hnull.2

/-! ## Concrete `(5,5)` specialization -/

/-- Coordinate carrier for the concrete split `(5,5)` form from `Pin55Formal`. -/
abbrev Vec55 := Fin 10 → ℚ

/-- Zero/null/generic stratum for the concrete `q55` coordinate form. -/
abbrev Q55Stratum (x : Vec55) : Prop :=
  OrbitStratum q55 x

/-- Concrete `q55` trichotomy. -/
theorem q55_orbit_classify_trichotomy (x : Vec55) :
    (x = 0) ∨
      (x ≠ 0 ∧ q55 x = 0) ∨
        (q55 x ≠ 0) :=
  orbit_classify_trichotomy q55 x

/-- Concrete `q55` stratum classifier. -/
def classifyQ55Orbit (x : Vec55) : Q55Stratum x :=
  classifyOrbit q55 x

/-- The positive basis vector `ε₀` is generic for `q55`. -/
theorem q55_epsilon0_isGeneric :
    Q55Stratum ε₀ := by
  exact OrbitStratum.isGeneric (by simp [q55_ε₀])

/-- The negative basis vector `ε₅` is generic for `q55`. -/
theorem q55_epsilon5_isGeneric :
    Q55Stratum ε₅ := by
  exact OrbitStratum.isGeneric (by simp [q55_ε₅])

/-! ## Stratum preservation under quadratic-value preserving maps -/

/-- A map that is sufficient to preserve the zero/null/generic quadratic strata.

The hypotheses are intentionally explicit and local: zero is mapped to zero,
zero is reflected, and the quadratic value is preserved.  No group action,
quotient, spin representation, or orbit theorem is asserted here. -/
abbrev PreservesOrbitStrata (Q : QuadraticForm R M) (f : M → M) : Prop :=
  f 0 = 0 ∧
    (∀ {x : M}, f x = 0 → x = 0) ∧
    ∀ x : M, Q (f x) = Q x

/-- A zero/null/generic stratum is preserved by any map satisfying
`PreservesOrbitStrata`. -/
theorem map_stratum_of_preserves {Q : QuadraticForm R M} {f : M → M}
    (hf : PreservesOrbitStrata Q f) {x : M} :
    OrbitStratum Q x → OrbitStratum Q (f x) := by
  intro h
  cases h with
  | isZero hx =>
      exact OrbitStratum.isZero (by rw [hx]; exact hf.1)
  | isNull hx hQ =>
      exact OrbitStratum.isNull
        (by
          intro hfx
          exact hx (hf.2.1 hfx))
        (by simpa [hf.2.2 x] using hQ)
  | isGeneric hQ =>
      exact OrbitStratum.isGeneric (by
        intro hfx
        exact hQ (by simpa [hf.2.2 x] using hfx))

/-- Coordinatewise negation on the concrete `q55` carrier. -/
def q55NegAll (x : Vec55) : Vec55 := fun i => -x i

@[simp] theorem q55NegAll_zero : q55NegAll 0 = 0 := by
  funext i
  simp [q55NegAll]

/-- Coordinatewise negation reflects zero. -/
theorem q55NegAll_reflect_zero {x : Vec55} : q55NegAll x = 0 → x = 0 := by
  intro hx
  funext i
  have hi := congrArg (fun f : Vec55 => f i) hx
  simpa [q55NegAll] using hi

/-- Coordinatewise negation preserves the concrete split `(5,5)` quadratic form. -/
theorem q55NegAll_preserves_q55 (x : Vec55) :
    q55 (q55NegAll x) =
      q55 x := by
  simp [q55, q55NegAll]

/-- Coordinatewise negation preserves the zero/null/generic strata for `q55`. -/
theorem q55NegAll_preserves_orbit_strata :
    PreservesOrbitStrata q55 q55NegAll := by
  refine ⟨q55NegAll_zero, ?_, q55NegAll_preserves_q55⟩
  intro x hx
  exact q55NegAll_reflect_zero hx

/-- Concrete stratum transport under coordinatewise negation. -/
theorem q55NegAll_maps_stratum {x : Vec55} :
    Q55Stratum x → Q55Stratum (q55NegAll x) :=
  map_stratum_of_preserves q55NegAll_preserves_orbit_strata

end InfoGeometry.Topology.SpinorOrbitStratum
