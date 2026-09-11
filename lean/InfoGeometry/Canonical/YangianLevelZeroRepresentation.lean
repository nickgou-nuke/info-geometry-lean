import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
# Level-zero representation substrate

This is the honest representation-theoretic layer below any Yangian claim.  It
uses Mathlib's `LieRingModule`/`LieModule` classes and packages the action of a
single Lie generator as a linear map.  No level-one generator, coproduct, or
Yangian relations are introduced here.
-/

variable {R L V : Type*}
  [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V]

/-- The linear endomorphism induced by one level-zero Lie generator. -/
def levelZeroAction (x : L) : V →ₗ[R] V where
  toFun := fun v => ⁅x, v⁆
  map_add' := fun v w => lie_add x v w
  map_smul' := fun r v => lie_smul r x v

/-- The Lie action satisfies the commutator identity on vectors. -/
theorem levelZeroAction_bracket (x y : L) (v : V) :
    levelZeroAction (R := R) ⁅x, y⁆ v =
      levelZeroAction (R := R) x (levelZeroAction (R := R) y v) -
        levelZeroAction (R := R) y (levelZeroAction (R := R) x v) := by
  simpa [levelZeroAction] using (lie_lie x y v).symm

/-- A vector annihilated by a chosen level-zero generator. -/
def IsLevelZeroInvariant (x : L) (v : V) : Prop :=
  levelZeroAction (R := R) x v = 0

/-- Level-zero invariants are closed under addition. -/
theorem levelZeroInvariant_add
    (x : L) (v w : V)
    (hv : IsLevelZeroInvariant (R := R) x v)
    (hw : IsLevelZeroInvariant (R := R) x w) :
    IsLevelZeroInvariant (R := R) x (v + w) := by
  unfold IsLevelZeroInvariant at hv hw ⊢
  rw [map_add, hv, hw, add_zero]

end InfoGeometry.Canonical
