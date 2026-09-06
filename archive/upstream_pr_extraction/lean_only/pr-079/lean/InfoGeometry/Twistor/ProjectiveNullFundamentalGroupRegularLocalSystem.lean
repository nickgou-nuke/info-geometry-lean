import InfoGeometry.Twistor.ProjectiveNullConfigurationLocalSystemMonodromy
import InfoGeometry.Twistor.ProjectiveNullFundamentalGroupRegularMonodromy
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# The path-torsor local system and regular fundamental-group monodromy

Fixing a basepoint `x`, the fiber over `y` is the free module on homotopy
classes of paths from `x` to `y`.  A fundamental-groupoid arrow transports a
basis path by concatenation.  At the basepoint this categorical transport is
exactly the faithful left-regular representation of the actual fundamental
group.

This constructs a genuine `ModuleCat`-valued local system retaining full path
classes.  It does not identify selected loops with Artin generators or supply
a Yang--Baxter, conformal-block, or anyon representation.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullFundamentalGroupRegularLocalSystem

open CategoryTheory
open InfoGeometry.Twistor.ProjectiveNullConfigurationLocalSystemMonodromy
open InfoGeometry.Twistor.ProjectiveNullFundamentalGroupRegularMonodromy

/-- Concatenation with a groupoid arrow is an equivalence between based path
torsors. -/
def basedPathPostcompEquiv
    {X : Type*} [TopologicalSpace X] (base : X)
    {y z : X} (gamma : Path.Homotopic.Quotient y z) :
    Path.Homotopic.Quotient base y ≃
      Path.Homotopic.Quotient base z where
  toFun delta := delta.trans gamma
  invFun delta := delta.trans gamma.symm
  left_inv delta := by
    dsimp
    rw [Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.trans_refl]
  right_inv delta := by
    dsimp
    rw [Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl]

@[simp] theorem basedPathPostcompEquiv_refl
    {X : Type*} [TopologicalSpace X] (base y : X) :
    basedPathPostcompEquiv base (Path.Homotopic.Quotient.refl y) =
      Equiv.refl (Path.Homotopic.Quotient base y) := by
  apply Equiv.ext
  intro delta
  exact Path.Homotopic.Quotient.trans_refl delta

theorem basedPathPostcompEquiv_trans
    {X : Type*} [TopologicalSpace X] (base : X)
    {y z w : X} (gamma : Path.Homotopic.Quotient y z)
    (delta : Path.Homotopic.Quotient z w) :
    (basedPathPostcompEquiv base gamma).trans
        (basedPathPostcompEquiv base delta) =
      basedPathPostcompEquiv base (gamma.trans delta) := by
  apply Equiv.ext
  intro eta
  exact Path.Homotopic.Quotient.trans_assoc eta gamma delta

/-- The free-module local system on based path torsors. -/
def basedPathRegularLocalSystem
    (R X : Type*) [Ring R] [TopologicalSpace X] (base : X) :
    FundamentalGroupoid X ⥤ ModuleCat R where
  obj y := ModuleCat.of R
    (Path.Homotopic.Quotient base y.as →₀ R)
  map {y z} gamma := ModuleCat.ofHom
    (Finsupp.domLCongr (R := R) (M := R)
      (basedPathPostcompEquiv base gamma)).toLinearMap
  map_id y := by
    change ModuleCat.ofHom (Finsupp.domLCongr (R := R) (M := R)
      (basedPathPostcompEquiv base
        (Path.Homotopic.Quotient.refl y.as))).toLinearMap =
      𝟙 (ModuleCat.of R
        (Path.Homotopic.Quotient base y.as →₀ R))
    rw [basedPathPostcompEquiv_refl]
    ext u i
    simp
  map_comp gamma delta := by
    change ModuleCat.ofHom (Finsupp.domLCongr (R := R) (M := R)
      (basedPathPostcompEquiv base (gamma.trans delta))).toLinearMap =
      ModuleCat.ofHom (Finsupp.domLCongr (R := R) (M := R)
        (basedPathPostcompEquiv base gamma)).toLinearMap ≫
      ModuleCat.ofHom (Finsupp.domLCongr (R := R) (M := R)
        (basedPathPostcompEquiv base delta)).toLinearMap
    rw [← basedPathPostcompEquiv_trans]
    ext u i
    simp

/-- On a path-basis vector, transport is literal path concatenation. -/
@[simp] theorem basedPathRegularLocalSystem_map_single
    (R X : Type*) [Ring R] [TopologicalSpace X] (base : X)
    {y z : FundamentalGroupoid X} (gamma : y ⟶ z)
    (delta : Path.Homotopic.Quotient base y.as) (r : R) :
    ((basedPathRegularLocalSystem R X base).map gamma).hom
        (Finsupp.single delta r) =
      Finsupp.single (delta.trans gamma) r := by
  exact Finsupp.domLCongr_single
    (basedPathPostcompEquiv base gamma) delta r

/-- At the basepoint, categorical path-torsor monodromy is exactly the native
left-regular representation. -/
def basedPathRegularLinearMonodromy
    (R X : Type*) [Ring R] [TopologicalSpace X] (base : X) :
    FundamentalGroup X base →*
      LinearMap.GeneralLinearGroup R
        (GroupRegularModule R (FundamentalGroup X base)) :=
  ((moduleCatEndToLinearEnd
      ((basedPathRegularLocalSystem R X base).obj
        (FundamentalGroupoid.mk base))).comp
    ((basedPathRegularLocalSystem R X base).mapEnd
      (FundamentalGroupoid.mk base))).toHomUnits

/-- At the basepoint, categorical path-torsor monodromy acts by native left
multiplication on every basis vector. -/
@[simp] theorem basedPathRegularLocalSystem_monodromy_single
    (R X : Type*) [Ring R] [TopologicalSpace X] (base : X)
    (gamma delta : FundamentalGroup X base) (r : R) :
    (basedPathRegularLinearMonodromy R X base gamma :
      GroupRegularModule R (FundamentalGroup X base) →ₗ[R]
        GroupRegularModule R (FundamentalGroup X base))
        (Finsupp.single delta r) =
      Finsupp.single (gamma * delta) r := by
  exact basedPathRegularLocalSystem_map_single R X base gamma delta r

/-- The complete categorical path-torsor monodromy agrees with the previously
exposed faithful regular representation, not only on named basis vectors. -/
theorem basedPathRegularLinearMonodromy_eq_regular
    (R X : Type*) [Ring R] [TopologicalSpace X] (base : X) :
    basedPathRegularLinearMonodromy R X base =
      fundamentalGroupRegularMonodromy R X base := by
  apply MonoidHom.ext
  intro gamma
  apply Units.ext
  apply LinearMap.ext
  intro x
  refine Finsupp.induction x ?_ ?_
  · rfl
  · intro delta r f hdelta hr ih
    rw [map_add, map_add, basedPathRegularLocalSystem_monodromy_single,
      fundamentalGroupRegularMonodromy_single, ih]

end InfoGeometry.Twistor.ProjectiveNullFundamentalGroupRegularLocalSystem
