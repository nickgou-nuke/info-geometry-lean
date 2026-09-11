import InfoGeometry.Clifford.RealQuadraticReflectionAlignment
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford

/-!
# Conjugation of generic real quadratic reflections

The reflection subgroup is normal because an isometry transports the normal
vector and preserves its nonzero quadratic value.  This is the generic native
form of the Q55 conjugation lemma.
-/

theorem realQuadraticReflection_conjugate
    {V : Type*} [AddCommGroup V] [Module ℝ V]
  (Q : QuadraticForm ℝ V) (f : Q.IsometryEquiv Q) (v : V)
    (hv : Q v ≠ 0) :
    f.symm.trans ((realQuadraticReflectionIsometry Q v hv).trans f) =
      realQuadraticReflectionIsometry Q (f v) (by
        intro h
        apply hv
        rw [← f.map_app v, h]) := by
  have hpolar (a b : V) :
      QuadraticMap.polar (⇑Q) (f a) (f b) =
        QuadraticMap.polar (⇑Q) a b := by
    change Q (f a + f b) - Q (f a) - Q (f b) =
      Q (a + b) - Q a - Q b
    rw [← map_add f a b, f.map_app (a + b), f.map_app a, f.map_app b]
  apply DFunLike.ext
  intro x
  have hpol := hpolar (f.symm x) v
  have hfx : f (f.symm x) = x := f.toLinearEquiv.apply_symm_apply x
  rw [hfx] at hpol
  change f (realQuadraticReflection Q v hv (f.symm x)) =
    realQuadraticReflection Q (f v) _ x
  rw [realQuadraticReflection_apply, realQuadraticReflection_apply]
  rw [map_sub, map_smul, hfx]
  rw [← hpol, ← f.map_app v]

theorem realQuadraticIsometry_preserves_polar
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (f : Q.IsometryEquiv Q) (a b : V) :
    QuadraticMap.polar (⇑Q) (f a) (f b) =
      QuadraticMap.polar (⇑Q) a b := by
  change Q (f a + f b) - Q (f a) - Q (f b) =
    Q (a + b) - Q a - Q b
  rw [← map_add f a b, f.map_app (a + b), f.map_app a, f.map_app b]

instance realQuadraticReflectionSubgroup_normal
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) :
    (realQuadraticReflectionSubgroup Q).Normal := by
  constructor
  intro n hn g
  refine Subgroup.closure_induction
    (p := fun n _ => g * n * g⁻¹ ∈ realQuadraticReflectionSubgroup Q)
    ?_ ?_ ?_ ?_ hn
  · intro n hn
    rcases hn with ⟨v, hv, rfl⟩
    rw [show g * realQuadraticReflectionIsometry Q v hv * g⁻¹ =
        realQuadraticReflectionIsometry Q (g v) (by
          intro h
          apply hv
          rw [← g.map_app v, h]) by
          apply DFunLike.ext _ _
          intro x
          change g (realQuadraticReflection Q v hv (g⁻¹ x)) =
            realQuadraticReflection Q (g v) _ x
          exact congrArg (fun f : Q.IsometryEquiv Q => f x)
            (realQuadraticReflection_conjugate Q g v hv)]
    exact realQuadraticReflectionIsometry_mem_subgroup Q _ _
  · simp
  · intro x y hx hy
    intro hx' hy'
    rw [show g * (x * y) * g⁻¹ =
          (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact (realQuadraticReflectionSubgroup Q).mul_mem hx' hy'
  · intro x hx
    intro hx'
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact (realQuadraticReflectionSubgroup Q).inv_mem hx'

end InfoGeometry.Clifford
