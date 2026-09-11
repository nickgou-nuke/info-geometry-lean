import InfoGeometry.Clifford.Cl55WittQuadraticReflection
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55WittReflectionGeneratedSubgroup

namespace InfoGeometry.Clifford.Clifford55

/-!
# Conjugation of quadratic reflections by native isometries

This is the normality identity needed by a reflection-generated subgroup.
It is proved directly from the quadratic polarization formula; no matrix
representation or external orthogonal-group theorem is used.
-/

theorem quadraticReflection_conjugate
    (f : Q55.IsometryEquiv Q55) (v : V55)
    (hv : Q55 v ≠ 0) :
    f.symm.trans ((quadraticReflection_isometry v hv).trans f) =
      quadraticReflection_isometry (f v) (by
        intro h
        apply hv
        rw [← f.map_app v, h]) := by
  have hpolar (a b : V55) :
      QuadraticMap.polar (⇑Q55) (f a) (f b) =
        QuadraticMap.polar (⇑Q55) a b := by
    change Q55 (f a + f b) - Q55 (f a) - Q55 (f b) =
      Q55 (a + b) - Q55 a - Q55 b
    rw [← map_add f a b, f.map_app (a + b), f.map_app a, f.map_app b]
  apply DFunLike.ext
  intro x
  have hpol := hpolar (f.symm x) v
  have hfx : f (f.symm x) = x := f.toLinearEquiv.apply_symm_apply x
  rw [hfx] at hpol
  change f (quadraticReflection v hv (f.symm x)) =
    quadraticReflection (f v) _ x
  rw [quadraticReflection_apply, quadraticReflection_apply]
  rw [map_sub, map_smul, hfx]
  rw [← hpol, ← f.map_app v]

theorem quadraticReflectionElement_conjugate
    (g : orthogonalGroup55) (v : V55) (hv : Q55 v ≠ 0) :
    g * quadraticReflectionElement v hv * g⁻¹ =
      quadraticReflectionElement (g.1 v) (by
        intro h
        apply hv
        rw [← g.2 v, h]) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.1 (quadraticReflection v hv (g⁻¹.1 x)) =
    quadraticReflection (g.1 v) _ x
  have h := quadraticReflection_conjugate
    (orthogonalGroup55ToIsometry g) v hv
  have hx := congrArg (fun f : Q55.IsometryEquiv Q55 => f x) h
  simpa [orthogonalGroup55ToIsometry] using hx

instance quadraticReflectionSubgroup_normal :
    quadraticReflectionSubgroup.Normal := by
  constructor
  intro n hn g
  refine Subgroup.closure_induction
    (p := fun n _ => g * n * g⁻¹ ∈ quadraticReflectionSubgroup) ?_ ?_ ?_ ?_ hn
  · intro n hn
    rcases hn with ⟨v, hv, rfl⟩
    rw [quadraticReflectionElement_conjugate]
    exact quadraticReflectionElement_mem_subgroup _ _
  · simp
  · intro x y hx hy
    intro hx' hy'
    rw [show g * (x * y) * g⁻¹ =
          (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact quadraticReflectionSubgroup.mul_mem hx' hy'
  · intro x hx
    intro hx'
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact quadraticReflectionSubgroup.inv_mem hx'

end InfoGeometry.Clifford.Clifford55
