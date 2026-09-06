import Mathlib

/-!
# Eigenvector transport through a Lie equivalence

This is the carrier-level core of root-space transport.  It makes no claim
about a particular Cartan, root system, or normalization: the old eigenvector
equation is simply transported along a genuine Lie equivalence.
-/

theorem LinearEquiv.map_bracket_eigenvector
    {R L : Type*}
    [CommRing R] [LieRing L] [Module R L]
    [LieAlgebra R L]
    (e : L ≃ₗ[R] L)
    (hbracket : ∀ u v, e ⁅u, v⁆ = ⁅e u, e v⁆)
    (x H K : L) (a : R)
    (hHK : e K = H)
    (heigen : ⁅K, x⁆ = a • x) :
    ⁅H, e x⁆ = a • e x := by
  calc
    ⁅H, e x⁆ = ⁅e K, e x⁆ := by rw [hHK]
    _ = e ⁅K, x⁆ := (hbracket K x).symm
    _ = e (a • x) := by rw [heigen]
    _ = a • e x := by exact e.map_smul a x

theorem LinearEquiv.map_eigenvector_under_conjugate_weight
    {R L H : Type*}
    [CommRing R] [LieRing L] [Module R L] [LieAlgebra R L]
    [AddCommGroup H] [Module R H]
    (e : L ≃ₗ[R] L) (c : H ≃ₗ[R] H)
    (ι : H →ₗ[R] L)
    (hbracket : ∀ u v, e ⁅u, v⁆ = ⁅e u, e v⁆)
    (hι : ∀ h, e (ι h) = ι (c h))
    (α : H →ₗ[R] R) (h : H) (x : L)
    (heigen : ⁅ι (c.symm h), x⁆ = α (c.symm h) • x) :
    ⁅ι h, e x⁆ = (α.comp c.symm.toLinearMap) h • e x := by
  have hι' : ι h = e (ι (c.symm h)) := by
    rw [hι]
    exact (congrArg ι (c.apply_symm_apply h)).symm
  rw [hι']
  rw [e.map_bracket_eigenvector hbracket x
    (e (ι (c.symm h))) (ι (c.symm h)) (α (c.symm h)) rfl heigen]
  simp [LinearMap.comp_apply]
