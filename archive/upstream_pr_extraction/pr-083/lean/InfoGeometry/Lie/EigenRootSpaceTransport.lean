import InfoGeometry.Lie.LieEquivEigenvectorTransport

/-!
# Transport of eigen-root spaces

The concrete Cartan normalizer supplies the maps `ι` and `c`.  This file keeps
the resulting root-space argument independent of any coordinate readback.
-/

def eigenRootSpace
    {R L H : Type*} [CommRing R] [LieRing L] [Module R L]
    [LieAlgebra R L] [AddCommGroup H] [Module R H]
    (ι : H →ₗ[R] L) (α : H →ₗ[R] R) : Set L :=
  {x | ∀ h, ⁅ι h, x⁆ = α h • x}

theorem LinearEquiv.map_mem_eigenRootSpace
    {R L H : Type*} [CommRing R] [LieRing L] [Module R L]
    [LieAlgebra R L] [AddCommGroup H] [Module R H]
    (e : L ≃ₗ[R] L) (c : H ≃ₗ[R] H)
    (ι : H →ₗ[R] L)
    (hbracket : ∀ u v, e ⁅u, v⁆ = ⁅e u, e v⁆)
    (hι : ∀ h, e (ι h) = ι (c h))
    (α : H →ₗ[R] R) (x : L)
    (hx : x ∈ eigenRootSpace ι α) :
    e x ∈ eigenRootSpace ι (α.comp c.symm.toLinearMap) := by
  intro h
  apply e.map_eigenvector_under_conjugate_weight c ι hbracket hι α h x
  exact hx (c.symm h)
