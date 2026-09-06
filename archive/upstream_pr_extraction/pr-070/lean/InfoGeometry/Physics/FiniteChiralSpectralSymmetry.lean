import Mathlib.Algebra.Algebra.Bilinear

/-!
# Finite chiral spectral symmetry

This is the algebraic eigenmode statement behind chiral block pairing.  It
does not assert that an arbitrary real operator has a symmetric spectrum;
the symmetry is derived from an explicit anticommuting involution.
-/

namespace InfoGeometry.Physics.FiniteChiralSpectralSymmetry

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A vector is an eigenmode of a linear operator. -/
def IsEigenmode (T : V →ₗ[R] V) (mu : R) (v : V) : Prop :=
  T v = mu • v

theorem anticommuting_maps_eigenmode_neg
    (T S : V →ₗ[R] V) (hTS : T.comp S = -(S.comp T))
    {mu : R} {v : V} (hv : IsEigenmode T mu v) :
    IsEigenmode T (-mu) (S v) := by
  rw [IsEigenmode]
  calc
    T (S v) = -(S (T v)) := by
      have h := congrArg (fun f : V →ₗ[R] V => f v) hTS
      simpa [LinearMap.comp_apply] using h
    _ = -(S (mu • v)) := by rw [hv]
    _ = (-mu) • S v := by simp

theorem anticommuting_involution_preserves_nonzero
    (T S : V →ₗ[R] V) (hTS : T.comp S = -(S.comp T))
    (hS : S.comp S = LinearMap.id) {mu : R} {v : V}
    (hv : IsEigenmode T mu v) (hv0 : v ≠ 0) :
    IsEigenmode T (-mu) (S v) ∧ S v ≠ 0 := by
  refine ⟨anticommuting_maps_eigenmode_neg T S hTS hv, ?_⟩
  intro hSv
  have h := congrArg (fun f : V →ₗ[R] V => f v) hS
  have hSS : S (S v) = v := by
    simpa [LinearMap.comp_apply] using h
  apply hv0
  calc
    v = S (S v) := hSS.symm
    _ = S 0 := by rw [hSv]
    _ = 0 := S.map_zero

end InfoGeometry.Physics.FiniteChiralSpectralSymmetry
