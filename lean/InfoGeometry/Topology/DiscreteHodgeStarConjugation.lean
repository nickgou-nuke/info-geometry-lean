import InfoGeometry.Canonical.DiscreteDiracHodgeChiral
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
  Finite Hodge-star conjugation for endomorphisms of a cochain carrier.

  This is the reusable operator layer behind a discrete codifferential.  A
  geometric star, an inner product, or a continuum Hodge theorem is not
  assumed here: the input is an explicit linear equivalence.
-/

namespace InfoGeometry.Topology.DiscreteHodgeStarConjugation

open InfoGeometry.Canonical.DiscreteDiracHodgeChiral

noncomputable section

def conjugateCodifferential
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (star : V ≃ₗ[ℝ] V) (d : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  (star.symm.toLinearMap : V →ₗ[ℝ] V).comp
    (d.comp (star.toLinearMap : V →ₗ[ℝ] V))

theorem conjugateCodifferential_sq_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (star : V ≃ₗ[ℝ] V) (d : V →ₗ[ℝ] V)
    (hd : d.comp d = 0) :
    (conjugateCodifferential star d).comp
        (conjugateCodifferential star d) = 0 := by
  ext x
  have hdx : d (d (star x)) = 0 := by
    have h := congrArg (fun f : V →ₗ[ℝ] V => f (star x)) hd
    simpa [LinearMap.comp_apply] using h
  simp [conjugateCodifferential, LinearMap.comp_apply, hdx]

def hodgeDirac
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d cod : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  d + cod

def hodgeLaplacian
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d cod : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  d.comp cod + cod.comp d

theorem hodgeDirac_sq_eq_laplacian
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : V →ₗ[ℝ] V) (star : V ≃ₗ[ℝ] V)
    (hd : d.comp d = 0) :
    (hodgeDirac d (conjugateCodifferential star d)).comp
        (hodgeDirac d (conjugateCodifferential star d)) =
      hodgeLaplacian d (conjugateCodifferential star d) := by
  exact diracHodge_sq_eq_hodgeLaplacian d
    (conjugateCodifferential star d) hd
    (conjugateCodifferential_sq_zero star d hd)

theorem identityStar_conjugateCodifferential
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : V →ₗ[ℝ] V) :
    conjugateCodifferential (LinearEquiv.refl ℝ V) d = d := by
  ext x
  rfl

end

end InfoGeometry.Topology.DiscreteHodgeStarConjugation
