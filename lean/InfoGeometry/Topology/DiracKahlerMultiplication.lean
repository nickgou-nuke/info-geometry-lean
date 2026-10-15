import InfoGeometry.Topology.DiscreteHodgeStarConjugation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
  The theorem-honest Portal 4 surface.

  A finite Dirac--Kähler datum is an endomorphism-level package: the odd
  differential, its codifferential, and a grading operator.  The Clifford
  multiplication rules are expressed as composition and anticommutator
  identities.  No unconstructed `Cl(5,5)` gamma-matrix representation is
  claimed here.
-/

namespace InfoGeometry.Topology.DiracKahlerMultiplication

open InfoGeometry.Canonical.DiscreteDiracHodgeChiral

noncomputable section

structure Data (V : Type*) [AddCommGroup V] [Module ℝ V] where
  d : V →ₗ[ℝ] V
  codifferential : V →ₗ[ℝ] V
  chirality : V →ₗ[ℝ] V
  d_sq_zero : d.comp d = 0
  codifferential_sq_zero : codifferential.comp codifferential = 0
  d_anticommutes : d.comp chirality = -(chirality.comp d)
  codifferential_anticommutes :
    codifferential.comp chirality = -(chirality.comp codifferential)

namespace Data

end Data

def dirac {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Data V) : V →ₗ[ℝ] V :=
  D.d + D.codifferential

def laplacian {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Data V) : V →ₗ[ℝ] V :=
  D.d.comp D.codifferential + D.codifferential.comp D.d

theorem dirac_square
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Data V) :
    (dirac D).comp (dirac D) = laplacian D := by
  exact diracHodge_sq_eq_hodgeLaplacian D.d D.codifferential
    D.d_sq_zero D.codifferential_sq_zero

theorem dirac_anticommutes_chirality
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Data V) :
    (dirac D).comp D.chirality =
      -(D.chirality.comp (dirac D)) := by
  exact diracHodge_anticommutes_chirality D.d D.codifferential D.chirality
    D.d_anticommutes D.codifferential_anticommutes

theorem laplacian_commutes_chirality
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Data V) :
    (laplacian D).comp D.chirality =
      D.chirality.comp (laplacian D) := by
  exact hodgeLaplacian_commutes_chirality D.d D.codifferential D.chirality
    D.d_sq_zero D.codifferential_sq_zero
    D.d_anticommutes D.codifferential_anticommutes

theorem dirac_square_expansion
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Data V) :
    (dirac D).comp (dirac D) =
      D.d.comp D.d + D.d.comp D.codifferential +
        (D.codifferential.comp D.d +
          D.codifferential.comp D.codifferential) := by
  ext x
  simp [dirac, LinearMap.comp_apply, LinearMap.add_apply, add_assoc, add_left_comm, add_comm]

/-! ### Sum and difference of the two nilpotents -/

/-- The difference Dirac operator `𝒟₋ = d − δ` squares to the negative Hodge
Laplacian: `(d − δ)² = −(dδ + δd)`. -/
theorem diracDifference_sq_eq_neg_laplacian
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Data V) :
    (D.d - D.codifferential).comp (D.d - D.codifferential) =
      -laplacian D := by
  ext x
  have hd : D.d (D.d x) = 0 := by
    have h := congrArg (fun f : V →ₗ[ℝ] V => f x) D.d_sq_zero
    simpa [LinearMap.comp_apply] using h
  have hc : D.codifferential (D.codifferential x) = 0 := by
    have h := congrArg (fun f : V →ₗ[ℝ] V => f x) D.codifferential_sq_zero
    simpa [LinearMap.comp_apply] using h
  simp only [laplacian, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.map_add, LinearMap.map_sub,
    LinearMap.neg_apply]
  rw [hd, hc]
  abel

/--
Anticommutation of the two Dirac operators assembled from the same pair of
nilpotents: the sum `𝒟₊ = d + δ` and the difference `𝒟₋ = d − δ` satisfy
`𝒟₊ ≫ 𝒟₋ + 𝒟₋ ≫ 𝒟₊ = 0`.

Only nilpotency of `d` and `δ` is used: every cross term cancels pairwise and
the two diagonal terms vanish because `d² = 0` and `δ² = 0`.
-/
theorem diracSum_anticommutes_diracDifference
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Data V) :
    (D.d + D.codifferential).comp (D.d - D.codifferential) +
    (D.d - D.codifferential).comp (D.d + D.codifferential) = 0 := by
  ext x
  have hd : ∀ y, D.d (D.d y) = 0 := fun y => by
    have h := congrArg (fun f : V →ₗ[ℝ] V => f y) D.d_sq_zero
    simpa [LinearMap.comp_apply] using h
  have hc : ∀ y, D.codifferential (D.codifferential y) = 0 := fun y => by
    have h := congrArg (fun f : V →ₗ[ℝ] V => f y) D.codifferential_sq_zero
    simpa [LinearMap.comp_apply] using h
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.map_add, LinearMap.map_sub, hd, hc]
  abel_nf
  simp

/--
The squares of the two Dirac operators cancel: `𝒟₊² + 𝒟₋² = 0`.

This is the operator form of `Δ + (−Δ) = 0`: the sum operator squares to the
Hodge Laplacian `dδ + δd`, the difference operator squares to its negative.
-/
theorem diracSum_sq_add_diracDifference_sq_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Data V) :
    (dirac D).comp (dirac D) +
    (D.d - D.codifferential).comp (D.d - D.codifferential) = 0 := by
  rw [dirac_square D, diracDifference_sq_eq_neg_laplacian D]
  abel

end

end InfoGeometry.Topology.DiracKahlerMultiplication
