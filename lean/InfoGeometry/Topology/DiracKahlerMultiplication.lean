import InfoGeometry.Topology.DiscreteHodgeStarConjugation

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
  codifferential_sq_zero :
    codifferential.comp codifferential = 0
  d_anticommutes :
    d.comp chirality = -(chirality.comp d)
  codifferential_anticommutes :
    codifferential.comp chirality = -(chirality.comp codifferential)

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
  unfold dirac
  simp only [LinearMap.add_comp, LinearMap.comp_add]
  abel

end

end InfoGeometry.Topology.DiracKahlerMultiplication
