import InfoGeometry.Feynman.FeynmanTwistedDeRhamComplex

noncomputable section

namespace InfoGeometry.Canonical.FiniteTwistedMaurerCartanBridge

open InfoGeometry.Feynman.FeynmanTwistedDeRhamComplex

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

abbrev Forms (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :=
  ExteriorAlgebra R M

/-- A finite Maurer--Cartan realization whose connection operator is the
    twisted exterior differential.  The curvature is represented by its
    operator square, so the carrier makes the intended type bridge explicit. -/
structure Data where
  twist : TwistedOneForm R M

def connection (D : Data (R := R) (M := M)) : Forms R M →ₗ[R] Forms R M :=
  twistedDifferential D.twist

def curvature (D : Data (R := R) (M := M)) : Forms R M →ₗ[R] Forms R M :=
  (connection D).comp (connection D)

@[simp] theorem curvature_apply (D : Data (R := R) (M := M)) (η : Forms R M) :
    curvature D η =
      twistedDifferential D.twist (twistedDifferential D.twist η) := rfl

theorem curvature_eq_zero (D : Data (R := R) (M := M)) :
    curvature D = 0 := by
  exact twistedDifferential_square_zero D.twist

theorem curvature_apply_eq_zero (D : Data (R := R) (M := M)) (η : Forms R M) :
    curvature D η = 0 := by
  rw [curvature_eq_zero D]
  rfl

end InfoGeometry.Canonical.FiniteTwistedMaurerCartanBridge
