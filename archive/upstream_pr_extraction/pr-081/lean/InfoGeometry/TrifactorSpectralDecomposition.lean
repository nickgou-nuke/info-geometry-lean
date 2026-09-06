import InfoGeometry.Canonical.TrifactorDecomposition

/-!
# Trifactor Spectral Decomposition

Compatibility namespace for the canonical tripotent-sector decomposition.
The proof owner is `InfoGeometry.Canonical.TrifactorDecomposition`.
-/

namespace InfoGeometry.TrifactorSpectralDecomposition

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The null boundary projector, corresponding to the `0` sector. -/
def P_zero (T : R) : R := InfoGeometry.Canonical.TrifactorDecomposition.P_zero T

/-- The positive conformal-flow projector, corresponding to the `+1` sector. -/
def P_plus (T : R) : R := InfoGeometry.Canonical.TrifactorDecomposition.P_plus T

/-- The negative mirror projector, corresponding to the `-1` sector. -/
def P_minus (T : R) : R := InfoGeometry.Canonical.TrifactorDecomposition.P_minus T

omit [Invertible (2 : R)] in
theorem P_zero_idempotent (T : R) (h_cube : T ^ 3 = T) :
    P_zero T * P_zero T = P_zero T :=
  InfoGeometry.Canonical.TrifactorDecomposition.P_zero_idempotent T h_cube

theorem P_plus_idempotent (T : R) (h_cube : T ^ 3 = T) :
    P_plus T * P_plus T = P_plus T :=
  InfoGeometry.Canonical.TrifactorDecomposition.P_plus_idempotent T h_cube

theorem P_minus_idempotent (T : R) (h_cube : T ^ 3 = T) :
    P_minus T * P_minus T = P_minus T :=
  InfoGeometry.Canonical.TrifactorDecomposition.P_minus_idempotent T h_cube

theorem P_plus_P_minus_orthogonal (T : R) (h_cube : T ^ 3 = T) :
    P_plus T * P_minus T = 0 :=
  InfoGeometry.Canonical.TrifactorDecomposition.P_plus_P_minus_orthogonal T h_cube

theorem P_zero_P_plus_orthogonal (T : R) (h_cube : T ^ 3 = T) :
    P_zero T * P_plus T = 0 :=
  InfoGeometry.Canonical.TrifactorDecomposition.P_zero_P_plus_orthogonal T h_cube

theorem P_zero_P_minus_orthogonal (T : R) (h_cube : T ^ 3 = T) :
    P_zero T * P_minus T = 0 :=
  InfoGeometry.Canonical.TrifactorDecomposition.P_zero_P_minus_orthogonal T h_cube

theorem partition_of_unity (T : R) :
    P_zero T + P_plus T + P_minus T = 1 :=
  InfoGeometry.Canonical.TrifactorDecomposition.partition_of_unity T

omit [Invertible (2 : R)] in
theorem T_on_P_zero (T : R) (h_cube : T ^ 3 = T) :
    T * P_zero T = 0 :=
  InfoGeometry.Canonical.TrifactorDecomposition.T_on_P_zero T h_cube

theorem T_on_P_plus (T : R) (h_cube : T ^ 3 = T) :
    T * P_plus T = P_plus T :=
  InfoGeometry.Canonical.TrifactorDecomposition.T_on_P_plus T h_cube

theorem T_on_P_minus (T : R) (h_cube : T ^ 3 = T) :
    T * P_minus T = -P_minus T :=
  InfoGeometry.Canonical.TrifactorDecomposition.T_on_P_minus T h_cube

theorem spectral_resolution (T : R) :
    P_plus T - P_minus T = T :=
  InfoGeometry.Canonical.TrifactorDecomposition.spectral_resolution T

theorem trifactor_capstone (T : R) (h_cube : T ^ 3 = T) :
    (P_zero T * P_zero T = P_zero T ∧
      P_plus T * P_plus T = P_plus T ∧
      P_minus T * P_minus T = P_minus T) ∧
    (P_plus T * P_minus T = 0 ∧
      P_zero T * P_plus T = 0 ∧
      P_zero T * P_minus T = 0) ∧
    P_zero T + P_plus T + P_minus T = 1 ∧
    (T * P_zero T = 0 ∧
      T * P_plus T = P_plus T ∧
      T * P_minus T = -P_minus T) ∧
    P_plus T - P_minus T = T :=
  InfoGeometry.Canonical.TrifactorDecomposition.trifactor_capstone T h_cube

end InfoGeometry.TrifactorSpectralDecomposition
