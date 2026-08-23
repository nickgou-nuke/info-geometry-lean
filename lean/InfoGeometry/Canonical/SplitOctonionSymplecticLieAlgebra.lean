import InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

/-!
# The infinitesimal symplectic endomorphism target

This owner deliberately stops at the native phase carrier.  It does not claim
that an existing split-octonion derivation owner acts on this carrier.
-/

namespace InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

open scoped BigOperators

noncomputable section

/-- Infinitesimal preservation of the native phase-space form. -/
def IsOmegaSymplectic (A : Phase →ₗ[ℝ] Phase) : Prop :=
  ∀ X Y, omega (A X) Y + omega X (A Y) = 0

private theorem omega_zero_left (Y : Phase) : omega 0 Y = 0 := by
  simp [omega, chiralPairing, InfoGeometry.Algebra.Vec3.dot]

private theorem omega_zero_right (X : Phase) : omega X 0 = 0 := by
  simp [omega, chiralPairing, InfoGeometry.Algebra.Vec3.dot]

private theorem omega_neg_left (X Y : Phase) :
    omega (-X) Y = -omega X Y := by
  have h := omega_smul_left (-1 : ℝ) X Y
  simpa using h

private theorem omega_neg_right (X Y : Phase) :
    omega X (-Y) = -omega X Y := by
  have h := omega_smul_right (-1 : ℝ) X Y
  simpa using h

theorem zero_isOmegaSymplectic :
    IsOmegaSymplectic (0 : Phase →ₗ[ℝ] Phase) := by
  intro X Y
  change omega 0 Y + omega X 0 = 0
  rw [omega_zero_left, omega_zero_right]
  simp

theorem add_isOmegaSymplectic
    {A B : Phase →ₗ[ℝ] Phase}
    (hA : IsOmegaSymplectic A)
    (hB : IsOmegaSymplectic B) :
    IsOmegaSymplectic (A + B) := by
  intro X Y
  rw [LinearMap.add_apply, LinearMap.add_apply, omega_add_left,
    omega_add_right]
  linear_combination hA X Y + hB X Y

theorem neg_isOmegaSymplectic
    {A : Phase →ₗ[ℝ] Phase}
    (hA : IsOmegaSymplectic A) :
    IsOmegaSymplectic (-A) := by
  intro X Y
  change omega (-(A X)) Y + omega X (-(A Y)) = 0
  rw [omega_neg_left, omega_neg_right]
  linear_combination -(hA X Y)

theorem smul_isOmegaSymplectic
    (c : ℝ) {A : Phase →ₗ[ℝ] Phase}
    (hA : IsOmegaSymplectic A) :
    IsOmegaSymplectic (c • A) := by
  intro X Y
  rw [LinearMap.smul_apply, LinearMap.smul_apply,
    omega_smul_left, omega_smul_right]
  linear_combination c * hA X Y

/-- The commutator of two infinitesimal symplectic endomorphisms. -/
def symplecticCommutator
    (A B : Phase →ₗ[ℝ] Phase) : Phase →ₗ[ℝ] Phase :=
  A.comp B - B.comp A

theorem commutator_isOmegaSymplectic
    {A B : Phase →ₗ[ℝ] Phase}
    (hA : IsOmegaSymplectic A)
    (hB : IsOmegaSymplectic B) :
    IsOmegaSymplectic (symplecticCommutator A B) := by
  intro X Y
  unfold symplecticCommutator
  rw [LinearMap.sub_apply, LinearMap.sub_apply]
  simp only [LinearMap.comp_apply]
  rw [sub_eq_add_neg, sub_eq_add_neg, omega_add_left, omega_add_right,
    omega_neg_left, omega_neg_right]
  have h₁ := hA (B X) Y
  have h₂ := hA X (B Y)
  have h₃ := hB (A X) Y
  have h₄ := hB X (A Y)
  linarith [h₁, h₂, h₃, h₄]

end
end InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
