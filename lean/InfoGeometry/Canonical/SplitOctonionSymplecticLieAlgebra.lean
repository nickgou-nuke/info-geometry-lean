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

theorem omega_sub_right (x y z : Phase) :
    omega x (y - z) = omega x y - omega x z := by
  rw [sub_eq_add_neg, omega_add_right, omega_neg_right]
  rfl

theorem omega_sub_left (x y z : Phase) :
    omega (x - y) z = omega x z - omega y z := by
  rw [sub_eq_add_neg, omega_add_left, omega_neg_left]
  rfl

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

structure PolarizedAction where
  plus : Vec →ₗ[ℝ] Vec
  minus : Vec →ₗ[ℝ] Vec
  pairing_invariant :
    ∀ q p : Vec,
      chiralPairing (plus q) p + chiralPairing q (minus p) = 0

namespace PolarizedAction

def toPhaseLinear (A : PolarizedAction) : Phase →ₗ[ℝ] Phase where
  toFun x := (A.plus x.1, A.minus x.2)
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

theorem toPhaseLinear_isOmegaSymplectic (A : PolarizedAction) :
    IsOmegaSymplectic A.toPhaseLinear := by
  rintro ⟨q, p⟩ ⟨r, s⟩
  change
    (chiralPairing (A.plus q) s - chiralPairing r (A.minus p)) +
      (chiralPairing q (A.minus s) - chiralPairing (A.plus r) p) = 0
  have hqs := A.pairing_invariant q s
  have hrp := A.pairing_invariant r p
  linarith

end PolarizedAction

def quadraticMoment (A : Phase →ₗ[ℝ] Phase) (x : Phase) : ℝ :=
  (1 / 2 : ℝ) * omega x (A x)

theorem quadraticMoment_polarization
    {A : Phase →ₗ[ℝ] Phase} (hA : IsOmegaSymplectic A)
    (x h : Phase) :
    quadraticMoment A (x + h) - quadraticMoment A x -
        quadraticMoment A h = omega h (A x) := by
  unfold quadraticMoment
  rw [map_add, omega_add_left, omega_add_right, omega_add_right]
  have hs := omega_skew (A x) h
  have ha := hA x h
  linarith

def quadraticMomentBracket
    (A B : Phase →ₗ[ℝ] Phase) (x : Phase) : ℝ :=
  -omega (A x) (B x)

theorem quadraticMomentBracket_eq_commutatorMoment
    {A B : Phase →ₗ[ℝ] Phase}
    (hA : IsOmegaSymplectic A) (hB : IsOmegaSymplectic B)
    (x : Phase) :
    quadraticMomentBracket A B x =
      quadraticMoment (symplecticCommutator A B) x := by
  unfold quadraticMomentBracket quadraticMoment
  rw [symplecticCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply]
  rw [omega_sub_right]
  have h₁ := hA x (B x)
  have h₂ := hB x (A x)
  have hs := omega_skew (B x) (A x)
  linarith

end
end InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
