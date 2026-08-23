import InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

/-!
# The symplectic Lie algebra of the Peirce phase carrier

This owner records the exact target for a future representation of the native
split-octonion derivations on the six-dimensional phase carrier.  It does not
identify that representation prematurely: a phase endomorphism belongs to the
symplectic Lie algebra precisely when its infinitesimal action preserves the
already proved Zorn mixed pairing.
-/

namespace InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

open scoped Matrix

noncomputable section

abbrev PhaseEnd := Module.End ℝ Phase

def IsSymplecticEnd (T : PhaseEnd) : Prop :=
  ∀ X Y : Phase, omega (T X) Y + omega X (T Y) = 0

@[simp]
theorem zero_isSymplecticEnd :
    IsSymplecticEnd (0 : PhaseEnd) := by
  intro X Y
  simp [omega]

theorem omega_sub_left (X Y Z : Phase) :
    omega (X - Y) Z = omega X Z - omega Y Z := by
  rw [sub_eq_add_neg, omega_add_left, ← neg_one_smul ℝ Y,
    omega_smul_left]
  ring

theorem omega_sub_right (X Y Z : Phase) :
    omega X (Y - Z) = omega X Y - omega X Z := by
  rw [sub_eq_add_neg, omega_add_right, ← neg_one_smul ℝ Z,
    omega_smul_right]
  ring

theorem add_isSymplecticEnd {S T : PhaseEnd}
    (hS : IsSymplecticEnd S) (hT : IsSymplecticEnd T) :
    IsSymplecticEnd (S + T) := by
  intro X Y
  rw [LinearMap.add_apply, LinearMap.add_apply]
  simp only [omega_add_left, omega_add_right]
  linarith [hS X Y, hT X Y]

theorem neg_isSymplecticEnd {T : PhaseEnd}
    (hT : IsSymplecticEnd T) :
    IsSymplecticEnd (-T) := by
  intro X Y
  rw [LinearMap.neg_apply, LinearMap.neg_apply]
  rw [← neg_one_smul ℝ (T X), ← neg_one_smul ℝ (T Y)]
  rw [omega_smul_left, omega_smul_right]
  linarith [hT X Y]

theorem smul_isSymplecticEnd (a : ℝ) {T : PhaseEnd}
    (hT : IsSymplecticEnd T) :
    IsSymplecticEnd (a • T) := by
  intro X Y
  rw [LinearMap.smul_apply, LinearMap.smul_apply]
  rw [omega_smul_left, omega_smul_right]
  rw [← mul_add, hT X Y, mul_zero]

def phaseCommutator (S T : PhaseEnd) : PhaseEnd :=
  S.comp T - T.comp S

theorem commutator_isSymplecticEnd {S T : PhaseEnd}
    (hS : IsSymplecticEnd S) (hT : IsSymplecticEnd T) :
    IsSymplecticEnd (phaseCommutator S T) := by
  intro X Y
  simp only [phaseCommutator, LinearMap.sub_apply, LinearMap.comp_apply]
  have hST := hS (T X) Y
  have hTS := hT X (S Y)
  have hS' := hS X (T Y)
  have hT' := hT (S X) Y
  rw [omega_sub_left, omega_sub_right]
  linarith [hST, hTS, hS', hT']

theorem phaseCommutator_skew (S T : PhaseEnd) :
    phaseCommutator S T = -(phaseCommutator T S) := by
  apply LinearMap.ext
  intro X
  simp [phaseCommutator, LinearMap.comp_apply, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc]

theorem phaseCommutator_jacobi (R S T : PhaseEnd) :
    phaseCommutator R (phaseCommutator S T) +
        phaseCommutator S (phaseCommutator T R) +
        phaseCommutator T (phaseCommutator R S) = 0 := by
  apply LinearMap.ext
  intro X
  simp [phaseCommutator, LinearMap.comp_apply, sub_eq_add_neg]
  abel

/-! ## Polarization-preserving actions and quadratic readouts -/

structure PolarizedAction where
  plus : Vec →ₗ[ℝ] Vec
  minus : Vec →ₗ[ℝ] Vec
  pairing_invariant :
    ∀ q p : Vec,
      chiralPairing (plus q) p + chiralPairing q (minus p) = 0

namespace PolarizedAction

def toPhaseLinear (A : PolarizedAction) : PhaseEnd where
  toFun x := (A.plus x.1, A.minus x.2)
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

theorem toPhaseLinear_isSymplecticEnd (A : PolarizedAction) :
    IsSymplecticEnd A.toPhaseLinear := by
  rintro ⟨q, p⟩ ⟨r, s⟩
  change
    (chiralPairing (A.plus q) s - chiralPairing r (A.minus p)) +
      (chiralPairing q (A.minus s) - chiralPairing (A.plus r) p) = 0
  have hqs := A.pairing_invariant q s
  have hrp := A.pairing_invariant r p
  linarith

end PolarizedAction

def quadraticMoment (D : PhaseEnd) (x : Phase) : ℝ :=
  (1 / 2 : ℝ) * omega x (D x)

theorem quadraticMoment_polarization
    {D : PhaseEnd} (hD : IsSymplecticEnd D) (x h : Phase) :
    quadraticMoment D (x + h) - quadraticMoment D x -
        quadraticMoment D h = omega h (D x) := by
  unfold quadraticMoment
  rw [map_add, omega_add_left, omega_add_right, omega_add_right]
  have hs := omega_skew (D x) h
  have hd := hD x h
  linarith

def quadraticMomentBracket (D E : PhaseEnd) (x : Phase) : ℝ :=
  -omega (D x) (E x)

theorem quadraticMomentBracket_eq_commutatorMoment
    {D E : PhaseEnd} (hD : IsSymplecticEnd D)
    (hE : IsSymplecticEnd E) (x : Phase) :
    quadraticMomentBracket D E x =
      quadraticMoment (phaseCommutator D E) x := by
  unfold quadraticMomentBracket quadraticMoment
  rw [phaseCommutator, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, omega_sub_right]
  have h1 := hD x (E x)
  have h2 := hE x (D x)
  have hs := omega_skew (E x) (D x)
  linarith

end
end InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
