import Mathlib.Tactic
import Mathlib

noncomputable section

namespace InfoGeometry.Physics.LorentzBoostMinkowski

/-- Four-vector with components `(t,x,y,z)`, represented natively as a product. -/
abbrev FourVector := ℝ × (ℝ × (ℝ × ℝ))

namespace FourVector

@[simp] def t (p : FourVector) : ℝ := p.1
@[simp] def x (p : FourVector) : ℝ := p.2.1
@[simp] def y (p : FourVector) : ℝ := p.2.2.1
@[simp] def z (p : FourVector) : ℝ := p.2.2.2

end FourVector

/-- Minkowski bilinear form with signature `(+---)`. -/
def minkowskiPair (a b : FourVector) : ℝ :=
  a.t * b.t - a.x * b.x - a.y * b.y - a.z * b.z

/-- Minkowski quadratic/Casimir. -/
def minkowskiSq (p : FourVector) : ℝ := minkowskiPair p p

/-- Standard boost in the x-direction with rapidity `φ`. -/
def boostX (φ : ℝ) (p : FourVector) : FourVector where
  fst := Real.cosh φ * p.t + Real.sinh φ * p.x
  snd :=
    (Real.sinh φ * p.t + Real.cosh φ * p.x,
      (p.y, p.z))

@[simp] theorem boostX_zero (p : FourVector) :
    boostX 0 p = p := by
  cases p
  simp [boostX]

theorem boostX_add (φ ψ : ℝ) (p : FourVector) :
    boostX (φ + ψ) p = boostX φ (boostX ψ p) := by
  cases p
  ext <;> simp [boostX, Real.cosh_add, Real.sinh_add] <;> ring

theorem boostX_neg_left (φ : ℝ) (p : FourVector) :
    boostX (-φ) (boostX φ p) = p := by
  rw [← boostX_add]
  simp

theorem boostX_neg_right (φ : ℝ) (p : FourVector) :
    boostX φ (boostX (-φ) p) = p := by
  rw [← boostX_add]
  simp

/-- The finite Lorentz boost is a real-linear equivalence of four-vectors. -/
def boostXLinearEquiv (φ : ℝ) : FourVector ≃ₗ[ℝ] FourVector where
  toFun := boostX φ
  invFun := boostX (-φ)
  left_inv := boostX_neg_left φ
  right_inv := boostX_neg_right φ
  map_add' := by
    intro p q
    cases p
    cases q
    ext <;> simp [boostX, add_mul, mul_add] <;> ring
  map_smul' := by
    intro c p
    cases p
    ext <;> simp [boostX, smul_eq_mul] <;> ring

@[simp] theorem boostXLinearEquiv_apply (φ : ℝ) (p : FourVector) :
    boostXLinearEquiv φ p = boostX φ p := rfl

@[simp] theorem boostXLinearEquiv_symm_apply (φ : ℝ) (p : FourVector) :
    (boostXLinearEquiv φ).symm p = boostX (-φ) p := rfl

@[simp] theorem minkowskiPair_symmetric (a b : FourVector) :
    minkowskiPair a b = minkowskiPair b a := by
  cases a
  cases b
  simp [minkowskiPair]
  ring

/-- Lorentz x-boost preserves the Minkowski bilinear form. -/
theorem boostX_preserves_minkowskiPair (φ : ℝ) (a b : FourVector) :
    minkowskiPair (boostX φ a) (boostX φ b) = minkowskiPair a b := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp [minkowskiPair, boostX]
  have h : Real.cosh φ ^ 2 - Real.sinh φ ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq φ
  calc
    (Real.cosh φ * a0 + Real.sinh φ * a1) * (Real.cosh φ * b0 + Real.sinh φ * b1) -
        (Real.sinh φ * a0 + Real.cosh φ * a1) * (Real.sinh φ * b0 + Real.cosh φ * b1)
        = (Real.cosh φ ^ 2 - Real.sinh φ ^ 2) * (a0 * b0 - a1 * b1) := by ring
    _ = a0 * b0 - a1 * b1 := by rw [h]; ring

/-- Lorentz x-boost preserves the mass/energy-momentum Casimir. -/
theorem boostX_preserves_minkowskiSq (φ : ℝ) (p : FourVector) :
    minkowskiSq (boostX φ p) = minkowskiSq p := by
  simp [minkowskiSq, boostX_preserves_minkowskiPair]

theorem boostXLinearEquiv_preserves_minkowskiPair
    (φ : ℝ) (a b : FourVector) :
    minkowskiPair (boostXLinearEquiv φ a) (boostXLinearEquiv φ b) =
      minkowskiPair a b := by
  simpa only [boostXLinearEquiv_apply] using
    boostX_preserves_minkowskiPair φ a b

theorem boostXLinearEquiv_preserves_minkowskiSq
    (φ : ℝ) (p : FourVector) :
    minkowskiSq (boostXLinearEquiv φ p) = minkowskiSq p := by
  simpa only [boostXLinearEquiv_apply] using
    boostX_preserves_minkowskiSq φ p

/-- The Souriau beta-energy pairing is Lorentz invariant when both beta and momentum are boosted. -/
theorem boostX_preserves_beta_energy_pair (φ : ℝ) (β p : FourVector) :
    minkowskiPair (boostX φ β) (boostX φ p) = minkowskiPair β p :=
  boostX_preserves_minkowskiPair φ β p

/-- Inverse-temperature four-vector at rest has norm `1/T²`. -/
theorem rest_beta_minkowskiSq (T : ℝ) :
    minkowskiSq ⟨1 / T, 0, 0, 0⟩ = 1 / T ^ 2 := by
  simp [minkowskiSq, minkowskiPair]
  ring

/-- Boosted rest beta vector also has norm `1/T²`. -/
theorem boosted_rest_beta_minkowskiSq (φ T : ℝ) :
    minkowskiSq (boostX φ ⟨1 / T, 0, 0, 0⟩) = 1 / T ^ 2 := by
  rw [boostX_preserves_minkowskiSq, rest_beta_minkowskiSq]

end InfoGeometry.Physics.LorentzBoostMinkowski
