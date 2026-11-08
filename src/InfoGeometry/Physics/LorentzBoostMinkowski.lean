import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Physics.LorentzBoostMinkowski

/-- Four-vector with components `(t,x,y,z)`. -/
structure FourVector where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

/-- Minkowski bilinear form with signature `(+---)`. -/
def minkowskiPair (a b : FourVector) : ℝ :=
  a.t * b.t - a.x * b.x - a.y * b.y - a.z * b.z

/-- Minkowski quadratic/Casimir. -/
def minkowskiSq (p : FourVector) : ℝ := minkowskiPair p p

/-- Standard boost in the x-direction with rapidity `φ`. -/
def boostX (φ : ℝ) (p : FourVector) : FourVector where
  t := Real.cosh φ * p.t + Real.sinh φ * p.x
  x := Real.sinh φ * p.t + Real.cosh φ * p.x
  y := p.y
  z := p.z

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
