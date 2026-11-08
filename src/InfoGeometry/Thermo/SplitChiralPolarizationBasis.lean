import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Thermo.SplitChiralPolarizationBasis

Proof-only chiral polarization basis on the split-complex temperature plane.

This module is the split-signature analogue of
`ComplexCircularPolarizationBasis`.  It installs only the finite algebraic
content:

* a split rapidity coordinate `(sigma, tau)`,
* light-cone coordinates `u = sigma + tau` and `v = sigma - tau`,
* reconstruction of `(sigma, tau)` from `(u, v)`,
* componentwise Boltzmann exponents on the two chiral idempotent lanes.

No analytic continuation, no zero theorem, and no CFT central-charge theorem is
claimed here.
-/

noncomputable section

namespace InfoGeometry.Thermo.SplitChiralPolarizationBasis

/-- Split-complex rapidity coordinate `sigma + j tau`, stored as real data. -/
@[rep_depth thermo]
structure SplitRapidity where
  sigma : ℝ
  tau : ℝ

namespace SplitRapidity

/-- Left-moving light-cone coordinate `u = sigma + tau`. -/
@[rep_depth thermo]
def leftCoord (s : SplitRapidity) : ℝ :=
  s.sigma + s.tau

/-- Right-moving light-cone coordinate `v = sigma - tau`. -/
@[rep_depth thermo]
def rightCoord (s : SplitRapidity) : ℝ :=
  s.sigma - s.tau

/-- Recover `sigma` from the two light-cone coordinates. -/
@[rep_depth thermo]
theorem sigma_eq_half_left_add_right (s : SplitRapidity) :
    s.sigma = (leftCoord s + rightCoord s) / 2 := by
  unfold leftCoord rightCoord
  ring

/-- Recover `tau` from the two light-cone coordinates. -/
@[rep_depth thermo]
theorem tau_eq_half_left_sub_right (s : SplitRapidity) :
    s.tau = (leftCoord s - rightCoord s) / 2 := by
  unfold leftCoord rightCoord
  ring

end SplitRapidity

/-- A split-complex scalar represented in the idempotent basis. -/
@[rep_depth thermo]
abbrev ChiralScalar := ℝ × ℝ

/-- The multiplicative identity in the idempotent basis. -/
@[rep_depth thermo]
def splitOne : ChiralScalar :=
  (1, 1)

/-- The hyperbolic unit in the idempotent basis. -/
@[rep_depth thermo]
def j : ChiralScalar :=
  (1, -1)

/-- The left idempotent projector `e₊`. -/
@[rep_depth thermo]
def ePlus : ChiralScalar :=
  (1, 0)

/-- The right idempotent projector `e₋`. -/
@[rep_depth thermo]
def eMinus : ChiralScalar :=
  (0, 1)

/-- Left idempotent coordinate of a chiral scalar. -/
@[rep_depth thermo]
def leftPart (x : ChiralScalar) : ℝ :=
  x.1

/-- Right idempotent coordinate of a chiral scalar. -/
@[rep_depth thermo]
def rightPart (x : ChiralScalar) : ℝ :=
  x.2

/-- Componentwise multiplication in the idempotent basis. -/
@[rep_depth thermo]
def chiralMul (x y : ChiralScalar) : ChiralScalar :=
  (x.1 * y.1, x.2 * y.2)

/-- Split-complex conjugation in the idempotent basis. -/
@[rep_depth thermo]
def conj (x : ChiralScalar) : ChiralScalar :=
  (x.2, x.1)

/-- Split-complex norm-square in the idempotent basis. -/
@[rep_depth thermo]
def normSq (x : ChiralScalar) : ℝ :=
  leftPart x * rightPart x

/-- Reconstruct a split scalar from its left and right coordinates. -/
@[rep_depth thermo]
def reconstruct (u v : ℝ) : ChiralScalar :=
  (u, v)

/-- Hyperbolic exponential in the idempotent basis. -/
@[rep_depth thermo]
def hyperbolicExp (θ : ℝ) : ChiralScalar :=
  (Real.exp θ, Real.exp (-θ))

@[simp, rep_depth thermo]
theorem leftPart_hyperbolicExp (θ : ℝ) :
    leftPart (hyperbolicExp θ) = Real.exp θ :=
  rfl

@[simp, rep_depth thermo]
theorem rightPart_hyperbolicExp (θ : ℝ) :
    rightPart (hyperbolicExp θ) = Real.exp (-θ) :=
  rfl

/-- Hyperbolic exponentials add under `chiralMul`. -/
@[rep_depth thermo]
theorem hyperbolicExp_add (θ φ : ℝ) :
    chiralMul (hyperbolicExp θ) (hyperbolicExp φ) =
      hyperbolicExp (θ + φ) := by
  ext <;> simp [hyperbolicExp, chiralMul, Real.exp_add, add_comm]

@[simp, rep_depth thermo]
theorem hyperbolicExp_zero :
    hyperbolicExp (0 : ℝ) = splitOne := by
  ext <;> simp [hyperbolicExp, splitOne]

@[simp, rep_depth thermo]
theorem leftPart_chiralMul (x y : ChiralScalar) :
    leftPart (chiralMul x y) = leftPart x * leftPart y :=
  rfl

@[simp, rep_depth thermo]
theorem rightPart_chiralMul (x y : ChiralScalar) :
    rightPart (chiralMul x y) = rightPart x * rightPart y :=
  rfl

@[simp, rep_depth thermo]
theorem leftPart_splitOne : leftPart splitOne = 1 :=
  rfl

@[simp, rep_depth thermo]
theorem rightPart_splitOne : rightPart splitOne = 1 :=
  rfl

@[simp, rep_depth thermo]
theorem leftPart_j : leftPart j = 1 :=
  rfl

@[simp, rep_depth thermo]
theorem rightPart_j : rightPart j = -1 :=
  rfl

@[simp, rep_depth thermo]
theorem leftPart_ePlus : leftPart ePlus = 1 :=
  rfl

@[simp, rep_depth thermo]
theorem rightPart_ePlus : rightPart ePlus = 0 :=
  rfl

@[simp, rep_depth thermo]
theorem leftPart_eMinus : leftPart eMinus = 0 :=
  rfl

@[simp, rep_depth thermo]
theorem rightPart_eMinus : rightPart eMinus = 1 :=
  rfl

/-- The hyperbolic unit squares to the identity. -/
@[simp, rep_depth thermo]
theorem j_mul_j : chiralMul j j = splitOne := by
  ext <;> simp [j, splitOne, chiralMul]

/-- The left idempotent is idempotent. -/
@[simp, rep_depth thermo]
theorem ePlus_idem : chiralMul ePlus ePlus = ePlus := by
  ext <;> simp [ePlus, chiralMul]

/-- The right idempotent is idempotent. -/
@[simp, rep_depth thermo]
theorem eMinus_idem : chiralMul eMinus eMinus = eMinus := by
  ext <;> simp [eMinus, chiralMul]

/-- The left and right idempotents annihilate one another. -/
@[simp, rep_depth thermo]
theorem ePlus_mul_eMinus : chiralMul ePlus eMinus = (0, 0) := by
  ext <;> simp [ePlus, eMinus, chiralMul]

/-- The right and left idempotents annihilate one another. -/
@[simp, rep_depth thermo]
theorem eMinus_mul_ePlus : chiralMul eMinus ePlus = (0, 0) := by
  ext <;> simp [ePlus, eMinus, chiralMul]

/-- The two idempotents resolve the identity. -/
@[simp, rep_depth thermo]
theorem ePlus_add_eMinus : ePlus + eMinus = splitOne := by
  ext <;> simp [ePlus, eMinus, splitOne]

/-- Conjugation is involutive. -/
@[simp, rep_depth thermo]
theorem conj_involutive (x : ChiralScalar) : conj (conj x) = x := by
  cases x
  rfl

/-- Conjugation preserves the norm-square. -/
@[simp, rep_depth thermo]
theorem normSq_conj (x : ChiralScalar) : normSq (conj x) = normSq x := by
  cases x
  simp [normSq, conj, leftPart, rightPart, mul_comm]

/-- The split scalar reconstructs from its left and right coordinates. -/
@[simp, rep_depth thermo]
theorem reconstruct_left_right (z : ChiralScalar) :
    reconstruct (leftPart z) (rightPart z) = z := by
  cases z
  rfl

/-- Reconstructing two split scalars multiplies componentwise. -/
@[simp, rep_depth thermo]
theorem reconstruct_mul (u v u' v' : ℝ) :
    chiralMul (reconstruct u v) (reconstruct u' v') =
      reconstruct (u * u') (v * v') := by
  rfl

/-- Left projection of a chiral function. -/
@[rep_depth thermo]
def chiralFunction (φL φR : ℝ → ℝ) (z : ChiralScalar) : ChiralScalar :=
  reconstruct (φL (leftPart z)) (φR (rightPart z))

@[simp, rep_depth thermo]
theorem leftPart_chiralFunction
    (φL φR : ℝ → ℝ) (z : ChiralScalar) :
    leftPart (chiralFunction φL φR z) = φL (leftPart z) := by
  rfl

@[simp, rep_depth thermo]
theorem rightPart_chiralFunction
    (φL φR : ℝ → ℝ) (z : ChiralScalar) :
    rightPart (chiralFunction φL φR z) = φR (rightPart z) := by
  rfl

/-- The normalized holonomy in left/right coordinates. -/
@[rep_depth thermo]
def normalizedHolonomyLR (E σ t : ℝ) : ChiralScalar :=
  reconstruct
    (Real.exp ((((1 : ℝ) / 2) - σ - t) * E))
    (Real.exp ((((1 : ℝ) / 2) - σ + t) * E))

/-- The critical line `σ = 1/2` has unit norm-square. -/
@[rep_depth thermo]
theorem normalizedHolonomyLR_normSq_critical (E t : ℝ) :
    normSq (normalizedHolonomyLR E ((1 : ℝ) / 2) t) = 1 := by
  unfold normalizedHolonomyLR normSq reconstruct leftPart rightPart
  have hL :
      ((((1 : ℝ) / 2) - (1 : ℝ) / 2 - t) * E) = -(t * E) := by
    ring
  have hR :
      ((((1 : ℝ) / 2) - (1 : ℝ) / 2 + t) * E) = t * E := by
    ring
  rw [hL, hR, ← Real.exp_add]
  have hsum : (-(t * E) + t * E) = 0 := by
    ring
  rw [hsum, Real.exp_zero]

/-- Left-moving thermal exponent. -/
@[rep_depth thermo]
def leftThermalExponent (E : ℝ) (s : SplitRapidity) : ℝ :=
  -(SplitRapidity.leftCoord s * E)

/-- Right-moving thermal exponent. -/
@[rep_depth thermo]
def rightThermalExponent (E : ℝ) (s : SplitRapidity) : ℝ :=
  -(SplitRapidity.rightCoord s * E)

/-- Elementary split-complex thermal exponent in the chiral idempotent basis. -/
@[rep_depth thermo]
def splitChiralThermalExponent (E : ℝ) (s : SplitRapidity) : ChiralScalar :=
  (leftThermalExponent E s, rightThermalExponent E s)

/-- Left-moving Boltzmann weight on the split plane. -/
@[rep_depth thermo]
def splitChiralLeftBoltzmannWeight (E : ℝ) (s : SplitRapidity) : ℝ :=
  Real.exp (leftThermalExponent E s)

/-- Right-moving Boltzmann weight on the split plane. -/
@[rep_depth thermo]
def splitChiralRightBoltzmannWeight (E : ℝ) (s : SplitRapidity) : ℝ :=
  Real.exp (rightThermalExponent E s)

/-- Split-complex Boltzmann weight in the chiral idempotent basis. -/
@[rep_depth thermo]
def splitChiralBoltzmannWeight (E : ℝ) (s : SplitRapidity) : ChiralScalar :=
  (splitChiralLeftBoltzmannWeight E s, splitChiralRightBoltzmannWeight E s)

/-- Left-moving thermal exponent component. -/
@[rep_depth thermo]
theorem leftPart_splitChiralThermalExponent (E : ℝ) (s : SplitRapidity) :
    leftPart (splitChiralThermalExponent E s) = leftThermalExponent E s :=
  rfl

/-- Right-moving thermal exponent component. -/
@[rep_depth thermo]
theorem rightPart_splitChiralThermalExponent (E : ℝ) (s : SplitRapidity) :
    rightPart (splitChiralThermalExponent E s) = rightThermalExponent E s :=
  rfl

/-! ## Clifford projector readout -/

end InfoGeometry.Thermo.SplitChiralPolarizationBasis
