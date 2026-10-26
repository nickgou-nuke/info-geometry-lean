/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearFeshbachReduction

/-!
# Effective complex transition operators and their norm metrics

Initial and final sectors may have different dimensions and different energies.
For a supplied physical E2 or M1 operator O, the exact effective operator is
Ωf† O Ωi, with both norm metrics retained. Tensor rank, effective charges and
magnetic moments are model inputs; this file does not infer them from CAR grade.
-/

noncomputable section
namespace InfoGeometry.Physics.NuclearEffectiveMultipole
open Matrix
open scoped ComplexOrder

variable {i f a b q : Type*}
  [Fintype i] [Fintype f] [Fintype a] [Fintype b] [Fintype q]

def effectiveTransition (Ωi : Matrix a i ℂ) (Ωf : Matrix b f ℂ)
    (O : Matrix b a ℂ) : Matrix f i ℂ := Ωfᴴ * O * Ωi

def normMetric (Ω : Matrix a i ℂ) : Matrix i i ℂ := Ωᴴ * Ω

def amplitude (O : Matrix b a ℂ) (initial : a → ℂ) (final : b → ℂ) : ℂ :=
  star final ⬝ᵥ (O *ᵥ initial)

theorem effective_amplitude (Ωi : Matrix a i ℂ) (Ωf : Matrix b f ℂ)
    (O : Matrix b a ℂ) (x : i → ℂ) (y : f → ℂ) :
    amplitude (effectiveTransition Ωi Ωf O) x y =
      amplitude O (Ωi *ᵥ x) (Ωf *ᵥ y) := by
  simp only [amplitude, effectiveTransition, ← mulVec_mulVec, star_mulVec,
    dotProduct_mulVec, vecMul_vecMul]

theorem normMetric_readout (Ω : Matrix a i ℂ) (x : i → ℂ) :
    star x ⬝ᵥ (normMetric Ω *ᵥ x) = star (Ω *ᵥ x) ⬝ᵥ (Ω *ᵥ x) := by
  simp only [normMetric, ← mulVec_mulVec, star_mulVec, dotProduct_mulVec]

/-- Reduced matrix element strength with both dressed norms and the 2Ji+1 factor.
The states must have positive norms, and O must contain reduced matrix elements
(not magnetic-substate components), for this interpretation. -/
def normalizedReducedStrength (twoJi : ℕ) (O : Matrix b a ℂ)
    (initial : a → ℂ) (final : b → ℂ) : ℝ :=
  Complex.normSq (amplitude O initial final) /
    (((twoJi : ℝ) + 1) * (star initial ⬝ᵥ initial).re * (star final ⬝ᵥ final).re)

theorem effective_normalized_strength (twoJi : ℕ)
    (Ωi : Matrix a i ℂ) (Ωf : Matrix b f ℂ) (O : Matrix b a ℂ)
    (x : i → ℂ) (y : f → ℂ) :
    Complex.normSq (amplitude (effectiveTransition Ωi Ωf O) x y) /
      (((twoJi : ℝ) + 1) * (star x ⬝ᵥ (normMetric Ωi *ᵥ x)).re *
        (star y ⬝ᵥ (normMetric Ωf *ᵥ y)).re) =
      normalizedReducedStrength twoJi O (Ωi *ᵥ x) (Ωf *ᵥ y) := by
  rw [effective_amplitude, normMetric_readout, normMetric_readout]
  rfl

/-- Matrix of the exact Feshbach reconstruction, with K = (D−E)⁻¹ on Q-space. -/
def feshbachDressing [DecidableEq i] (C : Matrix q i ℂ) (K : Matrix q q ℂ) : Matrix (i ⊕ q) i ℂ :=
  fromRows 1 (-(K * C))

theorem feshbachDressing_components [DecidableEq i] [DecidableEq q]
    (C : Matrix q i ℂ) (K : Matrix q q ℂ)
    (x : i → ℂ) :
    ((feshbachDressing C K *ᵥ x) ∘ Sum.inl,
      (feshbachDressing C K *ᵥ x) ∘ Sum.inr) =
      NuclearFeshbachReduction.reconstruction (Matrix.toLin' C) (Matrix.toLin' K) x := by
  simp [feshbachDressing, fromRows_mulVec, NuclearFeshbachReduction.reconstruction,
    Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]

theorem feshbach_normMetric [DecidableEq i] (C : Matrix q i ℂ) (K : Matrix q q ℂ) :
    normMetric (feshbachDressing C K) = 1 + (K * C)ᴴ * (K * C) := by
  simp [normMetric, feshbachDressing, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows]

/-- The Feshbach metric is strictly positive, not merely a formal normalization. -/
theorem feshbach_normMetric_posDef [DecidableEq i] (C : Matrix q i ℂ) (K : Matrix q q ℂ) :
    (normMetric (feshbachDressing C K)).PosDef := by
  rw [feshbach_normMetric]
  exact Matrix.PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self (K * C))

omit [Fintype i] in
/-- Self-adjoint Schur reduction for paired channels and a self-adjoint inverse. -/
theorem schur_hermitian (A : Matrix i i ℂ) (B : Matrix i q ℂ) (K : Matrix q q ℂ)
    (hA : A.IsHermitian) (hK : K.IsHermitian) : (A - B * K * Bᴴ).IsHermitian := by
  change (A - B * K * Bᴴ)ᴴ = A - B * K * Bᴴ
  simp [conjTranspose_sub, conjTranspose_mul, hA.eq, hK.eq, Matrix.mul_assoc]

/-- A two-sided inverse of a Hermitian denominator is itself Hermitian. -/
theorem inversePair_hermitian [DecidableEq q] (D K : Matrix q q ℂ) (hD : D.IsHermitian)
    (hK : NuclearOperatorSchurComplement.InversePair D K) : K.IsHermitian := by
  have hadj : Kᴴ * D = 1 := by
    have h := congrArg Matrix.conjTranspose hK.right_inv
    simpa [conjTranspose_mul, hD.eq] using h
  change Kᴴ = K
  calc
    Kᴴ = Kᴴ * (D * K) := by rw [hK.right_inv, mul_one]
    _ = (Kᴴ * D) * K := by rw [Matrix.mul_assoc]
    _ = K := by rw [hadj, one_mul]

/-- Spatial-parity covariance survives elimination if both dressings intertwine
the physical parity operators. This applies to E2 and M1 (both parity-even).
Hermiticity is needed on the final parity pair to transport the adjoint. -/
theorem effective_parity_intertwining
    (Ωi : Matrix a i ℂ) (Ωf : Matrix b f ℂ) (O : Matrix b a ℂ)
    (parityInitial : Matrix a a ℂ) (parityFinal : Matrix b b ℂ)
    (reducedParityInitial : Matrix i i ℂ) (reducedParityFinal : Matrix f f ℂ)
    (hf : parityFinal.IsHermitian) (hfr : reducedParityFinal.IsHermitian)
    (hiΩ : parityInitial * Ωi = Ωi * reducedParityInitial)
    (hfΩ : parityFinal * Ωf = Ωf * reducedParityFinal)
    (hO : parityFinal * O = O * parityInitial) :
    reducedParityFinal * effectiveTransition Ωi Ωf O =
      effectiveTransition Ωi Ωf O * reducedParityInitial := by
  have hadj : reducedParityFinal * Ωfᴴ = Ωfᴴ * parityFinal := by
    have h := congrArg Matrix.conjTranspose hfΩ
    simpa [conjTranspose_mul, hf.eq, hfr.eq] using h.symm
  unfold effectiveTransition
  calc
    reducedParityFinal * (Ωfᴴ * O * Ωi) = (reducedParityFinal * Ωfᴴ) * O * Ωi := by
      simp [Matrix.mul_assoc]
    _ = Ωfᴴ * (parityFinal * O) * Ωi := by rw [hadj]; simp [Matrix.mul_assoc]
    _ = Ωfᴴ * O * (parityInitial * Ωi) := by rw [hO]; simp [Matrix.mul_assoc]
    _ = Ωfᴴ * O * Ωi * reducedParityInitial := by rw [hiΩ]; simp [Matrix.mul_assoc]

/-- Opposite physical parity eigenstates have zero amplitude for a parity-even operator. -/
theorem parity_forbidden_amplitude (O : Matrix b a ℂ)
    (parityInitial : Matrix a a ℂ) (parityFinal : Matrix b b ℂ) (hf : parityFinal.IsHermitian)
    (hO : parityFinal * O = O * parityInitial) (x : a → ℂ) (y : b → ℂ)
    (hx : parityInitial *ᵥ x = x) (hy : parityFinal *ᵥ y = -y) : amplitude O x y = 0 := by
  have h := congrArg (fun M : Matrix b a ℂ => star y ⬝ᵥ (M *ᵥ x)) hO
  have hl : star y ⬝ᵥ ((parityFinal * O) *ᵥ x) = -amplitude O x y := by
    rw [← mulVec_mulVec, dotProduct_mulVec]
    rw [← hf.eq, ← star_mulVec, hy]
    simp [amplitude]
  rw [hl, ← mulVec_mulVec, hx] at h
  change -amplitude O x y = amplitude O x y at h
  have htwo : (2 : ℂ) * amplitude O x y = 0 := by linear_combination -h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Nonzero complex calibrations 1 and i need not reveal the sign of real
coherence: the two normalized states below have opposite cs and equal intensity. -/
theorem quadrature_calibration_ambiguity :
    Complex.normSq ((3/5 : ℂ) + (4/5 : ℂ) * Complex.I) =
      Complex.normSq ((3/5 : ℂ) - (4/5 : ℂ) * Complex.I) ∧
    (3/5 : ℝ) * (4/5 : ℝ) ≠ (3/5 : ℝ) * (-4/5 : ℝ) := by
  norm_num [Complex.normSq_apply]

end InfoGeometry.Physics.NuclearEffectiveMultipole
