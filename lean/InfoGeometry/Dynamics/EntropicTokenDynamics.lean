import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite entropic token generators

This owner records the finite-dimensional algebraic part of the token model.
The total generator is a linear operator `-iH - Γ`.  Differential equations,
positivity of `Γ`, and partial-isometry structure are deliberately separate:
they require additional hypotheses and are not consequences of linearity.
-/

namespace InfoGeometry.Dynamics

noncomputable section

variable {V : Type*} [Fintype V]

/-- The finite token carrier with a two-component internal chiral factor. -/
abbrev TokenHilbertSpace (V : Type*) [Fintype V] := (V × Fin 2) → ℂ

/-- The finite-dimensional Hermitian pairing on the token carrier. -/
noncomputable def tokenPairing (ψ φ : TokenHilbertSpace V) : ℂ :=
  ∑ x, star (ψ x) * φ x

lemma tokenPairing_sub (ψ φ χ : TokenHilbertSpace V) :
    tokenPairing ψ (φ - χ) = tokenPairing ψ φ - tokenPairing ψ χ := by
  simp [tokenPairing, Finset.sum_sub_distrib, mul_sub]

/-- A pair of linear Hamiltonian and filter operators. -/
structure TokenGenerator (V : Type*) [Fintype V] where
  H : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V
  Gamma : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V

/-- A generator together with exactly the hypotheses needed for the
    instantaneous dissipative estimate.  The cancellation hypothesis is
    stated explicitly so that no self-adjointness convention is hidden in the
    interface. -/
structure DissipativeTokenGenerator (V : Type*) [Fintype V]
    extends TokenGenerator V where
  hamiltonian_real_pairing_zero : ∀ ψ : TokenHilbertSpace V,
    (tokenPairing ψ ((-Complex.I) • H ψ)).re = 0
  gamma_real_pairing_nonneg : ∀ ψ : TokenHilbertSpace V,
    0 ≤ (tokenPairing ψ (Gamma ψ)).re

/-- The single total non-unitary token generator. -/
def totalTokenGenerator (gen : TokenGenerator V) :
    TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V :=
  (-Complex.I) • gen.H - gen.Gamma

@[simp] theorem totalTokenGenerator_apply (gen : TokenGenerator V)
    (ψ : TokenHilbertSpace V) :
    totalTokenGenerator gen ψ = (-Complex.I) • gen.H ψ - gen.Gamma ψ := rfl

theorem totalTokenGenerator_decomposition (gen : TokenGenerator V)
    (ψ : TokenHilbertSpace V) :
    totalTokenGenerator gen ψ =
      (-Complex.I) • gen.H ψ - gen.Gamma ψ := by
  rfl

@[simp] theorem totalTokenGenerator_zero (gen : TokenGenerator V) :
    totalTokenGenerator gen 0 = 0 := by
  simp [totalTokenGenerator]

theorem totalTokenGenerator_eq_zero_of_components_eq_zero
    (gen : TokenGenerator V) (ψ : TokenHilbertSpace V)
    (hH : gen.H ψ = 0) (hGamma : gen.Gamma ψ = 0) :
    totalTokenGenerator gen ψ = 0 := by
  rw [totalTokenGenerator_apply, hH, hGamma]
  simp

theorem dissipativeTokenGenerator_real_pairing
    (gen : DissipativeTokenGenerator V) (ψ : TokenHilbertSpace V) :
    (tokenPairing ψ (totalTokenGenerator gen.toTokenGenerator ψ)).re =
      -(tokenPairing ψ (gen.Gamma ψ)).re := by
  rw [totalTokenGenerator_apply, tokenPairing_sub]
  change (tokenPairing ψ ((-Complex.I) • gen.H ψ)).re -
      (tokenPairing ψ (gen.Gamma ψ)).re = _
  rw [gen.hamiltonian_real_pairing_zero]
  ring

theorem dissipativeTokenGenerator_real_pairing_nonpos
    (gen : DissipativeTokenGenerator V) (ψ : TokenHilbertSpace V) :
    (tokenPairing ψ (totalTokenGenerator gen.toTokenGenerator ψ)).re ≤ 0 := by
  rw [dissipativeTokenGenerator_real_pairing]
  exact neg_nonpos.mpr (gen.gamma_real_pairing_nonneg ψ)

/-- The exact static identity underlying the norm-decay calculation.  A
    time-dependent decay theorem additionally needs a differentiable
    trajectory, so it is intentionally not claimed here. -/
theorem dissipativeTokenGenerator_two_real_pairing
    (gen : DissipativeTokenGenerator V) (ψ : TokenHilbertSpace V) :
    2 * (tokenPairing ψ (totalTokenGenerator gen.toTokenGenerator ψ)).re =
      -2 * (tokenPairing ψ (gen.Gamma ψ)).re := by
  rw [dissipativeTokenGenerator_real_pairing]
  ring

theorem dissipativeTokenGenerator_two_real_pairing_nonpos
    (gen : DissipativeTokenGenerator V) (ψ : TokenHilbertSpace V) :
    2 * (tokenPairing ψ (totalTokenGenerator gen.toTokenGenerator ψ)).re ≤ 0 := by
  rw [dissipativeTokenGenerator_two_real_pairing]
  nlinarith [gen.gamma_real_pairing_nonneg ψ]

/-! ### Finite mode coupling and context backreaction -/

/-- The two-channel forward/backward non-Hermitian coupler. -/
def modeCouplerMatrix (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ![![(-Complex.I) * ωPlus - γPlus, κ],
    ![star κ, (-Complex.I) * ωMinus - γMinus]]

/-- The skew-coupling convention.  Unlike `modeCouplerMatrix`, its
    off-diagonal part is skew-Hermitian and therefore contributes no real
    quadratic pairing. -/
def modeCouplerMatrixSkewCoupling (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ![![(-Complex.I) * ωPlus - γPlus, κ],
    ![-star κ, (-Complex.I) * ωMinus - γMinus]]

@[simp] theorem modeCouplerMatrixSkewCoupling_offDiagonal_plus
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) :
    modeCouplerMatrixSkewCoupling ωPlus ωMinus γPlus γMinus κ 0 1 = κ := by
  simp [modeCouplerMatrixSkewCoupling]

@[simp] theorem modeCouplerMatrixSkewCoupling_offDiagonal_minus
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) :
    modeCouplerMatrixSkewCoupling ωPlus ωMinus γPlus γMinus κ 1 0 = -star κ := by
  simp [modeCouplerMatrixSkewCoupling]

lemma star_mul_coupler_cross (x κ y : ℂ) :
    star (star x * κ * y) = star y * star κ * x := by
  simp only [star_mul, star_star]
  ring

lemma real_sub_star_mul_coupler_cross (x κ y : ℂ) :
    (star x * κ * y - star y * star κ * x).re = 0 := by
  rw [← star_mul_coupler_cross x κ y]
  simp [Complex.sub_re]
  ring

lemma skew_coupler_cross_real_zero (x κ y : ℂ) :
    (star x * (κ * y) + star y * (-star κ * x)).re = 0 := by
  convert real_sub_star_mul_coupler_cross x κ y using 1
  all_goals ring_nf

lemma real_damped_complex_quadratic (ω γ : ℝ) (x : ℂ) :
    (star x * (((-Complex.I) * ω - γ) * x)).re =
      -γ * ‖x‖ ^ 2 := by
  rw [Complex.sq_norm]
  simp [Complex.mul_re, Complex.normSq_apply]
  ring

theorem modeCouplerMatrixSkewCoupling_mulVec_apply_zero
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) (a : Fin 2 → ℂ) :
    (modeCouplerMatrixSkewCoupling ωPlus ωMinus γPlus γMinus κ).mulVec a 0 =
      ((-Complex.I) * ωPlus - γPlus) * a 0 + κ * a 1 := by
  simp [Matrix.mulVec, modeCouplerMatrixSkewCoupling, dotProduct,
    Fin.sum_univ_two]

theorem modeCouplerMatrixSkewCoupling_mulVec_apply_one
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) (a : Fin 2 → ℂ) :
    (modeCouplerMatrixSkewCoupling ωPlus ωMinus γPlus γMinus κ).mulVec a 1 =
      -star κ * a 0 + ((-Complex.I) * ωMinus - γMinus) * a 1 := by
  simp [Matrix.mulVec, modeCouplerMatrixSkewCoupling, dotProduct,
    Fin.sum_univ_two]

theorem modeCouplerMatrixSkewCoupling_mulVec_readout
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) (a : Fin 2 → ℂ) :
    (modeCouplerMatrixSkewCoupling ωPlus ωMinus γPlus γMinus κ).mulVec a =
      ![ ((-Complex.I) * ωPlus - γPlus) * a 0 + κ * a 1,
        -star κ * a 0 + ((-Complex.I) * ωMinus - γMinus) * a 1 ] := by
  funext i
  fin_cases i
  · exact modeCouplerMatrixSkewCoupling_mulVec_apply_zero
      ωPlus ωMinus γPlus γMinus κ a
  · exact modeCouplerMatrixSkewCoupling_mulVec_apply_one
      ωPlus ωMinus γPlus γMinus κ a

theorem modeCouplerMatrixSkewCoupling_pairing_real
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) (a : Fin 2 → ℂ) :
    (∑ i : Fin 2, star (a i) *
      ((modeCouplerMatrixSkewCoupling ωPlus ωMinus γPlus γMinus κ).mulVec a i)).re =
      -γPlus * ‖a 0‖ ^ 2 - γMinus * ‖a 1‖ ^ 2 := by
  rw [Fin.sum_univ_two,
    modeCouplerMatrixSkewCoupling_mulVec_apply_zero,
    modeCouplerMatrixSkewCoupling_mulVec_apply_one]
  have hsplit :
      star (a 0) * (((-Complex.I) * ωPlus - γPlus) * a 0 + κ * a 1) +
          star (a 1) * (-star κ * a 0 +
            ((-Complex.I) * ωMinus - γMinus) * a 1) =
        star (a 0) * (((-Complex.I) * ωPlus - γPlus) * a 0) +
          star (a 1) * (((-Complex.I) * ωMinus - γMinus) * a 1) +
            (star (a 0) * (κ * a 1) +
              star (a 1) * (-star κ * a 0)) := by
    ring
  rw [hsplit]
  simp only [Complex.add_re]
  rw [real_damped_complex_quadratic, real_damped_complex_quadratic,
    ← Complex.add_re, skew_coupler_cross_real_zero]
  ring

theorem modeCouplerMatrixSkewCoupling_pairing_real_nonpos
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ)
    (hPlus : 0 ≤ γPlus) (hMinus : 0 ≤ γMinus) (a : Fin 2 → ℂ) :
    (∑ i : Fin 2, star (a i) *
      ((modeCouplerMatrixSkewCoupling ωPlus ωMinus γPlus γMinus κ).mulVec a i)).re ≤ 0 := by
  rw [modeCouplerMatrixSkewCoupling_pairing_real]
  have h0 : 0 ≤ ‖a 0‖ ^ 2 := sq_nonneg _
  have h1 : 0 ≤ ‖a 1‖ ^ 2 := sq_nonneg _
  nlinarith

theorem modeCouplerMatrixSkewCoupling_pairing_real_zero
    (ωPlus ωMinus : ℝ) (κ : ℂ) (a : Fin 2 → ℂ) :
    (∑ i : Fin 2, star (a i) *
      ((modeCouplerMatrixSkewCoupling ωPlus ωMinus 0 0 κ).mulVec a i)).re = 0 := by
  rw [modeCouplerMatrixSkewCoupling_pairing_real]
  simp

theorem modeCouplerMatrix_mulVec_apply_zero
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ)
    (a : Fin 2 → ℂ) :
  (modeCouplerMatrix ωPlus ωMinus γPlus γMinus κ).mulVec a 0 =
      ((-Complex.I) * ωPlus - γPlus) * a 0 + κ * a 1 := by
  simp [Matrix.mulVec, modeCouplerMatrix, dotProduct, Fin.sum_univ_two]

theorem modeCouplerMatrix_mulVec_apply_one
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ)
    (a : Fin 2 → ℂ) :
  (modeCouplerMatrix ωPlus ωMinus γPlus γMinus κ).mulVec a 1 =
      star κ * a 0 + ((-Complex.I) * ωMinus - γMinus) * a 1 := by
  simp [Matrix.mulVec, modeCouplerMatrix, dotProduct, Fin.sum_univ_two]

/-- Exact real quadratic pairing for the physical conjugate coupler. -/
theorem modeCouplerMatrix_pairing_real
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) (a : Fin 2 → ℂ) :
    (∑ i : Fin 2, star (a i) *
      ((modeCouplerMatrix ωPlus ωMinus γPlus γMinus κ).mulVec a i)).re =
      -γPlus * ‖a 0‖ ^ 2 - γMinus * ‖a 1‖ ^ 2 +
        2 * (star (a 0) * κ * a 1).re := by
  rw [Fin.sum_univ_two,
    modeCouplerMatrix_mulVec_apply_zero,
    modeCouplerMatrix_mulVec_apply_one]
  have hsplit :
      star (a 0) * (((-Complex.I) * ωPlus - γPlus) * a 0 + κ * a 1) +
          star (a 1) * (star κ * a 0 +
            ((-Complex.I) * ωMinus - γMinus) * a 1) =
        star (a 0) * (((-Complex.I) * ωPlus - γPlus) * a 0) +
          star (a 1) * (((-Complex.I) * ωMinus - γMinus) * a 1) +
            (star (a 0) * κ * a 1 +
              star (a 1) * star κ * a 0) := by
    ring
  rw [hsplit]
  simp only [Complex.add_re]
  rw [real_damped_complex_quadratic, real_damped_complex_quadratic]
  have hcross :
      (star (a 1) * star κ * a 0).re = (star (a 0) * κ * a 1).re := by
    rw [← star_mul_coupler_cross]
    simp
    ring
  rw [hcross]
  ring

/-- Dissipativity criterion for the conjugate coupler, with the coherent
    exchange term exposed as an explicit hypothesis. -/
theorem modeCouplerMatrix_pairing_real_nonpos_of_cross_bound
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) (a : Fin 2 → ℂ)
    (hcross : 2 * (star (a 0) * κ * a 1).re ≤
      γPlus * ‖a 0‖ ^ 2 + γMinus * ‖a 1‖ ^ 2) :
    (∑ i : Fin 2, star (a i) *
      ((modeCouplerMatrix ωPlus ωMinus γPlus γMinus κ).mulVec a i)).re ≤ 0 := by
  rw [modeCouplerMatrix_pairing_real]
  nlinarith

theorem modeCouplerMatrix_mulVec_readout
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ)
    (a : Fin 2 → ℂ) :
    (modeCouplerMatrix ωPlus ωMinus γPlus γMinus κ).mulVec a =
      ![ ((-Complex.I) * ωPlus - γPlus) * a 0 + κ * a 1,
        star κ * a 0 + ((-Complex.I) * ωMinus - γMinus) * a 1 ] := by
  funext i
  fin_cases i
  · exact modeCouplerMatrix_mulVec_apply_zero ωPlus ωMinus γPlus γMinus κ a
  · exact modeCouplerMatrix_mulVec_apply_one ωPlus ωMinus γPlus γMinus κ a

@[simp] theorem modeCouplerMatrix_zero_offDiagonal
    (ωPlus ωMinus γPlus γMinus : ℝ) :
    (modeCouplerMatrix ωPlus ωMinus γPlus γMinus 0) 0 1 = 0 := by
  simp [modeCouplerMatrix]

@[simp] theorem modeCouplerMatrix_reverse_offDiagonal
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) :
    (modeCouplerMatrix ωPlus ωMinus γPlus γMinus κ) 1 0 = star κ := by
  simp [modeCouplerMatrix]

theorem modeCouplerMatrix_real_diag_plus
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) :
    (modeCouplerMatrix ωPlus ωMinus γPlus γMinus κ 0 0).re = -γPlus := by
  simp [modeCouplerMatrix]

theorem modeCouplerMatrix_real_diag_minus
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) :
    (modeCouplerMatrix ωPlus ωMinus γPlus γMinus κ 1 1).re = -γMinus := by
  simp [modeCouplerMatrix]

theorem modeCouplerMatrix_real_trace
    (ωPlus ωMinus γPlus γMinus : ℝ) (κ : ℂ) :
    (Matrix.trace (modeCouplerMatrix ωPlus ωMinus γPlus γMinus κ)).re =
      -(γPlus + γMinus) := by
  simp [Matrix.trace, modeCouplerMatrix]
  ring

/-- The scalar four-wave mixing expression, including its conjugate term. -/
def fourWaveMixingTerm (χ aPlus aMinus aZero : ℂ) : ℂ :=
  χ * (star aPlus * star aMinus * aZero * aZero) +
    star χ * (star aZero * star aZero * aPlus * aMinus)

theorem star_fourWaveMixingTerm (χ aPlus aMinus aZero : ℂ) :
    star (fourWaveMixingTerm χ aPlus aMinus aZero) =
      fourWaveMixingTerm χ aPlus aMinus aZero := by
  simp only [fourWaveMixingTerm, star_add, star_mul, star_star]
  ring

@[simp] theorem fourWaveMixingTerm_zero_pump (χ aPlus aMinus : ℂ) :
    fourWaveMixingTerm χ aPlus aMinus 0 = 0 := by
  simp [fourWaveMixingTerm]

/-- A context operator with a positive linear decay rate. -/
structure ContextField (V : Type*) [Fintype V] where
  K : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V
  decayRate : ℝ
  decayRate_pos : 0 < decayRate

/-- The pairing-level self-adjointness predicate for a context operator. -/
def IsTokenPairingSelfAdjoint (K : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V) : Prop :=
  ∀ ψ φ, tokenPairing (K ψ) φ = tokenPairing ψ (K φ)

/-- A context field carrying, rather than assuming, its self-adjointness law. -/
structure SelfAdjointContextField (V : Type*) [Fintype V]
    extends ContextField V where
  K_selfAdjoint : IsTokenPairingSelfAdjoint K

/-- The algebraic right-hand side of the context equation. -/
def contextDerivative (ctx : ContextField V)
    (response : TokenHilbertSpace V → TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V)
    (D : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V)
    (ψ : TokenHilbertSpace V) : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V :=
  response ψ - (ctx.decayRate : ℂ) • ctx.K + (D.comp ctx.K - ctx.K.comp D)

@[simp] theorem contextDerivative_zero_response (ctx : ContextField V)
    (response : TokenHilbertSpace V → TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V)
    (D : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V)
    (ψ : TokenHilbertSpace V) (h : response ψ = 0) :
    contextDerivative ctx response D ψ =
      -(ctx.decayRate : ℂ) • ctx.K + (D.comp ctx.K - ctx.K.comp D) := by
  rw [contextDerivative, h]
  congr 1
  rw [zero_sub]
  exact (neg_smul (ctx.decayRate : ℂ) ctx.K).symm

/-! The zero-response, flat-transport specialization is the exact algebraic
    cooling equation. -/
theorem contextDerivative_decay_only (ctx : ContextField V)
    (response : TokenHilbertSpace V → TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V)
    (D : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V)
    (ψ : TokenHilbertSpace V) (hresponse : response ψ = 0)
    (hcomm : D.comp ctx.K = ctx.K.comp D) :
    contextDerivative ctx response D ψ = -(ctx.decayRate : ℂ) • ctx.K := by
  rw [contextDerivative_zero_response ctx response D ψ hresponse, hcomm]
  simp

end
end InfoGeometry.Dynamics
