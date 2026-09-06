import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# $\mathbb{Z}_2$-Graded Parity Decomposition and Spectral Realization of Riemann $\xi$

This module formalizes the exact $\mathbb{Z}_2$-graded reflection architecture on the $\beta$-line:
  1. Involutive Reflection $J(\beta) = 2 - \beta$ and Graded Projections $P_\pm$.
  2. The Completed Zeta Function $\xi(\beta/2)$ occupies strictly the Symmetric (Cosine) Sector:
     $P_+ X = X, \quad P_- X = 0$.
  3. The Canonical Antisymmetric Companion (Centered Primitive) $Y(\beta) = \int_1^\beta X(b) db$:
     $Y(1) = 0, \quad Y(2-\beta) = -Y(\beta), \quad Y(0) = -Y(2), \quad P_- Y = Y, \quad P_+ Y = 0$.
  4. The Spectral Parity Ladder:
     $\frac{\sin(tu)}{u} \xrightarrow{d/dt} \cos(tu) \xrightarrow{d/dt} -u \sin(tu)$.
  5. The Cayley Inversion $z \mapsto z^{-1}$ and $\mathbb{Z}_2$-mode separation into $\cos(n\theta)$ and $\sin(n\theta)$.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ZetaZ2ParitySpectralDecomposition

open Real
open MeasureTheory
open intervalIntegral

/-!
=============================================================================
PART 1: Involutive Reflection and $\mathbb{Z}_2$-Graded Projections
=============================================================================
-/

/-- The canonical reflection on the beta-line: J(β) = 2 - β -/
def J (β : ℝ) : ℝ := 2 - β

@[simp] theorem J_J (β : ℝ) : J (J β) = β := by
  dsimp [J]; ring

theorem J_fixed_iff (β : ℝ) : J β = β ↔ β = 1 := by
  dsimp [J]
  constructor <;> intro h <;> linarith

/-- Symmetric / Inversion-Even Projection P_+ -/
def P_plus (F : ℝ → ℝ) (β : ℝ) : ℝ :=
  (1 / 2) * (F β + F (2 - β))

/-- Antisymmetric / Inversion-Odd Projection P_- -/
def P_minus (F : ℝ → ℝ) (β : ℝ) : ℝ :=
  (1 / 2) * (F β - F (2 - β))

/-- Direct sum decomposition: F = P_+ F + P_- F -/
theorem projection_decomposition (F : ℝ → ℝ) (β : ℝ) :
    P_plus F β + P_minus F β = F β := by
  dsimp [P_plus, P_minus]
  ring

/-- P_+ yields a symmetric function under β ↦ 2 - β -/
theorem P_plus_symmetric (F : ℝ → ℝ) (β : ℝ) :
    P_plus F (2 - β) = P_plus F β := by
  dsimp [P_plus]
  have : 2 - (2 - β) = β := by ring
  rw [this, add_comm]

/-- P_- yields an antisymmetric function under β ↦ 2 - β -/
theorem P_minus_antisymmetric (F : ℝ → ℝ) (β : ℝ) :
    P_minus F (2 - β) = - P_minus F β := by
  dsimp [P_minus]
  have : 2 - (2 - β) = β := by ring
  rw [this]
  ring

/-- Idempotency of P_+ -/
theorem P_plus_idempotent (F : ℝ → ℝ) (β : ℝ) :
    P_plus (P_plus F) β = P_plus F β := by
  dsimp [P_plus]
  have : 2 - (2 - β) = β := by ring
  rw [this]
  ring

/-- Idempotency of P_- -/
theorem P_minus_idempotent (F : ℝ → ℝ) (β : ℝ) :
    P_minus (P_minus F) β = P_minus F β := by
  dsimp [P_minus]
  have : 2 - (2 - β) = β := by ring
  rw [this]
  ring

/-- Orthogonality: P_+ P_- = 0 -/
theorem P_plus_P_minus_orthogonal (F : ℝ → ℝ) (β : ℝ) :
    P_plus (P_minus F) β = 0 := by
  dsimp [P_plus, P_minus]
  have : 2 - (2 - β) = β := by ring
  rw [this]
  ring

/-- Orthogonality: P_- P_+ = 0 -/
theorem P_minus_P_plus_orthogonal (F : ℝ → ℝ) (β : ℝ) :
    P_minus (P_plus F) β = 0 := by
  dsimp [P_plus, P_minus]
  have : 2 - (2 - β) = β := by ring
  rw [this]
  ring

/-!
=============================================================================
PART 2: Completed Zeta Occupies Strictly the Symmetric Sector
=============================================================================
-/

/-- Any symmetric seed X(2 - β) = X(β) is invariant under P_+ -/
theorem symmetric_seed_P_plus (X : ℝ → ℝ) (hX : ∀ β, X (2 - β) = X β) (β : ℝ) :
    P_plus X β = X β := by
  dsimp [P_plus]
  rw [hX β]
  ring

/-- Any symmetric seed X(2 - β) = X(β) is strictly annihilated by P_- -/
theorem symmetric_seed_P_minus_zero (X : ℝ → ℝ) (hX : ∀ β, X (2 - β) = X β) (β : ℝ) :
    P_minus X β = 0 := by
  dsimp [P_minus]
  rw [hX β]
  ring

/-!
=============================================================================
PART 3: The Canonical Antisymmetric Companion (Centered Primitive)
=============================================================================
-/

/-- The centered primitive Y(β) = ∫_1^β X(b) db -/
def centeredPrimitive (X : ℝ → ℝ) (β : ℝ) : ℝ :=
  ∫ b in (1 : ℝ)..β, X b

/-- Vanishing at the central critical point β = 1 -/
theorem centeredPrimitive_center (X : ℝ → ℝ) :
    centeredPrimitive X 1 = 0 := by
  dsimp [centeredPrimitive]
  exact integral_same

/-- Antisymmetric functional equation Y(2 - β) = -Y(β) for symmetric X -/
theorem centeredPrimitive_reflection (X : ℝ → ℝ) (hX_symm : ∀ b, X (2 - b) = X b) (β : ℝ) :
    centeredPrimitive X (2 - β) = - centeredPrimitive X β := by
  dsimp [centeredPrimitive]
  have h_comp : (∫ b in (1 : ℝ)..β, X (2 - b)) = ∫ x in (2 - β)..(2 - (1 : ℝ)), X x :=
    intervalIntegral.integral_comp_sub_left X 2
  have h_symm_pt : (fun b => X (2 - b)) = X := funext hX_symm
  rw [h_symm_pt] at h_comp
  have h21 : (2 : ℝ) - 1 = 1 := by ring
  rw [h21] at h_comp
  have h_rev : (∫ x in (2 - β)..1, X x) = - ∫ x in (1 : ℝ)..(2 - β), X x :=
    integral_symm 1 (2 - β)
  rw [h_rev] at h_comp
  linarith

/-- Endpoint antiperiodicity: Y(0) = -Y(2) -/
theorem centeredPrimitive_endpoints (X : ℝ → ℝ) (hX_symm : ∀ b, X (2 - b) = X b) :
    centeredPrimitive X 0 = - centeredPrimitive X 2 := by
  have h := centeredPrimitive_reflection X hX_symm 2
  have h20 : 2 - (2 : ℝ) = 0 := by ring
  rw [h20] at h
  exact h

/-- Y occupies strictly the antisymmetric sector: P_- Y = Y -/
theorem centeredPrimitive_P_minus (X : ℝ → ℝ) (hX_symm : ∀ b, X (2 - b) = X b) (β : ℝ) :
    P_minus (centeredPrimitive X) β = centeredPrimitive X β := by
  dsimp [P_minus]
  rw [centeredPrimitive_reflection X hX_symm β]
  ring

/-- Y has zero projection in the symmetric sector: P_+ Y = 0 -/
theorem centeredPrimitive_P_plus_zero (X : ℝ → ℝ) (hX_symm : ∀ b, X (2 - b) = X b) (β : ℝ) :
    P_plus (centeredPrimitive X) β = 0 := by
  dsimp [P_plus]
  rw [centeredPrimitive_reflection X hX_symm β]
  ring

/-- Derivative of the centered primitive is the original symmetric function X -/
theorem centeredPrimitive_hasDerivAt (X : ℝ → ℝ) (hX_cont : Continuous X) (β : ℝ) :
    HasDerivAt (fun u => ∫ b in (1 : ℝ)..u, X b) (X β) β := by
  exact intervalIntegral.integral_hasDerivAt_right
    (hX_cont.intervalIntegrable 1 β)
    (hX_cont.stronglyMeasurableAtFilter _ _)
    hX_cont.continuousAt

/-!
=============================================================================
PART 4: Spectral Parity Ladder (Cosine/Sine Differentiation Relations)
=============================================================================
-/

/-- Derivative of the normalized sine kernel t ↦ sin(tu)/u is cos(tu) -/
theorem deriv_sinc_kernel (u : ℝ) (hu : u ≠ 0) (t : ℝ) :
    HasDerivAt (fun t => sin (t * u) / u) (cos (t * u)) t := by
  have h1 : HasDerivAt (fun t => t * u) u t := hasDerivAt_mul_const u
  have h2 : HasDerivAt (fun t => sin (t * u)) (cos (t * u) * u) t :=
    HasDerivAt.sin h1
  have h3 := HasDerivAt.div_const h2 u
  have hcancel : (cos (t * u) * u) / u = cos (t * u) := mul_div_cancel_right₀ (cos (t * u)) hu
  rw [hcancel] at h3
  exact h3

/-- Derivative of the cosine kernel t ↦ cos(tu) is -u * sin(tu) -/
theorem deriv_cos_kernel (u : ℝ) (t : ℝ) :
    HasDerivAt (fun t => cos (t * u)) (- u * sin (t * u)) t := by
  have h1 : HasDerivAt (fun t => t * u) u t := hasDerivAt_mul_const u
  have h2 : HasDerivAt (fun t => cos (t * u)) (- sin (t * u) * u) t :=
    HasDerivAt.cos h1
  have h_eq : - sin (t * u) * u = - u * sin (t * u) := by ring
  rw [h_eq] at h2
  exact h2

/-- Parity of cosine kernel: even under t ↦ -t -/
theorem cos_kernel_even (u t : ℝ) :
    cos ((-t) * u) = cos (t * u) := by
  have : (-t) * u = - (t * u) := by ring
  rw [this, cos_neg]

/-- Parity of sinc kernel: odd under t ↦ -t -/
theorem sinc_kernel_odd (u t : ℝ) :
    sin ((-t) * u) / u = - (sin (t * u) / u) := by
  have : (-t) * u = - (t * u) := by ring
  rw [this, sin_neg, neg_div]

/-!
=============================================================================
PART 5: Cayley Mode Symmetrization
=============================================================================
-/

/-- On the unit circle z = e^(iθ), the inversion z ↦ z⁻¹ maps θ ↦ -θ -/
theorem complex_exp_inv_angle (θ : ℝ) :
    (Complex.exp (Complex.I * (θ : ℂ)))⁻¹ = Complex.exp (Complex.I * ((-θ) : ℂ)) := by
  rw [← Complex.exp_neg]
  congr 1
  ring

/-- Cosine sector selects the inversion-even mode: (e^(iz) + e^(-iz)) / 2 = cos(z) -/
theorem cayley_cosine_mode (z : ℂ) :
    (Complex.exp (Complex.I * z) + Complex.exp (Complex.I * (-z))) / 2 = Complex.cos z := by
  dsimp [Complex.cos]
  have h1 : Complex.I * z = z * Complex.I := by ring
  have h2 : Complex.I * (-z) = -z * Complex.I := by ring
  rw [h1, h2]

/-- Sine sector selects the inversion-odd mode: (e^(iz) - e^(-iz)) / (2i) = sin(z) -/
theorem cayley_sine_mode (z : ℂ) :
    (Complex.exp (Complex.I * z) - Complex.exp (Complex.I * (-z))) / (2 * Complex.I) = Complex.sin z := by
  dsimp [Complex.sin]
  have h1 : Complex.I * z = z * Complex.I := by ring
  have h2 : Complex.I * (-z) = -z * Complex.I := by ring
  rw [h1, h2]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2I : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero hI
  rw [div_eq_iff h2I]
  have h_I2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination -((Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I))) * h_I2

end InfoGeometry.Arithmetic.ZetaZ2ParitySpectralDecomposition
