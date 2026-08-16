import Mathlib.Tactic
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.HestenesComplexTranslation

/-!
# Completed Xi in Hestenes Homogeneous and Klein-Cylinder Coordinates

Native theorem-safe algebraic bridge between:

* homogeneous coordinates `(p,q) = (s,1-s)`;
* the projective coordinate `s = p / (p+q)`;
* the Cayley/fugacity coordinate `τ = p/q = s/(1-x)`;
* the Hestenes generators `H`, `ε`, and `K = Hε`;
* the Cartan flow `τ ↦ exp(2t) τ`;
* the functional reflection `s ↦ 1-s`, represented by homogeneous swap;
* the existing critical-line/unit-circle Cayley theorem;
* the real doubled Hestenes embedding of the centered coordinate `s - 1/2`;
* the universal-cover Klein glide
  `(ρ,θ) ↦ (-ρ, θ + L/2)`.

No analytic continuation, explicit formula, zero-location theorem, quotient
manifold construction, or Riemann-hypothesis statement is asserted here.
-/

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.CompletedXiHestenesHomogeneousCoordinates

open Complex Matrix
open InfoGeometry.Krein
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.HestenesComplexTranslation

/-! ## 1. Homogeneous coordinates -/

/-- Homogeneous two-component complex carrier. -/
abbrev HomogeneousPair : Type :=
  ℂ × ℂ

/-- Homogeneous lift of the spectral parameter:
`Ψ(s) = (s, 1-s)`. -/
def homogeneousPsi (s : ℂ) : HomogeneousPair :=
  (s, 1 - s)

/-- Projective affine readout `s = p / (p+q)`. -/
def projectiveS (v : HomogeneousPair) : ℂ :=
  v.1 / (v.1 + v.2)

/-- Cross-ratio/Cayley readout `τ = p/q`. -/
def tauCoord (v : HomogeneousPair) : ℂ :=
  v.1 / v.2

/-- Nonzero homogeneous rescaling. -/
def scalePair (c : ℂ) (v : HomogeneousPair) : HomogeneousPair :=
  (c * v.1, c * v.2)

/-- Functional-equation Weyl swap `(p,q) ↦ (q,p)`. -/
def homogeneousSwap (v : HomogeneousPair) : HomogeneousPair :=
  (v.2, v.1)

/-- Diagonal Hestenes/Krein sign action `(p,q) ↦ (p,-q)`. -/
def homogeneousEpsilon (v : HomogeneousPair) : HomogeneousPair :=
  (v.1, -v.2)

/-- Quarter-turn action `(p,q) ↦ (-q,p)`. -/
def homogeneousK (v : HomogeneousPair) : HomogeneousPair :=
  (-v.2, v.1)

@[simp]
theorem homogeneousPsi_sum (s : ℂ) :
    (homogeneousPsi s).1 + (homogeneousPsi s).2 = 1 := by
  simp [homogeneousPsi]

@[simp]
theorem projectiveS_homogeneousPsi (s : ℂ) :
    projectiveS (homogeneousPsi s) = s := by
  change s / (s + (1 - s)) = s
  have hsum : s + (1 - s) = (1 : ℂ) := by
    ring
  rw [hsum, div_one]

@[simp]
theorem tauCoord_homogeneousPsi (s : ℂ) :
    tauCoord (homogeneousPsi s) =
      s / (1 - s) :=
  rfl

@[simp]
theorem tauCoord_homogeneousPsi_eq_cayleyToFugacity (s : ℂ) :
    tauCoord (homogeneousPsi s) =
      cayleyToFugacity s :=
  rfl

/-- Projective affine readout is invariant under nonzero homogeneous scaling. -/
theorem projectiveS_scalePair
    (c : ℂ)
    (hc : c ≠ 0)
    (v : HomogeneousPair) :
    projectiveS (scalePair c v) =
      projectiveS v := by
  rcases v with ⟨p, q⟩
  by_cases hsum : p + q = 0
  · have hscaled :
        c * p + c * q = 0 := by
      rw [← mul_add, hsum, mul_zero]
    simp [projectiveS, scalePair, hsum, hscaled]
  · change
      (c * p) / (c * p + c * q) =
        p / (p + q)
    rw [← mul_add]
    field_simp [hc, hsum]

/-- The cross-ratio coordinate is invariant under nonzero common scaling. -/
theorem tauCoord_scalePair
    (c : ℂ)
    (hc : c ≠ 0)
    (v : HomogeneousPair) :
    tauCoord (scalePair c v) =
      tauCoord v := by
  rcases v with ⟨p, q⟩
  by_cases hq : q = 0
  · simp [tauCoord, scalePair, hq]
  · change
      (c * p) / (c * q) = p / q
    field_simp [hc, hq]

@[simp]
theorem homogeneousSwap_homogeneousPsi (s : ℂ) :
    homogeneousSwap (homogeneousPsi s) =
      homogeneousPsi (1 - s) := by
  ext <;>
    simp [homogeneousSwap, homogeneousPsi]

@[simp]
theorem homogeneousSwap_involutive :
    Function.Involutive homogeneousSwap := by
  intro v
  rcases v with ⟨p, q⟩
  rfl

@[simp]
theorem homogeneousEpsilon_involutive :
    Function.Involutive homogeneousEpsilon := by
  intro v
  rcases v with ⟨p, q⟩
  simp [homogeneousEpsilon]

@[simp]
theorem homogeneousK_sq (v : HomogeneousPair) :
    homogeneousK (homogeneousK v) = -v := by
  rcases v with ⟨p, q⟩
  ext <;>
    simp [homogeneousK]

@[simp]
theorem homogeneousK_eq_swap_epsilon (v : HomogeneousPair) :
    homogeneousK v =
      homogeneousSwap (homogeneousEpsilon v) :=
  rfl

/-- Homogeneous swap sends `τ` to `τ⁻¹`. -/
theorem tauCoord_homogeneousSwap (v : HomogeneousPair) :
    tauCoord (homogeneousSwap v) =
      (tauCoord v)⁻¹ := by
  rcases v with ⟨p, q⟩
  change q / p = (p / q)⁻¹
  exact (inv_div p q).symm

/-- The quarter-turn sends `τ` to `-τ⁻¹`. -/
theorem tauCoord_homogeneousK (v : HomogeneousPair) :
    tauCoord (homogeneousK v) =
      -(tauCoord v)⁻¹ := by
  rcases v with ⟨p, q⟩
  change (-q) / p = -(p / q)⁻¹
  rw [neg_div]
  exact
    congrArg (fun z : ℂ => -z)
      (inv_div p q).symm

/-- Functional reflection becomes inversion in the `τ` coordinate. -/
theorem tauCoord_functionalReflection (s : ℂ) :
    tauCoord (homogeneousPsi (1 - s)) =
      (tauCoord (homogeneousPsi s))⁻¹ := by
  rw [← homogeneousSwap_homogeneousPsi]
  exact tauCoord_homogeneousSwap (homogeneousPsi s)

/-! ## 2. Concrete real Hestenes matrices -/

/-- Real `2 × 2` matrix carrier. -/
abbrev M2R : Type :=
  Matrix (Fin 2) (Fin 2) ℝ

/-- Weyl swap/reflection generator. -/
def matH : M2R :=
  !![0, 1;
     1, 0]

/-- Split-Cartan/sign generator. -/
def matEpsilon : M2R :=
  !![1, 0;
     0, -1]

/-- Hestenes phase/quarter-turn generator `K = Hε`. -/
def matK : M2R :=
  !![0, -1;
     1, 0]

theorem matH_mul_matEpsilon :
    matH * matEpsilon = matK := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [
      matH,
      matEpsilon,
      matK,
      Matrix.mul_apply,
      Fin.sum_univ_two
    ]

theorem matEpsilon_mul_matH :
    matEpsilon * matH = -matK := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [
      matH,
      matEpsilon,
      matK,
      Matrix.mul_apply,
      Fin.sum_univ_two
    ]

theorem matH_anticommutes_matEpsilon :
    matH * matEpsilon =
      -(matEpsilon * matH) := by
  rw [matH_mul_matEpsilon, matEpsilon_mul_matH]
  simp

theorem matH_sq :
    matH * matH = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [
      matH,
      Matrix.mul_apply,
      Fin.sum_univ_two
    ]

theorem matEpsilon_sq :
    matEpsilon * matEpsilon = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [
      matEpsilon,
      Matrix.mul_apply,
      Fin.sum_univ_two
    ]

theorem matK_sq :
    matK * matK = -(1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [
      matK,
      Matrix.mul_apply,
      Fin.sum_univ_two
    ]

/-- Weyl conjugation reverses the Cartan generator. -/
theorem matH_conjugates_matEpsilon :
    matH * matEpsilon * matH =
      -matEpsilon := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [
      matH,
      matEpsilon,
      Matrix.mul_apply,
      Fin.sum_univ_two
    ]

/-! ## Scalar extension and matrix action -/

/-- Entrywise extension of the real two-lane matrices to complex scalars. -/
def complexify (A : M2R) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (A i j : ℂ)

@[simp]
theorem complexify_apply (A : M2R) (i j : Fin 2) :
    complexify A i j = (A i j : ℂ) :=
  rfl

@[simp]
theorem complexify_one :
    complexify (1 : M2R) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  by_cases h : i = j <;> simp [complexify, Matrix.one_apply, h]

theorem complexify_mul (A B : M2R) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j
  simp [complexify, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The real matrix atom acting on the complex homogeneous pair. -/
def actMatrix (A : M2R) (v : HomogeneousPair) : HomogeneousPair :=
  ( ((complexify A).mulVec ![v.1, v.2]) 0,
    ((complexify A).mulVec ![v.1, v.2]) 1 )

theorem actMatrix_mul
    (A B : M2R) (v : HomogeneousPair) :
    actMatrix (A * B) v =
      actMatrix A (actMatrix B v) := by
  rcases v with ⟨p, q⟩
  have hvec :
      ![((complexify B).mulVec ![p, q]) 0,
        ((complexify B).mulVec ![p, q]) 1] =
        (complexify B).mulVec ![p, q] := by
    funext i
    fin_cases i <;> rfl
  have hmul :
      (complexify (A * B)).mulVec ![p, q] =
        (complexify A).mulVec ((complexify B).mulVec ![p, q]) := by
    rw [complexify_mul, Matrix.mulVec_mulVec]
  apply Prod.ext
  · change ((complexify (A * B)).mulVec ![p, q]) 0 =
      ((complexify A).mulVec
        ![((complexify B).mulVec ![p, q]) 0,
          ((complexify B).mulVec ![p, q]) 1]) 0
    rw [hvec]
    exact congrArg (fun w => w 0) hmul
  · change ((complexify (A * B)).mulVec ![p, q]) 1 =
      ((complexify A).mulVec
        ![((complexify B).mulVec ![p, q]) 0,
          ((complexify B).mulVec ![p, q]) 1]) 1
    rw [hvec]
    exact congrArg (fun w => w 1) hmul

@[simp]
theorem actMatrix_matH (v : HomogeneousPair) :
    actMatrix matH v = (v.2, v.1) := by
  rcases v with ⟨p, q⟩
  apply Prod.ext <;>
    simp [actMatrix, complexify, matH, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

@[simp]
theorem actMatrix_matEpsilon (v : HomogeneousPair) :
    actMatrix matEpsilon v = (v.1, -v.2) := by
  rcases v with ⟨p, q⟩
  apply Prod.ext <;>
    simp [actMatrix, complexify, matEpsilon, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

@[simp]
theorem actMatrix_matK (v : HomogeneousPair) :
    actMatrix matK v = (-v.2, v.1) := by
  rcases v with ⟨p, q⟩
  apply Prod.ext <;>
    simp [actMatrix, complexify, matK, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

theorem actMatrix_matH_involutive :
    Function.Involutive (actMatrix matH) := by
  intro v
  simpa using actMatrix_matH (actMatrix matH v)

theorem actMatrix_matK_sq (v : HomogeneousPair) :
    actMatrix matK (actMatrix matK v) = -v := by
  rcases v with ⟨p, q⟩
  simp [actMatrix_matK]

/-! ## 3. Split-Cartan flow -/

/-- Diagonal Cartan exponential `diag(exp t, exp(-t))`. -/
def cartanMatrix (t : ℝ) : M2R :=
  !![Real.exp t, 0;
     0, Real.exp (-t)]

/-- Cartan action on homogeneous coordinates. -/
def actCartan
    (t : ℝ)
    (v : HomogeneousPair) :
    HomogeneousPair :=
  ((Real.exp t : ℂ) * v.1,
   (Real.exp (-t) : ℂ) * v.2)

/-- The matrix Cartan action is the previously defined coordinate action. -/
theorem actMatrix_cartanMatrix_apply
    (t : ℝ) (v : HomogeneousPair) :
    actMatrix (cartanMatrix t) v = actCartan t v := by
  rcases v with ⟨p, q⟩
  apply Prod.ext <;>
    simp [actMatrix, actCartan, complexify, cartanMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-! ## Matrix action readback -/

@[simp]
theorem actMatrix_matH_homogeneousPsi (s : ℂ) :
    actMatrix matH (homogeneousPsi s) =
      homogeneousPsi (1 - s) := by
  rw [actMatrix_matH]
  simp [homogeneousPsi]

theorem actMatrix_matH_cartan_conjugacy
    (t : ℝ) (v : HomogeneousPair) :
    actMatrix matH
        (actMatrix (cartanMatrix t) (actMatrix matH v)) =
      actCartan (-t) v := by
  rcases v with ⟨p, q⟩
  apply Prod.ext <;>
    simp [actMatrix, complexify, matH, cartanMatrix, actCartan,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Real.exp_neg]

theorem projectiveS_actMatrix_matH
    (v : HomogeneousPair)
    (hsum : v.1 + v.2 ≠ 0) :
    projectiveS (actMatrix matH v) =
      1 - projectiveS v := by
  rw [actMatrix_matH]
  change v.2 / (v.2 + v.1) = 1 - v.1 / (v.1 + v.2)
  have hsum' : v.2 + v.1 ≠ 0 := by
    simpa [add_comm] using hsum
  field_simp [hsum, hsum'] <;> ring

theorem tauCoord_actMatrix_matH (v : HomogeneousPair) :
    tauCoord (actMatrix matH v) =
      (tauCoord v)⁻¹ := by
  rw [actMatrix_matH]
  change v.2 / v.1 = (v.1 / v.2)⁻¹
  rw [inv_div]

theorem tauCoord_actMatrix_matK (v : HomogeneousPair) :
    tauCoord (actMatrix matK v) =
      -(tauCoord v)⁻¹ := by
  rw [actMatrix_matK]
  change (-v.2) / v.1 = -(v.1 / v.2)⁻¹
  rw [inv_div]
  ring

@[simp]
theorem actCartan_zero (v : HomogeneousPair) :
    actCartan 0 v = v := by
  rcases v with ⟨p, q⟩
  simp [actCartan]

/-- The Cartan action is additive in its flow parameter. -/
theorem actCartan_add
    (s t : ℝ)
    (v : HomogeneousPair) :
    actCartan (s + t) v =
      actCartan s (actCartan t v) := by
  rcases v with ⟨p, q⟩
  ext <;>
    simp [actCartan, Real.exp_add] <;>
    ring

/-- Weyl conjugation reverses the Cartan flow. -/
theorem homogeneous_weyl_cartan_conjugacy
    (t : ℝ)
    (v : HomogeneousPair) :
    homogeneousSwap
        (actCartan t (homogeneousSwap v)) =
      actCartan (-t) v := by
  rcases v with ⟨p, q⟩
  ext <;>
    simp [homogeneousSwap, actCartan]

/-- Matrix-level Weyl relation
`H · exp(tε) · H = exp(-tε)`. -/
theorem matrix_weyl_cartan_conjugacy (t : ℝ) :
    matH * cartanMatrix t * matH =
      cartanMatrix (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [
      matH,
      cartanMatrix,
      Matrix.mul_apply,
      Fin.sum_univ_two
    ]

/-- The Cartan flow rescales `τ` by `exp(2t)`. -/
theorem tauCoord_actCartan
    (t : ℝ)
    (p q : ℂ)
    (hq : q ≠ 0) :
    tauCoord (actCartan t (p, q)) =
      (Real.exp (2 * t) : ℂ) *
        tauCoord (p, q) := by
  have hExpNeg :
      (Real.exp (-t) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (-t)

  have hScaleR :
      Real.exp t =
        Real.exp (2 * t) * Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring

  have hScaleC :
      (Real.exp t : ℂ) =
        (Real.exp (2 * t) : ℂ) *
          (Real.exp (-t) : ℂ) := by
    exact_mod_cast hScaleR

  change
    ((Real.exp t : ℂ) * p) /
        ((Real.exp (-t) : ℂ) * q) =
      (Real.exp (2 * t) : ℂ) * (p / q)

  field_simp [hq, hExpNeg]
  rw [hScaleC]
  ring_nf

/-! ## 4. Existing native Cayley critical-circle theorem -/

/-- The critical line is exactly the unit-circle locus of
`τ = s/(1-s)`. -/
theorem criticalLine_iff_tau_normSq_one (s : ℂ) :
    s.re = (1 / 2 : ℝ) ↔
      Complex.normSq
          (tauCoord (homogeneousPsi s)) =
        1 := by
  change
    OnCriticalLine s ↔
      OnLeeYangCircle (cayleyToFugacity s)
  exact criticalLine_iff_cayley_unitCircle s

/-- Standard critical-line point. -/
def criticalPoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * (t : ℂ)

@[simp]
theorem criticalPoint_re (t : ℝ) :
    (criticalPoint t).re = (1 / 2 : ℝ) := by
  simp [criticalPoint]

@[simp]
theorem criticalPoint_im (t : ℝ) :
    (criticalPoint t).im = t := by
  simp [criticalPoint]

/-- Every explicitly supplied critical-line point maps to the unit circle. -/
theorem tauCoord_criticalPoint_normSq (t : ℝ) :
    Complex.normSq
        (tauCoord
          (homogeneousPsi (criticalPoint t))) =
      1 := by
  exact
    (criticalLine_iff_tau_normSq_one
      (criticalPoint t)).mp
      (criticalPoint_re t)

/-! ## 5. Completed-Xi homogeneous readout -/

/-- A function on the affine spectral plane read through homogeneous
coordinates. -/
def xiHomogeneous
    (xi : ℂ → ℂ)
    (v : HomogeneousPair) :
    ℂ :=
  xi (projectiveS v)

@[simp]
theorem xiHomogeneous_homogeneousPsi
    (xi : ℂ → ℂ)
    (s : ℂ) :
    xiHomogeneous xi (homogeneousPsi s) =
      xi s := by
  simp [xiHomogeneous]

/-- Homogeneous readout is invariant under nonzero rescaling. -/
theorem xiHomogeneous_scalePair
    (xi : ℂ → ℂ)
    (c : ℂ)
    (hc : c ≠ 0)
    (v : HomogeneousPair) :
    xiHomogeneous xi (scalePair c v) =
      xiHomogeneous xi v := by
  unfold xiHomogeneous
  rw [projectiveS_scalePair c hc v]

/-- A supplied completed-Xi functional equation becomes invariance under
homogeneous Weyl swap on the normalized lift `Ψ(s)`. -/
theorem xiHomogeneous_swap_invariant
    (xi : ℂ → ℂ)
    (hxi : ∀ s : ℂ, xi (1 - s) = xi s)
    (s : ℂ) :
    xiHomogeneous xi
        (homogeneousSwap (homogeneousPsi s)) =
      xiHomogeneous xi (homogeneousPsi s) := by
  rw [homogeneousSwap_homogeneousPsi]
  simp [xiHomogeneous, hxi]

/-- A zero and its functional-reflection partner have the same homogeneous
completed-Xi readout. -/
theorem xiHomogeneous_zero_reflection
    (xi : ℂ → ℂ)
    (hxi : ∀ s : ℂ, xi (1 - s) = xi s)
    {s : ℂ}
    (hs : xi s = 0) :
    xiHomogeneous xi
        (homogeneousPsi (1 - s)) =
      0 := by
  simp [xiHomogeneous, hxi, hs]

/-! ## 6. Existing real doubled Hestenes embedding -/

section Hestenes

variable {E : Type}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]
variable [CompleteSpace E]

local notation "H₂" =>
  DoubledSpace E

local notation "EndH" =>
  H₂ →L[ℝ] H₂

/-- Centered spectral coordinate embedded into the real doubled Hestenes
endomorphism algebra. -/
def centeredHestenesCoordinate
    (s : ℂ) :
    EndH :=
  hestenesScalar (E := E)
    (s - (1 / 2 : ℂ))

@[simp]
theorem centeredHestenesCoordinate_half :
    centeredHestenesCoordinate
        (E := E) (1 / 2 : ℂ) =
      0 := by
  simp [centeredHestenesCoordinate]

/-- Functional reflection negates the centered coordinate before Hestenes
embedding. -/
theorem centeredHestenesCoordinate_functionalReflection
    (s : ℂ) :
    centeredHestenesCoordinate
        (E := E) (1 - s) =
      hestenesScalar (E := E)
        (-(s - (1 / 2 : ℂ))) := by
  unfold centeredHestenesCoordinate
  congr 1
  ring

/-- Modular reflection implements complex conjugation on the centered
Hestenes coordinate. -/
theorem modular_j_conjugates_centeredHestenesCoordinate
    (s : ℂ) :
    modular_j (E := E) *
          centeredHestenesCoordinate
            (E := E) s *
          modular_j (E := E) =
      hestenesScalar (E := E)
        (star (s - (1 / 2 : ℂ))) := by
  exact
    modular_j_conjugates_hestenesScalar
      (E := E)
      (s - (1 / 2 : ℂ))

/-- Equivalent readout with conjugation applied before centering. -/
theorem modular_j_conjugates_centeredHestenesCoordinate_eq
    (s : ℂ) :
    modular_j (E := E) *
          centeredHestenesCoordinate
            (E := E) s *
          modular_j (E := E) =
      centeredHestenesCoordinate
        (E := E) (star s) := by
  simpa [centeredHestenesCoordinate] using
    modular_j_conjugates_hestenesScalar
      (E := E)
      (s - (1 / 2 : ℂ))

end Hestenes

/-! ## 7. Universal-cover logarithmic cylinder and Klein glide -/

/-- Real universal-cover coordinates `W = ρ + Kθ`.

No global complex logarithm is chosen. -/
structure LogCylinderCoordinate where
  rho : ℝ
  theta : ℝ
  deriving DecidableEq

namespace LogCylinderCoordinate

@[ext]
theorem ext
    {x y : LogCylinderCoordinate}
    (hrho : x.rho = y.rho)
    (htheta : x.theta = y.theta) :
    x = y := by
  cases x
  cases y
  simp_all

/-- Translation along the angular/deck direction. -/
def deckTranslation
    (L : ℝ)
    (x : LogCylinderCoordinate) :
    LogCylinderCoordinate :=
  ⟨x.rho, x.theta + L⟩

/-- Translation in the transverse Cartan/radial direction. -/
def transverseTranslation
    (a : ℝ)
    (x : LogCylinderCoordinate) :
    LogCylinderCoordinate :=
  ⟨x.rho + a, x.theta⟩

/-- Antiunitary critical mirror on the logarithmic cylinder. -/
def radialMirror
    (x : LogCylinderCoordinate) :
    LogCylinderCoordinate :=
  ⟨-x.rho, x.theta⟩

/-- Klein glide:
radial reflection followed by a half-period angular shift. -/
def kleinGlide
    (L : ℝ)
    (x : LogCylinderCoordinate) :
    LogCylinderCoordinate :=
  ⟨-x.rho, x.theta + L / 2⟩

/-- Critical seam/equator of the logarithmic cylinder. -/
def OnSeam
    (x : LogCylinderCoordinate) :
    Prop :=
  x.rho = 0

@[simp]
theorem deckTranslation_zero
    (x : LogCylinderCoordinate) :
    deckTranslation 0 x = x := by
  ext <;>
    simp [deckTranslation]

theorem deckTranslation_add
    (L₁ L₂ : ℝ)
    (x : LogCylinderCoordinate) :
    deckTranslation L₁
        (deckTranslation L₂ x) =
      deckTranslation (L₁ + L₂) x := by
  ext <;>
    simp [deckTranslation];
    ring

@[simp]
theorem radialMirror_involutive :
    Function.Involutive radialMirror := by
  intro x
  ext <;>
    simp [radialMirror]

/-- The critical seam is exactly the fixed locus of the radial mirror. -/
theorem radialMirror_fixed_iff_OnSeam
    (x : LogCylinderCoordinate) :
    radialMirror x = x ↔
      OnSeam x := by
  constructor
  · intro h
    have hrho :=
      congrArg LogCylinderCoordinate.rho h
    simp [radialMirror, OnSeam] at hrho ⊢
    linarith
  · intro h
    ext
    · simp [radialMirror, OnSeam] at h ⊢
      linarith
    · simp [radialMirror]

/-- Two Klein glides equal one complete deck translation. -/
theorem kleinGlide_sq
    (L : ℝ)
    (x : LogCylinderCoordinate) :
    kleinGlide L (kleinGlide L x) =
      deckTranslation L x := by
  ext <;>
    simp [kleinGlide, deckTranslation];
    ring

/-- The Klein glide commutes with translation along its glide axis. -/
theorem kleinGlide_deckTranslation
    (L a : ℝ)
    (x : LogCylinderCoordinate) :
    kleinGlide L
        (deckTranslation a x) =
      deckTranslation a
        (kleinGlide L x) := by
  ext <;>
    simp [kleinGlide, deckTranslation];
    ring

/-- The Klein glide reverses the transverse translation direction:
`G Bₐ = B₋ₐ G`. -/
theorem kleinGlide_transverseTranslation
    (L a : ℝ)
    (x : LogCylinderCoordinate) :
    kleinGlide L
        (transverseTranslation a x) =
      transverseTranslation (-a)
        (kleinGlide L x) := by
  ext <;>
    simp [
      kleinGlide,
      transverseTranslation
    ];
    ring

/-- The Klein glide preserves the critical seam setwise. -/
theorem kleinGlide_preserves_OnSeam
    {L : ℝ}
    {x : LogCylinderCoordinate}
    (hx : OnSeam x) :
    OnSeam (kleinGlide L x) := by
  change -x.rho = 0
  rw [hx]
  simp

/-- On the seam, the Klein glide is exactly a half-period translation. -/
theorem kleinGlide_of_OnSeam
    {L : ℝ}
    {x : LogCylinderCoordinate}
    (hx : OnSeam x) :
    kleinGlide L x =
      deckTranslation (L / 2) x := by
  ext
  · change -x.rho = x.rho
    rw [hx]
    simp
  · simp [kleinGlide, deckTranslation]

end LogCylinderCoordinate

end InfoGeometry.Canonical.CompletedXiHestenesHomogeneousCoordinates

end
