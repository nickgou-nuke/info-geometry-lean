import InfoGeometry.Canonical.SpinConnection
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

open scoped InnerProductSpace Topology

namespace InfoGeometry.Canonical

open InfoGeometry.Krein
open InfoGeometry.Krein.NeutralSpace

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndN" => NeutralSpace E →L[ℝ] NeutralSpace E

/-!
# Infinitesimal Transport via Lie Derivative
-/

section ExplicitExponentialTransport

/-- Generic finite exponential conjugation transport in a normed algebra. -/
noncomputable def expTransport
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X A₀ : A) (t : ℝ) : A :=
  (NormedSpace.exp (t • X) * A₀) * NormedSpace.exp (t • (-X))

/-- Derivative of `t ↦ exp (t • X)` at `t = 0`. -/
lemma hasDerivAt_exp_smul_zero
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
  simpa [zero_smul, NormedSpace.exp_zero] using
    (hasDerivAt_exp_smul_const X (0 : ℝ))

/-- Derivative of `t ↦ exp (t • (-X))` at `t = 0`. -/
lemma hasDerivAt_exp_neg_smul_zero
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (-X))) (-X) 0 := by
  simpa [zero_smul, NormedSpace.exp_zero] using
    (hasDerivAt_exp_smul_const (-X) (0 : ℝ))

/-- Generic `HasDerivAt` commutator law for exponential conjugation. -/
lemma hasDerivAt_expTransport_at_zero
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X A₀ : A) :
    HasDerivAt (fun t => expTransport X A₀ t) ⁅X, A₀⁆ 0 := by
  let f : ℝ → A := fun t => NormedSpace.exp (t • X) * A₀
  let g : ℝ → A := fun t => NormedSpace.exp (t • (-X))
  have hfExp : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 :=
    hasDerivAt_exp_smul_zero X
  have hgExp : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (-X))) (-X) 0 :=
    hasDerivAt_exp_neg_smul_zero X
  have hf : HasDerivAt f (X * A₀) 0 := by
    simpa [f] using hfExp.mul_const A₀
  have hg : HasDerivAt g (-X) 0 := by
    simpa [g] using hgExp
  have hfg : HasDerivAt (fun t => f t * g t)
      (((X * A₀) * g 0) + f 0 * (-X)) 0 := by
    exact hf.mul hg
  have hmain : HasDerivAt (fun t => expTransport X A₀ t)
      (((X * A₀) * g 0) + f 0 * (-X)) 0 := by
    simpa only [f, g, expTransport] using hfg
  have hderiv : (((X * A₀) * g 0) + f 0 * (-X)) = ⁅X, A₀⁆ := by
    change ((X * A₀) * (NormedSpace.exp ((0 : ℝ) • (-X)))
        + (NormedSpace.exp ((0 : ℝ) • X) * A₀) * (-X)) = ⁅X, A₀⁆
    rw [zero_smul, NormedSpace.exp_zero, zero_smul, NormedSpace.exp_zero]
    rw [Ring.lie_def, sub_eq_add_neg]
    simp
  exact hderiv ▸ hmain

/-- Generic `HasDerivAt` commutator transport law for exponential conjugation at any `t`. -/
lemma hasDerivAt_expTransport
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X A₀ : A) (t : ℝ) :
    HasDerivAt (fun s => expTransport X A₀ s) (expTransport X ⁅X, A₀⁆ t) t := by
  let f : ℝ → A := fun s => NormedSpace.exp (s • X) * A₀
  let g : ℝ → A := fun s => NormedSpace.exp (s • (-X))
  have hfExp : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X))
      (NormedSpace.exp (t • X) * X) t := by
    simpa using (hasDerivAt_exp_smul_const X t)
  have hgExp : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (-X)))
      ((-X) * NormedSpace.exp (t • (-X))) t := by
    simpa using (hasDerivAt_exp_smul_const' (-X) t)
  have hf : HasDerivAt f (((NormedSpace.exp (t • X) * X) * A₀)) t := by
    simpa [f] using hfExp.mul_const A₀
  have hg : HasDerivAt g ((-X) * NormedSpace.exp (t • (-X))) t := by
    simpa [g] using hgExp
  have hfg : HasDerivAt (fun s => f s * g s)
      ((((NormedSpace.exp (t • X) * X) * A₀) * g t)
        + f t * ((-X) * NormedSpace.exp (t • (-X)))) t := by
    exact hf.mul hg
  have hmain : HasDerivAt (fun s => expTransport X A₀ s)
      ((((NormedSpace.exp (t • X) * X) * A₀) * g t)
        + f t * ((-X) * NormedSpace.exp (t • (-X)))) t := by
    simpa only [f, g, expTransport] using hfg
  have hderiv :
      ((((NormedSpace.exp (t • X) * X) * A₀) * g t)
        + f t * ((-X) * NormedSpace.exp (t • (-X))))
        = expTransport X ⁅X, A₀⁆ t := by
    unfold f g expTransport
    rw [Ring.lie_def, sub_eq_add_neg]
    simp [mul_assoc, left_distrib, right_distrib]
  exact hderiv ▸ hmain

/-- Generic derivative form of exponential conjugation at any `t`. -/
theorem deriv_expTransport
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X A₀ : A) (t : ℝ) :
    deriv (fun s => expTransport X A₀ s) t = expTransport X ⁅X, A₀⁆ t := by
  exact (hasDerivAt_expTransport X A₀ t).deriv

/-- Generic derivative form of exponential conjugation at `t = 0`. -/
theorem deriv_expTransport_at_zero
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X A₀ : A) :
    deriv (fun t => expTransport X A₀ t) 0 = ⁅X, A₀⁆ := by
  exact (hasDerivAt_expTransport_at_zero X A₀).deriv

/-- If the generator commutes with the seed operator, the infinitesimal transport vanishes. -/
theorem deriv_expTransport_at_zero_eq_zero_of_commute
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X A₀ : A) (hComm : Commute X A₀) :
    deriv (fun t => expTransport X A₀ t) 0 = 0 := by
  rw [deriv_expTransport_at_zero]
  simp [Ring.lie_def, hComm.eq]

@[simp] theorem expTransport_add_seed
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X A₁ A₂ : A) (t : ℝ) :
    expTransport X (A₁ + A₂) t = expTransport X A₁ t + expTransport X A₂ t := by
  unfold expTransport
  simp [mul_assoc, mul_add, add_mul]

/-- The exponential conjugation transport is multiplicative in its seed. -/
theorem expTransport_mul_seed
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X A₁ A₂ : A) (t : ℝ) :
    expTransport X (A₁ * A₂) t =
      expTransport X A₁ t * expTransport X A₂ t := by
  have hScaledNeg : Commute (t • (-X)) (t • X) := by
    rw [smul_neg]
    exact (Commute.refl (t • X)).neg_left
  have hInv :
      NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X) = 1 := by
    rw [← NormedSpace.exp_add_of_commute hScaledNeg]
    simp
  unfold expTransport
  calc
    (NormedSpace.exp (t • X) * (A₁ * A₂)) * NormedSpace.exp (t • (-X)) =
        NormedSpace.exp (t • X) *
          (A₁ * (A₂ * NormedSpace.exp (t • (-X)))) := by
            simp only [mul_assoc]
    _ = (NormedSpace.exp (t • X) * A₁) *
          (NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X)) *
          (A₂ * NormedSpace.exp (t • (-X))) := by
            rw [hInv]
            simp only [mul_one, mul_assoc]
    _ = ((NormedSpace.exp (t • X) * A₁) * NormedSpace.exp (t • (-X))) *
          ((NormedSpace.exp (t • X) * A₂) * NormedSpace.exp (t • (-X))) := by
            simp only [mul_assoc]

/-- Exponential conjugation preserves the associative-algebra Lie bracket. -/
theorem expTransport_lie
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X A₁ A₂ : A) (t : ℝ) :
    expTransport X ⁅A₁, A₂⁆ t =
      ⁅expTransport X A₁ t, expTransport X A₂ t⁆ := by
  have hScaledNeg : Commute (t • (-X)) (t • X) := by
    rw [smul_neg]
    exact (Commute.refl (t • X)).neg_left
  have hInv :
      NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X) = 1 := by
    rw [← NormedSpace.exp_add_of_commute hScaledNeg]
    simp
  unfold expTransport
  rw [Ring.lie_def, Ring.lie_def]
  calc
    (NormedSpace.exp (t • X) * (A₁ * A₂ - A₂ * A₁)) *
          NormedSpace.exp (t • (-X)) =
        (NormedSpace.exp (t • X) * A₁) *
            (A₂ * NormedSpace.exp (t • (-X))) -
          (NormedSpace.exp (t • X) * A₂) *
            (A₁ * NormedSpace.exp (t • (-X))) := by
              simp only [sub_mul, mul_sub, mul_assoc]
    _ = ((NormedSpace.exp (t • X) * A₁) *
            (NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X))) *
          (A₂ * NormedSpace.exp (t • (-X))) -
        ((NormedSpace.exp (t • X) * A₂) *
            (NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X))) *
          (A₁ * NormedSpace.exp (t • (-X))) := by
            rw [hInv]
            simp only [mul_one]
    _ = ((NormedSpace.exp (t • X) * A₁) *
            NormedSpace.exp (t • (-X))) *
          ((NormedSpace.exp (t • X) * A₂) *
            NormedSpace.exp (t • (-X))) -
        ((NormedSpace.exp (t • X) * A₂) *
            NormedSpace.exp (t • (-X))) *
          ((NormedSpace.exp (t • X) * A₁) *
            NormedSpace.exp (t • (-X))) := by
            simp only [mul_assoc]

/-- Exponential conjugation fixes the multiplicative identity. -/
@[simp] theorem expTransport_one_seed
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X : A) (t : ℝ) :
    expTransport X 1 t = 1 := by
  have hScaledNeg : Commute (t • X) (t • (-X)) := by
    rw [smul_neg]
    exact (Commute.refl (t • X)).neg_right
  unfold expTransport
  rw [mul_one, ← NormedSpace.exp_add_of_commute hScaledNeg]
  simp

/-- Exponential conjugation transports the zero seed to zero. -/
@[simp] theorem expTransport_zero_seed
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X : A) (t : ℝ) :
    expTransport X 0 t = 0 := by
  unfold expTransport
  simp

/-- Exponential conjugation is scalar-linear in its seed. -/
theorem expTransport_smul_seed
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X A₀ : A) (r : ℝ) (t : ℝ) :
    expTransport X (r • A₀) t = r • expTransport X A₀ t := by
  unfold expTransport
  simp only [smul_mul_assoc, mul_smul_comm]

/-- The finite exponential transport packaged as an `ℝ`-linear map. -/
noncomputable def expTransportLinear
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X : A) (t : ℝ) : A →ₗ[ℝ] A where
  toFun A₀ := expTransport X A₀ t
  map_add' A₁ A₂ := expTransport_add_seed X A₁ A₂ t
  map_smul' r A₀ := expTransport_smul_seed X A₀ r t

/-- The finite exponential transport packaged as a unital algebra homomorphism. -/
noncomputable def expTransportAlgHom
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X : A) (t : ℝ) : A →ₐ[ℝ] A :=
  AlgHom.ofLinearMap (expTransportLinear X t)
    (expTransport_one_seed X t)
    (fun A₁ A₂ => expTransport_mul_seed X A₁ A₂ t)

/-- Exponential conjugation preserves all natural powers of an observable. -/
theorem expTransport_pow_seed
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X A₀ : A) (n : ℕ) (t : ℝ) :
    expTransport X (A₀ ^ n) t = (expTransport X A₀ t) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, expTransport_mul_seed, ih, pow_succ]

/-- Exponential conjugation satisfies the additive-time composition law. -/
theorem expTransport_add_time
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X A₀ : A) (s t : ℝ) :
    expTransport X A₀ (s + t) =
      expTransport X (expTransport X A₀ t) s := by
  have hcomm : Commute (s • X) (t • X) :=
    ((Commute.refl X).smul_left s).smul_right t
  have hcommNeg : Commute (t • (-X)) (s • (-X)) :=
    ((Commute.refl (-X)).smul_left t).smul_right s
  have hneg : (s + t) • (-X) = t • (-X) + s • (-X) := by
    module
  unfold expTransport
  rw [add_smul, NormedSpace.exp_add_of_commute hcomm, hneg,
    NormedSpace.exp_add_of_commute hcommNeg]
  noncomm_ring

/-- Exponential conjugation at time zero is the identity on every seed. -/
@[simp] theorem expTransport_zero_time
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X A₀ : A) :
    expTransport X A₀ 0 = A₀ := by
  unfold expTransport
  simp

/-- Applying the inverse-time transport after the forward transport is the identity. -/
theorem expTransport_neg_left
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X A₀ : A) (t : ℝ) :
    expTransport X (expTransport X A₀ (-t)) t = A₀ := by
  rw [← expTransport_add_time X A₀ t (-t)]
  simp

/-- Applying the forward transport after the inverse-time transport is the identity. -/
theorem expTransport_neg_right
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X A₀ : A) (t : ℝ) :
    expTransport X (expTransport X A₀ t) (-t) = A₀ := by
  rw [← expTransport_add_time X A₀ (-t) t]
  simp

/-- The finite exponential transport as an `ℝ`-linear equivalence. -/
noncomputable def expTransportLinearEquiv
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X : A) (t : ℝ) : A ≃ₗ[ℝ] A :=
  LinearEquiv.ofBijective (expTransportLinear X t) (by
    constructor
    · intro A₁ A₂ h
      change expTransport X A₁ t = expTransport X A₂ t at h
      have h' := congrArg (fun B => expTransport X B (-t)) h
      dsimp at h'
      rw [expTransport_neg_right X A₁ t, expTransport_neg_right X A₂ t] at h'
      exact h'
    · intro A₀
      refine ⟨expTransport X A₀ (-t), ?_⟩
      change expTransport X (expTransport X A₀ (-t)) t = A₀
      exact expTransport_neg_left X A₀ t)

/-- The finite exponential transport as an `ℝ`-algebra equivalence. -/
noncomputable def expTransportAlgEquiv
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X : A) (t : ℝ) : A ≃ₐ[ℝ] A :=
  AlgEquiv.ofLinearEquiv (expTransportLinearEquiv X t)
    (expTransport_one_seed X t)
    (fun A₁ A₂ => expTransport_mul_seed X A₁ A₂ t)

/-- The finite transport equivalences form an additive one-parameter group. -/
theorem expTransportAlgEquiv_add
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X : A) (s t : ℝ) :
    expTransportAlgEquiv X (s + t) =
      (expTransportAlgEquiv X t).trans (expTransportAlgEquiv X s) := by
  ext A₀
  exact expTransport_add_time X A₀ s t

/-- The zero-time transport equivalence is the identity equivalence. -/
theorem expTransportAlgEquiv_zero
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X : A) :
    expTransportAlgEquiv X 0 = AlgEquiv.refl ℝ A := by
  ext A₀
  simp

/-- The negative-time transport is the inverse equivalence. -/
theorem expTransportAlgEquiv_neg_trans
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A]
      [CompleteSpace A]
    (X : A) (t : ℝ) :
    (expTransportAlgEquiv X (-t)).trans (expTransportAlgEquiv X t) =
      AlgEquiv.refl ℝ A := by
  ext A₀
  exact expTransport_neg_left X A₀ t

/--
Exact exponential conjugation fixes a seed that commutes with the generator.

This is the finite-time version of `deriv_expTransport_at_zero_eq_zero_of_commute`;
it turns a commutation property into a constructive transport-fixedness proof.
-/
theorem expTransport_eq_self_of_commute
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X A₀ : A) (t : ℝ) (hComm : Commute A₀ X) :
    expTransport X A₀ t = A₀ := by
  have hCommScaled : Commute A₀ (t • X) := by
    simpa using hComm.smul_right t
  have hCommExp : Commute A₀ (NormedSpace.exp (t • X)) := by
    simpa using hCommScaled.exp_right
  have hScaledNeg : Commute (t • X) (t • (-X)) := by
    rw [smul_neg]
    exact (Commute.refl (t • X)).neg_right
  unfold expTransport
  calc
    (NormedSpace.exp (t • X) * A₀) * NormedSpace.exp (t • (-X))
        = (A₀ * NormedSpace.exp (t • X)) * NormedSpace.exp (t • (-X)) := by
            rw [hCommExp.eq]
    _ = A₀ * (NormedSpace.exp (t • X) * NormedSpace.exp (t • (-X))) := by
          rw [mul_assoc]
    _ = A₀ * NormedSpace.exp (t • X + t • (-X)) := by
          rw [← NormedSpace.exp_add_of_commute hScaledNeg]
    _ = A₀ * 1 := by
          simp
    _ = A₀ := by
          simp

/-- Explicit finite exponential conjugation transport on `EndN`. -/
noncomputable def expTransportEnd (X A : EndN) (t : ℝ) : EndN :=
  expTransport X A t

/-- Main `HasDerivAt` transport law for exponential conjugation on `EndN`. -/
lemma hasDerivAt_expTransportEnd_at_zero
    (X A : EndN) :
    HasDerivAt (fun t => expTransportEnd X A t) ⁅X, A⁆ 0 := by
  simpa [expTransportEnd] using hasDerivAt_expTransport_at_zero X A

/-- Lie derivative of exponential transport at `t = 0` equals the commutator. -/
theorem deriv_expTransportEnd_at_zero
    (X A : EndN) :
    deriv (fun t => expTransportEnd X A t) 0 = ⁅X, A⁆ := by
  simpa [expTransportEnd] using deriv_expTransport_at_zero X A

/-- Commuting generators give infinitesimal stationarity for `EndN` transport. -/
theorem deriv_expTransportEnd_at_zero_eq_zero_of_commute
    (X A : EndN) (hComm : Commute X A) :
    deriv (fun t => expTransportEnd X A t) 0 = 0 := by
  rw [deriv_expTransportEnd_at_zero]
  simp [Ring.lie_def, hComm.eq]

end ExplicitExponentialTransport

section HestenesLanguage

/--
Typed Hestenes axis on doubled real space.
`K` plays the role of the imaginary unit via `K² = -1`, with explicit
skewness and orthogonality constraints encoded as geometric laws.
-/
structure KAxis (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  K : NeutralSpace E →L[ℝ] NeutralSpace E
  square_neg_one : K * K = -(1 : NeutralSpace E →L[ℝ] NeutralSpace E)
  skew : ∀ u v : NeutralSpace E, ⟪K u, v⟫_ℝ = -⟪u, K v⟫_ℝ
  orthogonal : ∀ u v : NeutralSpace E, ⟪K u, K v⟫_ℝ = ⟪u, v⟫_ℝ

/--
Modular CPT chiral atom on doubled space:
`{1, ε, J, Jε}` as a real operator-algebra presentation.
-/
structure ModularCPTChiralAtom (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  eps : NeutralSpace E →L[ℝ] NeutralSpace E
  J : NeutralSpace E →L[ℝ] NeutralSpace E
  eps_sq : eps * eps = (1 : NeutralSpace E →L[ℝ] NeutralSpace E)
  J_sq : J * J = (1 : NeutralSpace E →L[ℝ] NeutralSpace E)
  anticomm : J * eps = -(eps * J)
  K_sq_neg_one : (J * eps) * (J * eps) = -(1 : NeutralSpace E →L[ℝ] NeutralSpace E)
  K_skew : ∀ u v : NeutralSpace E, ⟪(J * eps) u, v⟫_ℝ = -⟪u, (J * eps) v⟫_ℝ
  K_orthogonal : ∀ u v : NeutralSpace E, ⟪(J * eps) u, (J * eps) v⟫_ℝ = ⟪u, v⟫_ℝ

namespace ModularCPTChiralAtom

/-- The modular axis `K := Jε`. -/
noncomputable def K
    (A : ModularCPTChiralAtom E) : EndN :=
  A.J * A.eps

lemma K_sq_neg_one_eq
    (A : ModularCPTChiralAtom E) :
    A.K * A.K = -(1 : EndN) := by
  unfold K
  simpa using A.K_sq_neg_one

/-- Canonical typed `K`-axis extracted from the modular CPT atom. -/
noncomputable def toKAxis
    (A : ModularCPTChiralAtom E) : KAxis E where
  K := A.K
  square_neg_one := A.K_sq_neg_one_eq
  skew := by
    intro u v
    simpa [K] using A.K_skew u v
  orthogonal := by
    intro u v
    simpa [K] using A.K_orthogonal u v

end ModularCPTChiralAtom

/--
Axis-linear endomorphisms commute with the Hestenes axis `K`.
This is the real doubled-space replacement of complex-linearity.
-/
def IsAxisLinear (A : KAxis E) (T : EndN) : Prop :=
  T * A.K = A.K * T

/--
Axis-antilinear endomorphisms anticommute with the Hestenes axis `K`.
This is the real doubled-space replacement of complex-antilinearity.
-/
def IsAxisAntilinear (A : KAxis E) (T : EndN) : Prop :=
  T * A.K = -(A.K * T)

/--
Axis conjugation by `K`: `T ↦ K T K`.
For `K² = -1`, this is the involutive splitter used for linear/antilinear parts.
-/
noncomputable def axisConjugate (A : KAxis E) (T : EndN) : EndN :=
  A.K * T * A.K

/-- Canonical axis-linear component of `T` relative to `K`. -/
noncomputable def axisLinearPart (A : KAxis E) (T : EndN) : EndN :=
  (1 / 2 : ℝ) • (T - axisConjugate A T)

/-- Canonical axis-antilinear component of `T` relative to `K`. -/
noncomputable def axisAntilinearPart (A : KAxis E) (T : EndN) : EndN :=
  (1 / 2 : ℝ) • (T + axisConjugate A T)

lemma axisConjugate_eq_neg_of_isAxisLinear
    (A : KAxis E) (T : EndN) (hLin : IsAxisLinear A T) :
    axisConjugate A T = -T := by
  apply ContinuousLinearMap.ext
  intro x
  have hCommAtX : T (A.K x) = A.K (T x) := by
    have hEq := congrArg (fun F : EndN => F x) hLin
    simpa [IsAxisLinear, ContinuousLinearMap.mul_apply] using hEq
  have hK2AtTx : A.K (A.K (T x)) = -T x := by
    have hSq := congrArg (fun F : EndN => F (T x)) A.square_neg_one
    simpa [ContinuousLinearMap.mul_apply] using hSq
  calc
    axisConjugate A T x = A.K (T (A.K x)) := by
      simp [axisConjugate, ContinuousLinearMap.mul_apply]
    _ = A.K (A.K (T x)) := by rw [hCommAtX]
    _ = -T x := hK2AtTx
    _ = (-T) x := by simp

lemma axisConjugate_eq_of_isAxisAntilinear
    (A : KAxis E) (T : EndN) (hAnti : IsAxisAntilinear A T) :
    axisConjugate A T = T := by
  apply ContinuousLinearMap.ext
  intro x
  have hAntiAtX : T (A.K x) = -(A.K (T x)) := by
    have hEq := congrArg (fun F : EndN => F x) hAnti
    simpa [IsAxisAntilinear, ContinuousLinearMap.mul_apply] using hEq
  have hK2AtTx : A.K (A.K (T x)) = -T x := by
    have hSq := congrArg (fun F : EndN => F (T x)) A.square_neg_one
    simpa [ContinuousLinearMap.mul_apply] using hSq
  calc
    axisConjugate A T x = A.K (T (A.K x)) := by
      simp [axisConjugate, ContinuousLinearMap.mul_apply]
    _ = A.K (-(A.K (T x))) := by rw [hAntiAtX]
    _ = -(A.K (A.K (T x))) := by simp
    _ = -(-T x) := by rw [hK2AtTx]
    _ = T x := by simp

lemma axisLinearPart_eq_self_of_isAxisLinear
    (A : KAxis E) (T : EndN) (hLin : IsAxisLinear A T) :
    axisLinearPart A T = T := by
  unfold axisLinearPart
  rw [axisConjugate_eq_neg_of_isAxisLinear A T hLin]
  calc
    (1 / 2 : ℝ) • (T - -T) = (1 / 2 : ℝ) • (T + T) := by rw [sub_eq_add_neg, neg_neg]
    _ = (1 / 2 : ℝ) • ((2 : ℝ) • T) := by rw [← two_smul ℝ T]
    _ = (((1 / 2 : ℝ) * (2 : ℝ)) : ℝ) • T := by simp [smul_smul]
    _ = (1 : ℝ) • T := by norm_num
    _ = T := by simp

lemma axisAntilinearPart_eq_zero_of_isAxisLinear
    (A : KAxis E) (T : EndN) (hLin : IsAxisLinear A T) :
    axisAntilinearPart A T = 0 := by
  unfold axisAntilinearPart
  rw [axisConjugate_eq_neg_of_isAxisLinear A T hLin]
  simp

lemma axisLinearPart_eq_zero_of_isAxisAntilinear
    (A : KAxis E) (T : EndN) (hAnti : IsAxisAntilinear A T) :
    axisLinearPart A T = 0 := by
  unfold axisLinearPart
  rw [axisConjugate_eq_of_isAxisAntilinear A T hAnti]
  simp

lemma axisAntilinearPart_eq_self_of_isAxisAntilinear
    (A : KAxis E) (T : EndN) (hAnti : IsAxisAntilinear A T) :
    axisAntilinearPart A T = T := by
  unfold axisAntilinearPart
  rw [axisConjugate_eq_of_isAxisAntilinear A T hAnti]
  calc
    (1 / 2 : ℝ) • (T + T) = (1 / 2 : ℝ) • ((2 : ℝ) • T) := by rw [← two_smul ℝ T]
    _ = (((1 / 2 : ℝ) * (2 : ℝ)) : ℝ) • T := by simp [smul_smul]
    _ = (1 : ℝ) • T := by norm_num
    _ = T := by simp

lemma axisLinearPart_add_axisAntilinearPart
    (A : KAxis E) (T : EndN) :
    axisLinearPart A T + axisAntilinearPart A T = T := by
  unfold axisLinearPart axisAntilinearPart
  calc
    (1 / 2 : ℝ) • (T - axisConjugate A T)
        + (1 / 2 : ℝ) • (T + axisConjugate A T)
      = ((1 / 2 : ℝ) • T - (1 / 2 : ℝ) • axisConjugate A T)
          + ((1 / 2 : ℝ) • T + (1 / 2 : ℝ) • axisConjugate A T) := by
            simp [smul_sub, smul_add]
    _ = (1 / 2 : ℝ) • T + (1 / 2 : ℝ) • T := by
          abel_nf
    _ = (2 : ℝ) • ((1 / 2 : ℝ) • T) := by
          simpa [two_smul] using (two_smul ℝ ((1 / 2 : ℝ) • T)).symm
    _ = (((2 : ℝ) * (1 / 2 : ℝ)) : ℝ) • T := by
          simp [smul_smul]
    _ = (1 : ℝ) • T := by
          norm_num
    _ = T := by simp

/-- The canonical split specialized to the modular CPT atom axis `K = Jε`. -/
noncomputable abbrev modularAxisLinearPart
    (A : ModularCPTChiralAtom E) (T : EndN) : EndN :=
  axisLinearPart A.toKAxis T

/-- The canonical split specialized to the modular CPT atom axis `K = Jε`. -/
noncomputable abbrev modularAxisAntilinearPart
    (A : ModularCPTChiralAtom E) (T : EndN) : EndN :=
  axisAntilinearPart A.toKAxis T

lemma modularAxisLinearPart_add_modularAxisAntilinearPart
    (A : ModularCPTChiralAtom E) (T : EndN) :
    modularAxisLinearPart A T + modularAxisAntilinearPart A T = T := by
  simpa [modularAxisLinearPart, modularAxisAntilinearPart] using
    axisLinearPart_add_axisAntilinearPart A.toKAxis T

/--
Hestenes-style rotor generated by an operator axis `B`.
This is the operator-algebra replacement of scalar-complex phase evolution.
-/
noncomputable abbrev rotor (B : EndN) (t : ℝ) : EndN :=
  NormedSpace.exp (t • B)

/--
Hestenes sandwich transport `R A R⁻¹` in doubled-space operator form.
Here `R⁻¹` is represented by `exp (t • (-B))`.
-/
noncomputable abbrev hestenesTransport (B A : EndN) (t : ℝ) : EndN :=
  expTransportEnd B A t

/--
Complex-scalar replacement on doubled space:
`a + b i` is represented as `a • 1 + b • K`.
-/
noncomputable def complexLikeByAxis (K : EndN) (a b : ℝ) : EndN :=
  a • (1 : EndN) + b • K

/-- Complex-like encoding using a typed Hestenes axis. -/
noncomputable abbrev complexLike (A : KAxis E) (a b : ℝ) : EndN :=
  complexLikeByAxis A.K a b

theorem deriv_hestenesTransport_at_zero
    (B A : EndN) :
    deriv (fun t => hestenesTransport B A t) 0 = ⁅B, A⁆ := by
  simpa [hestenesTransport] using deriv_expTransportEnd_at_zero B A

/--
Hestenes-axis sanity theorem: if `K² = -1`, then the encoded unit imaginary
`complexLikeByAxis K 0 1` squares to `-1`.
-/
lemma complexLikeByAxis_i_sq
    (K : EndN)
    (hK : K * K = -(1 : EndN)) :
    complexLikeByAxis K 0 1 * complexLikeByAxis K 0 1 = -(1 : EndN) := by
  have h0 : ((0 : ℝ) • (1 : EndN)) = (0 : EndN) := by
    exact zero_smul ℝ (1 : EndN)
  have h1 : ((1 : ℝ) • K) = K := by
    exact one_smul ℝ K
  have h01 : complexLikeByAxis K 0 1 = K := by
    calc
      complexLikeByAxis K 0 1
          = ((0 : ℝ) • (1 : EndN)) + ((1 : ℝ) • K) := rfl
      _ = (0 : EndN) + K := by rw [h0, h1]
      _ = K := by simp
  calc
    complexLikeByAxis K 0 1 * complexLikeByAxis K 0 1
        = K * K := by simp [h01]
    _ = -(1 : EndN) := hK

/-- Typed-axis version of `i² = -1` for the Hestenes replacement. -/
lemma complexLike_i_sq
    (A : KAxis E) :
    complexLike A 0 1 * complexLike A 0 1 = -(1 : EndN) := by
  simpa [complexLike] using complexLikeByAxis_i_sq A.K A.square_neg_one

end HestenesLanguage

section DifferentiableSpinConnection

/-- Differentiable enhancement of a spin connection. -/
structure DifferentiableSpinConnection (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    extends SpinConnection E where
  U_differentiable :
    Differentiable ℝ (fun t => ((U t : HessianOrthogonalGroup E) :
      NeutralSpace E ≃L[ℝ] NeutralSpace E).toContinuousLinearMap)
  U_inv_differentiable :
    Differentiable ℝ (fun t => ((U t : HessianOrthogonalGroup E) :
      NeutralSpace E ≃L[ℝ] NeutralSpace E).symm.toContinuousLinearMap)

/-- Infinitesimal generator of transport at `t = 0`. -/
noncomputable def transportGenerator
    (S : DifferentiableSpinConnection E) : EndN :=
  deriv
    (fun t =>
      (((S.U t : HessianOrthogonalGroup E) :
        NeutralSpace E ≃L[ℝ] NeutralSpace E).toContinuousLinearMap))
    0

/-- Lie derivative of an endomorphism under conjugation transport. -/
noncomputable def lieDerivEnd
    (S : DifferentiableSpinConnection E) (A : EndN) : EndN :=
  deriv (fun t => transportEnd S.toSpinConnection t A) 0

/-- Exponential-flow bridge from spin transport to the commutator law. -/
theorem lieDerivEnd_eq_commutator_of_exp_flow
    (S : DifferentiableSpinConnection E)
    (X A : EndN)
    (hflow :
      ∀ t, transportEnd S.toSpinConnection t A = expTransportEnd X A t) :
    lieDerivEnd S A = ⁅X, A⁆ := by
  have h_eq :
      (fun t => transportEnd S.toSpinConnection t A)
        = (fun t => expTransportEnd X A t) := funext hflow
  rw [lieDerivEnd, h_eq]
  exact deriv_expTransportEnd_at_zero X A

/-- Exponential-flow transport is infinitesimally stationary in the commuting regime. -/
theorem lieDerivEnd_eq_zero_of_commute_exp_flow
    (S : DifferentiableSpinConnection E)
    (X A : EndN)
    (hflow :
      ∀ t, transportEnd S.toSpinConnection t A = expTransportEnd X A t)
    (hComm : Commute X A) :
    lieDerivEnd S A = 0 := by
  rw [lieDerivEnd_eq_commutator_of_exp_flow S X A hflow]
  simp [Ring.lie_def, hComm.eq]

/-- Under an exponential flow, `transportGenerator` recovers the generator `X`. -/
theorem transportGenerator_eq_of_exp_flow
    (S : DifferentiableSpinConnection E)
    (X : EndN)
    (hflow :
      ∀ t,
        (((S.U t : HessianOrthogonalGroup E) :
          NeutralSpace E ≃L[ℝ] NeutralSpace E).toContinuousLinearMap)
          = NormedSpace.exp (t • X)) :
    transportGenerator S = X := by
  have h_eq :
      (fun t =>
        (((S.U t : HessianOrthogonalGroup E) :
          NeutralSpace E ≃L[ℝ] NeutralSpace E).toContinuousLinearMap))
        = (fun t => NormedSpace.exp (t • X)) := funext hflow
  rw [transportGenerator, h_eq]
  exact (hasDerivAt_exp_smul_zero X).deriv

/-- Generator-form commutator law for spin-transport Lie derivatives. -/
theorem lieDerivEnd_eq_commutator_generator
    (S : DifferentiableSpinConnection E)
    (A : EndN)
    (hflow :
      ∀ t, transportEnd S.toSpinConnection t A =
        expTransportEnd (transportGenerator S) A t) :
    lieDerivEnd S A = ⁅transportGenerator S, A⁆ := by
  exact lieDerivEnd_eq_commutator_of_exp_flow S (transportGenerator S) A hflow

/-- Generator-form infinitesimal stationarity criterion in commuting regime. -/
theorem lieDerivEnd_eq_zero_of_commute_generator
    (S : DifferentiableSpinConnection E)
    (A : EndN)
    (hflow :
      ∀ t, transportEnd S.toSpinConnection t A =
        expTransportEnd (transportGenerator S) A t)
    (hComm : Commute (transportGenerator S) A) :
    lieDerivEnd S A = 0 := by
  exact lieDerivEnd_eq_zero_of_commute_exp_flow S (transportGenerator S) A hflow hComm

end DifferentiableSpinConnection

section MetricTransport

/-- Metric seed bilinear form induced by an operator. -/
noncomputable def metricOfOperator
    (A : EndN) : LinearMap.BilinForm ℝ (NeutralSpace E) :=
  LinearMap.mk₂ ℝ
    (fun u v => ⟪A u, v⟫_ℝ)
    (by
      intro u₁ u₂ v
      simp [map_add, inner_add_left])
    (by
      intro c u v
      simp [map_smul, real_inner_smul_left])
    (by
      intro u v₁ v₂
      simp [inner_add_right])
    (by
      intro c u v
      simp [real_inner_smul_right])

lemma metricOfOperator_zero :
    metricOfOperator (E := E) (0 : EndN) = 0 := by
  ext u v
  simp [metricOfOperator]

lemma metricOfOperator_add (A B : EndN) :
    metricOfOperator (E := E) (A + B)
      = metricOfOperator (E := E) A + metricOfOperator (E := E) B := by
  ext u v
  simp [metricOfOperator, inner_add_left]

/-- Lie derivative of the metric seed induced by operator transport. -/
noncomputable def lieDerivMetricOfOperator
    (S : DifferentiableSpinConnection E) (A : EndN) :
    LinearMap.BilinForm ℝ (NeutralSpace E) :=
  metricOfOperator (lieDerivEnd S A)

/-- Metric lift of the commutator formula under exponential transport. -/
theorem lieDerivMetric_eq_metricOfComm
    (S : DifferentiableSpinConnection E)
    (X A : EndN)
    (hflow :
      ∀ t, transportEnd S.toSpinConnection t A = expTransportEnd X A t) :
    lieDerivMetricOfOperator S A = metricOfOperator ⁅X, A⁆ := by
  rw [lieDerivMetricOfOperator, lieDerivEnd_eq_commutator_of_exp_flow S X A hflow]

/-- Commuting with `X` implies vanishing infinitesimal metric transport. -/
theorem lieDerivMetric_eq_zero_of_commute_exp_flow
    (S : DifferentiableSpinConnection E)
    (X A : EndN)
    (hflow :
      ∀ t, transportEnd S.toSpinConnection t A = expTransportEnd X A t)
    (hComm : ⁅X, A⁆ = 0) :
    lieDerivMetricOfOperator S A = 0 := by
  calc
    lieDerivMetricOfOperator S A = metricOfOperator ⁅X, A⁆ := by
      exact lieDerivMetric_eq_metricOfComm S X A hflow
    _ = metricOfOperator 0 := by rw [hComm]
    _ = 0 := metricOfOperator_zero

/-- Metric stationarity under exponential transport when generator and seed commute. -/
theorem lieDerivMetric_eq_zero_of_commute_exp_flow_of_commute
    (S : DifferentiableSpinConnection E)
    (X A : EndN)
    (hflow :
      ∀ t, transportEnd S.toSpinConnection t A = expTransportEnd X A t)
    (hComm : Commute X A) :
    lieDerivMetricOfOperator S A = 0 := by
  have hLie : ⁅X, A⁆ = 0 := by
    simp [Ring.lie_def, hComm.eq]
  exact lieDerivMetric_eq_zero_of_commute_exp_flow S X A hflow
    hLie

/-- Generator-form infinitesimal stationarity criterion for metric transport. -/
theorem lieDerivMetric_eq_zero_of_commute_generator
    (S : DifferentiableSpinConnection E)
    (A : EndN)
    (hflow :
      ∀ t, transportEnd S.toSpinConnection t A =
        expTransportEnd (transportGenerator S) A t)
    (hComm : ⁅transportGenerator S, A⁆ = 0) :
    lieDerivMetricOfOperator S A = 0 := by
  exact lieDerivMetric_eq_zero_of_commute_exp_flow S (transportGenerator S) A hflow hComm

/-- Generator-form metric stationarity criterion in commuting regime. -/
theorem lieDerivMetric_eq_zero_of_commute_generator_of_commute
    (S : DifferentiableSpinConnection E)
    (A : EndN)
    (hflow :
      ∀ t, transportEnd S.toSpinConnection t A =
        expTransportEnd (transportGenerator S) A t)
    (hComm : Commute (transportGenerator S) A) :
    lieDerivMetricOfOperator S A = 0 := by
  exact lieDerivMetric_eq_zero_of_commute_exp_flow_of_commute
    S (transportGenerator S) A hflow hComm

end MetricTransport

end InfoGeometry.Canonical
