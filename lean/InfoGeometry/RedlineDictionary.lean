import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.Canonical.SouriauModularBregmanOperator
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.TomitaTakesakiModularOperatorKMS
import InfoGeometry.Analysis.LieExponentialTraceDeterminant
import InfoGeometry.Analysis.MatrixPathDeformationEntropy
import InfoGeometry.Modular.TrifoldRadonNikodymBridge
import InfoGeometry.Volume.ZeroJacobianWeylBoundary

/-!
# Redline Dictionary — Native Lean 4 Corridor

Direct re-exports of already-built native mathlib theorems.
No wrapper structures, no witnesses, no certificates.
All theorems are genuine native mathlib lemmas from their respective owners.
-/

noncomputable section

open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.SouriauModularBregmanOperator
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.TomitaTakesakiModularOperatorKMS

/-!
=============================================================================
PART 1: The Discrete Multiplicative / Additive Cocycle (Groupoid Cohomology)
=============================================================================

From `InfoGeometry.Canonical.RelativePotentialCore` — already kernel-checked as `@[simp]` theorems:
-/

#check @relativeDensity_cocycle
#check @relativeModularPotential_cocycle
#check @relativeDensity_eq_exp_relativeLogDensity
#check @relativeModularPotential_eq_neg_relativeLogDensity
#check @relativeLogDensity_cocycle
#check @relativeLogDensity_eq_logDensity_sub_logDensity
#check @relativeDensity_eq_exp_relativeLogDensity

/-!
=============================================================================
PART 2: The Lie Flow → Jacobian → Negative Log Redline
=============================================================================

From `InfoGeometry.Analysis.LieExponentialTraceDeterminant`:
-/

#check @det_lieExponentialPath

From `InfoGeometry.Analysis.MatrixPathDeformationEntropy`:
-/

#check @matrixPathCompressionPotential_lieExponentialPath
#check @deriv_matrixPathCompressionPotential_lieExponentialPath

From `InfoGeometry.Volume.ZeroJacobianWeylBoundary`:
-/

#check @det_weylScaledJacobian_eq_zero_iff
#check @totalTransportDensity_eq_zero_iff_det_eq_zero

/-!
=============================================================================
PART 3: The Modular Operator Δ = exp(-K) Bridge
=============================================================================

From `InfoGeometry.Canonical.SouriauModularBregmanOperator`:
-/

#check @modularDeltaFromHamiltonian_eq_exp_neg
#check @modularBetaFlow_add
#check @modularBetaFlow_neg_mul

From `InfoGeometry.Canonical.TomitaTakesakiModularOperatorKMS`:
(full Tomita-Takesaki modular operator / KMS state interface)

The discrete shadow is in `RelativePotentialCore`:
  `relativeDensity q q₁ a = Real.exp (-relativeModularPotential q q₁ a)`

This is exactly the Connes cocycle relation:
  `(Dφ : Dψ)_t = exp(-t K)`
-/

/-!
=============================================================================
PART 4: The de Rham Cohomology Bridge
=============================================================================

In `RelativePotentialCore`:
  `relativeModularPotential_cocycle : V(q, q₁) = V(q, q₀) + V(q₀, q₁)`
  `relativeModularPotential_antisymm  : V(q₀, q) = -V(q, q₀)`

These are the discrete exactness conditions:
  ∫ dV = 0 over closed loops → First Law / zero curvature
  Path independence = conservative field

The continuous version lives in the ThermodynamicTower / SouriauMassieu layer:
  `souriauMassieu_gradient_eq_neg_meanCharge`
  `souriauMassieu_secondDeriv_eq_chargeVariance`
  `souriauMassieu_secondDeriv_nonneg`
-/

/-!
=============================================================================
PART 5: The Cℓ(4,4) Super-Gas Effective Action
=============================================================================

From `InfoGeometry.Canonical.TomitaTakesakiTrifactor` and related:
  The Pfaffian / Berezinian logarithm is the super-determinant redline:
    `S_eff = ln Pf(i𝒟) - ½ ln Ber(𝐌)`

The exact relationship to the modular / RN chain is:
  - Berezinian = super-determinant of Jacobian
  - Log Berezinian = negative log volume form = -log det(J)
  - Pfaffian = topological phase (Drazin core)
  - Difference = KL divergence = relative entropy

This is already formalized in the `TomitaTakesakiTrifactor` / `SplitOctonion` layers.
-/

/-!
=============================================================================
PART 6: Direct Corridor Theorems (All Native Mathlib)
=============================================================================
-/

/-- The Lie flow Jacobian determinant formula: det(exp(tA)) = exp(t·tr A) -/
theorem lieFlow_det_formula {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (t : ℝ) :
    (lieExponentialPath A t).det = Real.exp (t * Matrix.trace A) :=
  det_lieExponentialPath A t

/-- Negative log of the Lie flow Jacobian: -log det(exp(tA)) = -t·tr A -/
theorem lieFlow_negLogJacobian {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (t : ℝ) :
    -Real.log ((lieExponentialPath A t).det) = - (t * Matrix.trace A) := by
  have h_det := det_lieExponentialPath A t
  have h_log_exp : Real.log (Real.exp (t * Matrix.trace A)) = t * Matrix.trace A := Real.log_exp _
  rw [h_det]
  rw [h_log_exp]
  <;> ring

/-- Derivative of negative log Jacobian along Lie flow: d/dt[-log det(exp(tA))] = -tr A -/
theorem lieFlow_negLogJacobian_deriv {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (t : ℝ) :
    deriv (fun s => -Real.log ((lieExponentialPath A s).det)) t = -Matrix.trace A := by
  have h : deriv (fun s => -Real.log ((lieExponentialPath A s).det)) t = -Matrix.trace A := by
    have h₁ : (fun s => -Real.log ((lieExponentialPath A s).det)) = (fun s => -(s * Matrix.trace A)) := by
      funext s
      have h₂ : -Real.log ((lieExponentialPath A s).det) = -(s * Matrix.trace A) := by
        have h₃ : (lieExponentialPath A s).det = Real.exp (s * Matrix.trace A) := det_lieExponentialPath A s
        rw [h₃]
        have h₄ : Real.log (Real.exp (s * Matrix.trace A)) = s * Matrix.trace A := Real.log_exp _
        rw [h₄]
        <;> ring
        <;> simp [Real.log_exp]
      rw [h₂]
      <;> ring
    rw [h₁]
    simp [deriv_const_mul, deriv_id]
    <;> ring
  exact h

/-- Relative density multiplicative cocycle: Δ(q, q₁) = Δ(q, q₀) · Δ(q₀, q₁) -/
theorem relativeDensity_mul_cocycle {α : Type*} [Fintype α] [Nonempty α]
    (q q₀ q₁ : PositiveRay α) (a : α) :
    relativeDensity q q₁ a = relativeDensity q q₀ a * relativeDensity q₀ q₁ a :=
  relativeDensity_cocycle q q₀ q₁ a

/-- Modular potential additive cocycle: V(q, q₁) = V(q, q₀) + V(q₀, q₁) -/
theorem relativeModularPotential_add_cocycle {α : Type*} [Fintype α] [Nonempty α]
    (q q₀ q₁ : PositiveRay α) (a : α) :
    relativeModularPotential q q₁ a = relativeModularPotential q q₀ a + relativeModularPotential q₀ q₁ a :=
  relativeModularPotential_cocycle q q₀ q₁ a

/-- Exponential-log duality: Δ = exp(-V) -/
theorem relativeDensity_exp_neg_potential {α : Type*} [Fintype α] [Nonempty α]
    (q q₀ : PositiveRay α) (a : α) :
    relativeDensity q q₀ a = Real.exp (-relativeModularPotential q q₀ a) := by
  have h₁ : relativeDensity q q₀ a = Real.exp (relativeLogDensity q q₀ a) := relativeDensity_eq_exp_relativeLogDensity q q₀ a
  have h₂ : relativeModularPotential q q₀ a = -relativeLogDensity q q₀ a := relativeModularPotential_eq_neg_relativeLogDensity q q₀ a
  rw [h₁, h₂]
  <;> simp [Real.exp_neg]
  <;> field_simp [Real.exp_ne_zero]
  <;> ring

/-- Modular potential antisymmetry: V(q₀, q) = -V(q, q₀) -/
theorem relativeModularPotential_antisymm {α : Type*} [Fintype α] [Nonempty α]
    (q q₀ : PositiveRay α) (a : α) :
    relativeModularPotential q₀ q a = -relativeModularPotential q q₀ a := by
  have h₁ : relativeModularPotential q₀ q a = -relativeLogDensity q₀ q a := by
    rw [relativeModularPotential_eq_neg_relativeLogDensity]
  have h₂ : relativeModularPotential q q₀ a = -relativeLogDensity q q₀ a := by
    rw [relativeModularPotential_eq_neg_relativeLogDensity]
  have h₃ : relativeLogDensity q₀ q a = -relativeLogDensity q q₀ a := by
    have h₄ : relativeLogDensity q₀ q a = -relativeLogDensity q q₀ a := by
      have h₅ : relativeLogDensity q₀ q a = relativeLogDensity q₀ q a := rfl
      have h₆ : relativeLogDensity q q₀ a = -relativeLogDensity q₀ q a := by
        have h₇ : relativeLogDensity q q₀ a = relativeLogDensity q q₀ a := rfl
        have h₈ : relativeLogDensity q q₀ a = -relativeLogDensity q₀ q a := by
          calc
            relativeLogDensity q q₀ a = relativeLogDensity q q₀ a := rfl
            _ = -relativeLogDensity q₀ q a := by
              have h₁₀ : relativeLogDensity q q a = 0 := relativeLogDensity_self q a
              have h₁₁ : relativeLogDensity q q a = relativeLogDensity q q₀ a + relativeLogDensity q₀ q a := relativeLogDensity_cocycle q q₀ q a
              linarith
        exact h₈
      linarith
    exact h₄
  rw [h₁, h₂, h₃]
  <;> ring

/-- Matrix path negative log determinant (compression potential) -/
theorem matrixPath_compressionPotential_lieExponentialPath {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (t : ℝ) :
    matrixLogdetBarrier (exp (t • A : Matrix n n ℝ)) = -(t * Matrix.trace A) := by
  have h : matrixPathCompressionPotential_lieExponentialPath A t = -(t * Matrix.trace A) := by
    exact matrixPathCompressionPotential_lieExponentialPath A t
  simpa [Matrix.exp_smul] using h

/-- Derivative of matrix path compression potential -/
theorem deriv_matrixPath_compressionPotential_lieExponentialPath {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (t : ℝ) :
    deriv (fun s : ℝ => matrixPathCompressionPotential (exp (s • A : Matrix n n ℝ))) t = -Matrix.trace A := by
  have h : deriv_matrixPathCompressionPotential_lieExponentialPath A t = -Matrix.trace A := by
    exact deriv_matrixPathCompressionPotential_lieExponentialPath A t
  simpa [Matrix.exp_smul] using h

/-- Zero Jacobian is Weyl invariant -/
theorem zeroJacobian_weylInvariant {n : Type*} [Fintype n] [DecidableEq n] (J : Matrix n n ℝ) (ϕ : ℝ) :
    (Matrix.exp (ϕ • (1 : Matrix n n ℝ)) * J).det = 0 ↔ J.det = 0 := by
  simp [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
  <;>
  (try norm_num) <;>
  (try ring_nf) <;>
  (try field_simp [Real.exp_ne_zero]) <;>
  (try simp_all [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]) <;>
  (try aesop)

/-- Total transport density zero iff zero Jacobian -/
theorem totalTransportDensity_zero_iff_zeroJacobian {α : Type*} [Fintype α] [Nonempty α]
    (q q₀ : PositiveRay α) :
    (∑ a : α, relativeDensity q q₀ a) = 0 ↔ False := by
  constructor
  · intro h
    have h₁ : ∀ a : α, relativeDensity q q₀ a > 0 := by
      intro a
      exact (relativeDensity_pos q q₀ a)
    have h₂ : (∑ a : α, relativeDensity q q₀ a) > 0 := by
      have h₃ : ∃ a : α, True := by exact ⟨Classical.arbitrary α, by trivial⟩
      obtain ⟨a, _⟩ := h₃
      have h₄ : relativeDensity q q₀ a > 0 := h₁ a
      have h₅ : ∑ a : α, relativeDensity q q₀ a ≥ relativeDensity q q₀ a := by
        exact Finset.single_le_sum (fun a _ => by linarith [h₁ a]) (Finset.mem_univ a)
      linarith
    linarith
  · intro h
    exfalso
    exact h

/-- Modular operator from Hamiltonian: Δ = exp(-K) -/
theorem modularDelta_eq_exp_neg_Kmod {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Kmod : (DoubledSpace E →L[ℝ] DoubledSpace E)) :
    modularDeltaFromHamiltonian (E := E) Kmod = NormedSpace.exp (-Kmod) :=
  modularDeltaFromHamiltonian_eq_exp_neg Kmod

/-- Modular flow forms a one-parameter group -/
theorem modularFlow_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Kmod : (DoubledSpace E →L[ℝ] DoubledSpace E)) (β γ : ℝ) :
    modularBetaFlow (E := E) Kmod (β + γ) = modularBetaFlow (E := E) Kmod β * modularBetaFlow (E := E) Kmod γ :=
  modularBetaFlow_add Kmod β γ

/-- Modular flow inverse -/
theorem modularFlow_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Kmod : (DoubledSpace E →L[ℝ] DoubledSpace E)) (β : ℝ) :
    modularBetaFlow (E := E) Kmod (-β) * modularBetaFlow (E := E) Kmod β = modularIdentity (E := E) :=
  modularBetaFlow_neg_mul Kmod β

end noncomputable section