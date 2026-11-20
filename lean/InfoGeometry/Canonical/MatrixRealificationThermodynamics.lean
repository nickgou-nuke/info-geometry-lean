/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.RealificationCFC
import InfoGeometry.Canonical.MatrixGibbsEntropy
import InfoGeometry.Canonical.MatrixRelativeModular
import InfoGeometry.Canonical.MatrixGeneralizedGibbs

/-!
# Trace-normalized thermodynamics in the internal-complex real sector

The unital operator map `realify` doubles the ordinary trace. The existing
state encoding `state ρ = realify ρ / 2` therefore adds `log 2` to the entropy
of a faithful trace-one state and leaves its relative entropy unchanged.
The real partition function is twice the complex partition function, so the
native real normalized exponential is exactly the encoded Gibbs state.

The relative modular matrix and its actual CFC logarithm intertwine the
ordered two-sided action on the realification image. Their full real and
complex superoperator carriers have different dimensions; no equivalence of
those entire carriers is asserted. All positivity is ordinary Hilbert
positivity, and no commutation of the source and reference states is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixRealificationThermodynamics

open Matrix
open InfoGeometry.Quantum.Realification
open MatrixEntropyUnitaryOrbit MatrixGibbsEntropy MatrixRelativeModular
open PolarFrameTraceDensity FiniteMatrixGibbsFunctional
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "CMat" => Matrix n n ℂ
local notation "RMat" => Matrix (n ⊕ n) (n ⊕ n) ℝ

omit [DecidableEq n] in
/-- Density-weighted trace pairing in either order agrees with the source. -/
theorem trace_state_mul_realify (ρ A : CMat) :
    trace (state ρ * realify A) = (trace (ρ * A)).re := by
  rw [trace_mul_comm, born_readout, trace_mul_comm]

/-- The exact entropy correction, also valid before imposing trace one. -/
theorem entropy_state (ρ : CMat) (hρ : IsStrictlyPositive ρ) :
    -trace (state ρ * CFC.log (state ρ)) =
      matrixEntropy ρ + Real.log 2 * (trace ρ).re := by
  rw [log_state ρ hρ, mul_sub, trace_sub, trace_state_mul_realify,
    mul_smul_comm, mul_one, trace_smul, trace_state, smul_eq_mul,
    matrixEntropy_eq]
  ring

/-- Ordinary real entropy has the necessary additive `log 2` normalization. -/
theorem entropy_state_of_trace_one (ρ : CMat) (hρ : IsStrictlyPositive ρ)
    (htrace : trace ρ = 1) :
    -trace (state ρ * CFC.log (state ρ)) = matrixEntropy ρ + Real.log 2 := by
  rw [entropy_state ρ hρ, htrace, Complex.one_re, mul_one]

/-- The common central logarithmic correction cancels in a relative logarithm. -/
theorem relativeLog_state (ρ σ : CMat)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    CFC.log (state ρ) - CFC.log (state σ) =
      realify (CFC.log ρ - CFC.log σ) := by
  rw [log_state ρ hρ, log_state σ hσ, realify_sub]
  abel

/-- Umegaki's actual relative-log trace is unchanged by the state encoding.
Trace one is not required for this equality. -/
theorem relativeLogTrace_state (ρ σ : CMat)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    trace (state ρ * (CFC.log (state ρ) - CFC.log (state σ))) =
      (trace (ρ * (CFC.log ρ - CFC.log σ))).re := by
  rw [relativeLog_state ρ σ hρ hσ, trace_state_mul_realify]

/-- The positive modular kernel gives the same information divergence after
realification, with both states normalized by the actual trace-one map. -/
theorem modularItakuraSaito_state (ρ σ : CMat)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ)
    (htrρ : trace ρ = 1) (htrσ : trace σ = 1) :
    squareRootExpectation (state ρ)
      (itakuraSaitoOperator (relativeModularMatrix (state ρ) (state σ))) =
        (trace (ρ * (CFC.log ρ - CFC.log σ))).re := by
  rw [squareRootExpectation_itakuraSaito_eq_relativeLogTrace (state ρ) (state σ)
    (state_isStrictlyPositive hρ) (state_isStrictlyPositive hσ)
    (trace_state_eq_one htrρ) (trace_state_eq_one htrσ),
    relativeLogTrace_state ρ σ hρ hσ]

omit [DecidableEq n] in
/-- The existing trace normalizer agrees with the native real trace normalizer. -/
theorem normalizedDensity_state (P : CMat) :
    state (normalizedDensity P) = (trace (realify P))⁻¹ • realify P := by
  rw [normalizedDensity, state, realify_smul, trace_realify, smul_smul]
  change ((1 / 2 : ℝ) * (trace P).re⁻¹) • realify P = _
  rw [_root_.mul_inv_rev]
  congr 1
  ring

/-- An arbitrary matrix generator is transported before forming its normalized
exponential. Selfadjointness gives the usual positive Gibbs interpretation. -/
theorem normalized_exp_state (K : CMat) :
    state (normalizedDensity (NormedSpace.exp (-K))) =
      (trace (NormedSpace.exp (-realify K)))⁻¹ •
        NormedSpace.exp (-realify K) := by
  rw [normalizedDensity_state, realify_exp, realify_neg]

/-- The partition function of the real Hamiltonian is exactly twice the
partition function of its complex presentation. -/
theorem gibbsPartition_realify (H : CMat) (hH : H.IsHermitian) (β : ℝ) :
    trace (NormedSpace.exp ((-β) • realify H)) = 2 * gibbsPartition H hH β := by
  rw [← realify_smul, ← realify_exp, trace_realify]
  rw [gibbsPartition, traceMass, gibbsDensity_eq_exp_neg_smul]

/-- The native normalized real exponential is the existing encoded Gibbs state. -/
theorem normalizedGibbsDensity_state (H : CMat) (hH : H.IsHermitian) (β : ℝ) :
    state (normalizedGibbsDensity H hH β) =
      (trace (NormedSpace.exp ((-β) • realify H)))⁻¹ •
        NormedSpace.exp ((-β) • realify H) := by
  rw [normalizedGibbsDensity_eq_normalized_exp, state, realify_smul,
    realify_exp, realify_smul, gibbsPartition_realify H hH β, smul_smul]
  congr 1
  rw [_root_.mul_inv_rev]
  ring

/-- Faithful positive Gibbs states remain faithful under the real normalization. -/
theorem real_normalizedGibbsDensity_isStrictlyPositive [Nonempty n]
    (H : CMat) (hH : H.IsHermitian) (β : ℝ) :
    IsStrictlyPositive
      ((trace (NormedSpace.exp ((-β) • realify H)))⁻¹ •
        NormedSpace.exp ((-β) • realify H)) := by
  rw [← normalizedGibbsDensity_state H hH β]
  exact state_isStrictlyPositive
    (normalizedGibbsDensity_isStrictlyPositive H hH β)

/-- The unital operator encoding intertwines the ordered modular action. -/
theorem modularAction_realify (ρ σ X : CMat) (hρ : IsUnit ρ) :
    realify (σ * X * ρ⁻¹) = realify σ * realify X * (realify ρ)⁻¹ := by
  rw [realify_mul, realify_mul, realify_inv ρ hρ]

/-- The state factors cancel between left multiplication and the right inverse. -/
theorem modularAction_state (ρ σ X : CMat) (hρ : IsUnit ρ) :
    state σ * realify X * (state ρ)⁻¹ = realify (σ * X * ρ⁻¹) := by
  rw [inv_state ρ hρ]
  simp only [state, smul_mul_assoc, mul_smul_comm, smul_smul,
    realify_mul]
  norm_num

/-- Actual relative modular matrices agree on encoded Hilbert--Schmidt inputs. -/
theorem relativeModularMatrix_state_mulVec (ρ σ X : CMat) (hρ : IsUnit ρ) :
    relativeModularMatrix (state ρ) (state σ) *ᵥ (realify X).vec =
      (realify (σ * X * ρ⁻¹)).vec := by
  rw [relativeModularMatrix_mulVec, modularAction_state ρ σ X hρ]

/-- The actual logarithmic modular action preserves the encoded sector.
Its two central normalization corrections cancel without commuting `ρ` and `σ`. -/
theorem modularLogAction_state (ρ σ X : CMat)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    CFC.log (state σ) * realify X - realify X * CFC.log (state ρ) =
      realify (CFC.log σ * X - X * CFC.log ρ) := by
  rw [log_state σ hσ, log_state ρ hρ]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, realify_sub, realify_mul]
  abel

/-- The native CFC logarithms of the relative modular matrices intertwine on
the realification image; this is a restriction statement, not a carrier equivalence. -/
theorem log_relativeModularMatrix_state_mulVec (ρ σ X : CMat)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    CFC.log (relativeModularMatrix (state ρ) (state σ)) *ᵥ (realify X).vec =
      (realify (CFC.log σ * X - X * CFC.log ρ)).vec := by
  rw [log_relativeModularMatrix_mulVec (state ρ) (state σ) (realify X)
    (state_isStrictlyPositive hρ) (state_isStrictlyPositive hσ),
    modularLogAction_state ρ σ X hρ hσ]

section GeneralizedGibbs

open MatrixGeneralizedGibbs

variable {ι : Type*} [Fintype ι]

omit [Fintype n] [DecidableEq n] in
/-- The real parameter vector is unchanged; its represented generator is realified. -/
theorem realify_chargePencil (Q : ι → CMat) (β : ι → ℝ) :
    realify (chargePencil Q β) = ∑ a, β a • realify (Q a) := by
  simp only [chargePencil_apply, realify_sum, realify_smul]

/-- The existing generalized Gibbs state is the normalized exponential of the
actual real charge pencil; the charges need not commute. -/
theorem generalizedGibbs_state (Q : ι → CMat)
    (hQ : ∀ a, (Q a).IsHermitian) (β : ι → ℝ) :
    state (normalizedGibbsDensity (chargePencil Q β)
      (chargePencil_isHermitian Q hQ β) 1) =
      (trace (NormedSpace.exp (-(∑ a, β a • realify (Q a)))))⁻¹ •
        NormedSpace.exp (-(∑ a, β a • realify (Q a))) := by
  simpa only [neg_one_smul, realify_chargePencil] using
    normalizedGibbsDensity_state (chargePencil Q β)
      (chargePencil_isHermitian Q hQ β) 1

/-- The generalized Gibbs charge/entropy balance has an entirely real matrix
readout. The two absolute entropy offsets cancel in the entropy difference. -/
theorem gibbs_charge_entropy_balance_state [Nonempty n]
    (Q : ι → CMat) (hQ : ∀ a, (Q a).IsHermitian) (β : ι → ℝ)
    (ρ : CMat) (hρ : IsStrictlyPositive ρ) (htrρ : trace ρ = 1) :
    let σ := normalizedGibbsDensity (chargePencil Q β)
      (chargePencil_isHermitian Q hQ β) 1
    (∑ a, β a * (trace (state ρ * realify (Q a)) -
      trace (state σ * realify (Q a)))) =
      (-trace (state ρ * CFC.log (state ρ))) -
        (-trace (state σ * CFC.log (state σ))) +
        trace (state ρ * (CFC.log (state ρ) - CFC.log (state σ))) := by
  dsimp only
  rw [entropy_state_of_trace_one ρ hρ htrρ,
    entropy_state_of_trace_one _ (normalizedGibbsDensity_isStrictlyPositive _ _ _)
      (trace_normalizedGibbsDensity _ _ _),
    relativeLogTrace_state ρ _ hρ (normalizedGibbsDensity_isStrictlyPositive _ _ _)]
  simp only [trace_state_mul_realify]
  have h := gibbs_charge_entropy_balance Q hQ β ρ htrρ
  linarith

end GeneralizedGibbs

end InfoGeometry.Canonical.MatrixRealificationThermodynamics
