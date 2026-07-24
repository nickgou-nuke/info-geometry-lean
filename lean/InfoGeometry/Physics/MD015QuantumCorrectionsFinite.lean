import Mathlib
import InfoGeometry.Section8
import InfoGeometry.Physics.Section29QuantumEffectiveAction

/-!
# Repaired MD 015: finite quantum-correction algebra

Requested source: `github-nick:nickgou-nuke/MD`, file `015.md`.

At the fetched upstream revision, `015.md` is absent; the closest available file
is `n015.md`, titled *Quantum Corrections and Perturbative Structure in
Quaternionic Emergent Gravity*.  That manuscript discusses path integrals,
one-loop trace-log formulae, renormalization group flow, perturbative expansion
around a quaternion condensate, propagators, vertices, asymptotic safety, black
holes, and information-preservation scenarios.  Those continuum/QFT claims
require measures, gauge fixing, functional determinants, regularization,
operator domains, and geometric field equations, so this owner extracts only the
finite algebraic socket:

* a formal three-loop scalar effective-action polynomial extending the existing
  Section 29 two-loop owner;
* a scalar one-loop trace-log slot `i/2 · T` with additivity and zero laws;
* a scalar FRG/Wetterich-style right-hand-side slot with additivity and zero
  cutoff-derivative law;
* a finite quadratic fluctuation action around a background, including the
  stationary-background remainder and evenness;
* a quaternion condensate fluctuation norm identity using the existing finite
  quaternion coordinate algebra.

No theorem here asserts a path-integral construction, one-loop determinant
formula, renormalizability, beta-function computation, exact RG equation,
asymptotic safety, Hawking radiation, black-hole back-reaction, or information
preservation.
-/

noncomputable section

namespace InfoGeometry.Physics.MD015QuantumCorrectionsFinite

open InfoGeometry.Physics.Section29QuantumEffectiveAction

/-- Finite scalar coefficients for a formal three-loop effective action. -/
structure Loop3ActionDatum where
  classical : ℝ
  oneLoop : ℝ
  twoLoop : ℝ
  threeLoop : ℝ

/-- Forget the third-loop slot to reuse the Section 29 two-loop owner. -/
def Loop3ActionDatum.toTwoLoop (D : Loop3ActionDatum) : LoopActionDatum :=
  ⟨D.classical, D.oneLoop, D.twoLoop⟩

/-- Formal three-loop effective action `Γ₃(ℏ)=S+ℏΓ₁+ℏ²Γ₂+ℏ³Γ₃`. -/
def effectiveActionThreeLoop (D : Loop3ActionDatum) (hbar : ℝ) : ℝ :=
  D.classical + hbar * D.oneLoop + hbar ^ 2 * D.twoLoop + hbar ^ 3 * D.threeLoop

/-- The three-loop action extends the already-owned two-loop action by `ℏ³Γ₃`. -/
theorem effectiveActionThreeLoop_eq_twoLoop_add_cubic
    (D : Loop3ActionDatum) (hbar : ℝ) :
    effectiveActionThreeLoop D hbar =
      effectiveActionTwoLoop D.toTwoLoop hbar + hbar ^ 3 * D.threeLoop := by
  simp [effectiveActionThreeLoop, Loop3ActionDatum.toTwoLoop, effectiveActionTwoLoop]

/-- Classical limit of the formal three-loop expansion. -/
theorem effectiveActionThreeLoop_zero (D : Loop3ActionDatum) :
    effectiveActionThreeLoop D 0 = D.classical := by
  simp [effectiveActionThreeLoop]

/-- The three-loop remainder is exactly the finite `ℏ`-weighted correction polynomial. -/
theorem effectiveActionThreeLoop_sub_classical (D : Loop3ActionDatum) (hbar : ℝ) :
    effectiveActionThreeLoop D hbar - D.classical =
      hbar * D.oneLoop + hbar ^ 2 * D.twoLoop + hbar ^ 3 * D.threeLoop := by
  unfold effectiveActionThreeLoop
  ring

/-- Scalar shadow of the one-loop trace-log slot `Γ¹ = (i/2) T`. -/
def oneLoopTraceLogShadow (traceLog : ℂ) : ℂ :=
  (Complex.I / 2) * traceLog

/-- The finite trace-log slot is additive in independent scalar trace contributions. -/
theorem oneLoopTraceLogShadow_add (T U : ℂ) :
    oneLoopTraceLogShadow (T + U) = oneLoopTraceLogShadow T + oneLoopTraceLogShadow U := by
  simp [oneLoopTraceLogShadow]
  ring

/-- A zero trace-log scalar gives a zero one-loop shadow. -/
theorem oneLoopTraceLogShadow_zero : oneLoopTraceLogShadow 0 = 0 := by
  simp [oneLoopTraceLogShadow]

/-- Finite scalar quadratic fluctuation action `S₀ + L δ + 1/2 H δ²`. -/
def quadraticFluctuationAction (S0 L H delta : ℝ) : ℝ :=
  S0 + L * delta + (1 / 2 : ℝ) * H * delta ^ 2

/-- At a stationary background (`L=0`), only the quadratic fluctuation remains. -/
theorem quadraticFluctuationAction_sub_background_of_stationary
    (S0 L H delta : ℝ) (hL : L = 0) :
    quadraticFluctuationAction S0 L H delta - S0 = (1 / 2 : ℝ) * H * delta ^ 2 := by
  simp [quadraticFluctuationAction, hL]

/-- At a stationary background the quadratic fluctuation slot is even in `δ`. -/
theorem quadraticFluctuationAction_even_of_stationary
    (S0 L H delta : ℝ) (hL : L = 0) :
    quadraticFluctuationAction S0 L H (-delta) = quadraticFluctuationAction S0 L H delta := by
  simp [quadraticFluctuationAction, hL]

/-- Scalar finite shadow of a Wetterich/FRG right-hand side: `1/2 · K⁻¹ · ∂R`. -/
def frgScalarRHS (inverseKernel cutoffDerivative : ℝ) : ℝ :=
  (1 / 2 : ℝ) * inverseKernel * cutoffDerivative

/-- The scalar FRG shadow is additive in the cutoff-derivative slot. -/
theorem frgScalarRHS_add_cutoffDerivative (inverseKernel dR dS : ℝ) :
    frgScalarRHS inverseKernel (dR + dS) = frgScalarRHS inverseKernel dR + frgScalarRHS inverseKernel dS := by
  simp [frgScalarRHS]
  ring

/-- If the cutoff derivative is zero, the scalar FRG shadow vanishes. -/
theorem frgScalarRHS_zero_cutoffDerivative (inverseKernel : ℝ) :
    frgScalarRHS inverseKernel 0 = 0 := by
  simp [frgScalarRHS]

/-- Coordinate dot product for the finite quaternion condensate/fluctuation algebra. -/
def quatDot (p q : Section8.Quat) : ℝ :=
  Section8.Quat.dot p q

/-- Finite quaternion fluctuation norm expansion `|Q₀+q|²=|Q₀|²+2<Q₀,q>+|q|²`. -/
theorem quaternionFluctuation_normSq_add (Q0 q : Section8.Quat) :
    Section8.Quat.normSq (Q0 + q) =
      Section8.Quat.normSq Q0 + 2 * quatDot Q0 q + Section8.Quat.normSq q := by
  simp [quatDot, Section8.Quat.normSq, Section8.Quat.dot]
  ring

/-- Repaired theorem-safe MD015 finite quantum-correction packet. -/
theorem repaired_MD015_quantum_corrections_packet
    (D : Loop3ActionDatum) (hbar : ℝ) (T U : ℂ)
    (S0 L H delta inverseKernel dR dS : ℝ) (hL : L = 0)
    (Q0 q : Section8.Quat) :
    effectiveActionThreeLoop D hbar =
      effectiveActionTwoLoop D.toTwoLoop hbar + hbar ^ 3 * D.threeLoop ∧
    effectiveActionThreeLoop D hbar - D.classical =
      hbar * D.oneLoop + hbar ^ 2 * D.twoLoop + hbar ^ 3 * D.threeLoop ∧
    oneLoopTraceLogShadow (T + U) = oneLoopTraceLogShadow T + oneLoopTraceLogShadow U ∧
    quadraticFluctuationAction S0 L H delta - S0 = (1 / 2 : ℝ) * H * delta ^ 2 ∧
    frgScalarRHS inverseKernel (dR + dS) = frgScalarRHS inverseKernel dR + frgScalarRHS inverseKernel dS ∧
    Section8.Quat.normSq (Q0 + q) =
      Section8.Quat.normSq Q0 + 2 * quatDot Q0 q + Section8.Quat.normSq q := by
  exact ⟨effectiveActionThreeLoop_eq_twoLoop_add_cubic D hbar,
    effectiveActionThreeLoop_sub_classical D hbar,
    oneLoopTraceLogShadow_add T U,
    quadraticFluctuationAction_sub_background_of_stationary S0 L H delta hL,
    frgScalarRHS_add_cutoffDerivative inverseKernel dR dS,
    quaternionFluctuation_normSq_add Q0 q⟩

end InfoGeometry.Physics.MD015QuantumCorrectionsFinite

end noncomputable section
