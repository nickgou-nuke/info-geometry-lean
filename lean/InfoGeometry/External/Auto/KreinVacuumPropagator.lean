import Mathlib.Tactic
import InfoGeometry.External.Auto.AnomalousKMSFlow

/-!
# Krein Vacuum Propagator

This module records the algebraic core of the doubled-Krein/ghost-sheet
propagator cancellation:

* an involutive chiral parity `ε`;
* a propagator `G` that anticommutes with `ε`;
* a cyclic linear trace.

Under these hypotheses the ordinary vacuum bubble `tr G` vanishes.  This is a
finite algebraic cancellation theorem; analytic trace-class and renormalization
claims must be supplied by later analytic models.
-/

noncomputable section

namespace InfoGeometry.Quantum.KreinVacuumPropagator

open Complex

/-- Algebraic propagator data for a doubled Krein sector. -/
structure ChiralPropagatorContext (H : Type*) [AddCommGroup H] [Module ℂ H] where
  epsilon : Module.End ℂ H
  propagator : Module.End ℂ H
  tr : Module.End ℂ H →ₗ[ℂ] ℂ
  epsilon_sq : epsilon * epsilon = 1
  propagator_chiral_anticommute : propagator * epsilon = -(epsilon * propagator)
  trace_cyclic : ∀ A B : Module.End ℂ H, tr (A * B) = tr (B * A)

/-- The vacuum bubble is the trace of the Green/propagator operator. -/
def vacuumBubble {H : Type*} [AddCommGroup H] [Module ℂ H]
    (C : ChiralPropagatorContext H) : ℂ :=
  C.tr C.propagator

/-- Anticommutation also gives the opposite ordering. -/
theorem epsilon_propagator_anticommute
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (C : ChiralPropagatorContext H) :
    C.epsilon * C.propagator = -(C.propagator * C.epsilon) := by
  calc
    C.epsilon * C.propagator = -(-(C.epsilon * C.propagator)) := by simp
    _ = -(C.propagator * C.epsilon) := by
      rw [C.propagator_chiral_anticommute]

/-- Chiral conjugation flips the sign of an odd propagator. -/
theorem chiral_conjugation_flips_propagator
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (C : ChiralPropagatorContext H) :
    C.epsilon * C.propagator * C.epsilon = -C.propagator := by
  calc
    C.epsilon * C.propagator * C.epsilon =
        (-(C.propagator * C.epsilon)) * C.epsilon := by
          rw [epsilon_propagator_anticommute C]
    _ = -(C.propagator * (C.epsilon * C.epsilon)) := by
          simp [mul_assoc]
    _ = -C.propagator := by
          rw [C.epsilon_sq]
          simp

/-- Cyclic trace and `ε² = 1` make chiral conjugation trace-invisible. -/
theorem chiral_trace_conjugation
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (C : ChiralPropagatorContext H) (A : Module.End ℂ H) :
    C.tr (C.epsilon * A * C.epsilon) = C.tr A := by
  calc
    C.tr (C.epsilon * A * C.epsilon) =
        C.tr ((C.epsilon * A) * C.epsilon) := by rfl
    _ = C.tr (C.epsilon * (C.epsilon * A)) := by
          rw [C.trace_cyclic (C.epsilon * A) C.epsilon]
    _ = C.tr ((C.epsilon * C.epsilon) * A) := by
          simp [mul_assoc]
    _ = C.tr A := by
          rw [C.epsilon_sq]
          simp

/--
Automatic algebraic UV cancellation.

If the Green operator is odd under an involutive chiral parity and the trace is
cyclic, then the ordinary propagator trace is forced to be zero.
-/
theorem uv_divergence_cancellation
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (C : ChiralPropagatorContext H) :
    vacuumBubble C = 0 := by
  unfold vacuumBubble
  have hsign : C.tr C.propagator = -C.tr C.propagator := by
    calc
      C.tr C.propagator =
          C.tr (C.epsilon * C.propagator * C.epsilon) := by
            exact (chiral_trace_conjugation C C.propagator).symm
      _ = C.tr (-C.propagator) := by
            rw [chiral_conjugation_flips_propagator C]
      _ = -C.tr C.propagator := by
            simp
  have htwo : (2 : ℂ) * C.tr C.propagator = 0 := by
    have h := congrArg (fun z => z + C.tr C.propagator) hsign
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Bundled statement of the algebraic vacuum cancellation package. -/
theorem krein_vacuum_propagator_package
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (C : ChiralPropagatorContext H) :
    C.epsilon * C.propagator * C.epsilon = -C.propagator ∧
      C.tr (C.epsilon * C.propagator * C.epsilon) = C.tr C.propagator ∧
      vacuumBubble C = 0 := by
  exact ⟨chiral_conjugation_flips_propagator C,
    chiral_trace_conjugation C C.propagator,
    uv_divergence_cancellation C⟩

/-- Concrete Klein-bottle (`ε` = Klein parity) propagator context on `Fin 2 → ℂ`. -/
def kleinBottle_vacuum_bubble_context
    (G : Module.End ℂ (Fin 2 → ℂ))
    (hGammaAnti : G * AnomalousKMSFlow.kleinBottleΓ = -(AnomalousKMSFlow.kleinBottleΓ * G)) :
    ChiralPropagatorContext (Fin 2 → ℂ) := by
  refine ⟨AnomalousKMSFlow.kleinBottleΓ, G, LinearMap.trace ℂ (Fin 2 → ℂ),
    AnomalousKMSFlow.kleinBottleΓ_sq, ?_, ?_⟩
  · exact hGammaAnti
  · intro A B
    simpa using (LinearMap.trace_mul_comm (R := ℂ) (M := Fin 2 → ℂ) A B)

/-- Vacuum bubble cancellation in the concrete Klein-bottle example. -/
theorem uv_divergence_cancellation_kleinBottle
    (G : Module.End ℂ (Fin 2 → ℂ))
    (hGammaAnti : G * AnomalousKMSFlow.kleinBottleΓ = -(AnomalousKMSFlow.kleinBottleΓ * G)) :
    vacuumBubble (kleinBottle_vacuum_bubble_context G hGammaAnti) = 0 :=
  uv_divergence_cancellation (C := kleinBottle_vacuum_bubble_context G hGammaAnti)

/-- Same physical bridge through the Tomita-canonical ghost parity `tomitaBottleΓ`. -/
def tomitaBottle_vacuum_bubble_context
    (G : Module.End ℂ (Fin 2 → ℂ))
    (hTomitaAnti : G * AnomalousKMSFlow.tomitaBottleΓ = -(AnomalousKMSFlow.tomitaBottleΓ * G)) :
    ChiralPropagatorContext (Fin 2 → ℂ) := by
  refine ⟨AnomalousKMSFlow.tomitaBottleΓ, G, LinearMap.trace ℂ (Fin 2 → ℂ),
    by simpa [AnomalousKMSFlow.tomitaBottleΓ_eq_kleinBottleΓ] using
      AnomalousKMSFlow.kleinBottleΓ_sq,
    ?_, ?_⟩
  · exact hTomitaAnti
  · intro A B
    simpa using (LinearMap.trace_mul_comm (R := ℂ) (M := Fin 2 → ℂ) A B)

/-- Vacuum bubble cancellation in the concrete Tomita example. -/
theorem uv_divergence_cancellation_tomitaBottle
    (G : Module.End ℂ (Fin 2 → ℂ))
    (hTomitaAnti : G * AnomalousKMSFlow.tomitaBottleΓ = -(AnomalousKMSFlow.tomitaBottleΓ * G)) :
    vacuumBubble (tomitaBottle_vacuum_bubble_context G hTomitaAnti) = 0 := by
  exact uv_divergence_cancellation (C := tomitaBottle_vacuum_bubble_context G hTomitaAnti)

/-- In the concrete Klein sector, the modular swap `J` is odd for chiral parity `Γ`. -/
theorem kleinBottleJ_chiral_anticommute :
    AnomalousKMSFlow.kleinBottleJ * AnomalousKMSFlow.kleinBottleΓ =
      -(AnomalousKMSFlow.kleinBottleΓ * AnomalousKMSFlow.kleinBottleJ) := by
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_mul]
  rw [show LinearMap.toMatrix'
        (-(AnomalousKMSFlow.kleinBottleΓ * AnomalousKMSFlow.kleinBottleJ)) =
        -(LinearMap.toMatrix'
          (AnomalousKMSFlow.kleinBottleΓ * AnomalousKMSFlow.kleinBottleJ)) by
        ext i j
        simp]
  rw [LinearMap.toMatrix'_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AnomalousKMSFlow.kleinBottleJ, AnomalousKMSFlow.kleinBottleΓ,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The same oddness, written with TOMITA-canonical imported matrices. -/
theorem tomitaBottleJ_chiral_anticommute :
    AnomalousKMSFlow.tomitaBottleJ * AnomalousKMSFlow.tomitaBottleΓ =
      -(AnomalousKMSFlow.tomitaBottleΓ * AnomalousKMSFlow.tomitaBottleJ) := by
  simpa [AnomalousKMSFlow.tomitaBottleJ_eq_kleinBottleJ,
    AnomalousKMSFlow.tomitaBottleΓ_eq_kleinBottleΓ]
    using kleinBottleJ_chiral_anticommute

/-- Closed-form finite Klein context with propagator witness `G = J`. -/
def kleinBottleJPropagatorContext : ChiralPropagatorContext (Fin 2 → ℂ) :=
  kleinBottle_vacuum_bubble_context
    AnomalousKMSFlow.kleinBottleJ
    kleinBottleJ_chiral_anticommute

/-- Closed-form finite TOMITA context with propagator witness `G = J`. -/
def tomitaBottleJPropagatorContext : ChiralPropagatorContext (Fin 2 → ℂ) :=
  tomitaBottle_vacuum_bubble_context
    AnomalousKMSFlow.tomitaBottleJ
    tomitaBottleJ_chiral_anticommute

/-- Fully concrete Klein V₄ physics-to-lemma bridge: `G = J` gives zero bubble. -/
theorem kleinBottleJ_vacuumBubble_vanishes :
    vacuumBubble kleinBottleJPropagatorContext = 0 :=
  uv_divergence_cancellation_kleinBottle
    AnomalousKMSFlow.kleinBottleJ
    kleinBottleJ_chiral_anticommute

/-- Fully concrete TOMITA notation for the same finite `G = J` cancellation. -/
theorem tomitaBottleJ_vacuumBubble_vanishes :
    vacuumBubble tomitaBottleJPropagatorContext = 0 :=
  uv_divergence_cancellation_tomitaBottle
    AnomalousKMSFlow.tomitaBottleJ
    tomitaBottleJ_chiral_anticommute

/-- Consolidated finite-sector bridge from Klein/TOMITA matrices to vacuum cancellation. -/
theorem klein_tomita_vacuum_bridge :
    vacuumBubble kleinBottleJPropagatorContext = 0 ∧
      vacuumBubble tomitaBottleJPropagatorContext = 0 :=
  ⟨kleinBottleJ_vacuumBubble_vanishes, tomitaBottleJ_vacuumBubble_vanishes⟩

end InfoGeometry.Quantum.KreinVacuumPropagator
