/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
import InfoGeometry.Canonical.FiniteMatrixGibbsParity

/-! Finite Gibbs parity transport from any seed stage. No Hamiltonian family
propagated from stage zero is required. The colimit consumer takes actual
functional compatibility explicitly; it does not construct a new state. -/
noncomputable section
namespace InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

/-- CFC density transport along an arbitrary native matrix-tower transition. -/
theorem gibbsDensity_rawMap {i j : ℕ} (hij : i ≤ j)
    (H : MatrixStage i) (H' : MatrixStage j)
    (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (hstep : H' = rawMap hij H) (β : ℝ) :
    rawMap hij (gibbsDensity H hH β) = gibbsDensity H' hH' β := by
  cases hstep
  change rawMap hij (hH.cfc (expWeight β)) = hH'.cfc (expWeight β)
  rw [← hH.cfc_eq, ← hH'.cfc_eq]
  exact StarAlgHom.map_cfc (rawMap hij) (expWeight β) H
    (by unfold expWeight; fun_prop)
    ((rawMap hij).toAlgHom.toLinearMap.continuous_of_finiteDimensional) hH hH'

/-- Normalized Gibbs transport, without any extension below the seed stage. -/
theorem gibbsFunctional_rawMap {i j : ℕ} (hij : i ≤ j)
    (H : MatrixStage i) (H' : MatrixStage j)
    (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (hstep : H' = rawMap hij H) (β : ℝ) (X : MatrixStage i) :
    gibbsFunctional H' hH' β (rawMap hij X) = gibbsFunctional H hH β X := by
  have hh (k : ℕ) (hik : i ≤ k) : (rawMap hik H).IsHermitian := by
    change star (rawMap hik H) = rawMap hik H
    rw [← map_star]
    exact congrArg (rawMap hik) hH
  have ht : ∀ {k : ℕ} (hik : i ≤ k),
      gibbsFunctional (rawMap hik H) (hh k hik) β (rawMap hik X) =
        gibbsFunctional H hH β X := by
    intro k hik
    induction hik with
    | refl =>
        simp [rawMap, concreteMap_id]
    | @step k hik ih =>
        have hs (Z : MatrixStage i) :
            rawMap (Nat.le.step hik) Z = concreteStep k (rawMap hik Z) := by
          simpa [rawMap, concreteData, concreteMap, map_succ] using
            congrArg (fun f => f Z) (map_succ concreteData hik)
        rw [hs X]
        exact (gibbsFunctional_concreteStep k (rawMap hik H)
          (rawMap (Nat.le.step hik) H) (hh k hik) (hh (k + 1) (Nat.le.step hik))
          (hs H) β (rawMap hik X)).trans ih
  cases hstep
  exact ht hij

/-- One-step cancellation uses only the original stage's parity hypotheses. -/
theorem gibbsFunctional_concreteStep_odd_zero (n : ℕ)
    (H Γ X : MatrixStage n) (H' : MatrixStage (n + 1))
    (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (hstep : H' = concreteStep n H) (hcomm : Commute H Γ)
    (hΓ : Γ * Γ = 1) (hodd : X * Γ = -(Γ * X)) (β : ℝ) :
    gibbsFunctional H' hH' β (concreteStep n X) = 0 := by
  rw [gibbsFunctional_concreteStep n H H' hH hH' hstep β X]
  exact gibbsFunctional_odd_zero H Γ X hH hcomm hΓ hodd β

/-- Cancellation at every later stage, from an arbitrary finite seed. -/
theorem gibbsFunctional_rawMap_odd_zero {i j : ℕ} (hij : i ≤ j)
    (H Γ X : MatrixStage i) (H' : MatrixStage j)
    (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (hstep : H' = rawMap hij H) (hcomm : Commute H Γ)
    (hΓ : Γ * Γ = 1) (hodd : X * Γ = -(Γ * X)) (β : ℝ) :
    gibbsFunctional H' hH' β (rawMap hij X) = 0 := by
  rw [gibbsFunctional_rawMap hij H H' hH hH' hstep β X]
  exact gibbsFunctional_odd_zero H Γ X hH hcomm hΓ hodd β

/-- Conditional colimit readout: compatibility is of functionals, not a
Hamiltonian extension from the scalar stage zero. -/
theorem gibbsColimitFunctional_transport_odd_zero
    (H : ∀ n, MatrixStage n) (hH : ∀ n, (H n).IsHermitian) (β : ℝ)
    (hCompat : Compatible (gibbsStageFunctional H hH β))
    {i j : ℕ} (hij : i ≤ j) (Γ X : MatrixStage i)
    (hcomm : Commute (H i) Γ) (hΓ : Γ * Γ = 1)
    (hodd : X * Γ = -(Γ * X)) :
    gibbsColimitFunctional H hH β hCompat (stageInjection j (rawMap hij X)) = 0 := by
  rw [gibbsColimitFunctional_stage]
  have hc := hCompat hij X
  change gibbsFunctional (H j) (hH j) β (rawMap hij X) =
    gibbsFunctional (H i) (hH i) β X at hc
  rw [hc]
  exact gibbsFunctional_odd_zero (H i) Γ X (hH i) hcomm hΓ hodd β

end InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
