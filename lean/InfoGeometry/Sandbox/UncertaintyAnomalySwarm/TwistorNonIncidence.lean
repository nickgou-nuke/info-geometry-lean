import Mathlib.Tactic
import InfoGeometry.Twistor.Incidence
import InfoGeometry.Quantum.PauliSoldering
import InfoGeometry.Topology.AmplituhedronTensorTowerColimit

namespace InfoGeometry.Sandbox.UncertaintyAnomalySwarm.TwistorNonIncidence

open InfoGeometry.Twistor.Incidence
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Topology.AmplituhedronColimit
open InfoGeometry.Clifford.Soldering

/-- 
Chiral Anomaly volume parameter.
-/
abbrev ChiralAnomalyVolume := ℝ

/--
A non-zero Chiral Anomaly volume rigorously breaks the Twistor Incidence relation
in the finite 2×2 algebraic model.
If the spacetime points `X` and `Y` have a vector difference whose soldered
determinant is exactly a non-zero anomaly volume `ω`, they cannot both be incident
to the same non-degenerate twistor, forcing lightrays into a massive Robinson congruence.
-/
theorem anomaly_breaks_incidence (ω : ChiralAnomalyVolume) (hω : ω ≠ 0)
    (Z : Twistor) (X Y : Vec22)
    (h_mass : q22 (X - Y) = ω) :
    ¬ (Incident Z X ∧ Incident Z Y ∧ Z.2 ≠ 0) := by
  intro h
  rcases h with ⟨hX, hY, hZ2⟩
  have h_null := incident_points_null_separated Z X Y hX hY hZ2
  rw [h_mass] at h_null
  exact hω h_null.symm

/--
Bridge to the Amplituhedron Tensor Tower Colimit.
We define an anomaly inclusion map from the 2×2 spacetime difference into the
4×n kinematic Amplituhedron algebra. For n ≥ 1, the 4 components of the spacetime
difference are mapped to the first column.
-/
def anomalyAmplituhedronBridge (n : ℕ) : 
    Vec22 →ₗ[ℝ] AmplituhedronAlgebra (n + 1) where
  toFun X i j := 
    if hj : j.val = 0 then
      if i.val = 0 then X 0 0
      else if i.val = 1 then X 0 1
      else if i.val = 2 then X 1 0
      else X 1 1
    else 0
  map_add' X Y := by
    ext i j
    by_cases hj : j.val = 0
    · simp only [hj, dif_pos]
      by_cases h0 : i.val = 0
      · simp [h0]
      by_cases h1 : i.val = 1
      · simp [h0, h1]
      by_cases h2 : i.val = 2
      · simp [h0, h1, h2]
      · simp [h0, h1, h2]
    · simp [hj]
  map_smul' c X := by
    ext i j
    by_cases hj : j.val = 0
    · simp only [hj, dif_pos]
      by_cases h0 : i.val = 0
      · simp [h0]
      by_cases h1 : i.val = 1
      · simp [h0, h1]
      by_cases h2 : i.val = 2
      · simp [h0, h1, h2]
      · simp [h0, h1, h2]
    · simp [hj]

/--
The anomaly bridge commutes with the amplituhedron tensor tower inclusion.
-/
theorem anomalyAmplituhedronBridge_comm (n : ℕ) (X : Vec22) :
    amplituhedronInclusion (n + 1) (anomalyAmplituhedronBridge n X) = 
    anomalyAmplituhedronBridge (n + 1) X := by
  ext i j
  dsimp [anomalyAmplituhedronBridge, amplituhedronInclusion]
  by_cases h_j_n1 : (j : Fin (n + 2)).val ≤ n
  · rw [dif_pos h_j_n1]
    by_cases h_j0 : j.val = 0
    · have h_j0_cast : (⟨j.val, by linarith⟩ : Fin (n+1)).val = 0 := h_j0
      rw [dif_pos h_j0, dif_pos h_j0_cast]
    · have h_j0_cast : (⟨j.val, by linarith⟩ : Fin (n+1)).val ≠ 0 := h_j0
      rw [dif_neg h_j0, dif_neg h_j0_cast]
  · rw [dif_neg h_j_n1]
    have h_j0 : j.val ≠ 0 := by
      intro h_eq
      rw [h_eq] at h_j_n1
      have : 0 ≤ n := Nat.zero_le n
      contradiction
    rw [dif_neg h_j0]

end InfoGeometry.Sandbox.UncertaintyAnomalySwarm.TwistorNonIncidence
