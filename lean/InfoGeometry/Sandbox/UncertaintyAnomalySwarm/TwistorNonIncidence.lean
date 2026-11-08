import Mathlib.Tactic
import InfoGeometry.Twistor.Incidence
import InfoGeometry.Quantum.PauliSoldering
import InfoGeometry.Topology.AmplituhedronTensorTowerColimit

namespace InfoGeometry.Sandbox.UncertaintyAnomalySwarm.TwistorNonIncidence

open InfoGeometry.Twistor.Incidence
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Topology.AmplituhedronColimit
open InfoGeometry.Clifford.Soldering

private def vec22Coord (X : Vec22) : Fin 4 → ℝ
  | 0 => X.1
  | 1 => X.2.1
  | 2 => X.2.2.1
  | 3 => X.2.2.2

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
  exact hω h_null

/--
Bridge to the Amplituhedron Tensor Tower Colimit.
We define an anomaly inclusion map from the 2×2 spacetime difference into the
4×n kinematic Amplituhedron algebra. For n ≥ 1, the 4 components of the spacetime
difference are mapped to the first column.
-/
def anomalyAmplituhedronBridge (n : ℕ) : 
    Vec22 →ₗ[ℝ] AmplituhedronAlgebra (n + 1) where
  toFun X := Matrix.of fun i j => if j.val = 0 then vec22Coord X i else 0
  map_add' X Y := by
    ext i j
    by_cases hj : j.val = 0
    · have hj' : j = 0 := Fin.ext hj
      simp [hj', vec22Coord]
      fin_cases i <;> ring
    · have hj' : j ≠ 0 := fun h => hj (congrArg Fin.val h)
      simp [hj']
  map_smul' c X := by
    ext i j
    by_cases hj : j.val = 0
    · have hj' : j = 0 := Fin.ext hj
      simp [hj', vec22Coord, smul_eq_mul]
      fin_cases i <;> ring
    · have hj' : j ≠ 0 := fun h => hj (congrArg Fin.val h)
      simp [hj']

/--
The anomaly bridge commutes with the amplituhedron tensor tower inclusion.
-/
theorem anomalyAmplituhedronBridge_comm (n : ℕ) (X : Vec22) :
    amplituhedronInclusion (n + 1) (anomalyAmplituhedronBridge n X) = 
    anomalyAmplituhedronBridge (n + 1) X := by
  ext i j
  dsimp [anomalyAmplituhedronBridge, amplituhedronInclusion]
  by_cases h_j_n1 : (j : Fin (n + 2)).val ≤ n
  · have h_lt : (j : Fin (n + 2)).val < n + 1 := by omega
    simp [h_lt]
  · have h_ne : (j : Fin (n + 2)).val ≠ 0 := by omega
    simp [h_ne]

end InfoGeometry.Sandbox.UncertaintyAnomalySwarm.TwistorNonIncidence
