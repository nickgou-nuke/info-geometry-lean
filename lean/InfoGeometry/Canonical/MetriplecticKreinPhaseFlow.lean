import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.SuperMetriplectic.Flow

/-!
# Metriplectic brackets on the neutral para-complex phase carrier

This owner combines two structures without identifying them:

* the canonical skew form `neutralOmega` on `E ⊕ E*`, used for the reversible
  bracket;
* an independently supplied positive-semidefinite `OnsagerMetricData`, used
  for the dissipative bracket.

The canonical neutral bilinear form is split/indefinite and is therefore not
used as an Onsager metric.  This distinction is necessary for the second-law
nonnegativity theorem.

No differentiability or analytic existence theorem is asserted.  The
`omegaForce` and `metricForce` fields are typed force/gradient readouts supplied
by a concrete model.
-/

noncomputable section

namespace InfoGeometry.Canonical.MetriplecticKreinPhaseFlow

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.SuperMetriplectic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

abbrev Phase := PhaseSpaceCarrier E

/-- Observable equipped with the two force representatives used by the
reversible and dissipative sectors. -/
structure Observable where
  val : Phase → ℝ
  omegaForce : Phase → Phase
  metricForce : Phase → Phase

/-- Reversible bracket induced by the canonical neutral symplectic form. -/
def poissonBracket (F G : Observable (E := E)) (z : Phase) : ℝ :=
  neutralOmega (E := E) (F.omegaForce z) (G.omegaForce z)

/-- Dissipative bracket associated with an independently supplied Onsager
operator. -/
def metricBracket
    (L : OnsagerMetricData Phase)
    (F G : Observable (E := E)) (z : Phase) : ℝ :=
  L.pairing (F.metricForce z) (L.onsager (G.metricForce z))

/-- The reversible bracket is skew-symmetric. -/
theorem poissonBracket_skew
    (F G : Observable (E := E)) (z : Phase) :
    poissonBracket F G z = -poissonBracket G F z := by
  exact neutralOmega_skew (E := E) (F.omegaForce z) (G.omegaForce z)

/-- Every observable has vanishing reversible self-bracket. -/
theorem poissonBracket_self
    (F : Observable (E := E)) (z : Phase) :
    poissonBracket F F z = 0 := by
  simp [poissonBracket, neutralOmega_apply]

/-- The Onsager bracket is symmetric by the metric packet law. -/
theorem metricBracket_symm
    (L : OnsagerMetricData Phase)
    (F G : Observable (E := E)) (z : Phase) :
    metricBracket L F G z = metricBracket L G F z := by
  exact L.metric_symmetric (F.metricForce z) (G.metricForce z)

/-- The dissipative self-bracket is nonnegative. -/
theorem metricBracket_self_nonnegative
    (L : OnsagerMetricData Phase)
    (F : Observable (E := E)) (z : Phase) :
    0 ≤ metricBracket L F F z := by
  exact L.metric_nonnegative (F.metricForce z)

/-- Scalar observable-level metriplectic evolution readout. -/
def evolution
    (L : OnsagerMetricData Phase)
    (H S F : Observable (E := E)) (z : Phase) : ℝ :=
  poissonBracket F H z + metricBracket L F S z

/-- GENERIC energy degeneracy: if the energy force lies in the kernel of the
Onsager operator, the dissipative contribution to energy evolution vanishes. -/
theorem dissipative_energy_change_eq_zero
    (L : OnsagerMetricData Phase)
    (H S : Observable (E := E)) (z : Phase)
    (hH : L.onsager (H.metricForce z) = 0) :
    metricBracket L H S z = 0 := by
  rw [metricBracket_symm]
  unfold metricBracket
  rw [hH]
  exact L.pairing_zero_right (S.metricForce z)

/-- First-law readout: under Onsager energy degeneracy, the full evolution of
`H` vanishes. -/
theorem energy_conservation_law
    (L : OnsagerMetricData Phase)
    (H S : Observable (E := E)) (z : Phase)
    (hH : L.onsager (H.metricForce z) = 0) :
    evolution L H S H z = 0 := by
  rw [evolution, poissonBracket_self,
    dissipative_energy_change_eq_zero L H S z hH]
  simp

/-- If the entropy force is a Casimir for the reversible `H`-flow, entropy
change is purely dissipative. -/
theorem entropy_production_law
    (L : OnsagerMetricData Phase)
    (H S : Observable (E := E)) (z : Phase)
    (hS : poissonBracket S H z = 0) :
    evolution L H S S z = metricBracket L S S z := by
  simp [evolution, hS]

/-- Second-law readout: reversible entropy degeneracy plus Onsager positivity
implies nonnegative entropy evolution. -/
theorem entropy_evolution_nonnegative
    (L : OnsagerMetricData Phase)
    (H S : Observable (E := E)) (z : Phase)
    (hS : poissonBracket S H z = 0) :
    0 ≤ evolution L H S S z := by
  rw [entropy_production_law L H S z hS]
  exact metricBracket_self_nonnegative L S z

/-- The canonical neutral metric is recovered from the symplectic form and the
para-complex involution, but remains distinct from the positive Onsager
metric. -/
theorem neutral_metric_from_omega_para
    (X Y : Phase) :
    neutralOmega (E := E) (neutralParaInvolution X) Y =
      canonicalNeutralBilin (E := E) X Y :=
  neutralOmega_paraK_left X Y

/-- Package the force data into the repository's native vector-valued
`MetriplecticFlow`, for any supplied reversible phase-space vector. -/
def toMetriplecticFlow
    (L : OnsagerMetricData Phase)
    (H S : Observable (E := E)) (z : Phase)
    (reversible : Phase)
    (hH : L.onsager (H.metricForce z) = 0) :
    MetriplecticFlow Phase where
  metric := L
  entropyForce := S.metricForce z
  energyForce := H.metricForce z
  reversibleFlow := reversible
  dissipativeFlow := L.onsager (S.metricForce z)
  totalFlow := reversible + L.onsager (S.metricForce z)
  entropyProduction :=
    L.pairing (S.metricForce z) (L.onsager (S.metricForce z))
  dissipativeFlow_eq_onsager_entropy := rfl
  totalFlow_eq_reversible_add_dissipative := rfl
  energy_degeneracy := hH
  entropyProduction_eq_quadratic := rfl

/-- The vector-valued packet inherits the native second-law theorem. -/
theorem toMetriplecticFlow_entropyProduction_nonnegative
    (L : OnsagerMetricData Phase)
    (H S : Observable (E := E)) (z : Phase)
    (reversible : Phase)
    (hH : L.onsager (H.metricForce z) = 0) :
    0 ≤ (toMetriplecticFlow L H S z reversible hH).entropyProduction :=
  (toMetriplecticFlow L H S z reversible hH).entropyProduction_nonnegative

end InfoGeometry.Canonical.MetriplecticKreinPhaseFlow
