import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Canonical.ThermodynamicGenerator
import InfoGeometry.Canonical.MajoranaKreinCartanSplit
import InfoGeometry.Canonical.KreinDiracWeightFunctionalLift
import InfoGeometry.Canonical.SouriauPlanckVector

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.DensityWeightIntertwinerBridge

Repo-native translation layer for density-weight language.

This file is intentionally a bridge rather than a new ontology. It records the
current multilingual correspondence:

- on the count/projective side, a density weight acts as an additive projective
  mass-shift correction to the canonical count Hamiltonian profile;
- on the doubled Hestenes/Krein carrier, the weight correction is carried by
  the internal phase/dilation axis `K = Jε`;
- and the currently owned nontrivial intertwiner surface for weight sectors is
  the transported Weyl plus/minus equivalence under strict symmetry.

This matches the present repo state honestly: arbitrary density-weight module
equivalences are not yet primitive owners, but the projective, Krein, and Weyl
weight presentations already exist and can be tied together canonically.
-/

namespace InfoGeometry.Canonical.DensityWeightIntertwinerBridge

open InfoGeometry.Canonical.RelativePotentialCountBridge
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.ThermodynamicGenerator
open InfoGeometry.Canonical.StateDependentTransport
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.KreinDiracWeightFunctionalLift
open InfoGeometry.Krein
open InfoGeometry.Quantum.RealMajorana

section CountProjective

variable {n : Nat} [Nonempty (Fin n)]

/-- Critical density weights in the Duval–Ovsienko sense. -/
@[rep_depth projective]
def IsCriticalDensityWeight (w : ℝ) : Prop :=
  w = 0 ∨ w = (1 : ℝ) / 2 ∨ w = 1

@[rep_depth projective] theorem isCriticalDensityWeight_zero :
    IsCriticalDensityWeight 0 := by
  left
  rfl

@[rep_depth projective] theorem isCriticalDensityWeight_half :
    IsCriticalDensityWeight ((1 : ℝ) / 2) := by
  right
  left
  rfl

@[rep_depth projective] theorem isCriticalDensityWeight_one :
    IsCriticalDensityWeight 1 := by
  right
  right
  rfl

/--
Weighted projective Hamiltonian profile.

This is the current projective/count-side avatar of a density-weight shift:
the canonical projective Hamiltonian profile plus the global projective
mass-shift correction scaled by the density weight.
-/
@[rep_depth projective]
noncomputable def projectiveDensityWeightHamiltonianProfile
    (w : ℝ)
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) : Fin n → ℝ :=
  fun i =>
    projectiveCountHamiltonianProfile counts ref hcounts href i
      + w * countMassShift counts ref hcounts href

@[rep_depth projective, simp]
theorem projectiveDensityWeightHamiltonianProfile_zero
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) :
    projectiveDensityWeightHamiltonianProfile 0 counts ref hcounts href
      =
    projectiveCountHamiltonianProfile counts ref hcounts href := by
  funext i
  unfold projectiveDensityWeightHamiltonianProfile
  ring

@[rep_depth projective]
theorem projectiveDensityWeightHamiltonianProfile_eq_relativeModularPotential_countRay_add_weightShift
    (w : ℝ)
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (i : Fin n) :
    projectiveDensityWeightHamiltonianProfile w counts ref hcounts href i
      =
    relativeModularPotential (α := Fin n)
      (countRay counts hcounts) (countRay ref href) i
      + w * countMassShift counts ref hcounts href := by
  unfold projectiveDensityWeightHamiltonianProfile
  rw [projectiveCountHamiltonianProfile_eq_relativeModularPotential_countRay]

end CountProjective

section DoubledCarrier

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Density-weight phase axis on the doubled carrier.

This is the Hestenes/Krein replacement for the external complex density phase:
the internal axis `K = Jε`.
-/
@[rep_depth krein]
noncomputable def densityWeightPhaseAxis : EndH :=
  modularComplexI (E := E)

@[rep_depth krein, simp] theorem densityWeightPhaseAxis_eq_complex_i :
    densityWeightPhaseAxis = complex_i (E := E) := by
  simp [densityWeightPhaseAxis]

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem densityWeightPhaseAxis_eq_modularComplexI :
    densityWeightPhaseAxis = modularComplexI (E := E) := rfl

attribute [deprecated densityWeightPhaseAxis_eq_complex_i (since := "2026-04-11")]
  densityWeightPhaseAxis_eq_modularComplexI

@[rep_depth krein, simp] theorem densityWeightPhaseAxis_eq_dilationOperator :
    densityWeightPhaseAxis = dilationOperator (E := E) := by
  exact modularComplexI_eq_dilationOperator (E := E)

/--
Weighted transport generator on the doubled carrier.

This is the thin Hestenes/Krein lift of density-weight language on the
generator side: the existing Souriau temperature vector plus a weight-scaled
copy of the internal phase/dilation axis.
-/
@[rep_depth transport]
noncomputable def densityWeightLiftedTransportGenerator
    (P : PotentialDatum (E := E)) (ψ : H₂) (w : ℝ) : EndH :=
  souriauTemperatureVector (E := E) P ψ + w • densityWeightPhaseAxis

/-- Legacy name retained as a compatibility alias for the weighted generator surface. -/
@[rep_depth transport]
noncomputable abbrev densityWeightLiftedModularSeed
    (P : PotentialDatum (E := E)) (ψ : H₂) (w : ℝ) : EndH :=
  densityWeightLiftedTransportGenerator (E := E) P ψ w

@[rep_depth transport, simp]
theorem densityWeightLiftedTransportGenerator_zero
    (P : PotentialDatum (E := E)) (ψ : H₂) :
    densityWeightLiftedTransportGenerator P ψ 0
      =
    souriauTemperatureVector (E := E) P ψ := by
  unfold densityWeightLiftedTransportGenerator
  rw [show (0 : ℝ) • densityWeightPhaseAxis (E := E) = 0 by
    ext x <;> simp]
  simp

@[rep_depth transport]
theorem densityWeightLiftedTransportGenerator_eq_souriau_add_weighted_dilation
    (P : PotentialDatum (E := E)) (ψ : H₂) (w : ℝ) :
    densityWeightLiftedTransportGenerator P ψ w
      =
    souriauTemperatureVector (E := E) P ψ
      + w • dilationOperator (E := E) := by
  unfold densityWeightLiftedTransportGenerator
  rw [densityWeightPhaseAxis_eq_dilationOperator (E := E)]

@[rep_depth transport, simp]
theorem densityWeightLiftedModularSeed_eq_transportGenerator
    (P : PotentialDatum (E := E)) (ψ : H₂) (w : ℝ) :
    densityWeightLiftedModularSeed (E := E) P ψ w
      =
    densityWeightLiftedTransportGenerator (E := E) P ψ w := rfl

/-- Weighted modular derivation/readout seed. -/
@[rep_depth transport]
noncomputable def densityWeightLiftedDynamics
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) (w : ℝ) : EndH :=
  transportCommutator (E := E)
    (densityWeightLiftedTransportGenerator (E := E) P ψ w) A

@[rep_depth transport, simp]
theorem densityWeightLiftedDynamics_zero
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    densityWeightLiftedDynamics P ψ A 0
      =
    transportCommutator (E := E) (souriauTemperatureVector (E := E) P ψ) A := by
  unfold densityWeightLiftedDynamics
  rw [densityWeightLiftedTransportGenerator_zero (E := E) (P := P) (ψ := ψ)]

/--
Weighted metric/phase readout on the doubled carrier, packaged through the
existing operatorial metric/phase surface of the weighted dynamics.
-/
@[rep_depth transport]
noncomputable def densityWeightLiftedReadout
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) (w : ℝ) :
    StateQGTReadout E :=
  { metric :=
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E) (densityWeightLiftedDynamics (E := E) P ψ A w)
    phase :=
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E) (densityWeightLiftedDynamics (E := E) P ψ A w) }

@[rep_depth transport]
theorem densityWeightLiftedReadout_zero_apply_eq_metricPhase_transportCommutator
    (P : PotentialDatum (E := E)) (ψ u v : H₂) (A : EndH) :
    ( (densityWeightLiftedReadout P ψ A 0).metric u v
    , (densityWeightLiftedReadout P ψ A 0).phase u v )
      =
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (souriauTemperatureVector (E := E) P ψ) A) u v
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (souriauTemperatureVector (E := E) P ψ) A) u v ) := by
  unfold densityWeightLiftedReadout
  rw [densityWeightLiftedDynamics_zero (E := E) (P := P) (ψ := ψ) (A := A)]

/--
Zero-weight density-lifted readout is exactly the comparison-state thermodynamic
readout.
-/
@[rep_depth transport]
theorem densityWeightLiftedReadout_zero_pair_eq_comparisonReadout_pair
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    ((densityWeightLiftedReadout (E := E) P ψ A 0).metric,
      (densityWeightLiftedReadout (E := E) P ψ A 0).phase)
      =
    (comparisonMetricReadout (E := E) P ψ A,
      comparisonPhaseReadout (E := E) P ψ A) := by
  apply Prod.ext
  · ext u v
    simp [densityWeightLiftedReadout, densityWeightLiftedDynamics_zero,
      StateDependentTransport.stateInducedDynamics,
      StateDependentTransport.stateTransportGenerator,
      StateDependentTransport.stateRelativeModularGenerator,
      BogoliubovTransport.relativeModularDeriv,
      BogoliubovTransport.relativeModularKGenerator,
      BogoliubovTransport.modularDeriv,
      BogoliubovTransport.modularTransportGenerator,
      comparisonMetricReadout_apply]
  · ext u v
    simp [densityWeightLiftedReadout, densityWeightLiftedDynamics_zero,
      StateDependentTransport.stateInducedDynamics,
      StateDependentTransport.stateTransportGenerator,
      StateDependentTransport.stateRelativeModularGenerator,
      BogoliubovTransport.relativeModularDeriv,
      BogoliubovTransport.relativeModularKGenerator,
      BogoliubovTransport.modularDeriv,
      BogoliubovTransport.modularTransportGenerator]

/--
A Gibbs-Souriau equilibrium seed forces the zero-weight density-lifted readout
packet to vanish.

This is an infinite operatorial theorem: it stays on the doubled carrier and
reuses the already-owned equilibrium-to-readout-stationarity route rather than
introducing any finite response matrix.
-/
@[rep_depth transport]
theorem densityWeightLiftedReadout_zero_pair_eq_zero_of_equilibriumSeed
    {P : PotentialDatum (E := E)} {ψ : H₂} {A : EndH}
    (hEq : InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed (E := E) P ψ A) :
    ((densityWeightLiftedReadout (E := E) P ψ A 0).metric,
      (densityWeightLiftedReadout (E := E) P ψ A 0).phase)
      = (0, 0) := by
  rw [densityWeightLiftedReadout_zero_pair_eq_comparisonReadout_pair (E := E) P ψ A]
  exact InfoGeometry.Canonical.SouriauPlanckVector.comparisonReadout_pair_eq_zero_of_equilibriumSeed
    (E := E) hEq

end DoubledCarrier

section WeylIntertwiners

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {M : RealMajoranaDatum (S := DoubledSpace E)}

local notation "H₂" => DoubledSpace E

/--
Current repo-native intertwiner surface for density/weight presentations.

This is the honest present counterpart of the paper's generic weight-module
equivalence: strict symmetry induces explicit transported Weyl plus/minus
equivalences on the doubled Majorana carrier.
-/
@[rep_depth transport]
noncomputable def densityWeightWeylIntertwiners_of_strictSymmetry
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    (M.weylPlus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylPlus) ×
    (M.weylMinus ≃ₗ[ℝ] (h.toBogoliubovTransform).transportWeylMinus) :=
  transportWeylWeightEquivs_of_strictSymmetry (M := M) h

@[rep_depth transport, simp]
theorem densityWeightWeylIntertwiners_of_strictSymmetry_fst
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    (densityWeightWeylIntertwiners_of_strictSymmetry (E := E) (M := M) h).1
      =
    transportWeylPlusEquiv_of_strictSymmetry (M := M) h := rfl

@[rep_depth transport, simp]
theorem densityWeightWeylIntertwiners_of_strictSymmetry_snd
    {X Y : PolarizedMajorana (S := H₂) M} (h : X ⟶ Y) :
    (densityWeightWeylIntertwiners_of_strictSymmetry (E := E) (M := M) h).2
      =
    transportWeylMinusEquiv_of_strictSymmetry (M := M) h := rfl

end WeylIntertwiners

end InfoGeometry.Canonical.DensityWeightIntertwinerBridge
