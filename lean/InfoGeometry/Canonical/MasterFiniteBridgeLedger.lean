import Mathlib
import InfoGeometry.Canonical.BayesianThermoMetricHodgeBridge
import InfoGeometry.Canonical.BuresMetricStabilization
import InfoGeometry.Canonical.InfinitesimalDictionaryBridge
import InfoGeometry.Canonical.KLDivergenceDecomposition
import InfoGeometry.Canonical.MaximumCaliberKLSplit
import InfoGeometry.Canonical.MaximumCaliberPath
import InfoGeometry.Canonical.BayesianHodgeCurrent
import InfoGeometry.Canonical.BayesianDiscreteHodgeBridge
import InfoGeometry.Topology.ThermodynamicGauge
import InfoGeometry.Topology.DiscreteHodgeStabilizer
import InfoGeometry.Topology.EckmannDiscreteHodge
import InfoGeometry.Canonical.KleinBottleWallpaper
import InfoGeometry.Canonical.WallpaperPin55SummaryLedger

/-!
# Master finite bridge ledger

Theorem-honest finite summary surface tying together the already-verified lanes:

* KL symmetric/antisymmetric decomposition;
* infinitesimal log-partition / modular / entropy dictionary;
* Bures/Wasserstein stabilization on a compatible tensor tower;
* Maximum Caliber / Bayesian Markov readbacks;
* discrete Hodge/stabilizer protection; and
* Klein-compatible wallpaper / `D₅` / `O(5,5)` cross-section data.

This file introduces no new mathematical objects. It only assembles existing,
verified owner theorems into one compact ledger packet.
-/

namespace MasterFiniteBridgeLedger

open InfoGeometry.Canonical.KLDivergenceDecomposition
open InfoGeometry.Canonical.InfinitesimalDictionaryBridge
open InfoGeometry.Canonical.BayesianThermoMetricHodgeBridge
open InfoGeometry.Canonical.BuresMetricStabilization
open InfoGeometry.Canonical.MaximumCaliberPath
open InfoGeometry.Canonical.MaximumCaliberKLSplit
open InfoGeometry.Canonical.BayesianHodgeCurrent
open InfoGeometry.Canonical.BayesianDiscreteHodgeBridge
open InfoGeometry.Topology.ThermodynamicGauge
open InfoGeometry.Topology.DiscreteHodgeStabilizer
open InfoGeometry.Topology.EckmannDiscreteHodge
open InfoGeometry.Canonical.KleinBottleWallpaper
open InfoGeometry.Canonical.WallpaperPin55SummaryLedger
open InfoGeometry.Canonical.WallpaperPin55RootCrossSection
open InfoGeometry.Canonical.TensorColimitExpectation

universe u v w

section KLLedger

variable {State : Type u}

/-- The directed divergence splits into symmetric and antisymmetric halves. -/
theorem kl_split_packet
    (D : State → State → ℝ) (p q : State) :
    D p q = symmetricPart D p q + antisymmetricPart D p q ∧
      D q p = symmetricPart D p q - antisymmetricPart D p q ∧
      symmetricPart D q p = symmetricPart D p q ∧
      antisymmetricPart D q p = -antisymmetricPart D p q := by
  exact ⟨KLDivergenceDecomposition.divergence_eq_symmetric_add_antisymmetric D p q,
    reverse_divergence_eq_symmetric_sub_antisymmetric D p q,
    symmetricPart_swap D p q,
    antisymmetricPart_swap D p q⟩

end KLLedger

section DictionaryLedger

variable {Θ V State Op Alg X : Type*}
variable [AddCommGroup V] [AddGroup Op] [Ring Alg]
variable (P : InfinitesimalDictionaryPacket Θ V State Op Alg X)

/-- Compact finite packet for the infinitesimal dictionary lane. -/
theorem infinitesimal_dictionary_packet (θ : Θ) (ω φ : State) :
    P.logPartition.info.Ψ θ = Real.log (P.logPartition.Q θ) ∧
      entropy_production P.gauge.flow = P.gauge.flow.d_ln_Q ∧
      InfoGeometry.Canonical.ArakiItakuraSaitoCollapse.restrictedAraki (fun s t => P.divergence s t) ω φ =
        P.operatorPacket.divergence (P.toOperator ω) (P.toOperator φ) ∧
      P.divergence ω φ = symmetricDivergence P.divergence ω φ +
        antisymmetricDivergence P.divergence ω φ ∧
      antisymmetricDivergence P.divergence φ ω =
        -antisymmetricDivergence P.divergence ω φ := by
  exact ⟨P.psi_eq_logQ θ,
    P.entropy_production_eq_dlnQ,
    P.restrictedAraki_eq_operatorPacket ω φ,
    P.divergence_eq_symmetric_add_antisymmetric ω φ,
    P.antisymmetric_swap ω φ⟩

end DictionaryLedger

section BuresLedger

variable {R : Type u} [CommSemiring R]
variable {A : ℕ → Type v}
variable [∀ n, Semiring (A n)] [∀ n, Algebra R (A n)]
variable {bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1)}
variable {L : TensorInductiveLimit (R := R) (A := A) bond}
variable (B : BuresMetricStabilizationBridge L)

/-- The Bures/Wasserstein cost is stable under one stage step and reads back from the limit. -/
theorem bures_stabilization_packet (n : ℕ) :
    (B.BW (n + 1)).squaredDist (B.rho (n + 1)) (B.sigma (n + 1)) =
      (B.BW n).squaredDist (B.rho n) (B.sigma n) ∧
    B.BWInf.squaredDist (B.toLimitState n (B.rho n)) (B.toLimitState n (B.sigma n)) =
      (B.BW n).squaredDist (B.rho n) (B.sigma n) := by
  exact ⟨B.bures_cost_one_step_stable n, B.bures_cost_limit_reads_stage n⟩

end BuresLedger

section IntegratedLedger

variable {Θ V State Op Alg X : Type*}
variable [AddCommGroup V] [AddGroup Op] [Ring Alg]
variable (P : InfinitesimalDictionaryPacket Θ V State Op Alg X)

variable {n0 n1 n2 : ℕ}

/-- Integrated finite packet: scalar `d log Q`, protected harmonic posterior, and coexact current. -/
theorem integrated_bridge_packet
    (ω φ : State)
    (hcal : antisymmetricDivergence P.divergence ω φ = P.pathConstraintScalar)
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {prior posterior exactErr coexactErr : EdgeCurrent n1}
    (hproj : BayesianProjectionReadout T (IsProtectedHarmonicCurrent d0 d1) prior posterior)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr)
    (C : CoexactMaxCalCurrentReadout (n0 := n0) (n1 := n1) (n2 := n2)) :
    antisymmetricDivergence P.divergence ω φ = P.pathReadout P.gauge.flow.d_ln_Q ∧
      eckmannDot posterior exactErr = 0 ∧
      eckmannDot posterior coexactErr = 0 ∧
      C.currentReadout C.current = C.flow.d_ln_Q := by
  exact ⟨antisymmetric_eq_scalar_dlnQ_of_calibration P ω φ hcal,
    (posterior_harmonic_protected d0 d1 T hproj hexact hcoexact).1,
    (posterior_harmonic_protected d0 d1 T hproj hexact hcoexact).2,
    coexact_current_eq_dlnQ C⟩

end IntegratedLedger

section WallpaperLedger

/-- Compact finite wallpaper / root / metric packet. -/
theorem wallpaper_packet (g r : Fin 8) (b d : ℝ) :
    IsCompatibleSymmetry (trans_y b) ∧
      IsCompatibleSymmetry (parallel_glide d) ∧
      IsCompatibleSymmetry rot_180 ∧
      IsCompatibleSymmetry mirror_perp ∧
      ¬ IsCompatibleSymmetry rot_90 ∧
      IsWallpaperB2Root (wallpaperB2Root r) := by
  exact ⟨pg_translation_lane b,
    pg_or_pgg_parallel_glide_lane d,
    pgg_half_turn_lane,
    pmg_perpendicular_mirror_lane,
    quarter_turn_excluded,
    visible_wallpaper_root_is_b2c2 r⟩

end WallpaperLedger

end MasterFiniteBridgeLedger
