import Mathlib.Tactic
import InfoGeometry.Canonical.MasterFiniteBridgeLedger
import InfoGeometry.Canonical.GrandSynthesis

/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
-/

namespace InfoGeometry.Canonical

/-
MasterSynthesis is an owner-level synthesis packet that combines existing finite
ledger identities with the existing GrandSynthesis closure scaffold.
-/

open MasterFiniteBridgeLedger
open InfinitesimalDictionaryBridge
open KLDivergenceDecomposition
open MaximumCaliberKLSplit
open BuresMetricStabilization
open TensorColimitExpectation
open InfoGeometry.Topology.ThermodynamicGauge

section FinitePacket

variable {State : Type*} {Θ V Op Alg X : Type*}
variable [AddCommGroup V] [AddGroup Op] [Ring Alg]
variable (P : InfinitesimalDictionaryPacket Θ V State Op Alg X)

/--
Finite bridge packet is preserved verbatim as a synthesis lemma for downstream
assembly files.
-/
theorem master_infinitesimal_dictionary_packet (θ : Θ) (ω φ : State) :
    P.logPartition.info.Ψ θ = Real.log (P.logPartition.Q θ) ∧
      entropy_production P.gauge.flow = P.gauge.flow.d_ln_Q ∧
      InfoGeometry.Canonical.ArakiItakuraSaitoCollapse.restrictedAraki (fun s t => P.divergence s t) ω φ =
        P.operatorPacket.divergence (P.toOperator ω) (P.toOperator φ) ∧
      P.divergence ω φ = symmetricDivergence P.divergence ω φ +
        antisymmetricDivergence P.divergence ω φ ∧
      antisymmetricDivergence P.divergence φ ω =
        -antisymmetricDivergence P.divergence ω φ := by
  exact infinitesimal_dictionary_packet (P := P) θ ω φ

/--
Finite KL decomposition packet is re-exported as part of the synthesis surface.
-/
theorem master_kl_split_packet (D : State → State → ℝ) (p q : State) :
    D p q = symmetricPart D p q + antisymmetricPart D p q ∧
      D q p = symmetricPart D p q - antisymmetricPart D p q ∧
      symmetricPart D q p = symmetricPart D p q ∧
      antisymmetricPart D q p = -antisymmetricPart D p q := by
  exact kl_split_packet (State := State) D p q

/--
Bures readback packet preserved as a finite synthesis block.
-/
theorem master_bures_stabilization_packet
    {R : Type*} [CommSemiring R] {A : ℕ → Type*}
    [∀ n, Semiring (A n)] [∀ n, Algebra R (A n)]
    {bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1)}
    {L : TensorInductiveLimit (R := R) (A := A) bond}
    (B : BuresMetricStabilizationBridge L)
    (n : ℕ) :
    (B.BW (n + 1)).squaredDist (B.rho (n + 1)) (B.sigma (n + 1)) =
      (B.BW n).squaredDist (B.rho n) (B.sigma n) ∧
    B.BWInf.squaredDist (B.toLimitState n (B.rho n)) (B.toLimitState n (B.sigma n)) =
      (B.BW n).squaredDist (B.rho n) (B.sigma n) := by
  exact bures_stabilization_packet (L := L) (B := B) n

end FinitePacket

section GrandPacket

open InfoGeometry.Canonical.GrandSynthesis

/--
GrandSynthesis canopy packet is available under the synthesis surface name.
-/
theorem master_thermo_canopy_packet (n : Nat)
    (P : ThermoCanopyPackage n) :
    ThermodynamicEquilibrium n P.trajectory ∧
      SinkhornEntropyMonotoneRN n P.trajectory.traj := by
  exact canopy_thermo_equilibrium_and_entropy (n := n) P

/--
Coupled finite/infinite synthesis packet: finite entropy dictionary data together
with thermodynamic canopy closure.
-/
theorem master_synthesis_packet
    {Θ V State Op Alg X : Type*}
    [AddCommGroup V] [AddGroup Op] [Ring Alg]
    (P : InfinitesimalDictionaryPacket Θ V State Op Alg X)
    (θ : Θ) (ω φ : State)
    (n : Nat) (C : ThermoCanopyPackage n) :
    P.logPartition.info.Ψ θ = Real.log (P.logPartition.Q θ) ∧
      entropy_production P.gauge.flow = P.gauge.flow.d_ln_Q ∧
      InfoGeometry.Canonical.ArakiItakuraSaitoCollapse.restrictedAraki (fun s t => P.divergence s t) ω φ =
        P.operatorPacket.divergence (P.toOperator ω) (P.toOperator φ) ∧
      P.divergence ω φ = symmetricDivergence P.divergence ω φ +
        antisymmetricDivergence P.divergence ω φ ∧
      antisymmetricDivergence P.divergence φ ω =
        -antisymmetricDivergence P.divergence ω φ ∧
      ThermodynamicEquilibrium n C.trajectory ∧
      SinkhornEntropyMonotoneRN n C.trajectory.traj := by
  have hfinite := infinitesimal_dictionary_packet (P := P) θ ω φ
  have hgrand := canopy_thermo_equilibrium_and_entropy (n := n) C
  exact ⟨hfinite.1, hfinite.2.1, hfinite.2.2.1, hfinite.2.2.2.1,
    hfinite.2.2.2.2, hgrand.1, hgrand.2⟩

end GrandPacket

end InfoGeometry.Canonical
