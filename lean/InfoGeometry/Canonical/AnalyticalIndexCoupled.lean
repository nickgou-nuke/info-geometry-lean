import InfoGeometry.Canonical.AnalyticalIndexCore
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Meta.Architecture

set_option linter.unnecessarySimpa false

namespace InfoGeometry.Canonical.AnalyticalIndex

open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.RicciMongeAmpere

/-
This file owns the coupled Sinkhorn/Ricci/index invariant layer built on top of
the analytical-index core.
-/

section CoupledInvariant

variable (n : Nat)
variable {X V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/--
Coupled invariant package:
thermodynamic Sinkhorn control, scalar-Ricci fixed-point collapse, and
analytical index invariance along a Dirac/grading family.
-/
@[rep_depth thermo, capstone]
def SinkhornRicciIndexInvariant
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V) : Prop :=
  (∀ k : Nat, ∀ label : PermMode n → CliffordLabel,
    trajectoryLyapunovNext n T.traj k ≤ trajectoryLyapunov n T.traj k ∧
      trajectorySelectedRoutingEpsilon n T (k + 1) label ≤ 1)
    ∧ (∀ s : ℝ, flow s = 0)
    ∧ IndexInvariantAlong D Γ

/--
Canonical constructor for the coupled invariant package from its three proved
components.
-/
@[rep_depth thermo, capstone]
theorem SinkhornRicciIndexInvariant.mk_components
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (hSinkhorn : ∀ k : Nat, ∀ label : PermMode n → CliffordLabel,
      trajectoryLyapunovNext n T.traj k ≤ trajectoryLyapunov n T.traj k ∧
        trajectorySelectedRoutingEpsilon n T (k + 1) label ≤ 1)
    (hRicciZero : ∀ s : ℝ, flow s = 0)
    (hIndex : IndexInvariantAlong D Γ) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  exact ⟨hSinkhorn, hRicciZero, hIndex⟩

/--
Derived constructor using modular-flow / Clifford-bundle transport conditions
for the chiral slices.
-/
@[rep_depth thermo, capstone]
theorem SinkhornRicciIndexInvariant.of_modularCliffordTransport
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hTrans :
      ChiralSliceModularCliffordTransportAlong (D := D) (Γ := Γ) σ clAct unit) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  refine SinkhornRicciIndexInvariant.mk_components
    (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
    ?_ ?_ ?_
  · intro k label
    exact sinkhorn_dynamics_step_control (n := n) T k label
  · exact normalizedKaehlerRicci_fixedpoint_eq_zero
      (E := X) flow hNorm hFixed
  · exact indexInvariantAlong_of_modularCliffordTransport
      (D := D) (Γ := Γ) (σ := σ) (clAct := clAct) (unit := unit) hTrans

/--
Primitive-condition form of the coupled Sinkhorn/Ricci/index invariant:
modular/Clifford transport is supplied as explicit component equalities.
-/
@[rep_depth thermo, capstone]
theorem SinkhornRicciIndexInvariant.of_modularCliffordTransport_components
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hUnit : clAct unit = LinearMap.id)
    (hσInj : ∀ s : ℝ, Function.Injective (σ s))
    (hPlusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSlicePlus (D s) (Γ s)).map ((clAct ℓ).comp (σ s))
        = chiralKernelSlicePlus (D 0) (Γ 0))
    (hMinusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSliceMinus (D s) (Γ s)).map ((clAct ℓ).comp (σ s))
        = chiralKernelSliceMinus (D 0) (Γ 0)) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  refine SinkhornRicciIndexInvariant.mk_components
    (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
    ?_ ?_ ?_
  · intro k label
    exact sinkhorn_dynamics_step_control (n := n) T k label
  · exact normalizedKaehlerRicci_fixedpoint_eq_zero
      (E := X) flow hNorm hFixed
  · exact indexInvariantAlong_of_modularCliffordTransport_components
      (D := D) (Γ := Γ) (σ := σ) (clAct := clAct) (unit := unit)
      hUnit hσInj hPlusMap hMinusMap

/--
Derived constructor using primitive flow-conjugacy conditions:
the Dirac/grading family is transported to baseline by linear equivalences.
-/
@[rep_depth thermo, capstone]
theorem SinkhornRicciIndexInvariant.of_conjugacy
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (eFlow : ℝ → V ≃ₗ[ℝ] V)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hConj : ChiralConjugacyAlong D Γ eFlow) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  refine SinkhornRicciIndexInvariant.mk_components
    (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
    ?_ ?_ ?_
  · intro k label
    exact sinkhorn_dynamics_step_control (n := n) T k label
  · exact normalizedKaehlerRicci_fixedpoint_eq_zero
      (E := X) flow hNorm hFixed
  · exact indexInvariantAlong_of_conjugacy
      (D := D) (Γ := Γ) (eFlow := eFlow) hConj

end CoupledInvariant

end InfoGeometry.Canonical.AnalyticalIndex
