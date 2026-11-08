import InfoGeometry.Physics.WittenOddSquareEvenBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.BayesianTuringCantor
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge

namespace InfoGeometry.Physics

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Physics.BayesianTuringCantor
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge

/-!
# Supergraded Dirac Cantor/Turing bridge

This file exposes direct readout and transport theorems over the existing
Cantor boundary and Bayesian/Turing owners.  It does not introduce a packet
whose fields merely restate those owners' hypotheses.
-/

noncomputable section

abbrev continuumTape
    {VInf : Type*}
    (continuum : VInf → TuringTape)
    (z : VInf) : TuringTape :=
  continuum z

def observedPrefixProgram
    {VInf : Type*}
    (continuum : VInf → TuringTape)
    (n : ℕ) (z : VInf) : FiniteProgram n :=
  InfoGeometry.Physics.BayesianTuringCantor.FiniteTapePrior.atomEvent
    (boundaryPrefix n (continuumTape continuum z))

theorem continuumTape_mem_observedPrefixProgram
    {VInf : Type*}
    (continuum : VInf → TuringTape)
    (n : ℕ) (z : VInf) :
    continuumTape continuum z ∈
      programCylinder n (observedPrefixProgram continuum n z) := by
  rw [mem_programCylinder_iff, observedPrefixProgram,
    InfoGeometry.Physics.BayesianTuringCantor.FiniteTapePrior.atomEvent]
  rfl

theorem continuumPrefix_tapeShift
    {VInf : Type*}
    (continuum : VInf → TuringTape)
    (n : ℕ) (z : VInf) (i : Fin n) :
    boundaryPrefix n (tapeShift (continuumTape continuum z)) i =
      boundaryPrefix (n + 1) (continuumTape continuum z)
        ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ :=
  boundaryPrefix_tapeShift n (continuumTape continuum z) i

def turingStageToContinuum
    {V VInf : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup VInf] [Module ℚ VInf]
    (map : V →ₗ[ℚ] VInf)
    (continuum : VInf → TuringTape) :
    V → TuringTape :=
  continuum ∘ map

theorem turingStageToContinuum_surjective
    {V VInf : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup VInf] [Module ℚ VInf]
    (map : V →ₗ[ℚ] VInf)
    (continuum : VInf → TuringTape)
    (map_surjective : Function.Surjective map)
    (continuum_surjective : Function.Surjective continuum) :
    Function.Surjective (turingStageToContinuum map continuum) := by
  intro ξ
  obtain ⟨z, rfl⟩ := continuum_surjective ξ
  obtain ⟨x, rfl⟩ := map_surjective z
  exact ⟨x, rfl⟩

theorem turing_target_hamiltonian_even
    {V VInf : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup VInf] [Module ℚ VInf]
    (stage : SupergradedDiracSystem V)
    (hstage : SupergradedDiracLaws stage)
    (targetGamma targetH : VInf →ₗ[ℚ] VInf)
    (map : V →ₗ[ℚ] VInf)
    (map_surjective : Function.Surjective map)
    (gamma_intertwines : ∀ x, map (stage.Gamma x) = targetGamma (map x))
    (hamiltonian_intertwines : ∀ x, map (stage.H x) = targetH (map x)) :
    targetGamma.comp targetH = targetH.comp targetGamma :=
  InfoGeometry.Physics.target_hamiltonian_even stage hstage targetGamma targetH map
    map_surjective gamma_intertwines hamiltonian_intertwines

theorem turing_target_witten_odd
    {V VInf : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup VInf] [Module ℚ VInf]
    (stage : SupergradedDiracSystem V)
    (hstage : SupergradedDiracLaws stage)
    (targetGamma targetQ : VInf →ₗ[ℚ] VInf)
    (map : V →ₗ[ℚ] VInf)
    (map_surjective : Function.Surjective map)
    (gamma_intertwines : ∀ x, map (stage.Gamma x) = targetGamma (map x))
    (charge_intertwines : ∀ x, map (stage.Q x) = targetQ (map x)) :
    targetGamma.comp targetQ = - targetQ.comp targetGamma :=
  InfoGeometry.Physics.target_witten_odd stage hstage targetGamma targetQ map
    map_surjective gamma_intertwines charge_intertwines

theorem turing_target_susy_algebra
    {V VInf : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup VInf] [Module ℚ VInf]
    (stage : SupergradedDiracSystem V)
    (hstage : SupergradedDiracLaws stage)
    (targetQ targetH : VInf →ₗ[ℚ] VInf)
    (map : V →ₗ[ℚ] VInf)
    (map_surjective : Function.Surjective map)
    (charge_intertwines : ∀ x, map (stage.Q x) = targetQ (map x))
    (hamiltonian_intertwines : ∀ x, map (stage.H x) = targetH (map x)) :
    targetQ.comp targetQ = targetH :=
  InfoGeometry.Physics.target_susy_algebra stage hstage targetQ targetH map
    map_surjective charge_intertwines hamiltonian_intertwines

end
end InfoGeometry.Physics
