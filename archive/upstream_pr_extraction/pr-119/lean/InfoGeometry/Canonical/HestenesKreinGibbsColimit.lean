import Mathlib.Tactic
import InfoGeometry.Thermo.Gibbs
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

/-!
# Finite Gibbs readouts on the Hestenes--Krein colimit

This owner translates the finite Gibbs/log-partition interface into native
real readouts on a filtered Hestenes--Krein cone.  The Gibbs identity and the
surprisal formula are finite theorems; compatibility with the colimit is an
explicit readout premise.  No thermodynamic limit or analytic continuation is
asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinGibbsColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Thermo
open InfoGeometry.Krein

variable {C : HestenesKreinCone}
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def stageGibbsProb
    (energy : ∀ n, Ω → DoubledSpace (C.Base n) → ℝ)
    (ε : ℝ) (n : ℕ) (ω : Ω) (x : DoubledSpace (C.Base n)) : ℝ :=
  gibbsProb (fun ω' => energy n ω' x) ε ω

def limitGibbsProb
    (energy : Ω → DoubledSpace C.LimitBase → ℝ)
    (ε : ℝ) (ω : Ω) (x : DoubledSpace C.LimitBase) : ℝ :=
  gibbsProb (fun ω' => energy ω' x) ε ω

def stageSurprisal
    (energy : ∀ n, Ω → DoubledSpace (C.Base n) → ℝ)
    (ε : ℝ) (n : ℕ) (ω : Ω) (x : DoubledSpace (C.Base n)) : ℝ :=
  energy n ω x / ε + logZ (fun ω' => energy n ω' x) ε

def limitSurprisal
    (energy : Ω → DoubledSpace C.LimitBase → ℝ)
    (ε : ℝ) (ω : Ω) (x : DoubledSpace C.LimitBase) : ℝ :=
  energy ω x / ε + logZ (fun ω' => energy ω' x) ε

theorem stageGibbsProb_eq_exp_sub_logZ
    (energy : ∀ n, Ω → DoubledSpace (C.Base n) → ℝ)
    (ε : ℝ) (n : ℕ) (ω : Ω) (x : DoubledSpace (C.Base n)) :
    stageGibbsProb energy ε n ω x =
      Real.exp (-(energy n ω x) / ε -
        logZ (fun ω' => energy n ω' x) ε) := by
  exact gibbsProb_eq_exp_sub_logZ (fun ω' => energy n ω' x) ε ω

theorem stageSurprisal_eq_neg_log_stageGibbsProb
    (energy : ∀ n, Ω → DoubledSpace (C.Base n) → ℝ)
    (ε : ℝ) (n : ℕ) (ω : Ω) (x : DoubledSpace (C.Base n)) :
    stageSurprisal energy ε n ω x =
      -Real.log (stageGibbsProb energy ε n ω x) := by
  unfold stageSurprisal stageGibbsProb
  rw [log_gibbsProb]
  ring

theorem stageGibbsProb_gauge_invariant
    (energy : ∀ n, Ω → DoubledSpace (C.Base n) → ℝ)
    (c ε : ℝ) (hε : ε ≠ 0) (n : ℕ)
    (ω : Ω) (x : DoubledSpace (C.Base n)) :
    stageGibbsProb (fun n ω x => energy n ω x + c) ε n ω x =
      stageGibbsProb energy ε n ω x := by
  exact gibbsProb_add_constant_invariant (fun ω' => energy n ω' x)
    c ε hε ω

theorem stageInternalEnergy_gauge_covariant
    (energy : ∀ n, Ω → DoubledSpace (C.Base n) → ℝ)
    (c ε : ℝ) (hε : ε ≠ 0) (n : ℕ)
    (x : DoubledSpace (C.Base n)) :
    internalEnergy (fun ω => energy n ω x + c) ε =
      internalEnergy (fun ω => energy n ω x) ε + c := by
  exact internalEnergy_add_constant (fun ω => energy n ω x) c ε hε

theorem stageShannonEntropy_gauge_invariant
    (energy : ∀ n, Ω → DoubledSpace (C.Base n) → ℝ)
    (c ε : ℝ) (hε : ε ≠ 0) (n : ℕ)
    (x : DoubledSpace (C.Base n)) :
    shannonEntropy (fun ω => energy n ω x + c) ε =
      shannonEntropy (fun ω => energy n ω x) ε := by
  exact shannonEntropy_add_constant (fun ω => energy n ω x) c ε hε

theorem stageFreeEnergy_gauge_covariant
    (energy : ∀ n, Ω → DoubledSpace (C.Base n) → ℝ)
    (c ε : ℝ) (hε : ε ≠ 0) (n : ℕ)
    (x : DoubledSpace (C.Base n)) :
    freeEnergy (fun ω => energy n ω x + c) ε =
      freeEnergy (fun ω => energy n ω x) ε + c := by
  exact freeEnergy_add_constant (fun ω => energy n ω x) c ε hε

omit [Nonempty Ω] in
theorem stageGibbsProb_eq_limit
    (stageEnergy : ∀ n, Ω → DoubledSpace (C.Base n) → ℝ)
    (limitEnergy : Ω → DoubledSpace C.LimitBase → ℝ)
    (ε : ℝ)
    (henergy : ∀ n ω x, stageEnergy n ω x = limitEnergy ω (C.ι n x))
    (n : ℕ) (ω : Ω) (x : DoubledSpace (C.Base n)) :
    stageGibbsProb stageEnergy ε n ω x =
      limitGibbsProb limitEnergy ε ω (C.ι n x) := by
  unfold stageGibbsProb limitGibbsProb
  congr 1
  funext ω'
  exact henergy n ω' x

omit [Nonempty Ω] in
theorem stageSurprisal_eq_limit
    (stageEnergy : ∀ n, Ω → DoubledSpace (C.Base n) → ℝ)
    (limitEnergy : Ω → DoubledSpace C.LimitBase → ℝ)
    (ε : ℝ)
    (henergy : ∀ n ω x, stageEnergy n ω x = limitEnergy ω (C.ι n x))
    (n : ℕ) (ω : Ω) (x : DoubledSpace (C.Base n)) :
    stageSurprisal stageEnergy ε n ω x =
      limitSurprisal limitEnergy ε ω (C.ι n x) := by
  unfold stageSurprisal limitSurprisal
  rw [henergy n ω x]
  congr 1
  apply congrArg (fun E : Ω → ℝ => logZ E ε)
  funext ω'
  exact henergy n ω' x

omit [Nonempty Ω] in
theorem stageGibbsProb_bondIterate_eq
    (stageEnergy : ∀ n, Ω → DoubledSpace (C.Base n) → ℝ)
    (ε : ℝ)
    (henergy : ∀ n m ω x,
      stageEnergy (n + m) ω
          (C.toFilteredPhaseCone.bondIterate n m x) =
        stageEnergy n ω x)
    (n m : ℕ) (ω : Ω) (x : DoubledSpace (C.Base n)) :
    stageGibbsProb stageEnergy ε (n + m) ω
        (C.toFilteredPhaseCone.bondIterate n m x) =
      stageGibbsProb stageEnergy ε n ω x := by
  unfold stageGibbsProb
  congr 1
  funext ω'
  exact henergy n m ω' x

omit [Nonempty Ω] in
theorem stageSurprisal_bondIterate_eq
    (stageEnergy : ∀ n, Ω → DoubledSpace (C.Base n) → ℝ)
    (ε : ℝ)
    (henergy : ∀ n m ω x,
      stageEnergy (n + m) ω
          (C.toFilteredPhaseCone.bondIterate n m x) =
        stageEnergy n ω x)
    (n m : ℕ) (ω : Ω) (x : DoubledSpace (C.Base n)) :
    stageSurprisal stageEnergy ε (n + m) ω
        (C.toFilteredPhaseCone.bondIterate n m x) =
      stageSurprisal stageEnergy ε n ω x := by
  unfold stageSurprisal
  rw [henergy n m ω x]
  congr 1
  apply congrArg (fun E : Ω → ℝ => logZ E ε)
  funext ω'
  exact henergy n m ω' x

end InfoGeometry.Canonical.HestenesKreinGibbsColimit

end noncomputable section
