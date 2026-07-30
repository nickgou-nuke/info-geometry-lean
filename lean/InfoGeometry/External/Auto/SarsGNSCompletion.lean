import Mathlib.Tactic

noncomputable section

namespace SarsGNSCompletion

open Complex

abbrev RPhaseSpace (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

def canonicalSigma {n : ℕ} (u v : RPhaseSpace n) : ℝ :=
  Finset.univ.sum (fun i => u.1 i * v.2 i - u.2 i * v.1 i)

def normSq {n : ℕ} (u : RPhaseSpace n) : ℝ :=
  Finset.univ.sum (fun i => u.1 i * u.1 i + u.2 i * u.2 i)

def weylPhase (σ : ℝ) : ℂ := Complex.exp (-(Complex.I / 2) * (σ : ℂ))

def fockState {n : ℕ} (u : RPhaseSpace n) : ℂ :=
  Complex.exp (-(normSq u : ℂ) / 4)

def pad1to2 (u : RPhaseSpace 1) : RPhaseSpace 2 :=
  (fun i => if (i : Nat) = 0 then u.1 0 else 0,
   fun i => if (i : Nat) = 0 then u.2 0 else 0)

@[simp] theorem pad1to2_sigma (u v : RPhaseSpace 1) :
    canonicalSigma (pad1to2 u) (pad1to2 v) = canonicalSigma u v := by
  simp [canonicalSigma, pad1to2]

@[simp] theorem pad1to2_normSq (u : RPhaseSpace 1) :
    normSq (pad1to2 u) = normSq u := by
  norm_num [normSq, pad1to2, Fin.sum_univ_two]

@[simp] theorem weyl_phase_compatible (u v : RPhaseSpace 1) :
    weylPhase (canonicalSigma (pad1to2 u) (pad1to2 v)) =
      weylPhase (canonicalSigma u v) := by
  rw [pad1to2_sigma]

@[simp] theorem fock_state_compatible (u : RPhaseSpace 1) :
    fockState (pad1to2 u) = fockState u := by
  unfold fockState
  rw [pad1to2_normSq]

@[simp] theorem fock_state_zero : fockState (0 : RPhaseSpace 1) = 1 := by
  unfold fockState normSq
  norm_num

structure TwoStageWeylState where
  omega1 : RPhaseSpace 1 → ℂ
  omega2 : RPhaseSpace 2 → ℂ
  compatible : ∀ u : RPhaseSpace 1, omega2 (pad1to2 u) = omega1 u

def fockTwoStageState : TwoStageWeylState where
  omega1 := fockState
  omega2 := fockState
  compatible := fock_state_compatible

@[simp] theorem two_stage_fock_compatible (u : RPhaseSpace 1) :
    fockTwoStageState.omega2 (pad1to2 u) = fockTwoStageState.omega1 u :=
  fockTwoStageState.compatible u

theorem canonicalSigma_skew {n : ℕ} (u v : RPhaseSpace n) :
    canonicalSigma v u = -canonicalSigma u v := by
  simp only [canonicalSigma]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

theorem canonicalSigma_self {n : ℕ} (u : RPhaseSpace n) :
    canonicalSigma u u = 0 := by
  unfold canonicalSigma
  apply Finset.sum_eq_zero
  intro i _
  ring

theorem normSq_nonneg {n : ℕ} (u : RPhaseSpace n) : 0 ≤ normSq u := by
  unfold normSq
  exact Finset.sum_nonneg (fun i _ =>
    add_nonneg (mul_self_nonneg (u.1 i)) (mul_self_nonneg (u.2 i)))

theorem weylPhase_zero : weylPhase 0 = 1 := by
  simp [weylPhase]

end SarsGNSCompletion

end noncomputable section
