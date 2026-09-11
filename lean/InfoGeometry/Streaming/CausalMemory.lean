import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section
namespace InfoGeometry.Streaming.CausalMemory

open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def state (T : Module.End ℝ V) (input : ℕ → V) (initial : V) : ℕ → V
  | 0 => initial
  | n + 1 => T (state T input initial n) + input n

theorem state_prefix (T : Module.End ℝ V) (u v : ℕ → V) (x : V) (n : ℕ)
    (h : ∀ k < n, u k = v k) : state T u x n = state T v x n := by
  revert h
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [state]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

theorem state_chunks (T : Module.End ℝ V) (u : ℕ → V) (x : V) (m n : ℕ) :
    state T u x (m + n) = state T (fun k => u (m + k)) (state T u x m) n := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    change T (state T u x (m + n)) + u (m + n) =
      T (state T (fun k => u (m + k)) (state T u x m) n) + u (m + n)
    exact congrArg (fun z => T z + u (m + n)) ih

theorem state_convolution (T : Module.End ℝ V) (u : ℕ → V) (x : V) (n : ℕ) :
    state T u x n = (T ^ n) x +
      ∑ k ∈ Finset.range n, (T ^ (n - 1 - k)) (u k) := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    rw [state, ih, map_add, map_sum, Finset.sum_range_succ]
    have hsum : (∑ k ∈ Finset.range n, T ((T ^ (n - 1 - k)) (u k))) =
        ∑ k ∈ Finset.range n, (T ^ (n + 1 - 1 - k)) (u k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hexp : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
      rw [hexp, pow_succ']
      rfl
    rw [hsum, pow_succ']
    simp only [Module.End.mul_apply, Nat.add_sub_cancel, Nat.sub_self, pow_zero,
      Module.End.one_apply]
    abel

theorem state_add (T : Module.End ℝ V) (u v : ℕ → V) (x y : V) (n : ℕ) :
    state T (u + v) (x + y) n = state T u x n + state T v y n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [state, ih, map_add, Pi.add_apply]; abel

def decay (rate t : ℝ) : ℝ := Real.exp (-rate * t)

theorem decay_add (rate s t : ℝ) : decay rate (s + t) = decay rate s * decay rate t := by
  unfold decay
  rw [mul_add, Real.exp_add]

theorem decay_pos (rate t : ℝ) : 0 < decay rate t := Real.exp_pos _

theorem decay_le_one (rate t : ℝ) (hr : 0 ≤ rate) (ht : 0 ≤ t) : decay rate t ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith

theorem zero_transition_forgets_previous_state (u : ℕ → V) (x : V) (n : ℕ) :
    state 0 u x (n + 1) = u n := by simp [state]

def exponentialMemory (rate : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-rate * t) * ∫ s in (0 : ℝ)..t, Real.exp (rate * s) * u s

theorem exponentialMemory_eq_convolution (rate : ℝ) (u : ℝ → ℝ) (t : ℝ) :
    exponentialMemory rate u t =
      ∫ s in (0 : ℝ)..t, Real.exp (-rate * (t - s)) * u s := by
  rw [exponentialMemory, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp
  rw [← mul_assoc, ← Real.exp_add]
  have harg : -rate * t + rate * s = -rate * (t - s) := by ring
  rw [harg]

theorem exponentialMemory_hasDerivAt (rate : ℝ) (u : ℝ → ℝ)
    (hu : Continuous u) (t : ℝ) :
    HasDerivAt (exponentialMemory rate u)
      (-rate * exponentialMemory rate u t + u t) t := by
  have hf : Continuous (fun s : ℝ => Real.exp (rate * s) * u s) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hu
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 t) hf.aestronglyMeasurable.stronglyMeasurableAtFilter
    hf.continuousAt
  have he := ((hasDerivAt_id t).const_mul (-rate)).exp
  have hc : Real.exp (-rate * t) * Real.exp (rate * t) = 1 := by
    rw [← Real.exp_add]
    have hz : -rate * t + rate * t = 0 := by ring
    rw [hz, Real.exp_zero]
  have hcu := congrArg (fun r : ℝ => r * u t) hc
  convert he.mul hi using 1 <;> dsimp [exponentialMemory] <;> nlinarith [hcu]

@[simp] theorem exponentialMemory_zero (rate : ℝ) (u : ℝ → ℝ) :
    exponentialMemory rate u 0 = 0 := by simp [exponentialMemory]

end InfoGeometry.Streaming.CausalMemory
