import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Projection
import InfoGeometry.Meta.Architecture
import Paperproof

/-!
# InfoGeometry.Algebraic.Fitting

The Algebraic Fitting Decomposition for infinite-dimensional modules.
This module formalizes the kernel-range splitting for operators with finite
ascent and descent at zero, strictly avoiding complex analysis.
-/

namespace InfoGeometry.Algebraic.Fitting

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Kernel stabilization at index `k` (ascent). -/
@[rep_depth operator]
def AscentStabilized (T : Module.End K V) (k : ℕ) : Prop :=
  (T ^ k).ker = (T ^ (k + 1)).ker

/-- Range stabilization at index `k` (descent). -/
@[rep_depth operator]
def DescentStabilized (T : Module.End K V) (k : ℕ) : Prop :=
  (T ^ k).range = (T ^ (k + 1)).range

/-- Ascent stabilization propagates. -/
theorem ascent_le {T : Module.End K V} {k n : ℕ}
    (h : AscentStabilized T k) (hkn : k ≤ n) :
    (T ^ n).ker = (T ^ (n + 1)).ker := by
  induction n, hkn using Nat.le_induction with
  | base => exact h
  | succ n hkn' ih =>
      apply le_antisymm
      · intro x hx
        simp only [LinearMap.mem_ker] at hx ⊢
        simpa [pow_succ'] using congrArg T hx
      · intro x hx
        simp only [LinearMap.mem_ker] at hx ⊢
        have hTx : (T ^ (n + 1)) (T x) = 0 := by
          simpa [pow_succ] using hx
        have hTx' : (T ^ n) (T x) = 0 := by
          simpa [LinearMap.mem_ker] using (show T x ∈ (T ^ n).ker by
            simpa [ih, LinearMap.mem_ker] using hTx)
        simpa [pow_succ] using hTx'

/-- Descent stabilization propagates. -/
theorem descent_le {T : Module.End K V} {k n : ℕ}
    (h : DescentStabilized T k) (hkn : k ≤ n) :
    (T ^ n).range = (T ^ (n + 1)).range := by
  induction n, hkn using Nat.le_induction with
  | base => exact h
  | succ n hkn' ih =>
      apply le_antisymm
      · intro y hy
        rcases hy with ⟨x, rfl⟩
        rcases (show (T ^ n) x ∈ (T ^ (n + 1)).range from by
            simpa [ih] using (show (T ^ n) x ∈ (T ^ n).range from ⟨x, rfl⟩)) with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        calc
          (T ^ (n + 2)) z = T ((T ^ (n + 1)) z) := by
            simp [pow_succ']
          _ = T ((T ^ n) x) := by rw [hz]
          _ = (T ^ (n + 1)) x := by simp [pow_succ']
      · intro y hy
        rcases hy with ⟨x, rfl⟩
        refine ⟨T x, ?_⟩
        simp [pow_succ]

/-- Ascent propagation: if kernel stabilizes at k, it stabilizes at all n ≥ k. -/
theorem ker_pow_eq_of_ascent_stabilized {T : Module.End K V} {k n : ℕ}
    (h : AscentStabilized T k) (hkn : k ≤ n) :
    (T ^ n).ker = (T ^ k).ker := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn' ih =>
      exact (ascent_le h hkn').symm.trans ih

/-- Descent propagation: if range stabilizes at k, it stabilizes at all n ≥ k. -/
theorem range_pow_eq_of_descent_stabilized {T : Module.End K V} {k n : ℕ}
    (h : DescentStabilized T k) (hkn : k ≤ n) :
    (T ^ n).range = (T ^ k).range := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn' ih =>
      exact (descent_le h hkn').symm.trans ih

/-- The core Fitting splitting theorem. -/
@[rep_depth operator]
theorem isCompl_ker_pow_range_pow {T : Module.End K V} {k : ℕ}
    (ha : AscentStabilized T k)
    (hd : DescentStabilized T k) :
    IsCompl (T ^ k).ker (T ^ k).range := by
  constructor
  · rw [disjoint_iff_inf_le]
    intro x hx
    rcases hx with ⟨hxK, hxR⟩
    rcases hxR with ⟨y, rfl⟩
    have h_ker : (T ^ k * T ^ k) y = 0 := hxK
    rw [← pow_add] at h_ker
    have h_mem : y ∈ (T ^ (k + k)).ker := h_ker
    rw [ker_pow_eq_of_ascent_stabilized ha (Nat.le_add_right k k)] at h_mem
    exact h_mem
  · rw [codisjoint_iff_le_sup]
    intro x _
    have h_ran : (T ^ (k + k)).range = (T ^ k).range :=
      range_pow_eq_of_descent_stabilized hd (Nat.le_add_right k k)
    have hx_ran : (T ^ k) x ∈ (T ^ k).range := ⟨x, rfl⟩
    rw [← h_ran] at hx_ran
    rcases hx_ran with ⟨y, hy⟩
    let xR := (T ^ k) y
    let xK := x - xR
    have h_xR_ran : xR ∈ (T ^ k).range := ⟨y, rfl⟩
    have h_xK_ker : xK ∈ (T ^ k).ker := by
      simp only [LinearMap.mem_ker]
      rw [LinearMap.map_sub]
      have : (T ^ k) xR = (T ^ (k + k)) y := by rw [pow_add]; rfl
      rw [this, hy, sub_self]
    rw [Submodule.mem_sup]
    exact ⟨xK, h_xK_ker, xR, ⟨y, rfl⟩, by simp [xK, xR]⟩

/-- Surjective on range. -/
theorem surjective_on_range {T : Module.End K V} {k : ℕ}
    (hd : DescentStabilized T k) :
    ∀ y ∈ (T ^ k).range, ∃ x ∈ (T ^ k).range, T x = y := by
  intro y hy
  have h_ran : (T ^ k).range = (T ^ (k + 1)).range := hd
  rw [h_ran] at hy
  rcases hy with ⟨x, hx⟩
  refine ⟨(T ^ k) x, ⟨x, rfl⟩, ?_⟩
  simpa [pow_succ'] using hx

/-- Injective on range. -/
theorem injective_on_range {T : Module.End K V} {k : ℕ}
    (ha : AscentStabilized T k)
    (hd : DescentStabilized T k) :
    ∀ x ∈ (T ^ k).range, T x = 0 → x = 0 := by
  let _ := hd
  intro x hx hTx
  rcases hx with ⟨y, rfl⟩
  have h_ker : (T ^ (k + 1)) y = 0 := by
    simpa [pow_succ'] using hTx
  have h_y : y ∈ (T ^ (k + 1)).ker := h_ker
  rw [← ha] at h_y
  exact h_y

end InfoGeometry.Algebraic.Fitting
