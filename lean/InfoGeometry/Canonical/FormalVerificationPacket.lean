import Mathlib.Tactic
import InfoGeometry.Canonical.ChiralCausalConeFlow
import InfoGeometry.Algebra.NilpotentModularAutomorphism

set_option autoImplicit false

open Finset

section LieTKK

def lie_bracket {A : Type*} [Ring A] (x y : A) : A := x * y - y * x

theorem lie_bracket_anticomm {A : Type*} [Ring A] (x y : A) :
    lie_bracket x y = - lie_bracket y x := by
  unfold lie_bracket; abel

theorem tkk_jacobi_identity_closure {A : Type*} [Ring A] (x y z : A) :
    lie_bracket x (lie_bracket y z) + lie_bracket y (lie_bracket z x) + lie_bracket z (lie_bracket x y) = 0 := by
  unfold lie_bracket
  simp [mul_sub, sub_mul, mul_assoc]
  abel

def anticommutator {A : Type*} [Ring A] (x y : A) : A := x * y + y * x

theorem tkk_quadratic_rep_equivalence {A : Type*} [Ring A] (x y : A) :
    anticommutator x (anticommutator x y) - anticommutator (x * x) y = x * (y * x) + x * (y * x) := by
  unfold anticommutator
  have h_expand :
      x * (x * y + y * x) + (x * y + y * x) * x - (x * x * y + y * (x * x))
        = x * (x * y) + x * (y * x) + ((x * y) * x + (y * x) * x) - (x * x * y + y * (x * x)) := by
    rw [mul_add, add_mul]
  rw [h_expand]
  simp [mul_assoc]
  abel

end LieTKK

section ThermofieldDouble

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

def tfd_vec (W : I → R) (i j : I) : R := if i = j then W i else 0
def tfd_density (W : I → R) (ix kx : I × I) : R := tfd_vec W ix.1 ix.2 * tfd_vec W kx.1 kx.2
def partial_trace_L (M : I × I → I × I → R) (j l : I) : R := ∑ i : I, M (i, j) (i, l)
def gibbs_thermal (W : I → R) (j l : I) : R := if j = l then W j * W j else 0

theorem tfd_partial_trace_is_gibbs (W : I → R) (j l : I) :
    partial_trace_L (tfd_density W) j l = gibbs_thermal W j l := by
  classical
  unfold partial_trace_L tfd_density gibbs_thermal
  by_cases h : j = l
  · subst h
    have hsum : (∑ i : I, tfd_vec W i j * tfd_vec W i j) = W j * W j := by
      have hsum' : (∑ i ∈ (Finset.univ : Finset I), tfd_vec W i j * tfd_vec W i j) = tfd_vec W j j * tfd_vec W j j := by
        refine Finset.sum_eq_single (a := j) (s := (Finset.univ : Finset I)) (f := fun i : I => tfd_vec W i j * tfd_vec W i j) ?_ ?_
        · intro i hi hij; simp [tfd_vec, hij]
        · intro hj; simp at hj
      simp [tfd_vec] at hsum' ⊢
    simp [tfd_vec] at hsum ⊢
  · have hsum0 : (∑ i : I, tfd_vec W i j * tfd_vec W i l) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      by_cases hij : i = j
      · subst hij; simp [tfd_vec, h]
      · simp [tfd_vec, hij]
    simp [h, hsum0]

end ThermofieldDouble

section RindlerWeyl

/- The chiral/Rindler owner is `ChiralCausalConeFlow`.  Exporting its
   declarations preserves this packet's historical unqualified interface
   without introducing a second definition or a second proof owner. -/
open InfoGeometry.Canonical.ChiralCausalConeFlow
export InfoGeometry.Canonical.ChiralCausalConeFlow
  (ChiralState weyl_trace causal_interval ModularTimeFlow rindler_boost
    weyl_gauge_scale rindler_flow_isometry weyl_trace_scaling)

structure SymmState2x2 (R : Type*) [CommRing R] where
  t : R
  x : R
  z : R

def trace_2x2 {R : Type*} [CommRing R] (S : SymmState2x2 R) : R := S.t + S.t
def symmState2x2_det {R : Type*} [CommRing R] (S : SymmState2x2 R) : R := S.t * S.t - S.x * S.x - S.z * S.z

theorem cartan_symmetric_interior (S : SymmState2x2 ℝ) (h_trace : trace_2x2 S = 1) (h_det : symmState2x2_det S > 0) :
    S.x * S.x + S.z * S.z < (1 / 2) * (1 / 2) := by
  unfold trace_2x2 at h_trace; unfold symmState2x2_det at h_det
  have ht : S.t = 1 / 2 := by linarith
  rw [ht] at h_det; linarith

theorem celestial_sphere_boundary_2x2 (S : SymmState2x2 ℝ) (h_trace : trace_2x2 S = 1) (h_det : symmState2x2_det S = 0) :
    S.x * S.x + S.z * S.z = (1 / 2) * (1 / 2) := by
  unfold trace_2x2 at h_trace; unfold symmState2x2_det at h_det
  have ht : S.t = 1 / 2 := by linarith
  rw [ht] at h_det; linarith

end RindlerWeyl
