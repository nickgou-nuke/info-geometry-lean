import Mathlib.Tactic

set_option autoImplicit false

open Finset

section NilpotentAutomorphism

theorem nilpotent_automorphism_expansion_general_time
    {A : Type*} [Ring A]
    (N X t : A)
    (ht_center : ∀ Y : A, Commute t Y)
    (_hN : N * N = 0) :
    (1 + t * N) * X * (1 - t * N)
      = X + t * (N * X - X * N) - (t * t) * (N * X * N) := by
  have htN : t * N = N * t := (ht_center N).eq
  have htX : t * X = X * t := (ht_center X).eq
  have h1 : X * (t * N) = t * (X * N) := by
    calc
      X * (t * N) = X * t * N := by simp [mul_assoc]
      _ = t * X * N := by rw [htX]
      _ = t * (X * N) := by simp [mul_assoc]
  have h2 : t * N * X * (t * N) = (t * t) * (N * X * N) := by
    calc
      t * N * X * (t * N) = t * (N * (X * t * N)) := by simp [mul_assoc]
      _ = t * (N * (t * X * N)) := by rw [← htX]
      _ = t * (N * t * X * N) := by simp [mul_assoc]
      _ = t * (t * N * X * N) := by rw [htN]
      _ = (t * t) * (N * X * N) := by simp [mul_assoc]
  have h3 :
      (1 + t * N) * X * (1 - t * N)
        = X - t * (X * N) + (t * (N * X) - (t * t) * (N * X * N)) := by
    calc
      (1 + t * N) * X * (1 - t * N)
          = (X + t * N * X) * (1 - t * N) := by rw [add_mul, one_mul]
      _ = X * (1 - t * N) + (t * N * X) * (1 - t * N) := by rw [add_mul]
      _ = X * 1 - X * (t * N) + ((t * N * X) * 1 - (t * N * X) * (t * N)) := by
            rw [mul_sub, mul_sub]
      _ = X - X * (t * N) + (t * (N * X) - t * N * X * (t * N)) := by
            simp [mul_assoc]
      _ = X - t * (X * N) + (t * (N * X) - t * N * X * (t * N)) := by rw [h1]
      _ = X - t * (X * N) + (t * (N * X) - (t * t) * (N * X * N)) := by rw [h2]
  rw [h3]
  have h4 :
      X + t * (N * X - X * N) - (t * t) * (N * X * N)
        = X + (t * (N * X) - t * (X * N)) - (t * t) * (N * X * N) := by
    rw [mul_sub]
  rw [h4]
  abel

end NilpotentAutomorphism

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

structure ChiralState (R : Type*) [CommRing R] where
  t : R
  x : R
  y : R
  z : R

def weyl_trace {R : Type*} [CommRing R] (X : ChiralState R) : R := X.t
def causal_interval {R : Type*} [CommRing R] (X : ChiralState R) : R := X.t * X.t - X.x * X.x - X.y * X.y - X.z * X.z

class ModularTimeFlow (R : Type*) [CommRing R] where
  cosh : R → R
  sinh : R → R
  hyperbolic_identity : ∀ η : R, cosh η * cosh η - sinh η * sinh η = 1

def rindler_boost {R : Type*} [CommRing R] [ModularTimeFlow R] (X : ChiralState R) (η : R) : ChiralState R :=
  ⟨X.t * ModularTimeFlow.cosh η + X.z * ModularTimeFlow.sinh η, X.x, X.y,
   X.z * ModularTimeFlow.cosh η + X.t * ModularTimeFlow.sinh η⟩

def weyl_gauge_scale {R : Type*} [CommRing R] (X : ChiralState R) (Λ : R) : ChiralState R :=
  ⟨Λ * X.t, Λ * X.x, Λ * X.y, Λ * X.z⟩

theorem rindler_flow_isometry {R : Type*} [CommRing R] [ModularTimeFlow R] (X : ChiralState R) (η : R) :
    causal_interval (rindler_boost X η) = causal_interval X := by
  unfold causal_interval rindler_boost
  have h := ModularTimeFlow.hyperbolic_identity (R := R) η
  calc
    (X.t * ModularTimeFlow.cosh η + X.z * ModularTimeFlow.sinh η) *
        (X.t * ModularTimeFlow.cosh η + X.z * ModularTimeFlow.sinh η) -
      X.x * X.x - X.y * X.y -
      (X.z * ModularTimeFlow.cosh η + X.t * ModularTimeFlow.sinh η) *
        (X.z * ModularTimeFlow.cosh η + X.t * ModularTimeFlow.sinh η)
      = X.t * X.t * (ModularTimeFlow.cosh η * ModularTimeFlow.cosh η - ModularTimeFlow.sinh η * ModularTimeFlow.sinh η) -
        X.z * X.z * (ModularTimeFlow.cosh η * ModularTimeFlow.cosh η - ModularTimeFlow.sinh η * ModularTimeFlow.sinh η) -
        X.x * X.x - X.y * X.y := by ring
    _ = X.t * X.t * 1 - X.z * X.z * 1 - X.x * X.x - X.y * X.y := by rw [h]
    _ = X.t * X.t - X.x * X.x - X.y * X.y - X.z * X.z := by ring

theorem weyl_trace_scaling {R : Type*} [CommRing R] (X : ChiralState R) (Λ : R) :
    weyl_trace (weyl_gauge_scale X Λ) = Λ * weyl_trace X := rfl

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
