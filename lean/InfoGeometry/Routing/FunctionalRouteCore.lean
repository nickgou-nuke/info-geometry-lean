/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Routing.CausalRouteDynamics
import InfoGeometry.Singular.MoorePenrose
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Synchronized finite-route cores and full-rank pseudoinverse factorization

Reuse the native deterministic attention representation and canonical inverse
predicates. A finite graph certificate consists of a recurrent embedding,
cycle permutation, synchronized retraction, and eventual entry in the core.
The Drazin equations and rectangular factorization are conclusions, not
certificate fields. This file does not prove correctness of Kahn's algorithm
or existence of such a certificate for every finite route.
-/
namespace InfoGeometry.Routing.FunctionalRouteCore

open Matrix DeterministicArgmaxAttention
open InfoGeometry.Routing.AttentionPolytope
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Singular.MoorePenrose

noncomputable section
variable {n c : ℕ}

/-- Inverse cycle motion after the phase-synchronized retraction. -/
def inverseRoute (embed : Fin c → Fin n) (sigma : Equiv.Perm (Fin c))
    (rho : Fin n → Fin c) : Fin n → Fin n := fun i => embed (sigma.symm (rho i))

/-- Restriction followed by lift is the identity in recurrent coordinates. -/
theorem retraction_split (embed : Fin c → Fin n) (rho : Fin n → Fin c)
    (hretract : ∀ j, rho (embed j) = j) :
    deterministicAttention embed * deterministicAttention rho = 1 := by
  rw [deterministic_mul]
  have h : rho ∘ embed = id := funext hretract
  rw [h, deterministic_id]

/-- The lift intertwines the full operator with the cycle permutation. -/
theorem route_intertwines_lift (f : Fin n → Fin n) (rho : Fin n → Fin c)
    (sigma : Equiv.Perm (Fin c)) (hsync : ∀ i, rho (f i) = sigma (rho i)) :
    deterministicAttention f * deterministicAttention rho =
      deterministicAttention rho * deterministicAttention sigma := by
  rw [deterministic_mul, deterministic_mul]
  congr 1
  exact funext hsync

/-- A graph retraction certificate yields the actual canonical Drazin witness. -/
theorem drazin_of_synchronized_retraction
    (f : Fin n → Fin n) (embed : Fin c → Fin n) (sigma : Equiv.Perm (Fin c))
    (rho : Fin n → Fin c) (k : ℕ)
    (hretract : ∀ j, rho (embed j) = j)
    (hcycle : ∀ j, f (embed j) = embed (sigma j))
    (hsync : ∀ i, rho (f i) = sigma (rho i))
    (hentry : ∀ i, ∃ j, f^[k] i = embed j) :
    IsDrazinInverse (deterministicAttention f)
      (deterministicAttention (inverseRoute embed sigma rho)) k := by
  let g := inverseRoute embed sigma rho
  have hgf (i : Fin n) : g (f i) = embed (rho i) := by
    simp [g, inverseRoute, hsync]
  have hfg (i : Fin n) : f (g i) = embed (rho i) := by
    simp [g, inverseRoute, hcycle]
  change IsDrazinInverse (deterministicAttention f) (deterministicAttention g) k
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · rw [deterministic_mul, deterministic_mul]
    congr 1
    funext i
    exact (hgf i).trans (hfg i).symm
  · rw [deterministic_mul, deterministic_mul]
    congr 1
    funext i
    change g (f (g i)) = g i
    rw [hfg]
    simp [g, inverseRoute, hretract]
  · rw [deterministic_pow, deterministic_mul, deterministic_pow]
    congr 1
    funext i
    change g (f^[k + 1] i) = f^[k] i
    rw [Function.iterate_succ_apply', hgf]
    obtain ⟨j, hj⟩ := hentry i
    rw [hj, hretract]

/-- The full-space Drazin projection is a lifted retraction, generally oblique. -/
theorem synchronized_projection (f : Fin n → Fin n) (embed : Fin c → Fin n)
    (sigma : Equiv.Perm (Fin c)) (rho : Fin n → Fin c)
    (hsync : ∀ i, rho (f i) = sigma (rho i)) :
    projection (deterministicAttention f)
      (deterministicAttention (inverseRoute embed sigma rho)) =
      deterministicAttention rho * deterministicAttention embed := by
  unfold projection
  rw [deterministic_mul, deterministic_mul]
  congr 1
  funext i
  simp [inverseRoute, Function.comp_def, hsync]

/-- The inverse is lift * inverse-permutation * restriction, not C-transpose. -/
theorem inverse_factorization (embed : Fin c → Fin n) (sigma : Equiv.Perm (Fin c))
    (rho : Fin n → Fin c) :
    deterministicAttention (inverseRoute embed sigma rho) =
      deterministicAttention rho * deterministicAttention sigma.symm *
        deterministicAttention embed := by
  rw [deterministic_mul, deterministic_mul]
  rfl

/-- The regular core is a lifted permutation, not an ambient Birkhoff vertex. -/
theorem core_factorization (f : Fin n → Fin n) (embed : Fin c → Fin n)
    (sigma : Equiv.Perm (Fin c)) (rho : Fin n → Fin c)
    (hsync : ∀ i, rho (f i) = sigma (rho i)) :
    core (deterministicAttention f)
      (deterministicAttention (inverseRoute embed sigma rho)) =
      deterministicAttention rho * deterministicAttention sigma *
        deterministicAttention embed := by
  rw [core_eq_mul_projection, synchronized_projection f embed sigma rho hsync,
    ← Matrix.mul_assoc, route_intertwines_lift f rho sigma hsync]

/-- Core trace is the size of recurrent coordinates when the retraction splits. -/
theorem synchronized_projection_trace (f : Fin n → Fin n) (embed : Fin c → Fin n)
    (sigma : Equiv.Perm (Fin c)) (rho : Fin n → Fin c)
    (hretract : ∀ j, rho (embed j) = j)
    (hsync : ∀ i, rho (f i) = sigma (rho i)) :
    Matrix.trace (projection (deterministicAttention f)
      (deterministicAttention (inverseRoute embed sigma rho))) = (c : ℝ) := by
  rw [synchronized_projection f embed sigma rho hsync, Matrix.trace_mul_comm,
    retraction_split embed rho hretract]
  simp [Matrix.trace, Matrix.one_apply]

/-- Full-column/full-row factorization gives a genuine MP inverse.
The support self-adjointness obligations must be supplied; they are not
inferred from a nonorthogonal change of coordinates. -/
theorem mp_of_split_factorization
    (U : Matrix (Fin n) (Fin c) ℝ) (B : Matrix (Fin c) (Fin n) ℝ)
    (L : Matrix (Fin c) (Fin n) ℝ) (T : Matrix (Fin n) (Fin c) ℝ)
    (hLU : L * U = 1) (hBT : B * T = 1)
    (hUL : (U * L).conjTranspose = U * L)
    (hTB : (T * B).conjTranspose = T * B) :
    IsMoorePenroseInverse (U * B) (T * L) := by
  have hleft : (U * B) * (T * L) = U * L := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc B T L, hBT, Matrix.one_mul]
  have hright : (T * L) * (U * B) = T * B := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc L U B, hLU, Matrix.one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hleft, Matrix.mul_assoc, ← Matrix.mul_assoc L U B, hLU, Matrix.one_mul]
  · rw [hright, Matrix.mul_assoc, ← Matrix.mul_assoc B T L, hBT, Matrix.one_mul]
  · rw [hleft]
    exact hUL
  · rw [hright]
    exact hTB

end
end InfoGeometry.Routing.FunctionalRouteCore
