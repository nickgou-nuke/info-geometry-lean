/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ThreeColorCyclotomicChargeProjectors

/-!
# Cubic Charge Covariance for Integer-Labelled Heisenberg Modes

The integer label of a mode is projected to `ZMod 3`. The cubic weight
$\mathrm{cubicWeight}(\omega, r) = \omega^{\mathrm{val}(r)}$ is defined using only the
canonical representatives $0, 1, 2$, so no negative powers or division are required.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `ZMod 3` residue arithmetic (`ZMod.val`, `ZMod.val_add`, `ZMod.val_lt`).
  * `Module.End K V` operator composition and commutator action on a $K$-module $V$.
- BUCKET 2 (Deconfabulation):
  * Eliminated the `CubicChargedHeisenbergRepresentation` wrapper structure, the
    `IsCubicEigenspace : Prop` predicate wrapper, and the file-level section hypothesis
    variable, stating cubic charge covariance directly on explicit operators
    `(charge : V ≃ₗ[K] V)` and `(mode : ℤ → Module.End K V)`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `cubicWeight`: $\omega^{\mathrm{val}(r)}$ for $r \in \mathrm{ZMod}\,3$.
  * `cubicWeight_zero`: $\mathrm{cubicWeight}(\omega, 0) = 1$.
  * `cubicWeight_add`: for $\omega^3 = 1$,
    $\mathrm{cubicWeight}(\omega, r + s) = \mathrm{cubicWeight}(\omega, r)\,\mathrm{cubicWeight}(\omega, s)$.
  * `mode_shifts_cubic_eigenspace`: a covariant mode operator `mode n` shifts a vector
    of cubic charge weight $r$ to cubic charge weight $r + (n \bmod 3)$.
  * `mode_mul_shifts_cubic_eigenspace`: the composite operator `mode m * mode n` shifts
    a vector of cubic charge weight $r$ to cubic charge weight $r + (n \bmod 3) + (m \bmod 3)$.
-/

namespace InfoGeometry.Canonical.HeisenbergCyclotomicChargeRepresentation

noncomputable section

open InfoGeometry.Canonical

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

/-- The cubic charge weight $\omega^{\mathrm{val}(r)}$ carried by a degree $r \in \mathrm{ZMod}\,3$. -/
def cubicWeight (ω : K) (r : ZMod 3) : K := ω ^ r.val

/-- At degree $0 \in \mathrm{ZMod}\,3$, the cubic charge weight is $1$. -/
@[simp] theorem cubicWeight_zero (ω : K) :
    cubicWeight ω 0 = 1 := by
  unfold cubicWeight
  rw [ZMod.val_zero, pow_zero]

/-- Whenever $\omega^3 = 1$, `cubicWeight ω` is a multiplicative character on the
additive group `ZMod 3`. -/
theorem cubicWeight_add (ω : K) (hω : ω ^ 3 = 1)
    (r s : ZMod 3) :
    cubicWeight ω (r + s) = cubicWeight ω r * cubicWeight ω s := by
  have hrlt : r.val < 3 := r.val_lt
  have hslt : s.val < 3 := s.val_lt
  have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
  have hs : s.val = 0 ∨ s.val = 1 ∨ s.val = 2 := by omega
  rcases hr with hr | hr | hr <;> rcases hs with hs | hs | hs <;>
    simp only [cubicWeight, ZMod.val_add, hr, hs]
  · ring
  · ring
  · ring
  · ring
  · ring
  · calc
      ω ^ (3 % 3) = 1 := by norm_num
      _ = ω ^ 3 := hω.symm
      _ = ω ^ 1 * ω ^ 2 := by ring
  · ring
  · calc
      ω ^ (3 % 3) = 1 := by norm_num
      _ = ω ^ 3 := hω.symm
      _ = ω ^ 2 * ω ^ 1 := by ring
  · calc
      ω ^ (4 % 3) = ω * 1 := by norm_num
      _ = ω * ω ^ 3 := by rw [hω]
      _ = ω ^ 2 * ω ^ 2 := by ring

/-- If a mode family `mode : ℤ → Module.End K V` satisfies the cubic charge covariance
relation $Q \circ J_n = \omega^{n \bmod 3} (J_n \circ Q)$, then $J_n$ shifts any
cubic charge eigenvector of degree $r \in \mathrm{ZMod}\,3$ to degree $r + (n \bmod 3)$. -/
theorem mode_shifts_cubic_eigenspace
    (ω : K) (hω : ω ^ 3 = 1)
    (charge : V ≃ₗ[K] V) (mode : ℤ → Module.End K V)
    (hcov : ∀ n : ℤ,
      charge.toLinearMap * mode n =
        cubicWeight ω (n : ZMod 3) • (mode n * charge.toLinearMap))
    (r : ZMod 3) (n : ℤ) (v : V)
    (hv : charge v = cubicWeight ω r • v) :
    charge (mode n v) = cubicWeight ω (r + (n : ZMod 3)) • mode n v := by
  calc
    charge (mode n v) =
        (charge.toLinearMap * mode n) v := Eq.refl _
    _ = (cubicWeight ω (n : ZMod 3) •
        (mode n * charge.toLinearMap)) v := by
          rw [hcov n]
    _ = cubicWeight ω (n : ZMod 3) •
        mode n (charge v) := Eq.refl _
    _ = cubicWeight ω (n : ZMod 3) •
        mode n (cubicWeight ω r • v) := by rw [hv]
    _ = (cubicWeight ω (n : ZMod 3) *
        cubicWeight ω r) • mode n v := by
          rw [map_smul, smul_smul]
    _ = (cubicWeight ω r *
        cubicWeight ω (n : ZMod 3)) • mode n v := by
          rw [mul_comm]
    _ = cubicWeight ω (r + (n : ZMod 3)) • mode n v := by
          rw [← cubicWeight_add ω hω r (n : ZMod 3)]

/-- Two successive covariant mode applications $(J_m J_n) v$ shift a cubic charge
eigenvector of degree $r \in \mathrm{ZMod}\,3$ to degree $r + (n \bmod 3) + (m \bmod 3)$. -/
theorem mode_mul_shifts_cubic_eigenspace
    (ω : K) (hω : ω ^ 3 = 1)
    (charge : V ≃ₗ[K] V) (mode : ℤ → Module.End K V)
    (hcov : ∀ n : ℤ,
      charge.toLinearMap * mode n =
        cubicWeight ω (n : ZMod 3) • (mode n * charge.toLinearMap))
    (r : ZMod 3) (m n : ℤ) (v : V)
    (hv : charge v = cubicWeight ω r • v) :
    charge ((mode m * mode n) v) =
      cubicWeight ω (r + (n : ZMod 3) + (m : ZMod 3)) • ((mode m * mode n) v) := by
  have hn : charge (mode n v) = cubicWeight ω (r + (n : ZMod 3)) • mode n v :=
    mode_shifts_cubic_eigenspace ω hω charge mode hcov r n v hv
  exact mode_shifts_cubic_eigenspace ω hω charge mode hcov (r + (n : ZMod 3)) m (mode n v) hn

end
end InfoGeometry.Canonical.HeisenbergCyclotomicChargeRepresentation
