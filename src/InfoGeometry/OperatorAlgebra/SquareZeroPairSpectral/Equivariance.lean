/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.KleinHadamard

/-!
# Equivariance of the spectral superoperators under `J`, `Φ`, `Σ` conjugation

For `g ∈ {J, Φ, Σ}` let `C_g = sandwichOp R g g : x ↦ g x g` in
`Module.End R A`. Each of `J, Φ, Σ` anticommutes with the other two and
commutes with the mass `V`. Hence `C_g` anticommutes with the inner
derivation by an anticommuting element, commutes with the inner derivation
by `g` itself and with `L_V`, and therefore commutes with every Laplacian
and every homogenized Klein–Hadamard superoperator. These are identities in
the operator ring, valid for all inputs `x`.
-/

namespace InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral

open InfoGeometry.OperatorAlgebra.LieJordan

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

section General

variable (R)

/-- If `g` anticommutes with `a`, two-sided multiplication by `g`
anticommutes with `ad_a`. -/
theorem lieOp_mul_sandwich_of_anticomm {a g : A} (h : g * a = -(a * g)) :
    lieOp R a * sandwichOp R g g = -(sandwichOp R g g * lieOp R a) := by
  ext x
  change a * (g * x * g) - g * x * g * a = -(g * (a * x - x * a) * g)
  have h' : a * g = -(g * a) := by rw [h, neg_neg]
  calc
    a * (g * x * g) - g * x * g * a = (a * g) * x * g - g * x * (g * a) := by
      noncomm_ring
    _ = -(g * a * x * g) + g * x * a * g := by
      rw [h', h]
      noncomm_ring
    _ = -(g * (a * x - x * a) * g) := by noncomm_ring

/-- If `g` commutes with `a`, two-sided multiplication by `g` commutes with `ad_a`. -/
theorem lieOp_commute_sandwich_of_commute {a g : A} (h : Commute g a) :
    Commute (lieOp R a) (sandwichOp R g g) := by
  ext x
  change a * (g * x * g) - g * x * g * a = g * (a * x - x * a) * g
  calc
    a * (g * x * g) - g * x * g * a = (a * g) * x * g - g * x * (g * a) := by
      noncomm_ring
    _ = g * a * x * g - g * x * a * g := by rw [← h.eq, h.eq, ← mul_assoc]
    _ = g * (a * x - x * a) * g := by noncomm_ring

theorem mulLeft_commute_sandwich {m g : A} (h : Commute m g) :
    Commute (LinearMap.mulLeft R m) (sandwichOp R g g) := by
  ext x
  change m * (g * x * g) = g * (m * x) * g
  rw [← mul_assoc, ← mul_assoc, h.eq, mul_assoc g m x]

/-- An operator anticommuting with `S` has a square commuting with `S`. -/
theorem commute_sq_of_anticomm {T S : Module.End R A} (h : T * S = -(S * T)) :
    Commute (T * T) S := by
  ext x
  change T (T (S x)) = S (T (T x))
  have hx := congrArg (fun f : Module.End R A => f x) h
  change T (S x) = -(S (T x)) at hx
  have hTx := congrArg (fun f : Module.End R A => f (T x)) h
  change T (S (T x)) = -(S (T (T x))) at hTx
  calc
    T (T (S x)) = T (-(S (T x))) := by rw [hx]
    _ = -(T (S (T x))) := map_neg T _
    _ = -(-(S (T (T x)))) := by rw [hTx]
    _ = S (T (T x)) := neg_neg _

end General

/-! ### Anticommutation table of `(Φ, J, Σ)` -/

section Table

variable {u v : A} (hu : u * u = 0) (hv : v * v = 0)
include hu hv

theorem difference_mul_sum_anticomm : (u - v) * (u + v) = -((u + v) * (u - v)) := by
  noncomm_ring [hu, hv]

theorem sum_mul_difference_anticomm : (u + v) * (u - v) = -((u - v) * (u + v)) := by
  noncomm_ring [hu, hv]

theorem spin_mul_sum_anticomm :
    (u * v - v * u) * (u + v) = -((u + v) * (u * v - v * u)) := by
  noncomm_ring [hu, hv, mul_mul_eq_zero_of_sq hu, mul_mul_eq_zero_of_sq hv]

theorem sum_mul_spin_anticomm :
    (u + v) * (u * v - v * u) = -((u * v - v * u) * (u + v)) := by
  noncomm_ring [hu, hv, mul_mul_eq_zero_of_sq hu, mul_mul_eq_zero_of_sq hv]

theorem spin_mul_difference_anticomm :
    (u * v - v * u) * (u - v) = -((u - v) * (u * v - v * u)) := by
  noncomm_ring [hu, hv, mul_mul_eq_zero_of_sq hu, mul_mul_eq_zero_of_sq hv]

theorem difference_mul_spin_anticomm :
    (u - v) * (u * v - v * u) = -((u * v - v * u) * (u - v)) := by
  noncomm_ring [hu, hv, mul_mul_eq_zero_of_sq hu, mul_mul_eq_zero_of_sq hv]

end Table

/-! ### Laplacians commute with `C_J`, `C_Φ`, `C_Σ` -/

section Laplacians

variable {u v : A} (hu : u * u = 0) (hv : v * v = 0)
include hu hv

theorem phiLaplacian_commute_conj_difference :
    Commute (phiLaplacian R u v) (sandwichOp R (u - v) (u - v)) :=
  (commute_sq_of_anticomm R
    (lieOp_mul_sandwich_of_anticomm R (difference_mul_sum_anticomm hu hv))).neg_left

theorem jLaplacian_commute_conj_difference :
    Commute (jLaplacian R u v) (sandwichOp R (u - v) (u - v)) :=
  (lieOp_commute_sandwich_of_commute R (Commute.refl (u - v))).mul_left
    (lieOp_commute_sandwich_of_commute R (Commute.refl (u - v)))

theorem spinLaplacian_commute_conj_difference :
    Commute (spinLaplacian R u v) (sandwichOp R (u - v) (u - v)) :=
  (commute_sq_of_anticomm R
    (lieOp_mul_sandwich_of_anticomm R (difference_mul_spin_anticomm hu hv))).neg_left

theorem phiLaplacian_commute_conj_sum :
    Commute (phiLaplacian R u v) (sandwichOp R (u + v) (u + v)) :=
  ((lieOp_commute_sandwich_of_commute R (Commute.refl (u + v))).mul_left
    (lieOp_commute_sandwich_of_commute R (Commute.refl (u + v)))).neg_left

theorem jLaplacian_commute_conj_sum :
    Commute (jLaplacian R u v) (sandwichOp R (u + v) (u + v)) :=
  commute_sq_of_anticomm R
    (lieOp_mul_sandwich_of_anticomm R (sum_mul_difference_anticomm hu hv))

theorem spinLaplacian_commute_conj_sum :
    Commute (spinLaplacian R u v) (sandwichOp R (u + v) (u + v)) :=
  (commute_sq_of_anticomm R
    (lieOp_mul_sandwich_of_anticomm R (sum_mul_spin_anticomm hu hv))).neg_left

theorem phiLaplacian_commute_conj_spin :
    Commute (phiLaplacian R u v) (sandwichOp R (u * v - v * u) (u * v - v * u)) :=
  (commute_sq_of_anticomm R
    (lieOp_mul_sandwich_of_anticomm R (spin_mul_sum_anticomm hu hv))).neg_left

theorem jLaplacian_commute_conj_spin :
    Commute (jLaplacian R u v) (sandwichOp R (u * v - v * u) (u * v - v * u)) :=
  commute_sq_of_anticomm R
    (lieOp_mul_sandwich_of_anticomm R (spin_mul_difference_anticomm hu hv))

theorem spinLaplacian_commute_conj_spin :
    Commute (spinLaplacian R u v) (sandwichOp R (u * v - v * u) (u * v - v * u)) :=
  ((lieOp_commute_sandwich_of_commute R (Commute.refl (u * v - v * u))).mul_left
    (lieOp_commute_sandwich_of_commute R (Commute.refl (u * v - v * u)))).neg_left

end Laplacians

/-! ### Homogenized Klein–Hadamard superoperators are `C_g`-equivariant -/

section Projectors

variable {u v : A} (hu : u * u = 0) (hv : v * v = 0)
include hu hv

/-- Any superoperator built from `L_V` and the three Laplacians by the
Klein–Hadamard sign table commutes with `C_g` once each building block does. -/
private theorem proj_commute_of {S : Module.End R A}
    (hV : Commute (massMul R u v) S) (hPhi : Commute (phiLaplacian R u v) S)
    (hJ : Commute (jLaplacian R u v) S) (hSpin : Commute (spinLaplacian R u v) S) :
    Commute (projMass R u v) S ∧ Commute (projSum R u v) S ∧
      Commute (projDifference R u v) S ∧ Commute (projSpin R u v) S := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((((hV.mul_left hV).smul_left (8 : ℕ)).add_left (hV.mul_left hPhi)).add_left
      (hV.mul_left hJ)).add_left hSpin
  · exact ((hV.mul_left hPhi).sub_left (hV.mul_left hJ)).sub_left hSpin
  · exact ((hV.mul_left hJ).sub_left (hV.mul_left hPhi)).sub_left hSpin
  · exact (hSpin.sub_left (hV.mul_left hPhi)).sub_left (hV.mul_left hJ)

private theorem conj_difference_blocks :
    Commute (projMass R u v) (sandwichOp R (u - v) (u - v)) ∧
      Commute (projSum R u v) (sandwichOp R (u - v) (u - v)) ∧
      Commute (projDifference R u v) (sandwichOp R (u - v) (u - v)) ∧
      Commute (projSpin R u v) (sandwichOp R (u - v) (u - v)) :=
  proj_commute_of hu hv (mulLeft_commute_sandwich R (mass_commute_difference hu hv))
    (phiLaplacian_commute_conj_difference hu hv) (jLaplacian_commute_conj_difference hu hv)
    (spinLaplacian_commute_conj_difference hu hv)

private theorem conj_sum_blocks :
    Commute (projMass R u v) (sandwichOp R (u + v) (u + v)) ∧
      Commute (projSum R u v) (sandwichOp R (u + v) (u + v)) ∧
      Commute (projDifference R u v) (sandwichOp R (u + v) (u + v)) ∧
      Commute (projSpin R u v) (sandwichOp R (u + v) (u + v)) :=
  proj_commute_of hu hv (mulLeft_commute_sandwich R (mass_commute_sum hu hv))
    (phiLaplacian_commute_conj_sum hu hv) (jLaplacian_commute_conj_sum hu hv)
    (spinLaplacian_commute_conj_sum hu hv)

private theorem conj_spin_blocks :
    Commute (projMass R u v) (sandwichOp R (u * v - v * u) (u * v - v * u)) ∧
      Commute (projSum R u v) (sandwichOp R (u * v - v * u) (u * v - v * u)) ∧
      Commute (projDifference R u v) (sandwichOp R (u * v - v * u) (u * v - v * u)) ∧
      Commute (projSpin R u v) (sandwichOp R (u * v - v * u) (u * v - v * u)) :=
  proj_commute_of hu hv (mulLeft_commute_sandwich R (mass_commute_spin hu hv))
    (phiLaplacian_commute_conj_spin hu hv) (jLaplacian_commute_conj_spin hu hv)
    (spinLaplacian_commute_conj_spin hu hv)

theorem projMass_commute_conj_difference :
    Commute (projMass R u v) (sandwichOp R (u - v) (u - v)) := (conj_difference_blocks hu hv).1
theorem projSum_commute_conj_difference :
    Commute (projSum R u v) (sandwichOp R (u - v) (u - v)) := (conj_difference_blocks hu hv).2.1
theorem projDifference_commute_conj_difference :
    Commute (projDifference R u v) (sandwichOp R (u - v) (u - v)) :=
  (conj_difference_blocks hu hv).2.2.1
theorem projSpin_commute_conj_difference :
    Commute (projSpin R u v) (sandwichOp R (u - v) (u - v)) :=
  (conj_difference_blocks hu hv).2.2.2

theorem projMass_commute_conj_sum :
    Commute (projMass R u v) (sandwichOp R (u + v) (u + v)) := (conj_sum_blocks hu hv).1
theorem projSum_commute_conj_sum :
    Commute (projSum R u v) (sandwichOp R (u + v) (u + v)) := (conj_sum_blocks hu hv).2.1
theorem projDifference_commute_conj_sum :
    Commute (projDifference R u v) (sandwichOp R (u + v) (u + v)) := (conj_sum_blocks hu hv).2.2.1
theorem projSpin_commute_conj_sum :
    Commute (projSpin R u v) (sandwichOp R (u + v) (u + v)) := (conj_sum_blocks hu hv).2.2.2

theorem projMass_commute_conj_spin :
    Commute (projMass R u v) (sandwichOp R (u * v - v * u) (u * v - v * u)) :=
  (conj_spin_blocks hu hv).1
theorem projSum_commute_conj_spin :
    Commute (projSum R u v) (sandwichOp R (u * v - v * u) (u * v - v * u)) :=
  (conj_spin_blocks hu hv).2.1
theorem projDifference_commute_conj_spin :
    Commute (projDifference R u v) (sandwichOp R (u * v - v * u) (u * v - v * u)) :=
  (conj_spin_blocks hu hv).2.2.1
theorem projSpin_commute_conj_spin :
    Commute (projSpin R u v) (sandwichOp R (u * v - v * u) (u * v - v * u)) :=
  (conj_spin_blocks hu hv).2.2.2

end Projectors

end InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral
