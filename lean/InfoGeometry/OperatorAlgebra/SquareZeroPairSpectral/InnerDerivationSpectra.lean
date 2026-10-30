/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.MassCommutant

/-!
# Inner-derivation spectra of a square-zero operator pair

For square-zero `u v` in an associative `R`-algebra `A`, with
`Φ = u + v`, `J = u - v`, `V = u v + v u`, `Σ = u v - v u`, we study the
following elements of the operator ring `Module.End R A`:

* `phiLaplacian = -(ad_Φ ∘ ad_Φ)`,
* `jLaplacian = ad_J ∘ ad_J`,

(`TrinityBridge` identifies the first two with the dissipators of
`PeirceDissipatorTrinity`.)
* `spinLaplacian = -(ad_Σ ∘ ad_Σ)`,
* the mixed ladders `ladderMinus = ad_Φ ∘ ad_J`, `ladderPlus = ad_J ∘ ad_Φ`,
* the Casimir `phiLaplacian + jLaplacian + spinLaplacian`.

Every eigen-relation has an operator-valued eigenvalue: left multiplication
by `V` or `V * V`, which commutes with all these operators
(`MassCommutant`). No scalar normalization of `V` is assumed.
-/

namespace InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral

open InfoGeometry.OperatorAlgebra.LieJordan

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

section Defs

variable (R)

/-- `-(ad_Φ)²` for `Φ = u + v`. -/
def phiLaplacian (u v : A) : Module.End R A := -(lieOp R (u + v) * lieOp R (u + v))

/-- `(ad_J)²` for `J = u - v`. -/
def jLaplacian (u v : A) : Module.End R A := lieOp R (u - v) * lieOp R (u - v)

/-- `-(ad_Σ)²` for `Σ = u v - v u`. -/
def spinLaplacian (u v : A) : Module.End R A :=
  -(lieOp R (u * v - v * u) * lieOp R (u * v - v * u))

/-- Mixed lowering ladder `ad_Φ ∘ ad_J`. -/
def ladderMinus (u v : A) : Module.End R A := lieOp R (u + v) * lieOp R (u - v)

/-- Mixed raising ladder `ad_J ∘ ad_Φ`. -/
def ladderPlus (u v : A) : Module.End R A := lieOp R (u - v) * lieOp R (u + v)

/-- Quadratic Casimir superoperator. -/
def casimir (u v : A) : Module.End R A :=
  phiLaplacian R u v + jLaplacian R u v + spinLaplacian R u v

end Defs

variable {u v : A}

/-- The two mixed ladders differ by the spin derivation:
`ad_Φ ad_J - ad_J ad_Φ = -2 ad_Σ` (an operator identity). -/
theorem ladderMinus_sub_ladderPlus (hu : u * u = 0) (hv : v * v = 0) :
    ladderMinus R u v - ladderPlus R u v = -((2 : ℕ) • lieOp R (u * v - v * u)) := by
  ext x
  change (u + v) * ((u - v) * x - x * (u - v)) - ((u - v) * x - x * (u - v)) * (u + v) -
      ((u - v) * ((u + v) * x - x * (u + v)) - ((u + v) * x - x * (u + v)) * (u - v)) =
    -((2 : ℕ) • ((u * v - v * u) * x - x * (u * v - v * u)))
  rw [two_nsmul]
  noncomm_ring [hu, hv]

/-! ### First-order actions -/

section FirstOrder

theorem adSum_sum : lieOp R (u + v) (u + v) = 0 := by simp

theorem adSum_difference (hu : u * u = 0) (hv : v * v = 0) :
    lieOp R (u + v) (u - v) = -((2 : ℕ) • (u * v - v * u)) := by
  rw [lieOp_apply]; exact lie_sum_difference hu hv

theorem adSum_mass (hu : u * u = 0) (hv : v * v = 0) :
    lieOp R (u + v) (u * v + v * u) = 0 := by
  rw [lieOp_apply, sub_eq_zero]; exact (mass_commute_sum hu hv).eq.symm

theorem adSum_spin (hu : u * u = 0) (hv : v * v = 0) :
    lieOp R (u + v) (u * v - v * u) = -((2 : ℕ) • ((u * v + v * u) * (u - v))) := by
  rw [lieOp_apply, ← lie_spin_sum hu hv]; abel

theorem adDifference_sum (hu : u * u = 0) (hv : v * v = 0) :
    lieOp R (u - v) (u + v) = (2 : ℕ) • (u * v - v * u) := by
  rw [lieOp_apply]; exact lie_difference_sum hu hv

theorem adDifference_difference : lieOp R (u - v) (u - v) = 0 := by simp

theorem adDifference_mass (hu : u * u = 0) (hv : v * v = 0) :
    lieOp R (u - v) (u * v + v * u) = 0 := by
  rw [lieOp_apply, sub_eq_zero]; exact (mass_commute_difference hu hv).eq.symm

theorem adDifference_spin (hu : u * u = 0) (hv : v * v = 0) :
    lieOp R (u - v) (u * v - v * u) = -((2 : ℕ) • ((u * v + v * u) * (u + v))) := by
  rw [lieOp_apply, ← lie_spin_difference hu hv]; abel

theorem adSpin_sum (hu : u * u = 0) (hv : v * v = 0) :
    lieOp R (u * v - v * u) (u + v) = (2 : ℕ) • ((u * v + v * u) * (u - v)) := by
  rw [lieOp_apply]; exact lie_spin_sum hu hv

theorem adSpin_difference (hu : u * u = 0) (hv : v * v = 0) :
    lieOp R (u * v - v * u) (u - v) = (2 : ℕ) • ((u * v + v * u) * (u + v)) := by
  rw [lieOp_apply]; exact lie_spin_difference hu hv

theorem adSpin_mass (hu : u * u = 0) (hv : v * v = 0) :
    lieOp R (u * v - v * u) (u * v + v * u) = 0 := by
  rw [lieOp_apply, sub_eq_zero]; exact (mass_commute_spin hu hv).eq.symm

theorem adSpin_spin : lieOp R (u * v - v * u) (u * v - v * u) = 0 := by simp

end FirstOrder

/-! ### Mass-weighted transport through the inner derivations -/

section MassWeighted

theorem adSum_mass_mul (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    lieOp R (u + v) ((u * v + v * u) * x) = (u * v + v * u) * lieOp R (u + v) x :=
  lieOp_mulLeft_apply R (mass_commute_sum hu hv) x

theorem adDifference_mass_mul (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    lieOp R (u - v) ((u * v + v * u) * x) = (u * v + v * u) * lieOp R (u - v) x :=
  lieOp_mulLeft_apply R (mass_commute_difference hu hv) x

theorem adSpin_mass_mul (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    lieOp R (u * v - v * u) ((u * v + v * u) * x) =
      (u * v + v * u) * lieOp R (u * v - v * u) x :=
  lieOp_mulLeft_apply R (mass_commute_spin hu hv) x

end MassWeighted

/-! ### Second-order spectra: the three Laplacians on `(Φ, J, V, Σ)` -/

section Laplacians

theorem phiLaplacian_apply (x : A) :
    phiLaplacian R u v x = -(lieOp R (u + v) (lieOp R (u + v) x)) := rfl

theorem jLaplacian_apply (x : A) :
    jLaplacian R u v x = lieOp R (u - v) (lieOp R (u - v) x) := rfl

theorem spinLaplacian_apply (x : A) :
    spinLaplacian R u v x = -(lieOp R (u * v - v * u) (lieOp R (u * v - v * u) x)) := rfl

theorem phiLaplacian_sum : phiLaplacian R u v (u + v) = 0 := by
  simp [phiLaplacian_apply]

theorem phiLaplacian_mass (hu : u * u = 0) (hv : v * v = 0) :
    phiLaplacian R u v (u * v + v * u) = 0 := by
  rw [phiLaplacian_apply, adSum_mass hu hv, map_zero, neg_zero]

theorem phiLaplacian_difference (hu : u * u = 0) (hv : v * v = 0) :
    phiLaplacian R u v (u - v) = -((4 : ℕ) • ((u * v + v * u) * (u - v))) := by
  rw [phiLaplacian_apply, adSum_difference hu hv, map_neg, map_nsmul, adSum_spin hu hv]
  abel

theorem phiLaplacian_spin (hu : u * u = 0) (hv : v * v = 0) :
    phiLaplacian R u v (u * v - v * u) = -((4 : ℕ) • ((u * v + v * u) * (u * v - v * u))) := by
  rw [phiLaplacian_apply, adSum_spin hu hv, map_neg, map_nsmul, adSum_mass_mul hu hv,
    adSum_difference hu hv, mul_neg, mul_smul_comm]
  abel

theorem jLaplacian_difference : jLaplacian R u v (u - v) = 0 := by
  simp [jLaplacian_apply]

theorem jLaplacian_mass (hu : u * u = 0) (hv : v * v = 0) :
    jLaplacian R u v (u * v + v * u) = 0 := by
  rw [jLaplacian_apply, adDifference_mass hu hv, map_zero]

theorem jLaplacian_sum (hu : u * u = 0) (hv : v * v = 0) :
    jLaplacian R u v (u + v) = -((4 : ℕ) • ((u * v + v * u) * (u + v))) := by
  rw [jLaplacian_apply, adDifference_sum hu hv, map_nsmul, adDifference_spin hu hv]
  abel

theorem jLaplacian_spin (hu : u * u = 0) (hv : v * v = 0) :
    jLaplacian R u v (u * v - v * u) = -((4 : ℕ) • ((u * v + v * u) * (u * v - v * u))) := by
  rw [jLaplacian_apply, adDifference_spin hu hv, map_neg, map_nsmul,
    adDifference_mass_mul hu hv, adDifference_sum hu hv, mul_smul_comm]
  abel

theorem spinLaplacian_spin : spinLaplacian R u v (u * v - v * u) = 0 := by
  simp [spinLaplacian_apply]

theorem spinLaplacian_mass (hu : u * u = 0) (hv : v * v = 0) :
    spinLaplacian R u v (u * v + v * u) = 0 := by
  rw [spinLaplacian_apply, adSpin_mass hu hv, map_zero, neg_zero]

theorem spinLaplacian_sum (hu : u * u = 0) (hv : v * v = 0) :
    spinLaplacian R u v (u + v) = -((4 : ℕ) • ((u * v + v * u) * (u * v + v * u) * (u + v))) := by
  rw [spinLaplacian_apply, adSpin_sum hu hv, map_nsmul, adSpin_mass_mul hu hv,
    adSpin_difference hu hv, mul_smul_comm, ← mul_assoc]
  abel

theorem spinLaplacian_difference (hu : u * u = 0) (hv : v * v = 0) :
    spinLaplacian R u v (u - v) =
      -((4 : ℕ) • ((u * v + v * u) * (u * v + v * u) * (u - v))) := by
  rw [spinLaplacian_apply, adSpin_difference hu hv, map_nsmul, adSpin_mass_mul hu hv,
    adSpin_sum hu hv, mul_smul_comm, ← mul_assoc]
  abel

end Laplacians

/-! ### Mixed ladders -/

section Ladders

theorem ladderMinus_apply (x : A) :
    ladderMinus R u v x = lieOp R (u + v) (lieOp R (u - v) x) := rfl

theorem ladderPlus_apply (x : A) :
    ladderPlus R u v x = lieOp R (u - v) (lieOp R (u + v) x) := rfl

theorem ladderMinus_difference : ladderMinus R u v (u - v) = 0 := by
  simp [ladderMinus_apply]

theorem ladderPlus_sum : ladderPlus R u v (u + v) = 0 := by
  simp [ladderPlus_apply]

theorem ladderMinus_sum (hu : u * u = 0) (hv : v * v = 0) :
    ladderMinus R u v (u + v) = -((4 : ℕ) • ((u * v + v * u) * (u - v))) := by
  rw [ladderMinus_apply, adDifference_sum hu hv, map_nsmul, adSum_spin hu hv]
  abel

theorem ladderPlus_difference (hu : u * u = 0) (hv : v * v = 0) :
    ladderPlus R u v (u - v) = (4 : ℕ) • ((u * v + v * u) * (u + v)) := by
  rw [ladderPlus_apply, adSum_difference hu hv, map_neg, map_nsmul, adDifference_spin hu hv]
  abel

theorem ladderMinus_mass_mul (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    ladderMinus R u v ((u * v + v * u) * x) = (u * v + v * u) * ladderMinus R u v x := by
  rw [ladderMinus_apply, ladderMinus_apply, adDifference_mass_mul hu hv, adSum_mass_mul hu hv]

theorem ladderPlus_mass_mul (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    ladderPlus R u v ((u * v + v * u) * x) = (u * v + v * u) * ladderPlus R u v x := by
  rw [ladderPlus_apply, ladderPlus_apply, adSum_mass_mul hu hv, adDifference_mass_mul hu hv]

/-- Nilpotency of the lowering ladder on its seed: `T₋² Φ = 0`. -/
theorem ladderMinus_sq_sum (hu : u * u = 0) (hv : v * v = 0) :
    ladderMinus R u v (ladderMinus R u v (u + v)) = 0 := by
  rw [ladderMinus_sum hu hv, map_neg, map_nsmul, ladderMinus_mass_mul hu hv,
    ladderMinus_difference, mul_zero, smul_zero, neg_zero]

/-- Nilpotency of the raising ladder on its seed: `T₊² J = 0`. -/
theorem ladderPlus_sq_difference (hu : u * u = 0) (hv : v * v = 0) :
    ladderPlus R u v (ladderPlus R u v (u - v)) = 0 := by
  rw [ladderPlus_difference hu hv, map_nsmul, ladderPlus_mass_mul hu hv,
    ladderPlus_sum, mul_zero, smul_zero]

/-- Raising after lowering: `T₊ T₋ Φ = -16 V² Φ`. -/
theorem ladderPlus_ladderMinus_sum (hu : u * u = 0) (hv : v * v = 0) :
    ladderPlus R u v (ladderMinus R u v (u + v)) =
      -((16 : ℕ) • ((u * v + v * u) * (u * v + v * u) * (u + v))) := by
  rw [ladderMinus_sum hu hv, map_neg, map_nsmul, ladderPlus_mass_mul hu hv,
    ladderPlus_difference hu hv, mul_smul_comm, ← mul_assoc, smul_smul]
  norm_num

/-- Lowering after raising: `T₋ T₊ J = -16 V² J`. -/
theorem ladderMinus_ladderPlus_difference (hu : u * u = 0) (hv : v * v = 0) :
    ladderMinus R u v (ladderPlus R u v (u - v)) =
      -((16 : ℕ) • ((u * v + v * u) * (u * v + v * u) * (u - v))) := by
  rw [ladderPlus_difference hu hv, map_nsmul, ladderMinus_mass_mul hu hv,
    ladderMinus_sum hu hv, mul_neg, mul_smul_comm, ← mul_assoc, smul_neg, smul_smul]
  norm_num

end Ladders

/-! ### Casimir spectrum -/

section Casimir

theorem casimir_apply (x : A) :
    casimir R u v x = phiLaplacian R u v x + jLaplacian R u v x + spinLaplacian R u v x := rfl

theorem casimir_mass (hu : u * u = 0) (hv : v * v = 0) :
    casimir R u v (u * v + v * u) = 0 := by
  rw [casimir_apply, phiLaplacian_mass hu hv, jLaplacian_mass hu hv,
    spinLaplacian_mass hu hv, add_zero, add_zero]

theorem casimir_spin (hu : u * u = 0) (hv : v * v = 0) :
    casimir R u v (u * v - v * u) = -((8 : ℕ) • ((u * v + v * u) * (u * v - v * u))) := by
  rw [casimir_apply, phiLaplacian_spin hu hv, jLaplacian_spin hu hv, spinLaplacian_spin,
    add_zero]
  abel

theorem casimir_sum (hu : u * u = 0) (hv : v * v = 0) :
    casimir R u v (u + v) = -((4 : ℕ) • ((u * v + v * u) * (u + v) +
      (u * v + v * u) * (u * v + v * u) * (u + v))) := by
  rw [casimir_apply, phiLaplacian_sum, jLaplacian_sum hu hv, spinLaplacian_sum hu hv,
    smul_add]
  abel

theorem casimir_difference (hu : u * u = 0) (hv : v * v = 0) :
    casimir R u v (u - v) = -((4 : ℕ) • ((u * v + v * u) * (u - v) +
      (u * v + v * u) * (u * v + v * u) * (u - v))) := by
  rw [casimir_apply, phiLaplacian_difference hu hv, jLaplacian_difference,
    spinLaplacian_difference hu hv, smul_add]
  abel

end Casimir

end InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral
