/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.InnerDerivationSpectra

/-!
# Klein–Hadamard character superoperators of a square-zero pair

The three Laplacians `D_Φ, D_J, D_Σ` of `InnerDerivationSpectra` are combined
with the sign table of the Klein four-group into four superoperators in
`Module.End R A`:

* raw: `Π_V = 8 + D_Φ + D_J + D_Σ`, `Π_Φ = D_Φ - D_J - D_Σ`, …;
* homogenized: `Π̃_V = 8 L_{V²} + L_V D_Φ + L_V D_J + D_Σ`, …, where `L_m`
  is left multiplication by `m` (an operator-valued weight, not a scalar).

The raw family sums to `8 • 1`; the homogenized family sums to `8 • L_{V²}`
and diagonalizes the tetraktys `(V, Φ, J, Σ)` with operator eigenvalue
`8 V²`. Because every `Π̃` commutes with `L_V`, second-order compositions
`Π̃_β ∘ Π̃_α` are again diagonal: mutual annihilation for `α ≠ β` and
idempotency at weight `8 V²`.
-/

namespace InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral

open InfoGeometry.OperatorAlgebra.LieJordan

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

section Defs

variable (R)

def rawProjMass (u v : A) : Module.End R A := (8 : ℕ) • 1 + casimir R u v

def rawProjSum (u v : A) : Module.End R A :=
  phiLaplacian R u v - jLaplacian R u v - spinLaplacian R u v

def rawProjDifference (u v : A) : Module.End R A :=
  jLaplacian R u v - phiLaplacian R u v - spinLaplacian R u v

def rawProjSpin (u v : A) : Module.End R A :=
  spinLaplacian R u v - phiLaplacian R u v - jLaplacian R u v

/-- Left multiplication by the mass `V = u v + v u`. -/
def massMul (u v : A) : Module.End R A := LinearMap.mulLeft R (u * v + v * u)

def projMass (u v : A) : Module.End R A :=
  (8 : ℕ) • (massMul R u v * massMul R u v) + massMul R u v * phiLaplacian R u v +
    massMul R u v * jLaplacian R u v + spinLaplacian R u v

def projSum (u v : A) : Module.End R A :=
  massMul R u v * phiLaplacian R u v - massMul R u v * jLaplacian R u v -
    spinLaplacian R u v

def projDifference (u v : A) : Module.End R A :=
  massMul R u v * jLaplacian R u v - massMul R u v * phiLaplacian R u v -
    spinLaplacian R u v

def projSpin (u v : A) : Module.End R A :=
  spinLaplacian R u v - massMul R u v * phiLaplacian R u v -
    massMul R u v * jLaplacian R u v

end Defs

variable {u v : A}

/-! ### Partitions (operator identities, no hypotheses) -/

theorem rawProj_partition :
    rawProjMass R u v + rawProjSum R u v + rawProjDifference R u v + rawProjSpin R u v =
      (8 : ℕ) • (1 : Module.End R A) := by
  simp only [rawProjMass, rawProjSum, rawProjDifference, rawProjSpin, casimir]
  abel

theorem proj_partition :
    projMass R u v + projSum R u v + projDifference R u v + projSpin R u v =
      (8 : ℕ) • (massMul R u v * massMul R u v) := by
  simp only [projMass, projSum, projDifference, projSpin]
  abel

/-! ### Raw character selection -/

section Raw

theorem rawProjMass_apply (x : A) :
    rawProjMass R u v x = (8 : ℕ) • x + casimir R u v x := by
  simp [rawProjMass]

theorem rawProjSum_apply (x : A) :
    rawProjSum R u v x = phiLaplacian R u v x - jLaplacian R u v x - spinLaplacian R u v x :=
  rfl

theorem rawProjDifference_apply (x : A) :
    rawProjDifference R u v x =
      jLaplacian R u v x - phiLaplacian R u v x - spinLaplacian R u v x := rfl

theorem rawProjSpin_apply (x : A) :
    rawProjSpin R u v x = spinLaplacian R u v x - phiLaplacian R u v x - jLaplacian R u v x :=
  rfl

theorem rawProjMass_mass (hu : u * u = 0) (hv : v * v = 0) :
    rawProjMass R u v (u * v + v * u) = (8 : ℕ) • (u * v + v * u) := by
  rw [rawProjMass_apply, casimir_mass hu hv, add_zero]

theorem rawProjSum_mass (hu : u * u = 0) (hv : v * v = 0) :
    rawProjSum R u v (u * v + v * u) = 0 := by
  rw [rawProjSum_apply, phiLaplacian_mass hu hv, jLaplacian_mass hu hv,
    spinLaplacian_mass hu hv]; abel

theorem rawProjSum_spin (hu : u * u = 0) (hv : v * v = 0) :
    rawProjSum R u v (u * v - v * u) = 0 := by
  rw [rawProjSum_apply, phiLaplacian_spin hu hv, jLaplacian_spin hu hv, spinLaplacian_spin]
  abel

theorem rawProjDifference_mass (hu : u * u = 0) (hv : v * v = 0) :
    rawProjDifference R u v (u * v + v * u) = 0 := by
  rw [rawProjDifference_apply, phiLaplacian_mass hu hv, jLaplacian_mass hu hv,
    spinLaplacian_mass hu hv]; abel

theorem rawProjDifference_spin (hu : u * u = 0) (hv : v * v = 0) :
    rawProjDifference R u v (u * v - v * u) = 0 := by
  rw [rawProjDifference_apply, phiLaplacian_spin hu hv, jLaplacian_spin hu hv,
    spinLaplacian_spin]
  abel

theorem rawProjSpin_mass (hu : u * u = 0) (hv : v * v = 0) :
    rawProjSpin R u v (u * v + v * u) = 0 := by
  rw [rawProjSpin_apply, phiLaplacian_mass hu hv, jLaplacian_mass hu hv,
    spinLaplacian_mass hu hv]; abel

theorem rawProjSpin_spin (hu : u * u = 0) (hv : v * v = 0) :
    rawProjSpin R u v (u * v - v * u) = (8 : ℕ) • ((u * v + v * u) * (u * v - v * u)) := by
  rw [rawProjSpin_apply, phiLaplacian_spin hu hv, jLaplacian_spin hu hv, spinLaplacian_spin]
  abel

theorem rawProjMass_spin (hu : u * u = 0) (hv : v * v = 0) :
    rawProjMass R u v (u * v - v * u) =
      (8 : ℕ) • ((u * v - v * u) - (u * v + v * u) * (u * v - v * u)) := by
  rw [rawProjMass_apply, casimir_spin hu hv, smul_sub]; abel

theorem rawProjSum_sum (hu : u * u = 0) (hv : v * v = 0) :
    rawProjSum R u v (u + v) = (4 : ℕ) • ((u * v + v * u) * (u + v) +
      (u * v + v * u) * (u * v + v * u) * (u + v)) := by
  rw [rawProjSum_apply, phiLaplacian_sum, jLaplacian_sum hu hv, spinLaplacian_sum hu hv,
    smul_add]; abel

theorem rawProjDifference_difference (hu : u * u = 0) (hv : v * v = 0) :
    rawProjDifference R u v (u - v) = (4 : ℕ) • ((u * v + v * u) * (u - v) +
      (u * v + v * u) * (u * v + v * u) * (u - v)) := by
  rw [rawProjDifference_apply, phiLaplacian_difference hu hv, jLaplacian_difference,
    spinLaplacian_difference hu hv, smul_add]; abel

end Raw

/-! ### `L_V` commutes with the Laplacians and with the homogenized projectors -/

section Commutant

theorem massMul_apply (x : A) : massMul R u v x = (u * v + v * u) * x := rfl

theorem phiLaplacian_mass_mul (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    phiLaplacian R u v ((u * v + v * u) * x) = (u * v + v * u) * phiLaplacian R u v x := by
  rw [phiLaplacian_apply, phiLaplacian_apply, adSum_mass_mul hu hv, adSum_mass_mul hu hv,
    mul_neg]

theorem jLaplacian_mass_mul (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    jLaplacian R u v ((u * v + v * u) * x) = (u * v + v * u) * jLaplacian R u v x := by
  rw [jLaplacian_apply, jLaplacian_apply, adDifference_mass_mul hu hv,
    adDifference_mass_mul hu hv]

theorem spinLaplacian_mass_mul (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    spinLaplacian R u v ((u * v + v * u) * x) = (u * v + v * u) * spinLaplacian R u v x := by
  rw [spinLaplacian_apply, spinLaplacian_apply, adSpin_mass_mul hu hv, adSpin_mass_mul hu hv,
    mul_neg]

theorem projMass_apply (x : A) :
    projMass R u v x = (8 : ℕ) • ((u * v + v * u) * ((u * v + v * u) * x)) +
      (u * v + v * u) * phiLaplacian R u v x + (u * v + v * u) * jLaplacian R u v x +
      spinLaplacian R u v x := by
  simp [projMass, massMul]

theorem projSum_apply (x : A) :
    projSum R u v x = (u * v + v * u) * phiLaplacian R u v x -
      (u * v + v * u) * jLaplacian R u v x - spinLaplacian R u v x := by
  simp [projSum, massMul]

theorem projDifference_apply (x : A) :
    projDifference R u v x = (u * v + v * u) * jLaplacian R u v x -
      (u * v + v * u) * phiLaplacian R u v x - spinLaplacian R u v x := by
  simp [projDifference, massMul]

theorem projSpin_apply (x : A) :
    projSpin R u v x = spinLaplacian R u v x - (u * v + v * u) * phiLaplacian R u v x -
      (u * v + v * u) * jLaplacian R u v x := by
  simp [projSpin, massMul]

theorem projMass_mass_mul (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    projMass R u v ((u * v + v * u) * x) = (u * v + v * u) * projMass R u v x := by
  rw [projMass_apply, projMass_apply, phiLaplacian_mass_mul hu hv, jLaplacian_mass_mul hu hv,
    spinLaplacian_mass_mul hu hv]
  simp only [mul_add, mul_smul_comm]

theorem projSum_mass_mul (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    projSum R u v ((u * v + v * u) * x) = (u * v + v * u) * projSum R u v x := by
  rw [projSum_apply, projSum_apply, phiLaplacian_mass_mul hu hv, jLaplacian_mass_mul hu hv,
    spinLaplacian_mass_mul hu hv]
  simp only [mul_sub]

theorem projDifference_mass_mul (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    projDifference R u v ((u * v + v * u) * x) = (u * v + v * u) * projDifference R u v x := by
  rw [projDifference_apply, projDifference_apply, phiLaplacian_mass_mul hu hv,
    jLaplacian_mass_mul hu hv, spinLaplacian_mass_mul hu hv]
  simp only [mul_sub]

theorem projSpin_mass_mul (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    projSpin R u v ((u * v + v * u) * x) = (u * v + v * u) * projSpin R u v x := by
  rw [projSpin_apply, projSpin_apply, phiLaplacian_mass_mul hu hv, jLaplacian_mass_mul hu hv,
    spinLaplacian_mass_mul hu hv]
  simp only [mul_sub]

end Commutant

/-! ### Homogenized diagonalization of the tetraktys -/

section Diagonal

variable (hu : u * u = 0) (hv : v * v = 0)
include hu hv

theorem projMass_mass :
    projMass R u v (u * v + v * u) =
      (8 : ℕ) • ((u * v + v * u) * (u * v + v * u) * (u * v + v * u)) := by
  rw [projMass_apply, phiLaplacian_mass hu hv, jLaplacian_mass hu hv,
    spinLaplacian_mass hu hv, mul_assoc]; simp

theorem projMass_sum : projMass R u v (u + v) = 0 := by
  rw [projMass_apply, phiLaplacian_sum, jLaplacian_sum hu hv, spinLaplacian_sum hu hv]
  simp only [mul_zero, add_zero, mul_neg, mul_smul_comm, ← mul_assoc]
  abel

theorem projMass_difference : projMass R u v (u - v) = 0 := by
  rw [projMass_apply, phiLaplacian_difference hu hv, jLaplacian_difference,
    spinLaplacian_difference hu hv]
  simp only [mul_zero, add_zero, mul_neg, mul_smul_comm, ← mul_assoc]
  abel

theorem projMass_spin : projMass R u v (u * v - v * u) = 0 := by
  rw [projMass_apply, phiLaplacian_spin hu hv, jLaplacian_spin hu hv, spinLaplacian_spin]
  simp only [add_zero, mul_neg, mul_smul_comm, ← mul_assoc]
  abel

theorem projSum_sum :
    projSum R u v (u + v) = (8 : ℕ) • ((u * v + v * u) * (u * v + v * u) * (u + v)) := by
  rw [projSum_apply, phiLaplacian_sum, jLaplacian_sum hu hv, spinLaplacian_sum hu hv]
  simp only [mul_zero, mul_neg, mul_smul_comm, ← mul_assoc]
  abel

theorem projSum_mass : projSum R u v (u * v + v * u) = 0 := by
  rw [projSum_apply, phiLaplacian_mass hu hv, jLaplacian_mass hu hv,
    spinLaplacian_mass hu hv]; simp

theorem projSum_difference : projSum R u v (u - v) = 0 := by
  rw [projSum_apply, phiLaplacian_difference hu hv, jLaplacian_difference,
    spinLaplacian_difference hu hv]
  simp only [mul_zero, mul_neg, mul_smul_comm, ← mul_assoc]
  abel

theorem projSum_spin : projSum R u v (u * v - v * u) = 0 := by
  rw [projSum_apply, phiLaplacian_spin hu hv, jLaplacian_spin hu hv, spinLaplacian_spin]
  simp only [mul_neg, mul_smul_comm, ← mul_assoc]
  abel

theorem projDifference_difference :
    projDifference R u v (u - v) =
      (8 : ℕ) • ((u * v + v * u) * (u * v + v * u) * (u - v)) := by
  rw [projDifference_apply, phiLaplacian_difference hu hv, jLaplacian_difference,
    spinLaplacian_difference hu hv]
  simp only [mul_zero, mul_neg, mul_smul_comm, ← mul_assoc]
  abel

theorem projDifference_mass : projDifference R u v (u * v + v * u) = 0 := by
  rw [projDifference_apply, phiLaplacian_mass hu hv, jLaplacian_mass hu hv,
    spinLaplacian_mass hu hv]; simp

theorem projDifference_sum : projDifference R u v (u + v) = 0 := by
  rw [projDifference_apply, phiLaplacian_sum, jLaplacian_sum hu hv, spinLaplacian_sum hu hv]
  simp only [mul_zero, mul_neg, mul_smul_comm, ← mul_assoc]
  abel

theorem projDifference_spin : projDifference R u v (u * v - v * u) = 0 := by
  rw [projDifference_apply, phiLaplacian_spin hu hv, jLaplacian_spin hu hv,
    spinLaplacian_spin]
  simp only [mul_neg, mul_smul_comm, ← mul_assoc]
  abel

theorem projSpin_spin :
    projSpin R u v (u * v - v * u) =
      (8 : ℕ) • ((u * v + v * u) * (u * v + v * u) * (u * v - v * u)) := by
  rw [projSpin_apply, phiLaplacian_spin hu hv, jLaplacian_spin hu hv, spinLaplacian_spin]
  simp only [mul_neg, mul_smul_comm, ← mul_assoc]
  abel

theorem projSpin_mass : projSpin R u v (u * v + v * u) = 0 := by
  rw [projSpin_apply, phiLaplacian_mass hu hv, jLaplacian_mass hu hv,
    spinLaplacian_mass hu hv]; simp

theorem projSpin_sum : projSpin R u v (u + v) = 0 := by
  rw [projSpin_apply, phiLaplacian_sum, jLaplacian_sum hu hv, spinLaplacian_sum hu hv]
  simp only [mul_zero, mul_neg, mul_smul_comm, ← mul_assoc]
  abel

theorem projSpin_difference : projSpin R u v (u - v) = 0 := by
  rw [projSpin_apply, phiLaplacian_difference hu hv, jLaplacian_difference,
    spinLaplacian_difference hu hv]
  simp only [mul_zero, mul_neg, mul_smul_comm, ← mul_assoc]
  abel

end Diagonal

/-! ### Second-order composition law

If a superoperator `T` commutes with `L_V` and `T g = 8 V² h`, then
`S (T g) = 8 V² S h` for any `S` commuting with `L_V`. Applied to the four
homogenized projectors this gives idempotency at weight `8 V²` and mutual
annihilation. -/

section SecondOrder

theorem apply_eight_massSq {S : Module.End R A}
    (hS : ∀ x, S ((u * v + v * u) * x) = (u * v + v * u) * S x) (g : A) :
    S ((8 : ℕ) • ((u * v + v * u) * (u * v + v * u) * g)) =
      (8 : ℕ) • ((u * v + v * u) * (u * v + v * u) * S g) := by
  rw [map_nsmul, mul_assoc, hS, hS, ← mul_assoc]

variable (hu : u * u = 0) (hv : v * v = 0)
include hu hv

theorem projMass_idem :
    projMass R u v (projMass R u v (u * v + v * u)) =
      (8 : ℕ) • ((u * v + v * u) * (u * v + v * u) * projMass R u v (u * v + v * u)) := by
  conv_lhs => rw [projMass_mass hu hv, apply_eight_massSq (projMass_mass_mul hu hv)]

theorem projSum_idem :
    projSum R u v (projSum R u v (u + v)) =
      (8 : ℕ) • ((u * v + v * u) * (u * v + v * u) * projSum R u v (u + v)) := by
  conv_lhs => rw [projSum_sum hu hv, apply_eight_massSq (projSum_mass_mul hu hv)]

theorem projDifference_idem :
    projDifference R u v (projDifference R u v (u - v)) =
      (8 : ℕ) • ((u * v + v * u) * (u * v + v * u) * projDifference R u v (u - v)) := by
  conv_lhs =>
    rw [projDifference_difference hu hv, apply_eight_massSq (projDifference_mass_mul hu hv)]

theorem projSpin_idem :
    projSpin R u v (projSpin R u v (u * v - v * u)) =
      (8 : ℕ) • ((u * v + v * u) * (u * v + v * u) * projSpin R u v (u * v - v * u)) := by
  conv_lhs => rw [projSpin_spin hu hv, apply_eight_massSq (projSpin_mass_mul hu hv)]

theorem projSum_projMass_mass : projSum R u v (projMass R u v (u * v + v * u)) = 0 := by
  rw [projMass_mass hu hv, apply_eight_massSq (projSum_mass_mul hu hv), projSum_mass hu hv]
  simp

theorem projDifference_projMass_mass :
    projDifference R u v (projMass R u v (u * v + v * u)) = 0 := by
  rw [projMass_mass hu hv, apply_eight_massSq (projDifference_mass_mul hu hv),
    projDifference_mass hu hv]
  simp

theorem projSpin_projMass_mass : projSpin R u v (projMass R u v (u * v + v * u)) = 0 := by
  rw [projMass_mass hu hv, apply_eight_massSq (projSpin_mass_mul hu hv), projSpin_mass hu hv]
  simp

theorem projMass_projSum_sum : projMass R u v (projSum R u v (u + v)) = 0 := by
  rw [projSum_sum hu hv, apply_eight_massSq (projMass_mass_mul hu hv), projMass_sum hu hv]
  simp

theorem projDifference_projSum_sum : projDifference R u v (projSum R u v (u + v)) = 0 := by
  rw [projSum_sum hu hv, apply_eight_massSq (projDifference_mass_mul hu hv),
    projDifference_sum hu hv]
  simp

theorem projSpin_projSum_sum : projSpin R u v (projSum R u v (u + v)) = 0 := by
  rw [projSum_sum hu hv, apply_eight_massSq (projSpin_mass_mul hu hv), projSpin_sum hu hv]
  simp

theorem projMass_projDifference_difference :
    projMass R u v (projDifference R u v (u - v)) = 0 := by
  rw [projDifference_difference hu hv, apply_eight_massSq (projMass_mass_mul hu hv),
    projMass_difference hu hv]
  simp

theorem projSum_projDifference_difference :
    projSum R u v (projDifference R u v (u - v)) = 0 := by
  rw [projDifference_difference hu hv, apply_eight_massSq (projSum_mass_mul hu hv),
    projSum_difference hu hv]
  simp

theorem projSpin_projDifference_difference :
    projSpin R u v (projDifference R u v (u - v)) = 0 := by
  rw [projDifference_difference hu hv, apply_eight_massSq (projSpin_mass_mul hu hv),
    projSpin_difference hu hv]
  simp

theorem projMass_projSpin_spin : projMass R u v (projSpin R u v (u * v - v * u)) = 0 := by
  rw [projSpin_spin hu hv, apply_eight_massSq (projMass_mass_mul hu hv), projMass_spin hu hv]
  simp

theorem projSum_projSpin_spin : projSum R u v (projSpin R u v (u * v - v * u)) = 0 := by
  rw [projSpin_spin hu hv, apply_eight_massSq (projSum_mass_mul hu hv), projSum_spin hu hv]
  simp

theorem projDifference_projSpin_spin :
    projDifference R u v (projSpin R u v (u * v - v * u)) = 0 := by
  rw [projSpin_spin hu hv, apply_eight_massSq (projDifference_mass_mul hu hv),
    projDifference_spin hu hv]
  simp

end SecondOrder

end InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral
