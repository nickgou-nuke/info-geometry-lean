/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.MobiusRealCotangentLift
import InfoGeometry.Volume.LogPotential
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Prod

/-!
# Ordinary and relative volume of real cotangent transport

The existing action on `Vector n × Covector n` is packaged as a native linear
equivalence, without identifying a vector space with its dual. Its ordinary
determinant is one for every invertible primal operator. The ratio of its two
block determinant characters is instead the square of the primal determinant.

Common nonzero scaling of both sectors multiplies ordinary volume by
`r ^ (2 * n)` and leaves the relative block character unchanged. These are
finite real linear-algebra statements for arbitrary operators; no commutation
or diagonalization of the primal operator is assumed. The relative character
is a readout of the two actual linear equivalences, not a construction of a
Berezinian for general supermatrices with off-diagonal blocks.
-/

noncomputable section

namespace InfoGeometry.Quantum.CotangentVolumeCharacters

open InfoGeometry.Quantum.DualFlatKreinGraph
open InfoGeometry.Quantum.MobiusRealCotangentLift
open InfoGeometry.Volume.LogPotential

variable {n : ℕ}

private theorem det_dualMap_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (g : V ≃ₗ[ℝ] V) :
    LinearEquiv.det g.dualMap = LinearEquiv.det g := by
  apply Units.ext
  simp only [LinearEquiv.coe_det]
  change LinearMap.det g.toLinearMap.dualMap = LinearMap.det g.toLinearMap
  exact LinearMap.det_dualMap g.toLinearMap

private theorem det_smulOfNeZero_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (r : ℝ) (hr : r ≠ 0) :
    LinearEquiv.det (LinearEquiv.smulOfNeZero (K := ℝ) (M := V) r hr) =
      (Units.mk0 r hr) ^ Module.finrank ℝ V := by
  apply Units.ext
  simp only [LinearEquiv.coe_det, Units.val_pow_eq_pow_val, Units.val_mk0]
  change LinearMap.det (r • (LinearMap.id : V →ₗ[ℝ] V)) =
    r ^ Module.finrank ℝ V
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]

private theorem finrank_covector (n : ℕ) :
    Module.finrank ℝ (Covector n) = n := by
  change Module.finrank ℝ (Module.Dual ℝ (Vector n)) = n
  rw [Subspace.dual_finrank_eq]
  exact finrank_euclideanSpace_fin

private theorem finrank_carrier (n : ℕ) :
    Module.finrank ℝ (Carrier n) = 2 * n := by
  change Module.finrank ℝ (Vector n × Covector n) = 2 * n
  rw [Module.finrank_prod, finrank_covector]
  simp [DualFlatKreinGraph.Vector, two_mul]

/-- The existing real cotangent action, now as a native linear equivalence. -/
def liftLinearEquiv (g : Vector n ≃ₗ[ℝ] Vector n) :
    Carrier n ≃ₗ[ℝ] Carrier n :=
  g.prodCongr g.symm.dualMap

/-- This packaging has exactly the previously constructed action. -/
@[simp] theorem liftLinearEquiv_apply (g : Vector n ≃ₗ[ℝ] Vector n)
    (x : Carrier n) : liftLinearEquiv g x = lift g x := rfl

/-- Composition retains the order of the original, possibly noncommuting,
primal operators. -/
theorem liftLinearEquiv_trans (g h : Vector n ≃ₗ[ℝ] Vector n) :
    liftLinearEquiv (g.trans h) = (liftLinearEquiv g).trans (liftLinearEquiv h) := by
  apply LinearEquiv.ext
  intro x
  exact lift_comp g h x

/-- Cotangent transport has ordinary determinant one for every primal
automorphism, including automorphisms that change primal volume. -/
@[simp] theorem det_liftLinearEquiv (g : Vector n ≃ₗ[ℝ] Vector n) :
    LinearEquiv.det (liftLinearEquiv g) = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change LinearMap.det
    (g.toLinearMap.prodMap g.symm.toLinearMap.dualMap) = (1 : ℝ)
  rw [LinearMap.det_prodMap, LinearMap.det_dualMap]
  exact g.det_mul_det_symm

/-- The repository's ordinary volume character is trivial on cotangent lifts. -/
@[simp] theorem volumeHom_liftLinearEquiv (g : Vector n ≃ₗ[ℝ] Vector n) :
    Base.VolumeHom (liftLinearEquiv g) = 1 :=
  det_liftLinearEquiv g

/-- The corresponding ordinary logarithmic volume potential vanishes. -/
@[simp] theorem logAbsVolume_liftLinearEquiv (g : Vector n ≃ₗ[ℝ] Vector n) :
    LogAbsVolume (liftLinearEquiv g) = 0 := by
  unfold LogAbsVolume
  rw [volumeHom_liftLinearEquiv]
  simp

/-- Relative determinant character of actual primal and dual automorphisms.
The two automorphisms retain their distinct carriers. -/
def relativeBlockCharacter
    (g : Vector n ≃ₗ[ℝ] Vector n)
    (h : Covector n ≃ₗ[ℝ] Covector n) : ℝˣ :=
  Base.VolumeHom g * (Base.VolumeHom h)⁻¹

/-- The relative readout is multiplicative under paired operator transport. -/
theorem relativeBlockCharacter_trans
    (g₁ g₂ : Vector n ≃ₗ[ℝ] Vector n)
    (h₁ h₂ : Covector n ≃ₗ[ℝ] Covector n) :
    relativeBlockCharacter (g₁.trans g₂) (h₁.trans h₂) =
      relativeBlockCharacter g₁ h₁ * relativeBlockCharacter g₂ h₂ := by
  simp [relativeBlockCharacter, Base.VolumeHom, LinearEquiv.det_trans,
    mul_assoc, mul_left_comm, mul_comm]

/-- Inverse-dual transport cancels in the ordinary determinant but doubles
the primal determinant character in the relative channel. -/
theorem relativeBlockCharacter_cotangent (g : Vector n ≃ₗ[ℝ] Vector n) :
    relativeBlockCharacter g g.symm.dualMap = (Base.VolumeHom g) ^ 2 := by
  unfold relativeBlockCharacter Base.VolumeHom
  rw [det_dualMap_eq, LinearEquiv.det_symm]
  simp [pow_two]

/-- A determinant-one primal operator has trivial relative character too. -/
theorem relativeBlockCharacter_cotangent_eq_one
    (g : Vector n ≃ₗ[ℝ] Vector n) (hg : Base.VolumeHom g = 1) :
    relativeBlockCharacter g g.symm.dualMap = 1 := by
  rw [relativeBlockCharacter_cotangent, hg, one_pow]

/-- Common dilation acts on both actual sectors by the same nonzero scalar. -/
def commonDilation (r : ℝ) (hr : r ≠ 0) : Carrier n ≃ₗ[ℝ] Carrier n :=
  (LinearEquiv.smulOfNeZero (K := ℝ) (M := Vector n) r hr).prodCongr
    (LinearEquiv.smulOfNeZero (K := ℝ) (M := Covector n) r hr)

@[simp] theorem commonDilation_apply (r : ℝ) (hr : r ≠ 0) (x : Carrier n) :
    commonDilation r hr x = r • x := rfl

theorem commonDilation_toLinearMap (r : ℝ) (hr : r ≠ 0) :
    (commonDilation (n := n) r hr).toLinearMap =
      r • (LinearMap.id : Carrier n →ₗ[ℝ] Carrier n) := by
  apply LinearMap.ext
  intro x
  rfl

/-- Ordinary volume sees the full dimension of the primal/dual carrier. -/
theorem det_commonDilation (r : ℝ) (hr : r ≠ 0) :
    LinearEquiv.det (commonDilation (n := n) r hr) =
      (Units.mk0 r hr) ^ (2 * n) := by
  apply Units.ext
  rw [LinearEquiv.coe_det, commonDilation_toLinearMap,
    LinearMap.det_smul, LinearMap.det_id, mul_one]
  change r ^ Module.finrank ℝ (Carrier n) = r ^ (2 * n)
  rw [finrank_carrier]

/-- Scalar-valued form of the actual native determinant calculation. -/
theorem coe_det_commonDilation (r : ℝ) (hr : r ≠ 0) :
    ((LinearEquiv.det (commonDilation (n := n) r hr) : ℝˣ) : ℝ) =
      r ^ (2 * n) := by
  rw [det_commonDilation]
  rfl

/-- Adding common scale to a cotangent transport changes ordinary volume only
by that common scale. -/
theorem det_commonDilation_trans_lift (r : ℝ) (hr : r ≠ 0)
    (g : Vector n ≃ₗ[ℝ] Vector n) :
    LinearEquiv.det ((commonDilation r hr).trans (liftLinearEquiv g)) =
      (Units.mk0 r hr) ^ (2 * n) := by
  rw [LinearEquiv.det_trans, det_liftLinearEquiv, one_mul, det_commonDilation]

/-- The ordinary logarithmic volume of common dilation has weight `2 * n`. -/
theorem logAbsVolume_commonDilation (r : ℝ) (hr : r ≠ 0) :
    LogAbsVolume (commonDilation (n := n) r hr) =
      ((2 * n : ℕ) : ℝ) * Real.log |r| := by
  unfold LogAbsVolume Base.VolumeHom
  rw [coe_det_commonDilation, abs_pow, Real.log_pow]

/-- Equal scaling of equal-dimensional primal and dual sectors has unit
relative character, including in dimension zero. -/
theorem relativeBlockCharacter_commonDilation (r : ℝ) (hr : r ≠ 0) :
    relativeBlockCharacter
      (LinearEquiv.smulOfNeZero (K := ℝ) (M := Vector n) r hr)
      (LinearEquiv.smulOfNeZero (K := ℝ) (M := Covector n) r hr) = 1 := by
  unfold relativeBlockCharacter Base.VolumeHom
  rw [det_smulOfNeZero_eq, det_smulOfNeZero_eq, finrank_covector]
  simp [DualFlatKreinGraph.Vector]

/-- Common scalar dilation preserves the relative character of arbitrary
primal and dual automorphisms, without a commutation assumption. -/
theorem relativeBlockCharacter_commonRescale (r : ℝ) (hr : r ≠ 0)
    (g : Vector n ≃ₗ[ℝ] Vector n)
    (h : Covector n ≃ₗ[ℝ] Covector n) :
    relativeBlockCharacter
      ((LinearEquiv.smulOfNeZero (K := ℝ) (M := Vector n) r hr).trans g)
      ((LinearEquiv.smulOfNeZero (K := ℝ) (M := Covector n) r hr).trans h) =
        relativeBlockCharacter g h := by
  rw [relativeBlockCharacter_trans, relativeBlockCharacter_commonDilation, one_mul]

end InfoGeometry.Quantum.CotangentVolumeCharacters
