/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.DoubledMinkowskiManifoldYangMillsPDE
import InfoGeometry.Lie.DoubledMinkowskiLatticeContinuumLimit
import InfoGeometry.Canonical.GradedChiralSpinMat4CCarrierMap
import InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

open InfoGeometry.Lie
open InfoGeometry.Clifford
open InfoGeometry.Clifford.SplitCl11GradedTensorTower
open InfoGeometry.Canonical.GradedChiralSpinMat4CCarrierMap
open scoped Topology

namespace InfoGeometry.Lie.GradedChiralSpinManifoldIdentification

/-- Euclidean 4-space carrier. -/
abbrev FourSpace := InfoGeometry.Canonical.RealDoubledChiralKreinFrame.FourSpace

/-!
# Smooth Yang–Mills & Lattice Continuum-Limit Identification with Graded Tower

This module formalizes the identification of the smooth Yang–Mills differential-form
geometry and the lattice `a → 0` continuum limits with the abstract tower of
graded tensor products of real `2 × 2` chiral spin matrices (`SplitClPower 2`):

1. **Carrier Identification (`liftToForms`, `splitClPowerTwoToMat4C`)**:
   Lifts `SplitClPower 2`-valued alternating differential forms (`SplitCl2Form k`)
   pointwise into continuous `Mat4C`-valued forms (`Mat4CForm k`).
2. **Algebraic Geometry Identification (`carrier_intertwines_commutator`,
   `carrier_intertwines_halfWedgeSelf`)**:
   Proves that the carrier map intertwines the non-Abelian matrix commutator
   and the pointwise quadratic wedge self-commutator `½ [A ∧ A]`.
3. **Continuum-Limit Identification (`carrier_intertwines_latticeCovariantDiff`,
   `carrier_intertwines_continuumCovariantDeriv`, `smooth_lattice_graded_tower_identification`)**:
   Proves that the normed lattice covariant difference `latticeCovariantDiff` and its
   `a → 0` continuum derivative `continuumCovariantDeriv` factor functorially through the
   real `2×2` graded tensor tower via `NormedSpace.map_exp` and `Matrix.exp_neg`.

## Three-bucket audit map

#### BUCKET 1: CLOSED FINITE THEOREMS
* `graded_tower_noncomm_witness`
* `carrier_intertwines_commutator`
* `carrier_intertwines_halfWedgeSelf`
* `carrier_intertwines_latticeCovariantDiff`
* `smooth_lattice_graded_tower_identification`

#### BUCKET 2: CONDITIONAL THEOREMS
* `carrier_intertwines_continuumCovariantDeriv` (for `DifferentiableAt ℝ` fields, via
  `tendsto_latticeCovariantDiff`)

#### BUCKET 3: OPEN CLOSURE DEBT
* Existence of 4D quantum Yang–Mills measures and a physical mass gap remains open.
-/

/-- Explicit T16 non-commutativity witness inside `SplitClPower 2` and `Mat4C`. -/
theorem graded_tower_noncomm_witness :
    (splitE01 * splitE10 ≠ splitE10 * splitE01) ∧
    (splitClPowerTwoToMat4C splitE01 * splitClPowerTwoToMat4C splitE10 ≠
      splitClPowerTwoToMat4C splitE10 * splitClPowerTwoToMat4C splitE01) := by
  refine ⟨fun h => splitClPowerTwoToMat4C_noncomm ?_, splitClPowerTwoToMat4C_noncomm⟩
  simpa only [map_mul] using congrArg splitClPowerTwoToMat4C h

/-- Pure algebraic `SplitClPower 2`-valued alternating `k`-form field on `FourSpace`. -/
abbrev SplitCl2Form (k : ℕ) :=
  FourSpace → (FourSpace [⋀^Fin k]→ₗ[ℝ] SplitClPower 2)

private def fin4BasisVec (j : Fin 4) : FourSpace := EuclideanSpace.single j 1

private lemma fourSpace_basis_decomp (v : FourSpace) :
    v = ∑ j : Fin 4, v j • fin4BasisVec j := by
  apply PiLp.ext
  intro a
  simp [fin4BasisVec, EuclideanSpace.single, Pi.single_apply]

section ElementwiseForms

open scoped Matrix.Norms.Elementwise

private lemma altMap_mat4C_bound {k : ℕ} (f : FourSpace [⋀^Fin k]→ₗ[ℝ] Mat4C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : Fin k → FourSpace, ‖f m‖ ≤ C * ∏ i : Fin k, ‖m i‖ := by
  let C : ℝ := ∑ α : Fin k → Fin 4, ‖f (fun i => fin4BasisVec (α i))‖
  refine ⟨C, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun m => ?_⟩
  have hm : m = fun i => ∑ j ∈ (Finset.univ : Finset (Fin 4)), m i j • fin4BasisVec j := by
    funext i
    exact fourSpace_basis_decomp (m i)
  have hexp : f m = ∑ α ∈ (Fintype.piFinset fun _ : Fin k => (Finset.univ : Finset (Fin 4))),
      (∏ i : Fin k, m i (α i)) • f (fun i => fin4BasisVec (α i)) := by
    conv_lhs => rw [hm]
    simpa [MultilinearMap.map_smul_univ] using
      (f.toMultilinearMap.map_sum_finset
        (A := fun _ : Fin k => (Finset.univ : Finset (Fin 4)))
        (g := fun i j => m i j • fin4BasisVec j))
  rw [hexp]
  calc
    ‖∑ α ∈ (Fintype.piFinset fun _ : Fin k => (Finset.univ : Finset (Fin 4))),
        (∏ i : Fin k, m i (α i)) • f (fun i => fin4BasisVec (α i))‖
        ≤ ∑ α ∈ (Fintype.piFinset fun _ : Fin k => (Finset.univ : Finset (Fin 4))),
            ‖(∏ i : Fin k, m i (α i)) • f (fun i => fin4BasisVec (α i))‖ := norm_sum_le _ _
    _ = ∑ α : Fin k → Fin 4,
          (∏ i : Fin k, ‖m i (α i)‖) * ‖f (fun i => fin4BasisVec (α i))‖ := by
          simp [norm_smul, norm_prod]
    _ ≤ ∑ α : Fin k → Fin 4,
          (∏ i : Fin k, ‖m i‖) * ‖f (fun i => fin4BasisVec (α i))‖ := by
          refine Finset.sum_le_sum fun α _ => ?_
          gcongr with i _
          exact PiLp.norm_apply_le (m i) (α i)
    _ = C * ∏ i : Fin k, ‖m i‖ := by
          rw [← Finset.mul_sum, mul_comm]

private def altMapMat4CToCont {k : ℕ} (f : FourSpace [⋀^Fin k]→ₗ[ℝ] Mat4C) :
    FourSpace [⋀^Fin k]→L[ℝ] Mat4C :=
  let h := altMap_mat4C_bound f
  AlternatingMap.mkContinuous f h.choose h.choose_spec.2

/-- Lift a `SplitClPower 2`-valued differential `k`-form pointwise into a continuous
`Mat4C`-valued differential `k`-form (`Mat4CForm k`). -/
def liftToForms (k : ℕ) (η : SplitCl2Form k) : Mat4CForm k :=
  fun x => altMapMat4CToCont (splitClPowerTwoToMat4C.toLinearMap.compAlternatingMap (η x))

@[simp]
theorem liftToForms_apply (k : ℕ) (η : SplitCl2Form k) (x : FourSpace) (w : Fin k → FourSpace) :
    liftToForms k η x w = splitClPowerTwoToMat4C (η x w) :=
  rfl

private lemma alt1_add (α : FourSpace [⋀^Fin 1]→ₗ[ℝ] SplitClPower 2) (u v : FourSpace) :
    α (fun _ => u + v) = α (fun _ => u) + α (fun _ => v) := by
  have h := α.map_update_add (fun _ => u) (0 : Fin 1) u v
  simpa [show Function.update (fun _ : Fin 1 => u) (0 : Fin 1) (u + v) = fun _ => u + v from
      funext fun k => by fin_cases k; simp,
    show Function.update (fun _ : Fin 1 => u) (0 : Fin 1) u = fun _ => u from
      funext fun k => by fin_cases k; simp,
    show Function.update (fun _ : Fin 1 => u) (0 : Fin 1) v = fun _ => v from
      funext fun k => by fin_cases k; simp] using h

private lemma alt1_smul (α : FourSpace [⋀^Fin 1]→ₗ[ℝ] SplitClPower 2) (c : ℝ) (u : FourSpace) :
    α (fun _ => c • u) = c • α (fun _ => u) := by
  have h := α.map_update_smul (fun _ => u) (0 : Fin 1) c u
  simpa [show Function.update (fun _ : Fin 1 => u) (0 : Fin 1) (c • u) = fun _ => c • u from
      funext fun k => by fin_cases k; simp,
    show Function.update (fun _ : Fin 1 => u) (0 : Fin 1) u = fun _ => u from
      funext fun k => by fin_cases k; simp] using h

/-- Intrinsic quadratic wedge self-commutator `½ [A ∧ A]` inside the graded tensor tower
`SplitClPower 2` (`(A ∧ A)(u, v) = [A(u), A(v)]`). -/
def splitClHalfWedgeSelf (A : SplitCl2Form 1) : SplitCl2Form 2 :=
  fun x =>
    { toFun := fun w =>
        A x (fun _ => w 0) * A x (fun _ => w 1) -
          A x (fun _ => w 1) * A x (fun _ => w 0)
      map_update_add' := fun m i v₁ v₂ => by
        fin_cases i
        · simp only [Function.update_apply]
          have h00 : (0 : Fin 2) = ⟨0, by omega⟩ := rfl
          have h10 : (1 : Fin 2) ≠ ⟨0, by omega⟩ := fun h => by
            have := congrArg Fin.val h; contradiction
          simp only [h00, h10, ↓reduceIte, alt1_add, add_mul, mul_add]
          abel
        · simp only [Function.update_apply]
          have h11 : (1 : Fin 2) = ⟨1, by omega⟩ := rfl
          have h01 : (0 : Fin 2) ≠ ⟨1, by omega⟩ := fun h => by
            have := congrArg Fin.val h; contradiction
          simp only [h11, h01, ↓reduceIte, alt1_add, mul_add, add_mul]
          abel
      map_update_smul' := fun m i c v => by
        fin_cases i
        · simp only [Function.update_apply]
          have h00 : (0 : Fin 2) = ⟨0, by omega⟩ := rfl
          have h10 : (1 : Fin 2) ≠ ⟨0, by omega⟩ := fun h => by
            have := congrArg Fin.val h; contradiction
          simp only [h00, h10, ↓reduceIte, alt1_smul, smul_mul_assoc, mul_smul_comm, smul_sub]
        · simp only [Function.update_apply]
          have h11 : (1 : Fin 2) = ⟨1, by omega⟩ := rfl
          have h01 : (0 : Fin 2) ≠ ⟨1, by omega⟩ := fun h => by
            have := congrArg Fin.val h; contradiction
          simp only [h11, h01, ↓reduceIte, alt1_smul, mul_smul_comm, smul_mul_assoc, smul_sub]
      map_eq_zero_of_eq' := fun m i j hm hij => by
        fin_cases i <;> fin_cases j <;> simp_all [sub_self] }

/-- The carrier map intertwines the algebraic matrix commutator. -/
theorem carrier_intertwines_commutator (X Y : SplitClPower 2) :
    splitClPowerTwoToMat4C (X * Y - Y * X) =
      splitClPowerTwoToMat4C X * splitClPowerTwoToMat4C Y -
        splitClPowerTwoToMat4C Y * splitClPowerTwoToMat4C X := by
  simp only [map_sub, map_mul]

/-- The carrier map intertwines the pointwise `halfWedgeSelf` quadratic curvature: lifting
`splitClHalfWedgeSelf A` from `SplitClPower 2` agrees identically with `halfWedgeSelf (liftToForms 1 A)`. -/
theorem carrier_intertwines_halfWedgeSelf (A : SplitCl2Form 1) (x : FourSpace) :
    liftToForms 2 (splitClHalfWedgeSelf A) x =
      halfWedgeSelf (liftToForms 1 A) x := by
  apply ContinuousAlternatingMap.ext
  intro w
  rw [halfWedgeSelf_apply, mat4CCommCLM_apply, liftToForms_apply]
  change splitClPowerTwoToMat4C
      (A x (fun _ => w 0) * A x (fun _ => w 1) -
        A x (fun _ => w 1) * A x (fun _ => w 0)) =
    splitClPowerTwoToMat4C (A x (fun _ => w 0)) * splitClPowerTwoToMat4C (A x (fun _ => w 1)) -
      splitClPowerTwoToMat4C (A x (fun _ => w 1)) * splitClPowerTwoToMat4C (A x (fun _ => w 0))
  exact carrier_intertwines_commutator _ _

end ElementwiseForms

section NormedLatticeIdentification

open scoped Matrix.Norms.Operator
open InfoGeometry.Canonical.RealDoubledChiralKreinFrame (frameBasis)

private def realToComplexMat4Hom : Mat4R →ₐ[ℝ] Mat4C :=
  (Algebra.ofId ℝ ℂ).mapMatrix

private lemma continuous_realToComplexMat4Hom : Continuous realToComplexMat4Hom :=
  realToComplexMat4Hom.toLinearMap.continuous_of_finiteDimensional

private lemma realToComplexMat4Hom_comp_equiv (X : SplitClPower 2) :
    realToComplexMat4Hom (splitClPowerEquivMat 2 X) = splitClPowerTwoToMat4C X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma realToComplexMat4Hom_exp (M : Mat4R) :
    realToComplexMat4Hom (NormedSpace.exp M) = NormedSpace.exp (realToComplexMat4Hom M) :=
  NormedSpace.map_exp realToComplexMat4Hom continuous_realToComplexMat4Hom M

/-- Intrinsic lattice covariant difference inside `SplitClPower 2` (`Mat4R`-normed transporter
pulled back along `splitClPowerEquivMat 2`). -/
def splitClLatticeCovariantDiff
    (A : FourSpace → Fin 4 → SplitClPower 2) (Φ : FourSpace → SplitClPower 2)
    (y : FourSpace) (μ : Fin 4) (a : ℝ) : SplitClPower 2 :=
  (splitClPowerEquivMat 2).symm
    (a⁻¹ • (NormedSpace.exp (a • splitClPowerEquivMat 2 (A y μ)) *
        splitClPowerEquivMat 2 (Φ (y + a • frameBasis μ)) *
        (NormedSpace.exp (a • splitClPowerEquivMat 2 (A y μ)))⁻¹ -
      splitClPowerEquivMat 2 (Φ y)))

set_option backward.isDefEq.respectTransparency false in
/-- The carrier map intertwines the lattice covariant difference `latticeCovariantDiff`
with its intrinsic `SplitClPower 2` realization `splitClLatticeCovariantDiff`. -/
theorem carrier_intertwines_latticeCovariantDiff
    (A : FourSpace → Fin 4 → SplitClPower 2) (Φ : FourSpace → SplitClPower 2)
    (y : FourSpace) (μ : Fin 4) (a : ℝ) :
    splitClPowerTwoToMat4C (splitClLatticeCovariantDiff A Φ y μ a) =
      latticeCovariantDiff (fun x k => splitClPowerTwoToMat4C (A x k))
        (fun x => splitClPowerTwoToMat4C (Φ x)) y μ a := by
  unfold splitClLatticeCovariantDiff latticeCovariantDiff
  rw [← realToComplexMat4Hom_comp_equiv]
  rw [AlgEquiv.apply_symm_apply]
  have hExp :
      realToComplexMat4Hom (NormedSpace.exp (a • splitClPowerEquivMat 2 (A y μ))) =
        NormedSpace.exp (a • splitClPowerTwoToMat4C (A y μ)) := by
    rw [realToComplexMat4Hom_exp, map_smul, realToComplexMat4Hom_comp_equiv]
  have hExpInv :
      realToComplexMat4Hom (NormedSpace.exp (a • splitClPowerEquivMat 2 (A y μ)))⁻¹ =
        (NormedSpace.exp (a • splitClPowerTwoToMat4C (A y μ)))⁻¹ := by
    rw [← Matrix.exp_neg, ← Matrix.exp_neg, realToComplexMat4Hom_exp,
      map_neg, map_smul, realToComplexMat4Hom_comp_equiv]
  simp only [map_smul, map_sub, map_mul, hExp, hExpInv, realToComplexMat4Hom_comp_equiv]

/-- Conditional `a → 0` continuum-limit identification: the lifted `SplitClPower 2` lattice
covariant difference converges to the continuum `Mat4C` covariant derivative. -/
theorem carrier_intertwines_continuumCovariantDeriv
    (A : FourSpace → Fin 4 → SplitClPower 2) (Φ : FourSpace → SplitClPower 2)
    (y : FourSpace) (μ : Fin 4)
    (hΦ : DifferentiableAt ℝ (fun x => splitClPowerTwoToMat4C (Φ x)) y) :
    Filter.Tendsto (fun a : ℝ => splitClPowerTwoToMat4C (splitClLatticeCovariantDiff A Φ y μ a))
      (𝓝[≠] 0)
      (𝓝 (continuumCovariantDeriv (fun x k => splitClPowerTwoToMat4C (A x k))
        (fun x => splitClPowerTwoToMat4C (Φ x)) y μ)) := by
  simpa only [carrier_intertwines_latticeCovariantDiff] using
    tendsto_latticeCovariantDiff (fun x k => splitClPowerTwoToMat4C (A x k))
      (fun x => splitClPowerTwoToMat4C (Φ x)) y μ hΦ

end NormedLatticeIdentification

/-- **Theorem (Smooth/Lattice identification with Graded Tower)**:
The carrier map `splitClPowerTwoToMat4C` intertwines both the normed lattice covariant difference
and the smooth differential-form quadratic self-commutator `halfWedgeSelf` directly with the
abstract graded `2 × 2` chiral tensor tower `SplitClPower 2`. -/
theorem smooth_lattice_graded_tower_identification :
    (∀ A Φ y μ a, splitClPowerTwoToMat4C (splitClLatticeCovariantDiff A Φ y μ a) =
      latticeCovariantDiff (fun x k => splitClPowerTwoToMat4C (A x k))
        (fun x => splitClPowerTwoToMat4C (Φ x)) y μ a) ∧
    (∀ A x, liftToForms 2 (splitClHalfWedgeSelf A) x =
      halfWedgeSelf (liftToForms 1 A) x) :=
  ⟨carrier_intertwines_latticeCovariantDiff, carrier_intertwines_halfWedgeSelf⟩

end InfoGeometry.Lie.GradedChiralSpinManifoldIdentification
