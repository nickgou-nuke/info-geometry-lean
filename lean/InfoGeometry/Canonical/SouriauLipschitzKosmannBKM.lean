/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.LipschitzWittRieszPrimary
import InfoGeometry.Canonical.SouriauKosmannLipschitzBridge
import InfoGeometry.Canonical.SouriauKillingLipschitzBridge
import InfoGeometry.Algebra.DerivationLieLane
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus
import InfoGeometry.Erlangen.BirkhoffHilbertConeMetric
import InfoGeometry.Canonical.BirkhoffHilbertChordSectorClosure
import InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
import InfoGeometry.Canonical.OperatorFrechetForms
import InfoGeometry.Canonical.ErlangenOperator2Bridge
import InfoGeometry.Canonical.BarbarescoSPILG2020
import InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap
import InfoGeometry.SuperMetriplectic.SouriauTomitaBKM

/-!
# Souriau, Lipschitz, Kosmann, and BKM Thermodynamic Geometry

## i. Overview
This module reconciles the Souriau–Lipschitz–Kosmann and Gibbs–BKM claims from
Turns 46–48 against the repository's verified Clifford, Lie-lane, Birkhoff–Hilbert,
and finite Gibbs-BKM owners without duplicating `hyperbolicRotor_darboux_and_spinGroup_witness`
in `R1R2R3UnifiedTriangleBridge.lean`.

## ii. Key results
- `M2-G1`: Unconditional Clifford scalar-sandwich scaling (`cliffordScalarMul_sandwich_scales`),
  the degenerate `Q = 0` boundary (`lipschitzGroup_zero_eq_bot`), and unit-conditioned
  Lipschitz scalar dilation (`lipschitzScalarUnit_mem_lipschitzGroup`,
  `lipschitzScalarDilated_mem_and_sandwich_scales`).
- `M2-G2`: Pure grade-2 `BivectorSubmodule` / `BivectorLie` packaged as a `LieActionLane`
  (`bivectorLieActionLane`) satisfying `IsLeibnizAction`, vector-range invariance, and
  Killing's polar equation (`bivectorLieActionLane_isLeibniz_and_killing`).
- `M2-G3`: Exact `Cl(1,1)` boost generator sign convention (`bivectorAction_q11_eq_boostGenerator`,
  `bivectorAction_q11_swap_eq_neg_boostGenerator`, `conformalAction_q11_eq_conformalBoostGenerator`,
  `polar_q11_eq_neg_two_minkowskiForm`).
- `M2-G4`: Lorentz boost invariance and Birkhoff–Hilbert projective isometry on the
  Rindler temperature cone (`boostFlowEquiv`,
  `boostFlow_preserves_interior_rindlerTemperatureCone`,
  `boostFlow_preserves_birkhoffHilbertMetric_rindlerCone`).
- `M2-G5`: Finite Gibbs heat-capacity identification with the symmetric nonnegative BKM Hessian
  (`souriau_gibbs_capacity_eq_bkm_hessian`, `souriau_gibbs_bkm_frechet_and_doubled_boundary`)
  together with the `DoubledSpace E` modular-swap Hessian separation boundary.

## iii. Table of contents
- Section 1 (`M2-G1`): Clifford scalar dilation, degenerate `Q = 0` boundary, and Lipschitz group.
- Section 2 (`M2-G2`): Grade-2 bivector Lie algebra and Leibniz `LieActionLane`.
- Section 3 (`M2-G3`): Exact `q11` boost generator sign and Minkowski polar calibration.
- Section 4 (`M2-G4`): Rindler temperature cone interior invariance and Birkhoff–Hilbert isometry.
- Section 5 (`M2-G5`): Souriau–Gibbs–BKM capacity equivalence and `DoubledSpace` boundary.

## iv. References
- `InfoGeometry.Clifford.LipschitzWittRieszPrimary`
- `InfoGeometry.Canonical.SouriauKosmannLipschitzBridge`
- `InfoGeometry.Canonical.SouriauKillingLipschitzBridge`
- `InfoGeometry.Algebra.DerivationLieLane`
- `InfoGeometry.Erlangen.BirkhoffHilbertConeMetric`
- `InfoGeometry.SuperMetriplectic.SouriauTomitaBKM`
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauLipschitzKosmannBKM

/-! ## Section 1: Clifford scalar dilation and Lipschitz group (`M2-G1`) -/

section CliffordScalarDilation

open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Clifford.LipschitzWittRieszPrimary

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Local scalar trace identity on `algebraMap R (CliffordAlgebra Q) r`, using the
public `InfoGeometry.Riemannian.hTrace_cl` map. -/
lemma hTrace_cl_algebraMap [Invertible (2 : R)] (Q : QuadraticForm R M) (r : R) :
    InfoGeometry.Riemannian.hTrace_cl Q (algebraMap R (CliffordAlgebra Q) r) = r := by
  change ExteriorAlgebra.algebraMapInv
      (CliffordAlgebra.equivExterior Q (algebraMap R (CliffordAlgebra Q) r)) = r
  rw [equivExterior_algebraMap]
  exact AlgHom.commutes (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R M →ₐ[R] R) r

/-- Injectivity of `algebraMap R (CliffordAlgebra Q)` when `2` is invertible in `R`. -/
lemma clifford_algebraMap_injective_of_inv2 [Invertible (2 : R)] (Q : QuadraticForm R M) :
    Function.Injective (algebraMap R (CliffordAlgebra Q)) := by
  intro r₁ r₂ h
  have ht := congrArg (InfoGeometry.Riemannian.hTrace_cl Q) h
  rwa [hTrace_cl_algebraMap, hTrace_cl_algebraMap] at ht

/-- Scalar unit in `(CliffordAlgebra Q)ˣ` induced by `c : Rˣ`. -/
def lipschitzScalarUnit (Q : QuadraticForm R M) (c : Rˣ) : (CliffordAlgebra Q)ˣ :=
  Units.map (algebraMap R (CliffordAlgebra Q)).toMonoidHom c

/-- Unconditional Clifford sandwich scaling under left scalar multiplication:
`(c • g) * ι Q v * reverse (c • g) = (c ^ 2) • (g * ι Q v * reverse g)`. -/
lemma cliffordScalarMul_sandwich_scales (Q : QuadraticForm R M)
    (c : R) (g : CliffordAlgebra Q) (v : M) :
    (algebraMap R (CliffordAlgebra Q) c * g) * CliffordAlgebra.ι Q v *
        CliffordAlgebra.reverse (Q := Q) (algebraMap R (CliffordAlgebra Q) c * g) =
      (c ^ 2) • (g * CliffordAlgebra.ι Q v * CliffordAlgebra.reverse (Q := Q) g) := by
  rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse.commutes]
  rw [Algebra.smul_def, sq, map_mul]
  calc
    (algebraMap R (CliffordAlgebra Q) c * g) * CliffordAlgebra.ι Q v *
        (CliffordAlgebra.reverse (Q := Q) g * algebraMap R (CliffordAlgebra Q) c)
        = algebraMap R (CliffordAlgebra Q) c *
            ((g * CliffordAlgebra.ι Q v * CliffordAlgebra.reverse (Q := Q) g) *
              algebraMap R (CliffordAlgebra Q) c) := by noncomm_ring
    _ = algebraMap R (CliffordAlgebra Q) c *
          (algebraMap R (CliffordAlgebra Q) c *
            (g * CliffordAlgebra.ι Q v * CliffordAlgebra.reverse (Q := Q) g)) := by
          rw [(Algebra.commutes c
            (g * CliffordAlgebra.ι Q v * CliffordAlgebra.reverse (Q := Q) g)).symm]
    _ = (algebraMap R (CliffordAlgebra Q) c * algebraMap R (CliffordAlgebra Q) c) *
          (g * CliffordAlgebra.ι Q v * CliffordAlgebra.reverse (Q := Q) g) := by
          noncomm_ring

/-- On the degenerate zero quadratic form `Q = 0`, the Lipschitz group collapses to `⊥`,
showing why scalar-unit membership in `_root_.lipschitzGroup Q` requires a unit vector. -/
lemma lipschitzGroup_zero_eq_bot :
    _root_.lipschitzGroup (0 : QuadraticForm R M) = ⊥ := by
  unfold _root_.lipschitzGroup
  rw [eq_bot_iff, Subgroup.closure_le]
  intro u hu
  rcases hu with ⟨a, ha⟩
  have hsq :
      (u : CliffordAlgebra (0 : QuadraticForm R M)) *
        (u : CliffordAlgebra (0 : QuadraticForm R M)) = 0 := by
    rw [← ha, CliffordAlgebra.ι_sq_scalar]
    simp
  have hone : (1 : CliffordAlgebra (0 : QuadraticForm R M)) = 0 := by
    let ui : CliffordAlgebra (0 : QuadraticForm R M) :=
      ((u⁻¹ : (CliffordAlgebra (0 : QuadraticForm R M))ˣ) : CliffordAlgebra (0 : QuadraticForm R M))
    have hmul_inv :
        (u : CliffordAlgebra (0 : QuadraticForm R M)) * ui = 1 := by
      change (u : CliffordAlgebra (0 : QuadraticForm R M)) *
          ((u⁻¹ : (CliffordAlgebra (0 : QuadraticForm R M))ˣ) :
            CliffordAlgebra (0 : QuadraticForm R M)) = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 :
        ((u : CliffordAlgebra (0 : QuadraticForm R M)) *
            (u : CliffordAlgebra (0 : QuadraticForm R M))) * (ui * ui) =
          (u : CliffordAlgebra (0 : QuadraticForm R M)) *
            ((u : CliffordAlgebra (0 : QuadraticForm R M)) * ui) * ui := by
      noncomm_ring
    rw [hsq, zero_mul, hmul_inv, mul_one, hmul_inv] at h2
    exact h2.symm
  change u = 1
  apply Units.ext
  calc
    (u : CliffordAlgebra (0 : QuadraticForm R M))
        = (u : CliffordAlgebra (0 : QuadraticForm R M)) * 1 := (mul_one _).symm
    _ = (u : CliffordAlgebra (0 : QuadraticForm R M)) * 0 := by rw [hone]
    _ = 0 := mul_zero _
    _ = 1 := hone.symm

/-- Whenever `Q` admits a vector `a` with `IsUnit (Q a)`, every scalar unit
`lipschitzScalarUnit Q c` factors as a product of two vector units and lies in
`_root_.lipschitzGroup Q`. -/
lemma lipschitzScalarUnit_mem_lipschitzGroup (Q : QuadraticForm R M)
    (hunit : ∃ a : M, IsUnit (Q a)) (c : Rˣ) :
    lipschitzScalarUnit Q c ∈ _root_.lipschitzGroup Q := by
  rcases hunit with ⟨a, hQa⟩
  let _ : Invertible (Q a) := hQa.invertible
  let u₁ : (CliffordAlgebra Q)ˣ :=
    ⟨CliffordAlgebra.ι Q ((c : R) • a),
     CliffordAlgebra.ι Q ((((c⁻¹ : Rˣ) : R) * ⅟(Q a)) • a),
     by
       rw [map_smul, map_smul, smul_mul_assoc, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
         Algebra.algebraMap_eq_smul_one, smul_smul, smul_smul]
       have hscalar : (c : R) * (((c⁻¹ : Rˣ) : R) * ⅟(Q a)) * Q a = 1 := by
         calc
           (c : R) * (((c⁻¹ : Rˣ) : R) * ⅟(Q a)) * Q a
               = ((c : R) * ((c⁻¹ : Rˣ) : R)) * (⅟(Q a) * Q a) := by ring
           _ = 1 * 1 := by rw [Units.mul_inv, invOf_mul_self]
           _ = 1 := one_mul 1
       rw [hscalar, one_smul],
     by
       rw [map_smul, map_smul, smul_mul_assoc, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
         Algebra.algebraMap_eq_smul_one, smul_smul, smul_smul]
       have hscalar : (((c⁻¹ : Rˣ) : R) * ⅟(Q a)) * (c : R) * Q a = 1 := by
         calc
           (((c⁻¹ : Rˣ) : R) * ⅟(Q a)) * (c : R) * Q a
               = (((c⁻¹ : Rˣ) : R) * (c : R)) * (⅟(Q a) * Q a) := by ring
           _ = 1 * 1 := by rw [Units.inv_mul, invOf_mul_self]
           _ = 1 := one_mul 1
       rw [hscalar, one_smul]⟩
  let u₂ : (CliffordAlgebra Q)ˣ :=
    ⟨CliffordAlgebra.ι Q (⅟(Q a) • a), CliffordAlgebra.ι Q a,
     by
       rw [map_smul, smul_mul_assoc, CliffordAlgebra.ι_sq_scalar,
         Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul],
     by
       rw [map_smul, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
         Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul]⟩
  have hu₁ : u₁ ∈ _root_.lipschitzGroup Q :=
    Subgroup.subset_closure ⟨(c : R) • a, rfl⟩
  have hu₂ : u₂ ∈ _root_.lipschitzGroup Q :=
    Subgroup.subset_closure ⟨⅟(Q a) • a, rfl⟩
  have hprod : u₁ * u₂ = lipschitzScalarUnit Q c := by
    apply Units.ext
    change CliffordAlgebra.ι Q ((c : R) • a) * CliffordAlgebra.ι Q (⅟(Q a) • a) =
      algebraMap R (CliffordAlgebra Q) (c : R)
    rw [map_smul, map_smul, smul_mul_assoc, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
      Algebra.algebraMap_eq_smul_one, smul_smul, smul_smul, mul_assoc, invOf_mul_self, mul_one,
      ← Algebra.algebraMap_eq_smul_one]
  rw [← hprod]
  exact Subgroup.mul_mem _ hu₁ hu₂

/-- Spinor norm and twisted-isometry action on a scalar unit `lipschitzScalarUnit Q c`. -/
lemma lipschitzScalarUnit_norm_and_isometry [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hunit : ∃ a : M, IsUnit (Q a)) (c : Rˣ) :
    let hc : lipschitzScalarUnit Q c ∈ _root_.lipschitzGroup Q :=
      lipschitzScalarUnit_mem_lipschitzGroup Q hunit c
    lipschitzSpinorNormHom Q ⟨lipschitzScalarUnit Q c, hc⟩ = c ^ 2 ∧
      lipschitzGroupToIsometryHom Q ⟨lipschitzScalarUnit Q c, hc⟩ = 1 := by
  intro hc
  refine ⟨?_, ?_⟩
  · apply Units.ext
    apply clifford_algebraMap_injective_of_inv2 Q
    change algebraMap R (CliffordAlgebra Q)
        (lipschitzSpinorNormVal Q ⟨lipschitzScalarUnit Q c, hc⟩) =
      algebraMap R (CliffordAlgebra Q) ((c ^ 2 : Rˣ) : R)
    rw [algebraMap_lipschitzSpinorNormVal]
    change CliffordAlgebra.reverse (Q := Q) (algebraMap R (CliffordAlgebra Q) (c : R)) *
        algebraMap R (CliffordAlgebra Q) (c : R) =
      algebraMap R (CliffordAlgebra Q) ((c : R) ^ 2)
    rw [CliffordAlgebra.reverse.commutes, sq, map_mul]
  · apply DFunLike.ext
    intro v
    apply clifford_ι_injective Q
    rw [ι_lipschitzGroupToIsometryHom]
    change CliffordAlgebra.involute (Q := Q) (algebraMap R (CliffordAlgebra Q) (c : R)) *
        CliffordAlgebra.ι Q v * algebraMap R (CliffordAlgebra Q) ((c⁻¹ : Rˣ) : R) =
      CliffordAlgebra.ι Q ((1 : Q.IsometryEquiv Q) v)
    rw [AlgHom.commutes, mul_assoc,
      ← Algebra.commutes ((c⁻¹ : Rˣ) : R) (CliffordAlgebra.ι Q v)]
    calc
      algebraMap R (CliffordAlgebra Q) (c : R) *
          (algebraMap R (CliffordAlgebra Q) ((c⁻¹ : Rˣ) : R) * CliffordAlgebra.ι Q v)
          = algebraMap R (CliffordAlgebra Q) ((c : R) * ((c⁻¹ : Rˣ) : R)) *
              CliffordAlgebra.ι Q v := by rw [map_mul, mul_assoc]
      _ = CliffordAlgebra.ι Q ((1 : Q.IsometryEquiv Q) v) := by
          rw [Units.mul_inv, map_one, one_mul]; rfl

/-- Scalar dilation of a Lipschitz group element stays in `_root_.lipschitzGroup Q` (when `Q`
attains a unit value), scales `lipschitzSpinorNormHom` by `c ^ 2`, preserves
`lipschitzGroupToIsometryHom`, and scales the un-normalized Clifford sandwich by `(c : R) ^ 2`. -/
lemma lipschitzScalarDilated_mem_and_sandwich_scales [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hunit : ∃ a : M, IsUnit (Q a)) (c : Rˣ) (g : _root_.lipschitzGroup Q) (v : M) :
    let hc : (lipschitzScalarUnit Q c * (g : (CliffordAlgebra Q)ˣ) : (CliffordAlgebra Q)ˣ) ∈
        _root_.lipschitzGroup Q :=
      Subgroup.mul_mem _ (lipschitzScalarUnit_mem_lipschitzGroup Q hunit c) g.2
    lipschitzSpinorNormHom Q ⟨lipschitzScalarUnit Q c * g.1, hc⟩ =
        c ^ 2 * lipschitzSpinorNormHom Q g ∧
      lipschitzGroupToIsometryHom Q ⟨lipschitzScalarUnit Q c * g.1, hc⟩ =
        lipschitzGroupToIsometryHom Q g ∧
      ((lipschitzScalarUnit Q c * (g : (CliffordAlgebra Q)ˣ) : (CliffordAlgebra Q)ˣ) :
          CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        CliffordAlgebra.reverse (Q := Q)
          ((lipschitzScalarUnit Q c * (g : (CliffordAlgebra Q)ˣ) : (CliffordAlgebra Q)ˣ) :
            CliffordAlgebra Q) =
        ((c : R) ^ 2) • ((g.1 : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
          CliffordAlgebra.reverse (Q := Q) (g.1 : CliffordAlgebra Q)) := by
  intro hc
  have hc₀ : lipschitzScalarUnit Q c ∈ _root_.lipschitzGroup Q :=
    lipschitzScalarUnit_mem_lipschitzGroup Q hunit c
  have hfac :
      (⟨lipschitzScalarUnit Q c * g.1, hc⟩ : _root_.lipschitzGroup Q) =
        ⟨lipschitzScalarUnit Q c, hc₀⟩ * g := by
    apply Subtype.ext
    rfl
  obtain ⟨hnorm₀, hisom₀⟩ := lipschitzScalarUnit_norm_and_isometry Q hunit c
  refine ⟨?_, ?_, ?_⟩
  · rw [hfac, map_mul, hnorm₀]
  · rw [hfac, map_mul, hisom₀, one_mul]
  · simpa [lipschitzScalarUnit] using
      cliffordScalarMul_sandwich_scales Q (c : R) (g.1 : CliffordAlgebra Q) v

end CliffordScalarDilation

/-! ## Section 2: Grade-2 bivector Lie algebra and `LieActionLane` (`M2-G2`) -/

section BivectorLieAction

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Algebra
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Canonical.SouriauKosmannLipschitzBridge
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

variable {M : Type*} [AddCommGroup M] [Module ℝ M] (Q : QuadraticForm ℝ M)

/-- Pure grade-2 bivector generator `(1 / 2) • (ι a * ι b - ι b * ι a)` in `CliffordAlgebra Q`. -/
def bivectorBasisElem (a b : M) : CliffordAlgebra Q :=
  (1 / 2 : ℝ) • (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b -
    CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q a)

/-- Relating `bivectorBasisElem Q a b` to `ι a * ι b` via the polar scalar part. -/
lemma bivectorBasisElem_add_polar (a b : M) :
    bivectorBasisElem Q a b +
        (1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a b) =
      CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b := by
  unfold bivectorBasisElem
  have hswap := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q) a b
  have hsub : CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b -
      CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q a =
      (2 : ℝ) • (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) -
        algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a b) := by
    rw [two_smul]
    calc
      CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b -
          CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q a
          = CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b +
              CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b -
              (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b +
                CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q a) := by noncomm_ring
      _ = _ := by rw [hswap]
  rw [hsub, smul_sub, smul_smul]
  have hhalf : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  rw [hhalf, one_smul, sub_add_cancel]

/-- Commutator with `bivectorBasisElem Q a b` equals the commutator with `ι a * ι b`. -/
lemma bivectorBasisElem_comm_eq (a b : M) (x : CliffordAlgebra Q) :
    bivectorBasisElem Q a b * x - x * bivectorBasisElem Q a b =
      (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) * x -
        x * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) := by
  have h := bivectorBasisElem_add_polar Q a b
  have hdef : bivectorBasisElem Q a b = CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b -
      (1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a b) :=
    eq_sub_of_add_eq h
  rw [hdef, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    ← Algebra.commutes (QuadraticMap.polar Q a b) x]
  noncomm_ring

/-- Pure grade-2 bivector submodule spanned by all `bivectorBasisElem Q a b`. -/
def BivectorSubmodule : Submodule ℝ (CliffordAlgebra Q) :=
  Submodule.span ℝ {B | ∃ a b : M, B = bivectorBasisElem Q a b}

/-- Carrier type for the grade-2 bivector Lie algebra `↥(BivectorSubmodule Q)`. -/
abbrev BivectorLie := ↥(BivectorSubmodule Q)

/-- Explicit closure formula for `(1 / 2) • [bivectorBasisElem Q a b, bivectorBasisElem Q c d]`
in terms of four bivector generators. -/
lemma bivectorBasisElem_halfCommutator_eq (a b c d : M) :
    (1 / 2 : ℝ) •
        (bivectorBasisElem Q a b * bivectorBasisElem Q c d -
          bivectorBasisElem Q c d * bivectorBasisElem Q a b) =
      (1 / 2 : ℝ) •
        (QuadraticMap.polar Q b c • bivectorBasisElem Q a d -
          QuadraticMap.polar Q a c • bivectorBasisElem Q b d +
          QuadraticMap.polar Q b d • bivectorBasisElem Q c a -
          QuadraticMap.polar Q a d • bivectorBasisElem Q c b) := by
  rw [bivectorBasisElem_comm_eq]
  have hcomm := congrArg
    (fun t => (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) * t -
      t * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b))
    (eq_sub_of_add_eq (bivectorBasisElem_add_polar Q c d))
  have hscalar_comm :
      (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) *
          ((1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q c d)) =
        ((1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q c d)) *
          (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) := by
    rw [mul_smul_comm, smul_mul_assoc, Algebra.commutes]
  have h1 :
      (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) * bivectorBasisElem Q c d -
          bivectorBasisElem Q c d * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) =
        (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) *
            (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q d) -
          (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q d) *
            (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) := by
    rw [hcomm, mul_sub, sub_mul, hscalar_comm]
    noncomm_ring
  rw [h1]
  have hsplit :
      (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) *
          (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q d) -
        (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q d) *
          (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) =
      (CliffordAlgebra.ι Q a * (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q c) -
        CliffordAlgebra.ι Q c * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b)) *
          CliffordAlgebra.ι Q d +
      CliffordAlgebra.ι Q c *
        (CliffordAlgebra.ι Q a * (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q d) -
          CliffordAlgebra.ι Q d * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b)) := by
    noncomm_ring
  rw [hsplit, bivector_commutator Q a b c, bivector_commutator Q a b d]
  have hsub_mul_l :
      (algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q b c) * CliffordAlgebra.ι Q a -
          algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a c) * CliffordAlgebra.ι Q b) *
        CliffordAlgebra.ι Q d =
        QuadraticMap.polar Q b c • (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q d) -
        QuadraticMap.polar Q a c • (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q d) := by
    simp only [Algebra.smul_def]
    noncomm_ring
  have hmul_sub_r :
      CliffordAlgebra.ι Q c *
          (algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q b d) * CliffordAlgebra.ι Q a -
            algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a d) * CliffordAlgebra.ι Q b) =
        QuadraticMap.polar Q b d • (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q a) -
        QuadraticMap.polar Q a d • (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q b) := by
    rw [mul_sub]
    have hc1 : CliffordAlgebra.ι Q c *
        (algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q b d) * CliffordAlgebra.ι Q a) =
        QuadraticMap.polar Q b d • (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q a) := by
      rw [Algebra.smul_def, Algebra.commutes (QuadraticMap.polar Q b d) (CliffordAlgebra.ι Q a),
        ← mul_assoc, ← Algebra.commutes (QuadraticMap.polar Q b d)
          (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q a)]
    have hc2 : CliffordAlgebra.ι Q c *
        (algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a d) * CliffordAlgebra.ι Q b) =
        QuadraticMap.polar Q a d • (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q b) := by
      rw [Algebra.smul_def, Algebra.commutes (QuadraticMap.polar Q a d) (CliffordAlgebra.ι Q b),
        ← mul_assoc, ← Algebra.commutes (QuadraticMap.polar Q a d)
          (CliffordAlgebra.ι Q c * CliffordAlgebra.ι Q b)]
    rw [hc1, hc2]
  rw [hsub_mul_l, hmul_sub_r]
  rw [← bivectorBasisElem_add_polar Q a d, ← bivectorBasisElem_add_polar Q b d,
    ← bivectorBasisElem_add_polar Q c a, ← bivectorBasisElem_add_polar Q c b]
  have hsmul_alg : ∀ r s : ℝ,
      r • ((1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) s) =
        algebraMap ℝ (CliffordAlgebra Q) (r * ((1 / 2 : ℝ) * s)) := fun r s => by
    rw [smul_smul, Algebra.smul_def, ← map_mul, mul_assoc]
  have hcancel :
      QuadraticMap.polar Q b c •
          ((1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a d)) -
        QuadraticMap.polar Q a c •
          ((1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q b d)) +
        QuadraticMap.polar Q b d •
          ((1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q c a)) -
        QuadraticMap.polar Q a d •
          ((1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q c b)) = 0 := by
    simp only [hsmul_alg, ← map_sub, ← map_add]
    rw [QuadraticMap.polar_comm Q c a, QuadraticMap.polar_comm Q c b]
    have hzero :
        QuadraticMap.polar Q b c * ((1 / 2 : ℝ) * QuadraticMap.polar Q a d) -
          QuadraticMap.polar Q a c * ((1 / 2 : ℝ) * QuadraticMap.polar Q b d) +
          QuadraticMap.polar Q b d * ((1 / 2 : ℝ) * QuadraticMap.polar Q a c) -
          QuadraticMap.polar Q a d * ((1 / 2 : ℝ) * QuadraticMap.polar Q b c) = 0 := by ring
    rw [hzero, map_zero]
  congr 1
  calc
    QuadraticMap.polar Q b c •
          (bivectorBasisElem Q a d +
            (1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a d)) -
        QuadraticMap.polar Q a c •
          (bivectorBasisElem Q b d +
            (1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q b d)) +
        (QuadraticMap.polar Q b d •
          (bivectorBasisElem Q c a +
            (1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q c a)) -
        QuadraticMap.polar Q a d •
          (bivectorBasisElem Q c b +
            (1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q c b)))
        = (QuadraticMap.polar Q b c • bivectorBasisElem Q a d -
            QuadraticMap.polar Q a c • bivectorBasisElem Q b d +
            QuadraticMap.polar Q b d • bivectorBasisElem Q c a -
            QuadraticMap.polar Q a d • bivectorBasisElem Q c b) +
          (QuadraticMap.polar Q b c •
              ((1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a d)) -
            QuadraticMap.polar Q a c •
              ((1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q b d)) +
            QuadraticMap.polar Q b d •
              ((1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q c a)) -
            QuadraticMap.polar Q a d •
              ((1 / 2 : ℝ) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q c b))) := by
          simp only [smul_add]
          abel
    _ = QuadraticMap.polar Q b c • bivectorBasisElem Q a d -
          QuadraticMap.polar Q a c • bivectorBasisElem Q b d +
          QuadraticMap.polar Q b d • bivectorBasisElem Q c a -
          QuadraticMap.polar Q a d • bivectorBasisElem Q c b := by
          rw [hcancel, add_zero]

/-- Closure of `BivectorSubmodule Q` under the normalized `(1 / 2) • [B₁, B₂]` bracket. -/
lemma bivector_halfCommutator_mem {B₁ B₂ : CliffordAlgebra Q}
    (h₁ : B₁ ∈ BivectorSubmodule Q) (h₂ : B₂ ∈ BivectorSubmodule Q) :
    (1 / 2 : ℝ) • (B₁ * B₂ - B₂ * B₁) ∈ BivectorSubmodule Q := by
  induction h₁ using Submodule.span_induction generalizing B₂ with
  | mem x hx =>
    rcases hx with ⟨a, b, rfl⟩
    induction h₂ using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨c, d, rfl⟩
      rw [bivectorBasisElem_halfCommutator_eq]
      refine Submodule.smul_mem _ _ ?_
      refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_) ?_
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, d, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, d, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, a, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, b, rfl⟩)
    | zero => simp
    | add y₁ y₂ _ _ hy₁ hy₂ =>
      have h : (1 / 2 : ℝ) • (bivectorBasisElem Q a b * (y₁ + y₂) -
          (y₁ + y₂) * bivectorBasisElem Q a b) =
          (1 / 2 : ℝ) • (bivectorBasisElem Q a b * y₁ - y₁ * bivectorBasisElem Q a b) +
          (1 / 2 : ℝ) • (bivectorBasisElem Q a b * y₂ - y₂ * bivectorBasisElem Q a b) := by
        rw [mul_add, add_mul, ← smul_add]
        congr 1
        abel
      rw [h]
      exact Submodule.add_mem _ hy₁ hy₂
    | smul r y _ hy =>
      have h : (1 / 2 : ℝ) • (bivectorBasisElem Q a b * (r • y) -
          (r • y) * bivectorBasisElem Q a b) =
          r • ((1 / 2 : ℝ) • (bivectorBasisElem Q a b * y - y * bivectorBasisElem Q a b)) := by
        rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_comm]
      rw [h]
      exact Submodule.smul_mem _ r hy
  | zero => simp
  | add x₁ x₂ _ _ hx₁ hx₂ =>
    have h : (1 / 2 : ℝ) • ((x₁ + x₂) * B₂ - B₂ * (x₁ + x₂)) =
        (1 / 2 : ℝ) • (x₁ * B₂ - B₂ * x₁) + (1 / 2 : ℝ) • (x₂ * B₂ - B₂ * x₂) := by
      rw [add_mul, mul_add, ← smul_add]
      congr 1
      abel
    rw [h]
    exact Submodule.add_mem _ (hx₁ h₂) (hx₂ h₂)
  | smul r x _ hx =>
    have h : (1 / 2 : ℝ) • ((r • x) * B₂ - B₂ * (r • x)) =
        r • ((1 / 2 : ℝ) • (x * B₂ - B₂ * x)) := by
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_comm]
    rw [h]
    exact Submodule.smul_mem _ r (hx h₂)

/-- Lie bracket `⁅B₁, B₂⁆ = (1 / 2) • [B₁, B₂]` on `BivectorLie Q`. -/
instance instBracketBivectorLie : Bracket (BivectorLie Q) (BivectorLie Q) where
  bracket B₁ B₂ :=
    ⟨(1 / 2 : ℝ) • (B₁.1 * B₂.1 - B₂.1 * B₁.1), bivector_halfCommutator_mem Q B₁.2 B₂.2⟩

/-- `LieRing` instance on `BivectorLie Q` with the `(1 / 2)`-normalized commutator. -/
instance instLieRingBivectorLie : LieRing (BivectorLie Q) where
  add_lie B₁ B₂ B₃ := by
    apply Subtype.ext
    change (1 / 2 : ℝ) • ((B₁.1 + B₂.1) * B₃.1 - B₃.1 * (B₁.1 + B₂.1)) =
      (1 / 2 : ℝ) • (B₁.1 * B₃.1 - B₃.1 * B₁.1) + (1 / 2 : ℝ) • (B₂.1 * B₃.1 - B₃.1 * B₂.1)
    rw [add_mul, mul_add, ← smul_add]
    congr 1
    abel
  lie_add B₁ B₂ B₃ := by
    apply Subtype.ext
    change (1 / 2 : ℝ) • (B₁.1 * (B₂.1 + B₃.1) - (B₂.1 + B₃.1) * B₁.1) =
      (1 / 2 : ℝ) • (B₁.1 * B₂.1 - B₂.1 * B₁.1) + (1 / 2 : ℝ) • (B₁.1 * B₃.1 - B₃.1 * B₁.1)
    rw [mul_add, add_mul, ← smul_add]
    congr 1
    abel
  lie_self B := by
    apply Subtype.ext
    change (1 / 2 : ℝ) • (B.1 * B.1 - B.1 * B.1) = 0
    simp
  leibniz_lie B₁ B₂ B₃ := by
    apply Subtype.ext
    change (1 / 2 : ℝ) • (B₁.1 * ((1 / 2 : ℝ) • (B₂.1 * B₃.1 - B₃.1 * B₂.1)) -
        ((1 / 2 : ℝ) • (B₂.1 * B₃.1 - B₃.1 * B₂.1)) * B₁.1) =
      (1 / 2 : ℝ) • (((1 / 2 : ℝ) • (B₁.1 * B₂.1 - B₂.1 * B₁.1)) * B₃.1 -
        B₃.1 * ((1 / 2 : ℝ) • (B₁.1 * B₂.1 - B₂.1 * B₁.1))) +
      (1 / 2 : ℝ) • (B₂.1 * ((1 / 2 : ℝ) • (B₁.1 * B₃.1 - B₃.1 * B₁.1)) -
        ((1 / 2 : ℝ) • (B₁.1 * B₃.1 - B₃.1 * B₁.1)) * B₂.1)
    simp only [mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_smul, ← smul_add]
    congr 1
    noncomm_ring

/-- `LieAlgebra ℝ` instance on `BivectorLie Q`. -/
instance instLieAlgebraBivectorLie : LieAlgebra ℝ (BivectorLie Q) where
  lie_smul r B₁ B₂ := by
    apply Subtype.ext
    change (1 / 2 : ℝ) • (B₁.1 * (r • B₂.1) - (r • B₂.1) * B₁.1) =
      r • ((1 / 2 : ℝ) • (B₁.1 * B₂.1 - B₂.1 * B₁.1))
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_comm]

/-- Endomorphism of `CliffordAlgebra Q` given by `x ↦ (1 / 2) • [B, x]`. -/
def bivectorEnd (B : BivectorLie Q) : Module.End ℝ (CliffordAlgebra Q) where
  toFun x := (1 / 2 : ℝ) • (B.1 * x - x * B.1)
  map_add' x y := by
    rw [mul_add, add_mul, ← smul_add]
    congr 1
    abel
  map_smul' r x := by
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_comm]
    rfl

/-- Canonical grade-2 bivector `LieActionLane ℝ (CliffordAlgebra Q)`. -/
def bivectorLieActionLane : LieActionLane ℝ (CliffordAlgebra Q) where
  L := BivectorLie Q
  lieRing := instLieRingBivectorLie Q
  lieAlgebra := instLieAlgebraBivectorLie Q
  act :=
    { toFun := bivectorEnd Q
      map_add' := fun B₁ B₂ => by
        ext x
        change (1 / 2 : ℝ) • ((B₁.1 + B₂.1) * x - x * (B₁.1 + B₂.1)) =
          (1 / 2 : ℝ) • (B₁.1 * x - x * B₁.1) + (1 / 2 : ℝ) • (B₂.1 * x - x * B₂.1)
        rw [add_mul, mul_add, ← smul_add]
        congr 1
        abel
      map_smul' := fun r B => by
        ext x
        change (1 / 2 : ℝ) • ((r • B.1) * x - x * (r • B.1)) =
          r • ((1 / 2 : ℝ) • (B.1 * x - x * B.1))
        rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_comm]
      map_lie' := fun {B₁ B₂} => by
        ext x
        change (1 / 2 : ℝ) • (((1 / 2 : ℝ) • (B₁.1 * B₂.1 - B₂.1 * B₁.1)) * x -
            x * ((1 / 2 : ℝ) • (B₁.1 * B₂.1 - B₂.1 * B₁.1))) =
          (1 / 2 : ℝ) • (B₁.1 * ((1 / 2 : ℝ) • (B₂.1 * x - x * B₂.1)) -
            ((1 / 2 : ℝ) • (B₂.1 * x - x * B₂.1)) * B₁.1) -
          (1 / 2 : ℝ) • (B₂.1 * ((1 / 2 : ℝ) • (B₁.1 * x - x * B₁.1)) -
            ((1 / 2 : ℝ) • (B₁.1 * x - x * B₁.1)) * B₂.1)
        simp only [mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_smul]
        congr 1
        noncomm_ring }

/-- The bivector `LieActionLane` preserves the embedded vector subspace `range (ι Q)`. -/
lemma bivectorLie_act_ι_mem_range (B : BivectorLie Q) (v : M) :
    (bivectorLieActionLane Q).operatorAction B (CliffordAlgebra.ι Q v) ∈
      LinearMap.range (CliffordAlgebra.ι Q) := by
  change (1 / 2 : ℝ) • (B.1 * CliffordAlgebra.ι Q v - CliffordAlgebra.ι Q v * B.1) ∈
    LinearMap.range (CliffordAlgebra.ι Q)
  rcases B with ⟨Bval, hB⟩
  induction hB using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨a, b, rfl⟩
    rw [bivectorBasisElem_comm_eq, mul_assoc, ← ι_bivectorAction Q a b v]
    exact ⟨bivectorAction Q a b v, rfl⟩
  | zero => simp
  | add x₁ x₂ _ _ hx₁ hx₂ =>
    have h : (1 / 2 : ℝ) • ((x₁ + x₂) * CliffordAlgebra.ι Q v -
        CliffordAlgebra.ι Q v * (x₁ + x₂)) =
        (1 / 2 : ℝ) • (x₁ * CliffordAlgebra.ι Q v - CliffordAlgebra.ι Q v * x₁) +
        (1 / 2 : ℝ) • (x₂ * CliffordAlgebra.ι Q v - CliffordAlgebra.ι Q v * x₂) := by
      rw [add_mul, mul_add, ← smul_add]
      congr 1
      abel
    rw [h]
    exact Submodule.add_mem _ hx₁ hx₂
  | smul r x _ hx =>
    have h : (1 / 2 : ℝ) • ((r • x) * CliffordAlgebra.ι Q v -
        CliffordAlgebra.ι Q v * (r • x)) =
        r • ((1 / 2 : ℝ) • (x * CliffordAlgebra.ι Q v - CliffordAlgebra.ι Q v * x)) := by
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_comm]
    rw [h]
    exact Submodule.smul_mem _ r hx

/-- Helper cancelling `CliffordAlgebra.ι Q` with `(LinearEquiv.ofInjective (CliffordAlgebra.ι Q) _).symm`. -/
lemma ι_ofInjective_symm (y : CliffordAlgebra Q)
    (hy : y ∈ LinearMap.range (CliffordAlgebra.ι Q)) :
    CliffordAlgebra.ι Q
        ((LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (clifford_ι_injective Q)).symm ⟨y, hy⟩) =
      y :=
  congrArg Subtype.val
    ((LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (clifford_ι_injective Q)).apply_symm_apply
      ⟨y, hy⟩)

/-- Induced vector-space endomorphism `bivectorLieVectorAction Q B : M →ₗ[ℝ] M` extracted
from `bivectorLieActionLane Q` via `LinearEquiv.ofInjective (CliffordAlgebra.ι Q)`. -/
def bivectorLieVectorAction : BivectorLie Q →ₗ[ℝ] (M →ₗ[ℝ] M) where
  toFun B :=
    { toFun := fun v =>
        (LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (clifford_ι_injective Q)).symm
          ⟨(bivectorLieActionLane Q).operatorAction B (CliffordAlgebra.ι Q v),
            bivectorLie_act_ι_mem_range Q B v⟩
      map_add' := fun u w => by
        apply clifford_ι_injective Q
        rw [ι_ofInjective_symm]
        conv_rhs => rw [map_add]
        rw [ι_ofInjective_symm, ι_ofInjective_symm, map_add]
        exact ((bivectorLieActionLane Q).operatorAction B).map_add _ _
      map_smul' := fun r u => by
        apply clifford_ι_injective Q
        rw [ι_ofInjective_symm]
        conv_rhs => rw [map_smul]
        rw [ι_ofInjective_symm, map_smul]
        exact ((bivectorLieActionLane Q).operatorAction B).map_smul r _ }
  map_add' B₁ B₂ := by
    ext v
    apply clifford_ι_injective Q
    change CliffordAlgebra.ι Q
        ((LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (clifford_ι_injective Q)).symm
          ⟨(bivectorLieActionLane Q).operatorAction (B₁ + B₂) (CliffordAlgebra.ι Q v),
            bivectorLie_act_ι_mem_range Q (B₁ + B₂) v⟩) =
      CliffordAlgebra.ι Q
        ((LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (clifford_ι_injective Q)).symm
          ⟨(bivectorLieActionLane Q).operatorAction B₁ (CliffordAlgebra.ι Q v),
            bivectorLie_act_ι_mem_range Q B₁ v⟩ +
         (LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (clifford_ι_injective Q)).symm
          ⟨(bivectorLieActionLane Q).operatorAction B₂ (CliffordAlgebra.ι Q v),
            bivectorLie_act_ι_mem_range Q B₂ v⟩)
    rw [map_add, ι_ofInjective_symm, ι_ofInjective_symm, ι_ofInjective_symm]
    have hadd :
        (bivectorLieActionLane Q).operatorAction (B₁ + B₂) =
          (bivectorLieActionLane Q).operatorAction B₁ +
            (bivectorLieActionLane Q).operatorAction B₂ :=
      (bivectorLieActionLane Q).operatorAction.map_add B₁ B₂
    rw [hadd, LinearMap.add_apply]
  map_smul' r B := by
    ext v
    apply clifford_ι_injective Q
    change CliffordAlgebra.ι Q
        ((LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (clifford_ι_injective Q)).symm
          ⟨(bivectorLieActionLane Q).operatorAction (r • B) (CliffordAlgebra.ι Q v),
            bivectorLie_act_ι_mem_range Q (r • B) v⟩) =
      CliffordAlgebra.ι Q
        (r • (LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (clifford_ι_injective Q)).symm
          ⟨(bivectorLieActionLane Q).operatorAction B (CliffordAlgebra.ι Q v),
            bivectorLie_act_ι_mem_range Q B v⟩)
    rw [map_smul, ι_ofInjective_symm, ι_ofInjective_symm]
    have hsmul :
        (bivectorLieActionLane Q).operatorAction (r • B) =
          r • (bivectorLieActionLane Q).operatorAction B :=
      (bivectorLieActionLane Q).operatorAction.map_smul r B
    rw [hsmul, LinearMap.smul_apply]

/-- On every bivector generator `bivectorBasisElem Q a b`, `bivectorLieVectorAction`
recovers `bivectorAction Q a b`. -/
lemma bivectorLieVectorAction_basis (a b : M) :
    bivectorLieVectorAction Q
        ⟨bivectorBasisElem Q a b, Submodule.subset_span ⟨a, b, rfl⟩⟩ =
      bivectorAction Q a b := by
  ext v
  apply clifford_ι_injective Q
  change CliffordAlgebra.ι Q
      ((LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (clifford_ι_injective Q)).symm
        ⟨(bivectorLieActionLane Q).operatorAction
            ⟨bivectorBasisElem Q a b, Submodule.subset_span ⟨a, b, rfl⟩⟩
            (CliffordAlgebra.ι Q v),
          bivectorLie_act_ι_mem_range Q
            ⟨bivectorBasisElem Q a b, Submodule.subset_span ⟨a, b, rfl⟩⟩ v⟩) =
    CliffordAlgebra.ι Q (bivectorAction Q a b v)
  rw [ι_ofInjective_symm]
  change (1 / 2 : ℝ) • (bivectorBasisElem Q a b * CliffordAlgebra.ι Q v -
      CliffordAlgebra.ι Q v * bivectorBasisElem Q a b) =
    CliffordAlgebra.ι Q (bivectorAction Q a b v)
  rw [bivectorBasisElem_comm_eq, mul_assoc, ← ι_bivectorAction]

/-- `bivectorLieActionLane Q` is a Leibniz derivation action on `CliffordAlgebra Q`,
preserves `LinearMap.range (CliffordAlgebra.ι Q)`, and induces Killing vector fields
on `(M, Q)` for every `B : BivectorLie Q`. -/
lemma bivectorLieActionLane_isLeibniz_and_killing (B : BivectorLie Q) (u w : M) :
    IsLeibnizAction (bivectorLieActionLane Q) ∧
      (∀ v : M, (bivectorLieActionLane Q).operatorAction B (CliffordAlgebra.ι Q v) ∈
        LinearMap.range (CliffordAlgebra.ι Q)) ∧
      QuadraticMap.polar Q (bivectorLieVectorAction Q B u) w +
        QuadraticMap.polar Q u (bivectorLieVectorAction Q B w) = 0 := by
  refine ⟨?_, bivectorLie_act_ι_mem_range Q B, ?_⟩
  · intro B' x y
    change (1 / 2 : ℝ) • (B'.1 * (x * y) - (x * y) * B'.1) =
      ((1 / 2 : ℝ) • (B'.1 * x - x * B'.1)) * y +
        x * ((1 / 2 : ℝ) • (B'.1 * y - y * B'.1))
    rw [smul_mul_assoc, mul_smul_comm, ← smul_add]
    congr 1
    noncomm_ring
  · rcases B with ⟨Bval, hB⟩
    induction hB using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨a, b, rfl⟩
      rw [bivectorLieVectorAction_basis Q a b]
      exact bivectorAction_isKilling Q a b u w
    | zero =>
      have hz : (⟨0, Submodule.zero_mem _⟩ : BivectorLie Q) = 0 := rfl
      rw [hz, map_zero, LinearMap.zero_apply, LinearMap.zero_apply,
        QuadraticMap.polar_zero_left, QuadraticMap.polar_zero_right, add_zero]
    | add x y hx hy ihx ihy =>
      have hadd : (⟨x + y, Submodule.add_mem _ hx hy⟩ : BivectorLie Q) =
          ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [hadd, map_add, LinearMap.add_apply, LinearMap.add_apply,
        QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
        add_add_add_comm, ihx, ihy, add_zero]
    | smul r x hx ih =>
      have hsmul : (⟨r • x, Submodule.smul_mem _ r hx⟩ : BivectorLie Q) =
          r • ⟨x, hx⟩ := rfl
      rw [hsmul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
        smul_eq_mul, smul_eq_mul, ← mul_add, ih, mul_zero]

end BivectorLieAction

/-! ## Section 3: Exact `q11` boost sign and Minkowski calibration (`M2-G3`) -/

section Q11BoostSign

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Canonical.SouriauKosmannLipschitzBridge
open InfoGeometry.Canonical.SouriauKillingLipschitzBridge hiding Vec11

/-- Exact calibration between `QuadraticMap.polar q11` and `-2 * minkowskiForm`. -/
lemma polar_q11_eq_neg_two_minkowskiForm (u v : Vec11) :
    QuadraticMap.polar q11 u v = -2 * minkowskiForm u v := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  simp [QuadraticMap.polar, q11_apply, minkowskiForm]
  ring

/-- First `Cl(1,1)` basis generator `ι q11 (1, 0)`. -/
def q11E0 : CliffordAlgebra q11 :=
  CliffordAlgebra.ι q11 ((1 : ℝ), (0 : ℝ))

/-- Second `Cl(1,1)` basis generator `ι q11 (0, 1)`. -/
def q11E1 : CliffordAlgebra q11 :=
  CliffordAlgebra.ι q11 ((0 : ℝ), (1 : ℝ))

/-- Explicit Clifford non-commutativity and anticommutation witness on `Cl(1,1)`:
`q11E0` and `q11E1` anticommute and do not commute. -/
lemma clifford_q11_noncommutative :
    q11E0 * q11E1 + q11E1 * q11E0 = 0 ∧ q11E0 * q11E1 ≠ q11E1 * q11E0 := by
  have hanti : q11E0 * q11E1 + q11E1 * q11E0 = 0 := by
    unfold q11E0 q11E1
    rw [CliffordAlgebra.ι_mul_ι_add_swap, polar_q11_eq_neg_two_minkowskiForm]
    norm_num [minkowskiForm]
  refine ⟨hanti, ?_⟩
  intro heq
  have htwo : (2 : ℝ) • (q11E0 * q11E1) = 0 := by
    rw [two_smul]
    calc
      q11E0 * q11E1 + q11E0 * q11E1 = q11E0 * q11E1 + q11E1 * q11E0 := by rw [← heq]
      _ = 0 := hanti
  have hprod : q11E0 * q11E1 = 0 := by
    have hsmul := congrArg (fun x : CliffordAlgebra q11 => (1 / 2 : ℝ) • x) htwo
    rw [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul, smul_zero] at hsmul
    exact hsmul
  have hsq : q11E0 * q11E0 = 1 := by
    unfold q11E0
    rw [CliffordAlgebra.ι_sq_scalar]
    norm_num [q11_apply]
  have hzero_vec :
      CliffordAlgebra.ι q11 ((0 : ℝ), (1 : ℝ)) = CliffordAlgebra.ι q11 ((0 : ℝ), (0 : ℝ)) := by
    calc
      CliffordAlgebra.ι q11 ((0 : ℝ), (1 : ℝ))
          = (q11E0 * q11E0) * q11E1 := by rw [hsq, one_mul]; rfl
      _ = q11E0 * (q11E0 * q11E1) := mul_assoc _ _ _
      _ = 0 := by rw [hprod, mul_zero]
      _ = CliffordAlgebra.ι q11 ((0 : ℝ), (0 : ℝ)) := by
          rw [show ((0 : ℝ), (0 : ℝ)) = 0 from rfl, map_zero]
  have hinj := InfoGeometry.Clifford.GradedGraceContraction.clifford_ι_injective q11 hzero_vec
  have h1 : (1 : ℝ) = 0 := congrArg Prod.snd hinj
  norm_num at h1

/-- Exact `Cl(1,1)` boost generator sign: `bivectorAction q11 (0, 1) (1, 0) = boostGenerator`. -/
lemma bivectorAction_q11_eq_boostGenerator (v : Vec11) :
    bivectorAction q11 ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) v = boostGenerator v := by
  rcases v with ⟨t, z⟩
  ext <;> simp [bivectorAction, QuadraticMap.polar, q11_apply, boostGenerator] <;> ring

/-- Swapping the bivector arguments negates the boost generator:
`bivectorAction q11 (1, 0) (0, 1) = -boostGenerator`. -/
lemma bivectorAction_q11_swap_eq_neg_boostGenerator (v : Vec11) :
    bivectorAction q11 ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) v = -boostGenerator v := by
  rcases v with ⟨t, z⟩
  ext <;> simp [bivectorAction, QuadraticMap.polar, q11_apply, boostGenerator] <;> ring

/-- Conformal boost generator `(2 * σ) • v + bivectorAction q11 (0, 1) (1, 0) v` agrees
with `conformalBoostGenerator σ v` and satisfies the conformal Killing identity. -/
lemma conformalAction_q11_eq_conformalBoostGenerator (σ : ℝ) (v : Vec11) :
    (2 * σ) • v + bivectorAction q11 ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) v =
      conformalBoostGenerator σ v := by
  rw [bivectorAction_q11_eq_boostGenerator]
  rcases v with ⟨t, z⟩
  ext <;> (simp [boostGenerator, conformalBoostGenerator]; try ring)

end Q11BoostSign

/-! ## Section 4: Rindler temperature cone Birkhoff–Hilbert isometry (`M2-G4`) -/

section RindlerConeBirkhoffHilbert

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Canonical.SouriauKillingLipschitzBridge hiding Vec11
open InfoGeometry.Erlangen.BirkhoffHilbertConeMetric

/-- Continuous linear equivalence on `Vec11 = ℝ × ℝ` realizing the Lorentz boost `boostFlow s`. -/
def boostFlowEquiv (s : ℝ) : Vec11 ≃L[ℝ] Vec11 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := boostFlow s
      invFun := boostFlow (-s)
      map_add' := fun u v => by
        rcases u with ⟨u₁, u₂⟩
        rcases v with ⟨v₁, v₂⟩
        ext <;> simp [boostFlow] <;> ring
      map_smul' := fun r v => by
        rcases v with ⟨v₁, v₂⟩
        ext <;> simp [boostFlow] <;> ring
      left_inv := fun v => by
        rw [← boostFlow_add, neg_add_cancel, boostFlow_zero]
      right_inv := fun v => by
        rw [← boostFlow_add, add_neg_cancel, boostFlow_zero] }

/-- `boostFlow s` preserves the topological interior of `rindlerTemperatureCone`. -/
lemma boostFlow_preserves_interior_rindlerTemperatureCone (s : ℝ) {v : Vec11}
    (hv : v ∈ interior (rindlerTemperatureCone : Set Vec11)) :
    boostFlow s v ∈ interior (rindlerTemperatureCone : Set Vec11) := by
  have himage :
      (boostFlowEquiv s).toHomeomorph '' (rindlerTemperatureCone : Set Vec11) =
        (rindlerTemperatureCone : Set Vec11) := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact boostFlow_preserves_rindlerTemperatureCone hu
    · intro hw
      refine ⟨boostFlow (-s) w, boostFlow_preserves_rindlerTemperatureCone hw, ?_⟩
      change boostFlow s (boostFlow (-s) w) = w
      rw [← boostFlow_add, add_neg_cancel, boostFlow_zero]
  have hin :
      (boostFlowEquiv s).toHomeomorph v ∈
        (boostFlowEquiv s).toHomeomorph '' interior (rindlerTemperatureCone : Set Vec11) :=
    ⟨v, hv, rfl⟩
  rw [(boostFlowEquiv s).toHomeomorph.image_interior, himage] at hin
  exact hin

/-- The Lorentz boost flow `boostFlow s` acts by isometries on the interior of
`rindlerTemperatureCone` with respect to `birkhoffHilbertMetric`. -/
lemma boostFlow_preserves_birkhoffHilbertMetric_rindlerCone (s : ℝ)
    {u v : Vec11}
    (hu : u ∈ interior (rindlerTemperatureCone : Set Vec11))
    (hv : v ∈ interior (rindlerTemperatureCone : Set Vec11)) :
    birkhoffHilbertMetric rindlerTemperatureCone (boostFlow s u) (boostFlow s v) =
      birkhoffHilbertMetric rindlerTemperatureCone u v := by
  exact birkhoffHilbertMetric_linearEquiv_isometry
    rindlerTemperatureCone rindlerTemperatureCone
    rindlerTemperatureCone_salient rindlerTemperatureCone_salient
    (boostFlowEquiv s)
    (fun _ hw => boostFlow_preserves_rindlerTemperatureCone hw)
    (fun _ hw => boostFlow_preserves_rindlerTemperatureCone hw)
    hu hv

end RindlerConeBirkhoffHilbert

/-! ## Section 5: Finite Gibbs capacity, BKM Hessian, and `DoubledSpace` boundary (`M2-G5`) -/

section SouriauGibbsBKM

open InfoGeometry.SuperMetriplectic
open InfoGeometry.Canonical.OperatorFrechetForms
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open InfoGeometry.Canonical.BarbarescoSPILG2020
open InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap

/-- Finite Souriau Gibbs heat capacity (`massieuHessian` / `massieuBilinForm`) equals the
symmetric nonnegative BKM covariance on every `FiniteGibbsBKMHessianModel`. -/
lemma souriau_gibbs_capacity_eq_bkm_hessian
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : FiniteGibbsBKMHessianModel n V) (v w : V) :
    M.massieuHessian v w = M.bkmCovariance v w ∧
      M.massieuBilinForm.IsSymm ∧ 0 ≤ M.massieuBilinForm v v :=
  ⟨M.massieuHessian_eq_bkmCovariance v w, M.massieuBilinForm_isSymm, M.massieuBilinForm_nonneg v⟩

/-- Fréchet exterior-derivative alignment, discrete Massieu second difference, and the
explicit `DoubledSpace E` modular-swap Hessian separation boundary (`SouriauTomitaBKM`). -/
lemma souriau_gibbs_bkm_frechet_and_doubled_boundary
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : FiniteGibbsBKMHessianModel n V) (v w : V) (β : ℚ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [Nontrivial E]
    (MD : FiniteGibbsBKMHessianModel n (InfoGeometry.Krein.DoubledSpace E))
    (z : InfoGeometry.Krein.DoubledSpace E) (x : E) :
    frechetExtDeriv (logPartitionOneForm n) M.hamiltonian ![M.observable v, M.observable w] = 0 ∧
      (secondFDerivLogPartitionReadout M.hamiltonian (M.observable v) (M.observable w)).re =
        M.bkmCovariance v w ∧
      massieu (β + 1) - 2 * massieu β + massieu (β - 1) = 1 ∧
      (¬ ∀ z' u : InfoGeometry.Krein.DoubledSpace E,
        MD.massieuHessian u u =
          (fderiv ℝ (fderiv ℝ
            (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z') u u) ∧
      (fderiv ℝ (fderiv ℝ
        (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z)
          (WithLp.toLp (2 : ENNReal) (x, 0))
          (WithLp.toLp (2 : ENNReal) (x, 0)) = -‖x‖ ^ 2 := by
  have halign := frechetExtDeriv_logPartition_bkmHessian_alignment
    M.hamiltonian M.hamiltonian_selfAdjoint M.partition_positive
    (M.observable v) (M.observable w) (M.observable_selfAdjoint v) (M.observable_selfAdjoint w)
  refine ⟨halign.1, halign.2.1, massieu_centered_second_difference β, ?_, ?_⟩
  · exact finiteGibbsBKMHessian_not_full_doubled_modularSwapHessian MD
  · exact hessian_quadraticMoment_modularSwap_firstSheet z x

end SouriauGibbsBKM

end InfoGeometry.Canonical.SouriauLipschitzKosmannBKM
