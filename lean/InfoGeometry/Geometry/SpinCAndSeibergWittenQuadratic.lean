/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.LipschitzWittRieszPrimary
import InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions
import InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis
import InfoGeometry.Canonical.KahlerAtiyahSpinConnection
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import InfoGeometry.Superalgebra.DonaldsonWittenSeibergMonopole
import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Circle
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
# `Spinᶜ` Group, `U(n) → Spinᶜ(2n)`, 4D Seiberg–Witten Quadratic Map & `C⁰` Bounds

This module formalizes the core Clifford, spinor, and algebraic foundations of Seiberg–Witten
theory from Nicolaescu (*Notes on Seiberg–Witten Theory*, Chapters 1–3):

1. **`Spinᶜ(V, Q)` & Canonical `U(n) →* Spinᶜ(2n)` Lift (Prop. 1.3.10)**:
   * `SpinCGroup Q ha := (_root_.spinGroup Q × Circle) ⧸ z2DiagSubgroup Q ha`, reusing
     `_root_.spinGroup Q` and `lipschitz_pin_spin_doubleCover_witness` from
     `InfoGeometry.Clifford.LipschitzWittRieszPrimary`.
   * Exact-sequence homomorphisms `spinCToIsometryHom : SpinCGroup Q ha →* Q.IsometryEquiv Q`,
     `spinCToCircleHom : SpinCGroup Q ha →* Circle` (`[g, z] ↦ z²`), injective embeddings
     `spinToSpinCHom` and `circleToSpinCHom`, and faithful complexified Clifford embedding
     `spinCEmbed : SpinCGroup Q ha →* (ℂ ⊗[ℝ] CliffordAlgebra Q)ˣ`.
   * Algebraic Householder/exterior-spinor construction of the canonical homomorphism
     `unitaryToSpinCHom : Matrix.unitaryGroup (Fin n) ℂ →* SpinC (2 * n)` (`[NeZero n]`)
     satisfying `spinCToIsometryHom ∘ unitaryToSpinCHom = realifyIsometry` and
     `spinCToCircleHom ∘ unitaryToSpinCHom = det` (Prop. 1.3.10), plus explicit 4D
     `SpinC4UnitaryPair` compatibility (`xiJ4D`).
2. **Genuine 4D Seiberg–Witten Quadratic Map `q(ψ)` & `su(2) ≃ Λ²₊(ℝ⁴)` (Ex. 1.3.3, Lemma 2.1.5, Prop. 3.2.4)**:
   * `swQuadraticMap4D (ψ : Fin 2 → ℂ) := ψ ψ* - (1/2)‖ψ‖² I₂` (traceless Hermitian endomorphism)
     and its `su(2)` skew-Hermitian counterpart `swQuadraticSkew4D ψ := I • swQuadraticMap4D ψ`.
   * Exact Frobenius norm `tr(q(ψ) q(ψ)ᴴ) = (1/2) ‖ψ‖⁴`, `U(2)`-equivariance, traceless
     Hermitian operator bound `|⟨Tψ, ψ⟩| ≤ 2 r ‖ψ‖²`, explicit `su(2) ≃ Λ²₊(ℝ⁴)` isomorphism
     via `cliffordSDAction`, and Kähler `(α, β)` splitting + vortex decoupling (Prop. 3.2.4).
3. **Algebraic Lichnerowicz / Energy Identity (Prop. 2.1.4) & `C⁰` Pointwise Bound (Lemma 2.2.3, Cor. 2.2.6)**:
   * Exact cancelling pointwise Seiberg–Witten energy identity (noting Nicolaescu's printed
     factor-of-`1/2` discrepancy between Def. 2.1.3 and Prop. 2.1.4, and establishing both
     normalizations).
   * Maximum-principle `C⁰` bounds `‖ψ‖² ≤ 2 * max 0 (-s + 4‖η⁺‖)` (Nicolaescu Lemma 2.2.3)
     and `‖ψ‖² ≤ max 0 (-s + 4‖η⁺‖)` (unit-`q` normalization), yielding Corollary 2.2.6:
     `0 ≤ s ∧ ‖η⁺‖ ≤ s / 4 → ψ = 0`.
   * Reuses `KahlerDiracWeitzenbockSynthesis` (`exteriorWedge`, `exteriorContract`,
     `exterior_cartan_homotopy_car`) and `CliffordExtensiveRotorsAndBiquaternions`
     (`cliffordNegSqForm`, `cGen`, `cBlade`, `bladeRepr`).

## Long-Term Mathlib Frontiers

Smooth 4-manifold Sobolev/Fredholm moduli spaces, Riemannian Lichnerowicz curvature
derivations on smooth `Spinᶜ` bundles, and global PDE compactness/gluing theorems
(Nicolaescu Ch. 1.2, 1.5, 2.2–2.3, 4) lie beyond current Mathlib manifold infrastructure and
are documented honestly here without axioms or `sorry`.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Geometry.SpinCAndSeibergWittenQuadratic

open CliffordAlgebra Matrix
open scoped TensorProduct
open InfoGeometry.Clifford.LipschitzWittRieszPrimary
open InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions
open InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis
open InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis

/-!
## Section 0: Closed Non-Commutativity Witnesses (`T16`)
-/

section NonCommutativityWitnesses

/-- Closed `T16` non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem complex_mat2_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
  refine ⟨X, Z, ?_⟩
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [X, Z, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- Closed `T16` non-commutativity witness for `Matrix (Fin n) (Fin n) ℂ` (`2 ≤ n`). -/
theorem complex_matN_noncomm_witness (n : ℕ) (hn : 2 ≤ n) :
    ∃ A B : Matrix (Fin n) (Fin n) ℂ, A * B ≠ B * A := by
  let i0 : Fin n := ⟨0, lt_of_lt_of_le (by omega) hn⟩
  let i1 : Fin n := ⟨1, lt_of_lt_of_le (by omega) hn⟩
  have hne : i0 ≠ i1 := by
    intro h
    have hv : (i0 : ℕ) = (i1 : ℕ) := congrArg Fin.val h
    simp [i0, i1] at hv
  let E01 : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if i = i0 ∧ j = i1 then 1 else 0
  let E10 : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if i = i1 ∧ j = i0 then 1 else 0
  refine ⟨E01, E10, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h i0) i0
  simp [E01, E10, Matrix.mul_apply, hne] at h00

/-- Closed `T16` non-commutativity witness for `ℂ ⊗[ℝ] CliffordAlgebra (cliffordNegSqForm ℝ 4)`. -/
theorem complexified_clifford4_noncomm_witness :
    ∃ x y : ℂ ⊗[ℝ] CliffordAlgebra (cliffordNegSqForm ℝ 4), x * y ≠ y * x := by
  refine ⟨(1 : ℂ) ⊗ₜ[ℝ] cGen ℝ 4 0, (1 : ℂ) ⊗ₜ[ℝ] cGen ℝ 4 1, ?_⟩
  intro h
  let projRe : ℂ ⊗[ℝ] CliffordAlgebra (cliffordNegSqForm ℝ 4) →ₗ[ℝ]
      CliffordAlgebra (cliffordNegSqForm ℝ 4) :=
    TensorProduct.lift (LinearMap.lsmul ℝ (CliffordAlgebra (cliffordNegSqForm ℝ 4)) ∘ₗ
      Complex.reLm)
  have hre := congrArg projRe h
  simp only [projRe, Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.lift.tmul,
    LinearMap.comp_apply, LinearMap.lsmul_apply] at hre
  change (1 : ℂ).re • (cGen ℝ 4 0 * cGen ℝ 4 1) = (1 : ℂ).re • (cGen ℝ 4 1 * cGen ℝ 4 0) at hre
  simp only [Complex.one_re, one_smul] at hre
  exact cGen4_noncomm_witness hre

/-- Closed `T16` non-commutativity witness for `Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ))`
when `1 ≤ n`. -/
theorem exterior_end_noncomm_witness (n : ℕ) (hn : 1 ≤ n) :
    ∃ A B : Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)), A * B ≠ B * A := by
  let i0 : Fin n := ⟨0, hn⟩
  let v : Fin n → ℂ := Pi.single i0 1
  let φ : Module.Dual ℂ (Fin n → ℂ) := LinearMap.proj i0
  refine ⟨exteriorWedge ℂ v, exteriorContract φ, ?_⟩
  intro h
  have h1 := congrArg (fun T : Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) => T 1) h
  have hcar := congrArg (fun T : Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) => T 1)
    (exterior_cartan_homotopy_car (R := ℂ) φ v)
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply]
    at hcar
  have hv_phi : φ v = 1 := by simp [φ, v]
  rw [hv_phi, one_smul] at hcar
  have hc1 : exteriorContract φ (1 : ExteriorAlgebra ℂ (Fin n → ℂ)) = 0 :=
    exteriorContract_one φ
  have h2 : exteriorWedge ℂ v (exteriorContract φ 1) =
      exteriorContract φ (exteriorWedge ℂ v 1) := h1
  rw [hc1, map_zero] at h2
  rw [← h2, zero_add] at hcar
  rw [hc1, map_zero] at hcar
  have hdeg : (1 : ExteriorAlgebra ℂ (Fin n → ℂ)) ≠ 0 := one_ne_zero
  exact hdeg hcar.symm

end NonCommutativityWitnesses

/-!
## Section 1: `SpinCGroup`, Exact Sequence, `spinCEmbed`, and `U(n) →* SpinC(2n)` (Prop. 1.3.10)
-/

section SpinCGroupSection

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The central element `-1` inside Mathlib's `_root_.spinGroup Q`. -/
def negOneSpinGroup (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    _root_.spinGroup Q :=
  ⟨-1, (lipschitz_pin_spin_doubleCover_witness Q ha).2.2.1⟩

@[simp]
theorem coe_negOneSpinGroup (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    ((negOneSpinGroup Q ha : _root_.spinGroup Q) : CliffordAlgebra Q) = -1 := rfl

@[simp]
theorem negOneSpinGroup_sq (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    negOneSpinGroup Q ha * negOneSpinGroup Q ha = 1 := by
  apply Subtype.ext
  change (-1 : CliffordAlgebra Q) * (-1 : CliffordAlgebra Q) = 1
  simp

@[simp]
theorem negOneSpinGroup_inv (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    (negOneSpinGroup Q ha)⁻¹ = negOneSpinGroup Q ha := by
  apply Subtype.ext
  change star (-1 : CliffordAlgebra Q) = -1
  simp

theorem negOneSpinGroup_ne_one (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    negOneSpinGroup Q ha ≠ 1 := by
  intro h
  have hc := congrArg (fun g : _root_.spinGroup Q => (g : CliffordAlgebra Q)) h
  exact (lipschitz_pin_spin_doubleCover_witness Q ha).2.2.2.1 hc

/-- Diagonal central subgroup `ℤ₂ = {(1, 1), (-1, -1)} ⊆ Spin(V, Q) × S¹`. -/
def z2DiagSubgroup (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    Subgroup (_root_.spinGroup Q × Circle) where
  carrier := { (1, 1), (negOneSpinGroup Q ha, -1) }
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro ⟨g₁, z₁⟩ ⟨g₂, z₂⟩ h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · simp_all
    · right; simp_all
    · right; simp_all
    · left
      have hg : g₁ = negOneSpinGroup Q ha := congrArg Prod.fst h₁
      have hz : z₁ = -1 := congrArg Prod.snd h₁
      have hg2 : g₂ = negOneSpinGroup Q ha := congrArg Prod.fst h₂
      have hz2 : z₂ = -1 := congrArg Prod.snd h₂
      ext <;> simp [hg, hg2, hz, hz2]
  inv_mem' := by
    rintro ⟨g, z⟩ h
    rcases h with h | h
    · left; simp_all
    · right
      have hg : g = negOneSpinGroup Q ha := congrArg Prod.fst h
      have hz : z = -1 := congrArg Prod.snd h
      ext <;> simp [hg, hz]

instance z2DiagSubgroup_normal (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    (z2DiagSubgroup Q ha).Normal where
  conj_mem := by
    rintro ⟨g, z⟩ h ⟨k, w⟩
    rcases h with h | h
    · left
      have hg : g = 1 := congrArg Prod.fst h
      have hz : z = 1 := congrArg Prod.snd h
      simp [hg, hz]
    · right
      have hg : g = negOneSpinGroup Q ha := congrArg Prod.fst h
      have hz : z = -1 := congrArg Prod.snd h
      have h1 : k * g * k⁻¹ = negOneSpinGroup Q ha := by
        apply Subtype.ext
        change (k : CliffordAlgebra Q) * (g : CliffordAlgebra Q) *
          ((k⁻¹ : _root_.spinGroup Q) : CliffordAlgebra Q) = -1
        rw [hg, coe_negOneSpinGroup]
        have hmul : k * k⁻¹ = (1 : _root_.spinGroup Q) := mul_inv_cancel k
        have hmul' : (k : CliffordAlgebra Q) * ((k⁻¹ : _root_.spinGroup Q) : CliffordAlgebra Q) = 1 :=
          congrArg (fun u : _root_.spinGroup Q => (u : CliffordAlgebra Q)) hmul
        calc
          (k : CliffordAlgebra Q) * (-1 : CliffordAlgebra Q) *
              ((k⁻¹ : _root_.spinGroup Q) : CliffordAlgebra Q)
              = -((k : CliffordAlgebra Q) * ((k⁻¹ : _root_.spinGroup Q) : CliffordAlgebra Q)) := by
                noncomm_ring
          _ = -1 := by rw [hmul']
      have h2 : w * z * w⁻¹ = -1 := by
        rw [hz, mul_comm w (-1), mul_assoc, mul_inv_cancel, mul_one]
      exact Prod.ext h1 h2

/-- The `Spinᶜ(V, Q)` group `(Spin(V, Q) × S¹) ⧸ {(1, 1), (-1, -1)}` (Nicolaescu §1.3.2). -/
abbrev SpinCGroup (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) : Type _ :=
  (_root_.spinGroup Q × Circle) ⧸ z2DiagSubgroup Q ha

theorem spinGroupToIsometryHom_negOne (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    spinGroupToIsometryHom Q (negOneSpinGroup Q ha) = 1 := by
  apply DFunLike.ext
  intro v
  apply InfoGeometry.Clifford.GradedGraceContraction.clifford_ι_injective Q
  change CliffordAlgebra.ι Q (spinGroupIsometryEquiv Q (negOneSpinGroup Q ha) v) =
    CliffordAlgebra.ι Q v
  rw [ι_spinGroupIsometryEquiv]
  simp [negOneSpinGroup]

/-- Double cover projection `Spinᶜ(V, Q) →* SO(V, Q)` sending `[(g, z)]` to `spinGroupToIsometryHom g`. -/
def spinCToIsometryHom (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    SpinCGroup Q ha →* Q.IsometryEquiv Q :=
  QuotientGroup.lift (z2DiagSubgroup Q ha)
    (MonoidHom.comp (spinGroupToIsometryHom Q) (MonoidHom.fst (_root_.spinGroup Q) Circle))
    (by
      rintro ⟨g, z⟩ h
      rcases h with h | h
      · have hg : g = 1 := congrArg Prod.fst h
        simp [hg]
      · have hg : g = negOneSpinGroup Q ha := congrArg Prod.fst h
        simp [hg, spinGroupToIsometryHom_negOne Q ha])

@[simp]
theorem spinCToIsometryHom_mk (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a))
    (g : _root_.spinGroup Q) (z : Circle) :
    spinCToIsometryHom Q ha (QuotientGroup.mk (g, z)) = spinGroupToIsometryHom Q g := rfl

/-- Determinant character `Spinᶜ(V, Q) →* S¹` sending `[(g, z)] ↦ z²`. -/
def spinCToCircleHom (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    SpinCGroup Q ha →* Circle :=
  QuotientGroup.lift (z2DiagSubgroup Q ha)
    ({ toFun := fun p => p.2 ^ 2
       map_one' := by simp
       map_mul' := fun p q => by simp [mul_pow] } : _root_.spinGroup Q × Circle →* Circle)
    (by
      rintro ⟨g, z⟩ h
      rcases h with h | h
      · have hz : z = 1 := congrArg Prod.snd h
        simp [hz]
      · have hz : z = -1 := congrArg Prod.snd h
        simp [hz])

@[simp]
theorem spinCToCircleHom_mk (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a))
    (g : _root_.spinGroup Q) (z : Circle) :
    spinCToCircleHom Q ha (QuotientGroup.mk (g, z)) = z ^ 2 := rfl

/-- Canonical inclusion `Spin(V, Q) →* Spinᶜ(V, Q)`, `g ↦ [(g, 1)]`. -/
def spinToSpinCHom (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    _root_.spinGroup Q →* SpinCGroup Q ha :=
  (QuotientGroup.mk' (z2DiagSubgroup Q ha)).comp (MonoidHom.inl (_root_.spinGroup Q) Circle)

theorem spinToSpinCHom_injective (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    Function.Injective (spinToSpinCHom Q ha) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : (g, (1 : Circle)) ∈ z2DiagSubgroup Q ha :=
    (QuotientGroup.eq_one_iff (g, (1 : Circle))).mp hg
  rcases hmem with h | h
  · exact congrArg Prod.fst h
  · exfalso
    have h1 : (1 : Circle) = -1 := congrArg Prod.snd h
    exact (Circle.neg_ne_self (1 : Circle)).symm h1

/-- Canonical central `S¹` inclusion `S¹ →* Spinᶜ(V, Q)`, `z ↦ [(1, z)]`. -/
def circleToSpinCHom (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    Circle →* SpinCGroup Q ha :=
  (QuotientGroup.mk' (z2DiagSubgroup Q ha)).comp (MonoidHom.inr (_root_.spinGroup Q) Circle)

theorem circleToSpinCHom_injective (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    Function.Injective (circleToSpinCHom Q ha) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hmem : ((1 : _root_.spinGroup Q), z) ∈ z2DiagSubgroup Q ha :=
    (QuotientGroup.eq_one_iff ((1 : _root_.spinGroup Q), z)).mp hz
  rcases hmem with h | h
  · exact congrArg Prod.snd h
  · exfalso
    have h1 : (1 : _root_.spinGroup Q) = negOneSpinGroup Q ha := congrArg Prod.fst h
    exact (negOneSpinGroup_ne_one Q ha) h1.symm

open scoped TensorProduct

private def spinCPreEmbed (Q : QuadraticForm ℝ V) :
    _root_.spinGroup Q × Circle →* (ℂ ⊗[ℝ] CliffordAlgebra Q)ˣ where
  toFun p :=
    { val := (p.2 : ℂ) ⊗ₜ[ℝ] (p.1 : CliffordAlgebra Q)
      inv := ((p.2⁻¹ : Circle) : ℂ) ⊗ₜ[ℝ] ((p.1⁻¹ : _root_.spinGroup Q) : CliffordAlgebra Q)
      val_inv := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        have hz : (p.2 : ℂ) * ((p.2⁻¹ : Circle) : ℂ) = 1 := by
          rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
        have hg : (p.1 : CliffordAlgebra Q) * ((p.1⁻¹ : _root_.spinGroup Q) : CliffordAlgebra Q) = 1 :=
          congrArg (fun u : _root_.spinGroup Q => (u : CliffordAlgebra Q)) (mul_inv_cancel p.1)
        rw [hz, hg, Algebra.TensorProduct.one_def]
      inv_val := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        have hz : ((p.2⁻¹ : Circle) : ℂ) * (p.2 : ℂ) = 1 := by
          rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
        have hg : ((p.1⁻¹ : _root_.spinGroup Q) : CliffordAlgebra Q) * (p.1 : CliffordAlgebra Q) = 1 :=
          congrArg (fun u : _root_.spinGroup Q => (u : CliffordAlgebra Q)) (inv_mul_cancel p.1)
        rw [hz, hg, Algebra.TensorProduct.one_def] }
  map_one' := Units.ext <| by simp [Algebra.TensorProduct.one_def]
  map_mul' p q := Units.ext <| by
    simp [Algebra.TensorProduct.tmul_mul_tmul, Circle.coe_mul]

/-- Faithful embedding `Spinᶜ(V, Q) →* (ℂ ⊗[ℝ] Cl(V, Q))ˣ` sending `[(g, z)] ↦ z ⊗ₜ g`. -/
def spinCEmbed (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    SpinCGroup Q ha →* (ℂ ⊗[ℝ] CliffordAlgebra Q)ˣ :=
  QuotientGroup.lift (z2DiagSubgroup Q ha) (spinCPreEmbed Q) (by
    rintro ⟨g, z⟩ h
    apply Units.ext
    rcases h with h | h
    · have hg : g = 1 := congrArg Prod.fst h
      have hz : z = 1 := congrArg Prod.snd h
      simp [spinCPreEmbed, hg, hz, Algebra.TensorProduct.one_def]
    · have hg : g = negOneSpinGroup Q ha := congrArg Prod.fst h
      have hz : z = -1 := congrArg Prod.snd h
      simp [spinCPreEmbed, hg, hz, TensorProduct.neg_tmul, TensorProduct.tmul_neg,
        Algebra.TensorProduct.one_def])

@[simp]
theorem spinCEmbed_mk_val (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a))
    (g : _root_.spinGroup Q) (z : Circle) :
    ((spinCEmbed Q ha (QuotientGroup.mk (g, z)) : (ℂ ⊗[ℝ] CliffordAlgebra Q)ˣ) :
      ℂ ⊗[ℝ] CliffordAlgebra Q) = (z : ℂ) ⊗ₜ[ℝ] (g : CliffordAlgebra Q) := rfl

theorem spinCEmbed_injective (Q : QuadraticForm ℝ V) (ha : ∃ a : V, IsUnit (Q a)) :
    Function.Injective (spinCEmbed Q ha) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H p =>
    rcases p with ⟨g, z⟩
    have hxval : (z : ℂ) ⊗ₜ[ℝ] (g : CliffordAlgebra Q) = 1 := by
      simpa [spinCEmbed_mk_val] using congrArg Units.val hx
    have hz_g : (z : ℂ) ⊗ₜ[ℝ] (1 : CliffordAlgebra Q) =
        (1 : ℂ) ⊗ₜ[ℝ] ((g⁻¹ : _root_.spinGroup Q) : CliffordAlgebra Q) := by
      have hmul := congrArg (fun u => u * ((1 : ℂ) ⊗ₜ[ℝ] ((g⁻¹ : _root_.spinGroup Q) : CliffordAlgebra Q))) hxval
      have hgmul : (g : CliffordAlgebra Q) * ((g⁻¹ : _root_.spinGroup Q) : CliffordAlgebra Q) = 1 :=
        congrArg (fun u : _root_.spinGroup Q => (u : CliffordAlgebra Q)) (mul_inv_cancel g)
      simpa [Algebra.TensorProduct.tmul_mul_tmul, hgmul, mul_one, one_mul] using hmul
    let imProj : ℂ ⊗[ℝ] CliffordAlgebra Q →ₗ[ℝ] CliffordAlgebra Q :=
      TensorProduct.lift (LinearMap.lsmul ℝ (CliffordAlgebra Q) ∘ₗ Complex.imLm)
    let reProj : ℂ ⊗[ℝ] CliffordAlgebra Q →ₗ[ℝ] CliffordAlgebra Q :=
      TensorProduct.lift (LinearMap.lsmul ℝ (CliffordAlgebra Q) ∘ₗ Complex.reLm)
    have him := congrArg imProj hz_g
    simp only [imProj, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply] at him
    change (z : ℂ).im • (1 : CliffordAlgebra Q) =
      (1 : ℂ).im • ((g⁻¹ : _root_.spinGroup Q) : CliffordAlgebra Q) at him
    simp only [Complex.one_im, zero_smul] at him
    have h1ne0 : (1 : CliffordAlgebra Q) ≠ 0 := by
      intro h10
      have hne := (lipschitz_pin_spin_doubleCover_witness Q ha).2.2.2.1
      rw [show (-1 : CliffordAlgebra Q) = 1 from by rw [h10, neg_zero]] at hne
      exact hne rfl
    have hzim : (z : ℂ).im = 0 := (smul_eq_zero.mp him).resolve_right h1ne0
    have hzre_sq : (z : ℂ).re ^ 2 = 1 := by
      have hn := z.normSq_coe
      rw [Complex.normSq_apply, hzim, mul_zero, add_zero, ← sq] at hn
      exact hn
    have hz_pm : z = 1 ∨ z = -1 := by
      rcases sq_eq_one_iff.mp hzre_sq with h1 | h1
      · left; apply Circle.ext; exact Complex.ext h1 hzim
      · right; apply Circle.ext; exact Complex.ext h1 (by simp [hzim])
    apply (QuotientGroup.eq_one_iff (g, z)).mpr
    have hre := congrArg reProj hz_g
    simp only [reProj, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply] at hre
    change (z : ℂ).re • (1 : CliffordAlgebra Q) =
      (1 : ℂ).re • ((g⁻¹ : _root_.spinGroup Q) : CliffordAlgebra Q) at hre
    simp only [Complex.one_re, one_smul] at hre
    rcases hz_pm with rfl | rfl
    · left
      have hg_inv_one : g⁻¹ = 1 := by
        apply Subtype.ext
        simpa using hre.symm
      have hg_one : g = 1 := inv_eq_one.mp hg_inv_one
      exact Prod.ext hg_one rfl
    · right
      have hg_inv_neg : g⁻¹ = negOneSpinGroup Q ha := by
        apply Subtype.ext
        simpa [negOneSpinGroup] using hre.symm
      have hg_neg : g = negOneSpinGroup Q ha := by
        calc
          g = (g⁻¹)⁻¹ := (inv_inv g).symm
          _ = (negOneSpinGroup Q ha)⁻¹ := by rw [hg_inv_neg]
          _ = negOneSpinGroup Q ha := negOneSpinGroup_inv Q ha
      exact Prod.ext hg_neg rfl

theorem exists_isUnit_cliffordNegSqForm (n : ℕ) [NeZero n] :
    ∃ a : Fin n → ℝ, IsUnit (cliffordNegSqForm ℝ n a) := by
  let x : Fin n → ℝ := Pi.single (0 : Fin n) (1 : ℝ)
  refine ⟨x, ?_⟩
  rw [cliffordNegSqForm_apply]
  have hs : ∑ i : Fin n, x i * x i = 1 := by
    rw [Fintype.sum_eq_single (0 : Fin n)]
    · simp [x]
    · intro i hi; simp [x, Pi.single_eq_of_ne hi]
  rw [hs]
  exact isUnit_one.neg

/-- Euclidean `Spinᶜ(n)` built over `cliffordNegSqForm ℝ n` (`n ≥ 1`). -/
abbrev SpinC (n : ℕ) [NeZero n] : Type _ :=
  SpinCGroup (cliffordNegSqForm ℝ n) (exists_isUnit_cliffordNegSqForm n)

/-!
### Canonical `U(n) →* Spinᶜ(2n)` Homomorphism (Nicolaescu Prop. 1.3.10)
-/

section UnitaryToSpinC

/-- Realification `ℂⁿ →ₗ[ℝ] ℝ²ⁿ` sending `z` to `(Re z, Im z)`. -/
def realifyVec {n : ℕ} (z : Fin n → ℂ) : Fin (2 * n) → ℝ :=
  fun k => if h : k.val < n then (z ⟨k.val, h⟩).re else (z ⟨k.val - n, by omega⟩).im

def realifyVecLin (n : ℕ) : (Fin n → ℂ) →ₗ[ℝ] (Fin (2 * n) → ℝ) where
  toFun := realifyVec
  map_add' z w := by
    ext k; unfold realifyVec; by_cases h : k.val < n <;> simp [h]
  map_smul' c z := by
    ext k; unfold realifyVec; by_cases h : k.val < n <;> simp [h]

/-- Inverse realification `ℝ²ⁿ →ₗ[ℝ] ℂⁿ` sending `(x, y) ↦ x + i y`. -/
def complexifyVec {n : ℕ} (v : Fin (2 * n) → ℝ) : Fin n → ℂ :=
  fun k => ((v ⟨k.val, by omega⟩ : ℝ) : ℂ) + Complex.I * (v ⟨n + k.val, by omega⟩ : ℂ)

def complexifyVecLin (n : ℕ) : (Fin (2 * n) → ℝ) →ₗ[ℝ] (Fin n → ℂ) where
  toFun := complexifyVec
  map_add' u v := by ext k; simp [complexifyVec]; ring
  map_smul' c v := by ext k; simp [complexifyVec]; ring

@[simp]
theorem complexifyVec_realifyVec {n : ℕ} (z : Fin n → ℂ) :
    complexifyVec (realifyVec z) = z := by
  ext k
  have hk1 : k.val < n := k.isLt
  have hk2 : ¬ (n + k.val < n) := by omega
  have h1 : realifyVec z ⟨k.val, by omega⟩ = (z k).re := by
    unfold realifyVec
    rw [dif_pos hk1]
  have h2 : realifyVec z ⟨n + k.val, by omega⟩ = (z k).im := by
    unfold realifyVec
    rw [dif_neg hk2]
    congr 2
    exact Fin.ext (by dsimp; omega)
  simp only [complexifyVec, h1, h2]
  rw [mul_comm]
  exact Complex.re_add_im (z k)

@[simp]
theorem realifyVec_complexifyVec {n : ℕ} (v : Fin (2 * n) → ℝ) :
    realifyVec (complexifyVec v) = v := by
  ext k
  unfold realifyVec complexifyVec
  by_cases hk : k.val < n
  · simp only [dif_pos hk, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]
  · simp only [dif_neg hk, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      mul_zero, Complex.I_im, Complex.ofReal_re, one_mul, add_zero, zero_add]
    have hklt := k.isLt
    exact congrArg v (Fin.ext (by dsimp; omega))

/-- Realification linear equivalence `(Fin n → ℂ) ≃ₗ[ℝ] (Fin (2 * n) → ℝ)`. -/
def realifyEquiv (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℝ] (Fin (2 * n) → ℝ) where
  toLinearMap := realifyVecLin n
  invFun := complexifyVec
  left_inv := complexifyVec_realifyVec
  right_inv := realifyVec_complexifyVec

theorem cliffordNegSqForm_realifyVec {n : ℕ} (z : Fin n → ℂ) :
    cliffordNegSqForm ℝ (2 * n) (realifyVec z) = -∑ k : Fin n, Complex.normSq (z k) := by
  rw [cliffordNegSqForm_apply]
  congr 1
  let e : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
    finSumFinEquiv.trans (finCongr (by omega))
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (e (Sum.inl k)).val < n := by simp [e]
  have h2 : ¬ ((e (Sum.inr k)).val < n) := by simp [e]
  simp only [realifyVec, dif_pos h1, dif_neg h2, Complex.normSq_apply]
  have he1 : (⟨(e (Sum.inl k)).val, h1⟩ : Fin n) = k := by ext; simp [e]
  have he2 : (⟨(e (Sum.inr k)).val - n, by omega⟩ : Fin n) = k := by
    ext; simp [e]
  rw [he1, he2]

theorem realifyVec_unitary_normSq {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) :
    ∑ k : Fin n, Complex.normSq ((U.1 *ᵥ z) k) = ∑ k : Fin n, Complex.normSq (z k) := by
  have hdot : (star (U.1 *ᵥ z) ⬝ᵥ (U.1 *ᵥ z)) = star z ⬝ᵥ z := by
    calc
      star (U.1 *ᵥ z) ⬝ᵥ (U.1 *ᵥ z)
          = (star z ᵥ* star U.1) ⬝ᵥ (U.1 *ᵥ z) := by
            rw [Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
      _ = star z ⬝ᵥ (star U.1 *ᵥ (U.1 *ᵥ z)) := by rw [← Matrix.dotProduct_mulVec]
      _ = star z ⬝ᵥ ((star U.1 * U.1) *ᵥ z) := by rw [Matrix.mulVec_mulVec]
      _ = star z ⬝ᵥ z := by
        have hU : star U.1 * U.1 = 1 := U.2.1
        rw [hU, Matrix.one_mulVec]
  have hre : (star (U.1 *ᵥ z) ⬝ᵥ (U.1 *ᵥ z)).re = (star z ⬝ᵥ z).re := by
    rw [hdot]
  have hid : ∀ w : Fin n → ℂ, (star w ⬝ᵥ w).re = ∑ k : Fin n, Complex.normSq (w k) := by
    intro w
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.re_sum, Complex.normSq_apply]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hid, hid] at hre
  exact hre

/-- Realification embedding `U(n) →* SO(2n)` into `IsometryEquiv (cliffordNegSqForm ℝ (2 * n))`. -/
def realifyIsometry {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (cliffordNegSqForm ℝ (2 * n)).IsometryEquiv (cliffordNegSqForm ℝ (2 * n)) where
  toLinearEquiv :=
    { toFun := fun v => realifyVec (U.1 *ᵥ complexifyVec v)
      invFun := fun v => realifyVec (star U.1 *ᵥ complexifyVec v)
      map_add' := fun u v => by
        have hadd := (complexifyVecLin n).map_add u v
        have hradd := (realifyVecLin n).map_add
          (U.1 *ᵥ complexifyVec u) (U.1 *ᵥ complexifyVec v)
        dsimp only [complexifyVecLin, realifyVecLin, LinearMap.coe_mk, AddHom.coe_mk] at hadd hradd
        rw [hadd, Matrix.mulVec_add, hradd]
      map_smul' := fun c v => by
        rw [show complexifyVec (c • v) = (c : ℂ) • complexifyVec v from by
          ext k; simp [complexifyVec]; ring, Matrix.mulVec_smul]
        ext k; unfold realifyVec; by_cases h : k.val < n <;> simp [h]
      left_inv := fun v => by
        dsimp only
        rw [complexifyVec_realifyVec, Matrix.mulVec_mulVec, U.2.1, Matrix.one_mulVec,
          realifyVec_complexifyVec]
      right_inv := fun v => by
        dsimp only
        rw [complexifyVec_realifyVec, Matrix.mulVec_mulVec, U.2.2, Matrix.one_mulVec,
          realifyVec_complexifyVec] }
  map_app' v := by
    change cliffordNegSqForm ℝ (2 * n) (realifyVec (U.1 *ᵥ complexifyVec v)) =
      cliffordNegSqForm ℝ (2 * n) v
    rw [cliffordNegSqForm_realifyVec, realifyVec_unitary_normSq]
    have h2 : cliffordNegSqForm ℝ (2 * n) (realifyVec (complexifyVec v)) =
        -∑ k : Fin n, Complex.normSq (complexifyVec v k) :=
      cliffordNegSqForm_realifyVec _
    rw [realifyVec_complexifyVec] at h2
    exact h2.symm

def realifyIsometryHom (n : ℕ) :
    Matrix.unitaryGroup (Fin n) ℂ →*
      (cliffordNegSqForm ℝ (2 * n)).IsometryEquiv (cliffordNegSqForm ℝ (2 * n)) where
  toFun := realifyIsometry
  map_one' := by
    apply DFunLike.ext; intro v
    change realifyVec ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ complexifyVec v) = v
    simp
  map_mul' U₁ U₂ := by
    apply DFunLike.ext; intro v
    change realifyVec ((U₁.1 * U₂.1) *ᵥ complexifyVec v) =
      realifyVec (U₁.1 *ᵥ complexifyVec (realifyVec (U₂.1 *ᵥ complexifyVec v)))
    rw [complexifyVec_realifyVec, Matrix.mulVec_mulVec]

/-- Dual covector `w ↦ u ⬝ᵥ w` on `ℂⁿ`. -/
def dotDual {n : ℕ} (u : Fin n → ℂ) : Module.Dual ℂ (Fin n → ℂ) where
  toFun w := u ⬝ᵥ w
  map_add' w₁ w₂ := dotProduct_add u w₁ w₂
  map_smul' c w := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

@[simp]
theorem dotDual_apply {n : ℕ} (u w : Fin n → ℂ) : dotDual u w = u ⬝ᵥ w := rfl

/-- Fundamental Clifford action `c₀(v) = ε(v̄) - ι(v)` on `ExteriorAlgebra ℂ (Fin n → ℂ)`. -/
def spinorCliffordMap (n : ℕ) :
    (Fin (2 * n) → ℝ) →ₗ[ℝ] Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) where
  toFun v :=
    exteriorWedge ℂ (star (complexifyVec v)) - exteriorContract (dotDual (complexifyVec v))
  map_add' u v := by
    have hc : complexifyVec (u + v) = complexifyVec u + complexifyVec v :=
      (complexifyVecLin n).map_add u v
    rw [hc, star_add]
    apply LinearMap.ext; intro ω
    change exteriorWedge ℂ (star (complexifyVec u) + star (complexifyVec v)) ω -
        exteriorContract (dotDual (complexifyVec u + complexifyVec v)) ω =
      (exteriorWedge ℂ (star (complexifyVec u)) ω - exteriorContract (dotDual (complexifyVec u)) ω) +
      (exteriorWedge ℂ (star (complexifyVec v)) ω - exteriorContract (dotDual (complexifyVec v)) ω)
    have hw : exteriorWedge ℂ (star (complexifyVec u) + star (complexifyVec v)) ω =
        exteriorWedge ℂ (star (complexifyVec u)) ω + exteriorWedge ℂ (star (complexifyVec v)) ω := by
      simp [exteriorWedge, map_add, add_mul]
    have hd : dotDual (complexifyVec u + complexifyVec v) =
        dotDual (complexifyVec u) + dotDual (complexifyVec v) := by
      ext w; simp [dotDual, add_dotProduct]
    have hcon : exteriorContract (dotDual (complexifyVec u) + dotDual (complexifyVec v)) ω =
        exteriorContract (dotDual (complexifyVec u)) ω +
        exteriorContract (dotDual (complexifyVec v)) ω := by
      simp [exteriorContract, map_add]
    rw [hw, hd, hcon]
    abel
  map_smul' r v := by
    have hc : complexifyVec (r • v) = (r : ℂ) • complexifyVec v := by
      ext k; simp [complexifyVec]; ring
    rw [hc]
    apply LinearMap.ext; intro ω
    have hstar : star ((r : ℂ) • complexifyVec v) = (r : ℂ) • star (complexifyVec v) := by
      ext k; simp
    have hw : exteriorWedge ℂ (star ((r : ℂ) • complexifyVec v)) ω =
        (r : ℂ) • exteriorWedge ℂ (star (complexifyVec v)) ω := by
      rw [hstar]
      simp [exteriorWedge, map_smul, smul_mul_assoc]
    have hd : dotDual ((r : ℂ) • complexifyVec v) = (r : ℂ) • dotDual (complexifyVec v) := by
      ext w; simp [dotDual, smul_dotProduct]
    have hcon : exteriorContract (dotDual ((r : ℂ) • complexifyVec v)) ω =
        (r : ℂ) • exteriorContract (dotDual (complexifyVec v)) ω := by
      rw [hd]
      simp [exteriorContract, map_smul]
    simp only [RingHom.id_apply, LinearMap.sub_apply, hw, hcon, LinearMap.smul_apply]
    change (r : ℂ) • exteriorWedge ℂ (star (complexifyVec v)) ω -
        (r : ℂ) • exteriorContract (dotDual (complexifyVec v)) ω =
      r • (exteriorWedge ℂ (star (complexifyVec v)) ω -
        exteriorContract (dotDual (complexifyVec v)) ω)
    rw [← smul_sub]
    exact (algebraMap_smul ℂ r _).symm

theorem spinorCliffordMap_sq (n : ℕ) (v : Fin (2 * n) → ℝ) :
    spinorCliffordMap n v * spinorCliffordMap n v =
      algebraMap ℝ (Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)))
        (cliffordNegSqForm ℝ (2 * n) v) := by
  let w := star (complexifyVec v)
  let φ := dotDual (complexifyVec v)
  have h1 : spinorCliffordMap n v * spinorCliffordMap n v =
      (exteriorWedge ℂ w - exteriorContract φ) * (exteriorWedge ℂ w - exteriorContract φ) := rfl
  rw [h1]
  have hsq_w : exteriorWedge ℂ w * exteriorWedge ℂ w = 0 := exteriorWedge_sq ℂ w
  have hsq_c : exteriorContract φ * exteriorContract φ = 0 := exteriorContract_sq φ
  have hcar := exterior_cartan_homotopy_car (R := ℂ) φ w
  have hexp : (exteriorWedge ℂ w - exteriorContract φ) * (exteriorWedge ℂ w - exteriorContract φ) =
      -(exteriorContract φ * exteriorWedge ℂ w + exteriorWedge ℂ w * exteriorContract φ) := by
    calc
      (exteriorWedge ℂ w - exteriorContract φ) * (exteriorWedge ℂ w - exteriorContract φ)
          = exteriorWedge ℂ w * exteriorWedge ℂ w -
            exteriorWedge ℂ w * exteriorContract φ -
            exteriorContract φ * exteriorWedge ℂ w +
            exteriorContract φ * exteriorContract φ := by
              simp only [sub_mul, mul_sub]; abel
      _ = 0 - exteriorWedge ℂ w * exteriorContract φ -
            exteriorContract φ * exteriorWedge ℂ w + 0 := by rw [hsq_w, hsq_c]
      _ = -(exteriorContract φ * exteriorWedge ℂ w + exteriorWedge ℂ w * exteriorContract φ) := by
            abel
  rw [hexp, hcar]
  have hval : φ w = ((-cliffordNegSqForm ℝ (2 * n) v : ℝ) : ℂ) := by
    have hv := realifyVec_complexifyVec v
    have hnorm := cliffordNegSqForm_realifyVec (complexifyVec v)
    rw [hv] at hnorm
    have hdot : φ w = (∑ k : Fin n, (Complex.normSq (complexifyVec v k) : ℝ) : ℂ) := by
      simp only [φ, w, dotDual_apply, dotProduct, Pi.star_apply, Complex.star_def,
        Complex.mul_conj, Complex.ofReal_sum]
    rw [hdot, hnorm]
    simp
  rw [hval]
  apply LinearMap.ext; intro ω
  simp only [Algebra.algebraMap_eq_smul_one, LinearMap.neg_apply, LinearMap.smul_apply,
    Module.End.one_apply, neg_smul, Complex.ofReal_neg, neg_neg]
  change (cliffordNegSqForm ℝ (2 * n) v : ℂ) • ω = cliffordNegSqForm ℝ (2 * n) v • ω
  exact algebraMap_smul ℂ (cliffordNegSqForm ℝ (2 * n) v) ω

/-- Complexified Clifford spinor representation
`ℂ ⊗[ℝ] Cl(0, 2n) →ₐ[ℂ] End_ℂ(Λ^* ℂⁿ)`. -/
def spinorRepC (n : ℕ) :
    ℂ ⊗[ℝ] CliffordAlgebra (cliffordNegSqForm ℝ (2 * n)) →ₐ[ℂ]
      Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) :=
  let toReal : ℂ ⊗[ℝ] CliffordAlgebra (cliffordNegSqForm ℝ (2 * n)) →ₐ[ℝ]
      Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) :=
    Algebra.TensorProduct.lift
      ((Algebra.ofId ℂ (Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)))).restrictScalars ℝ)
      (CliffordAlgebra.lift (cliffordNegSqForm ℝ (2 * n))
        ⟨spinorCliffordMap n, spinorCliffordMap_sq n⟩)
      (fun c x => Algebra.commutes c _)
  { toRingHom := toReal.toRingHom
    commutes' := fun c => by
      change ((Algebra.ofId ℂ (Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)))).restrictScalars ℝ) c *
          (CliffordAlgebra.lift (cliffordNegSqForm ℝ (2 * n))
            ⟨spinorCliffordMap n, spinorCliffordMap_sq n⟩) 1 =
        algebraMap ℂ _ c
      rw [map_one, mul_one]
      rfl }

@[simp]
theorem spinorRepC_tmul_ι (n : ℕ) (c : ℂ) (v : Fin (2 * n) → ℝ) :
    spinorRepC n (c ⊗ₜ[ℝ] ι (cliffordNegSqForm ℝ (2 * n)) v) =
      c • spinorCliffordMap n v := by
  change ((Algebra.ofId ℂ (Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)))).restrictScalars ℝ) c *
      (CliffordAlgebra.lift (cliffordNegSqForm ℝ (2 * n))
        ⟨spinorCliffordMap n, spinorCliffordMap_sq n⟩) (ι (cliffordNegSqForm ℝ (2 * n)) v) =
    c • spinorCliffordMap n v
  rw [CliffordAlgebra.lift_ι_apply]
  simp [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]

theorem spinorCliffordMap_injective (n : ℕ) : Function.Injective (spinorCliffordMap n) := by
  intro u v huv
  have h1 := congrArg (fun T : Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) => T 1) huv
  simp only [spinorCliffordMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
    exteriorWedge_apply, mul_one, exteriorContract_one, sub_zero] at h1
  have hstar : star (complexifyVec u) = star (complexifyVec v) := by
    have := congrArg ExteriorAlgebra.ιInv h1
    simpa [ExteriorAlgebra.ι_leftInverse _] using this
  have hc : complexifyVec u = complexifyVec v := star_injective hstar
  simpa [realifyVec_complexifyVec] using congrArg realifyVec hc

theorem spinorRepC_rotor_sandwich {n : ℕ} (g : _root_.spinGroup (cliffordNegSqForm ℝ (2 * n)))
    (v : Fin (2 * n) → ℝ) :
    spinorRepC n ((1 : ℂ) ⊗ₜ[ℝ] (g : CliffordAlgebra (cliffordNegSqForm ℝ (2 * n)))) *
        spinorCliffordMap n v *
        spinorRepC n ((1 : ℂ) ⊗ₜ[ℝ] CliffordAlgebra.reverse (g : CliffordAlgebra _)) =
      spinorCliffordMap n (spinGroupToIsometryHom (cliffordNegSqForm ℝ (2 * n)) g v) := by
  have hsand := ι_spinGroupIsometryEquiv (Q := cliffordNegSqForm ℝ (2 * n)) g v
  change ι (cliffordNegSqForm ℝ (2 * n))
      (spinGroupToIsometryHom (cliffordNegSqForm ℝ (2 * n)) g v) =
    (g : CliffordAlgebra _) * ι (cliffordNegSqForm ℝ (2 * n)) v *
      CliffordAlgebra.reverse (g : CliffordAlgebra _) at hsand
  have hrep := congrArg (fun x => spinorRepC n ((1 : ℂ) ⊗ₜ[ℝ] x)) hsand
  simp only [spinorRepC_tmul_ι, one_smul] at hrep
  have htmul : ∀ a b : CliffordAlgebra (cliffordNegSqForm ℝ (2 * n)),
      ((1 : ℂ) ⊗ₜ[ℝ] (a * b)) = ((1 : ℂ) ⊗ₜ[ℝ] a) * ((1 : ℂ) ⊗ₜ[ℝ] b) := by
    intro a b; simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [htmul, htmul, map_mul, map_mul, spinorRepC_tmul_ι, one_smul] at hrep
  exact hrep.symm

/-! #### Kernel of `spinGroupToIsometryHom` on `Cl(0, m)` (`{±1}`) -/

private lemma cGen_mul_sorted_listProd (m : ℕ) (r : Fin m) :
    ∀ L : List (Fin m), L.Pairwise (· < ·) →
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ L' : List (Fin m),
        L'.Pairwise (· < ·) ∧
        (∀ x ∈ L', x = r ∨ x ∈ L) ∧
        L'.toFinset = symmDiff {r} L.toFinset ∧
        cGen ℝ m r * (L.map (cGen ℝ m)).prod = ε • (L'.map (cGen ℝ m)).prod
  | [], _ =>
    ⟨1, Or.inl rfl, [r], List.pairwise_singleton _ _, fun _ hx => by simp_all,
      by ext x; simp [Finset.mem_symmDiff], by simp⟩
  | a :: tl, hnd => by
    have ha_lt : ∀ x ∈ tl, a < x := (List.pairwise_cons.mp hnd).1
    have htl : tl.Pairwise (· < ·) := (List.pairwise_cons.mp hnd).2
    rcases lt_trichotomy r a with hra | rfl | har
    · have hr_not : r ∉ a :: tl := fun hmem => by
        rcases List.mem_cons.mp hmem with rfl | hxtl
        · exact lt_irrefl _ hra
        · exact absurd (ha_lt r hxtl) (lt_asymm hra)
      have hset : (r :: a :: tl).toFinset = symmDiff {r} (a :: tl).toFinset := by
        ext x
        simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_symmDiff,
          Finset.mem_singleton, List.mem_toFinset]
        by_cases hxr : x = r
        · subst hxr
          have hne : x ≠ a := hra.ne
          have hr_tl : x ∉ tl := fun h => hr_not (List.mem_cons_of_mem _ h)
          simp [hne, hr_tl]
        · simp [hxr]
      refine ⟨1, Or.inl rfl, r :: a :: tl, List.pairwise_cons.mpr ⟨fun x hx => ?_, hnd⟩,
        fun x hx => by simp_all, hset, by simp [List.prod_cons]⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hxtl
      · exact hra
      · exact lt_trans hra (ha_lt x hxtl)
    · have hr_not : r ∉ tl := fun hmem => lt_irrefl _ (ha_lt r hmem)
      have hset : tl.toFinset = symmDiff {r} (r :: tl).toFinset := by
        ext x
        simp only [List.toFinset_cons, Finset.mem_symmDiff, Finset.mem_singleton,
          Finset.mem_insert, List.mem_toFinset]
        by_cases hxr : x = r
        · subst hxr; simp [hr_not]
        · simp [hxr]
      refine ⟨-1, Or.inr rfl, tl, htl, fun x hx => Or.inr (List.mem_cons_of_mem _ hx), hset, ?_⟩
      simp only [List.map_cons, List.prod_cons, ← mul_assoc, cGen_sq, neg_one_mul, neg_one_smul]
    · rcases cGen_mul_sorted_listProd m r tl htl with
        ⟨ε₀, hε₀, tl', htl', hmem', hset', heq⟩
      have ha_tl' : ∀ x ∈ tl', a < x := fun x hx => by
        rcases hmem' x hx with rfl | hxtl
        · exact har
        · exact ha_lt x hxtl
      have ha_not_tl : a ∉ tl := fun h => lt_irrefl _ (ha_lt a h)
      have ha_not_tl' : a ∉ tl' := fun h => lt_irrefl _ (ha_tl' a h)
      have hset : (a :: tl').toFinset = symmDiff {r} (a :: tl).toFinset := by
        ext x
        simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_symmDiff,
          Finset.mem_singleton, List.mem_toFinset]
        have hx' := Finset.ext_iff.mp hset' x
        simp only [List.mem_toFinset, Finset.mem_symmDiff, Finset.mem_singleton] at hx'
        by_cases hxa : x = a
        · subst hxa; simp [har.ne, ha_not_tl, ha_not_tl']
        · simp [hxa, hx']
      refine ⟨-ε₀, by rcases hε₀ with rfl | rfl <;> [right; left] <;> ring,
        a :: tl', List.pairwise_cons.mpr ⟨ha_tl', htl'⟩, fun x hx => ?_, hset, ?_⟩
      · simp only [List.mem_cons] at hx
        rcases hx with rfl | hxtl'
        · exact Or.inr List.mem_cons_self
        · rcases hmem' x hxtl' with rfl | hxtl
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem _ hxtl)
      · calc
          cGen ℝ m r * ((a :: tl).map (cGen ℝ m)).prod
              = (cGen ℝ m r * cGen ℝ m a) * (tl.map (cGen ℝ m)).prod := by
                simp only [List.map_cons, List.prod_cons, mul_assoc]
          _ = -(cGen ℝ m a * cGen ℝ m r) * (tl.map (cGen ℝ m)).prod := by
                rw [cGen_anticomm har.ne']
          _ = -(cGen ℝ m a * (cGen ℝ m r * (tl.map (cGen ℝ m)).prod)) := by noncomm_ring
          _ = -(cGen ℝ m a * (ε₀ • (tl'.map (cGen ℝ m)).prod)) := by rw [heq]
          _ = (-ε₀) • ((a :: tl').map (cGen ℝ m)).prod := by
                rw [mul_smul_comm, ← neg_smul, List.map_cons, List.prod_cons]

private lemma sorted_list_eq_bladeList {m : ℕ} {L : List (Fin m)}
    (hL : L.Pairwise (· < ·)) : L = bladeList L.toFinset := by
  have hp : L.Perm (bladeList L.toFinset) := by
    refine (List.perm_ext_iff_of_nodup hL.nodup (bladeList_nodup _)).mpr fun x => ?_
    rw [mem_bladeList, List.mem_toFinset]
  exact hp.eq_of_pairwise' hL (bladeList_pairwise_lt _)

private lemma cGen_mul_cBlade_eq_pm (m : ℕ) (r : Fin m) (S : Finset (Fin m)) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      cGen ℝ m r * cBlade ℝ m S = ε • cBlade ℝ m (symmDiff {r} S) := by
  rcases cGen_mul_sorted_listProd m r (bladeList S) (bladeList_pairwise_lt S) with
    ⟨ε, hε, L', hL', _, hset, heq⟩
  have hL'_eq : (L'.map (cGen ℝ m)).prod = cBlade ℝ m L'.toFinset := by
    conv_lhs => rw [sorted_list_eq_bladeList hL']
    rfl
  rw [bladeList_toFinset] at hset
  change cGen ℝ m r * cBlade ℝ m S = ε • (L'.map (cGen ℝ m)).prod at heq
  rw [hL'_eq, hset] at heq
  exact ⟨ε, hε, heq⟩

private lemma span_cBlade_mul_cGen (m : ℕ) (r : Fin m) (S : Finset (Fin m)) :
    cGen ℝ m r * cBlade ℝ m S ∈ Submodule.span ℝ (Set.range (cBlade ℝ m)) := by
  rcases cGen_mul_cBlade_eq_pm m r S with ⟨ε, _, heq⟩
  rw [heq]
  exact Submodule.smul_mem _ ε (Submodule.subset_span ⟨symmDiff {r} S, rfl⟩)

private theorem mem_span_cBlade (m : ℕ) (X : CliffordAlgebra (cliffordNegSqForm ℝ m)) :
    X ∈ Submodule.span ℝ (Set.range (cBlade ℝ m)) := by
  let Sspan : Submodule ℝ (CliffordAlgebra (cliffordNegSqForm ℝ m)) :=
    Submodule.span ℝ (Set.range (cBlade ℝ m))
  have hmul_gen : ∀ (r : Fin m) (Y : CliffordAlgebra (cliffordNegSqForm ℝ m)),
      Y ∈ Sspan → cGen ℝ m r * Y ∈ Sspan := by
    intro r Y hY
    induction hY using Submodule.span_induction with
    | mem Z hZ =>
      rcases hZ with ⟨S, rfl⟩
      exact span_cBlade_mul_cGen m r S
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact Sspan.add_mem ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Sspan.smul_mem c ha
  have hmul_vec : ∀ (v : Fin m → ℝ) (Y : CliffordAlgebra (cliffordNegSqForm ℝ m)),
      Y ∈ Sspan → ι (cliffordNegSqForm ℝ m) v * Y ∈ Sspan := by
    intro v Y hY
    have hv : v = ∑ r : Fin m, v r • Pi.single r (1 : ℝ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum, Finset.sum_mul]
    refine Sspan.sum_mem fun r _ => ?_
    rw [map_smul, smul_mul_assoc]
    exact Sspan.smul_mem _ (hmul_gen r Y hY)
  have hmul_closed : ∀ (A B : CliffordAlgebra (cliffordNegSqForm ℝ m)),
      B ∈ Sspan → A * B ∈ Sspan := by
    intro A B hB
    revert B hB
    induction A using CliffordAlgebra.induction with
    | algebraMap c =>
      intro B hB
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact Sspan.smul_mem c hB
    | ι v => exact fun B hB => hmul_vec v B hB
    | add a b iha ihb =>
      intro B hB
      rw [add_mul]
      exact Sspan.add_mem (iha B hB) (ihb B hB)
    | mul a b iha ihb =>
      intro B hB
      rw [mul_assoc]
      exact iha (b * B) (ihb B hB)
  induction X using CliffordAlgebra.induction with
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one, ← cBlade_empty ℝ m]
    exact Sspan.smul_mem c (Submodule.subset_span ⟨∅, rfl⟩)
  | ι v =>
    simpa using hmul_vec v 1 (by rw [← cBlade_empty ℝ m]; exact Submodule.subset_span ⟨∅, rfl⟩)
  | add a b iha ihb => exact Sspan.add_mem iha ihb
  | mul a b _ ihb => exact hmul_closed a b ihb

theorem clifford_eq_sum_bladeRepr (m : ℕ) (X : CliffordAlgebra (cliffordNegSqForm ℝ m)) :
    X = ∑ S : Finset (Fin m), bladeRepr ℝ m X S • cBlade ℝ m S := by
  have hmem := mem_span_cBlade m X
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  rcases hmem with ⟨coeff, hX⟩
  have hX' : X = ∑ S : Finset (Fin m), coeff S • cBlade ℝ m S := by
    rw [← hX]
  rw [hX']
  refine Finset.sum_congr rfl fun S _ => ?_
  have hrep : bladeRepr ℝ m (∑ T : Finset (Fin m), coeff T • cBlade ℝ m T) S = coeff S := by
    simp only [bladeRepr, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hb : ∀ T : Finset (Fin m),
        cliffordEndRep ℝ m (cBlade ℝ m T) (Pi.single ∅ 1) S = if T = S then 1 else 0 := by
      intro T
      change bladeRepr ℝ m (cBlade ℝ m T) S = _
      rw [bladeRepr_cBlade]
      simp [Pi.single_apply, eq_comm]
    simp only [hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hrep]

theorem spinGroup_commutes_cGen_imp_scalar {m : ℕ}
    (g : _root_.spinGroup (cliffordNegSqForm ℝ m))
    (hcomm : ∀ r : Fin m,
      cGen ℝ m r * (g : CliffordAlgebra (cliffordNegSqForm ℝ m)) =
        (g : CliffordAlgebra (cliffordNegSqForm ℝ m)) * cGen ℝ m r) :
    (g : CliffordAlgebra (cliffordNegSqForm ℝ m)) = 1 ∨
      (g : CliffordAlgebra (cliffordNegSqForm ℝ m)) = -1 := by
  let X : CliffordAlgebra (cliffordNegSqForm ℝ m) := g
  let coeff : Finset (Fin m) → ℝ := bladeRepr ℝ m X
  have hX : X = ∑ S : Finset (Fin m), coeff S • cBlade ℝ m S :=
    clifford_eq_sum_bladeRepr m X
  have hinv : CliffordAlgebra.involute X = X := _root_.spinGroup.involute_eq g.2
  have hodd : ∀ S : Finset (Fin m), Odd S.card → coeff S = 0 := by
    intro S hS
    have h1 : bladeRepr ℝ m (CliffordAlgebra.involute X) S = coeff S := by rw [hinv]
    have h2 : CliffordAlgebra.involute X =
        ∑ T : Finset (Fin m), ((-1 : ℝ) ^ T.card * coeff T) • cBlade ℝ m T := by
      conv_lhs => rw [hX]
      rw [map_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [map_smul, involute_cBlade, smul_smul, mul_comm]
    have h3 : bladeRepr ℝ m (CliffordAlgebra.involute X) S = (-1 : ℝ) ^ S.card * coeff S := by
      rw [h2]
      simp only [bladeRepr, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hb : ∀ T : Finset (Fin m),
          cliffordEndRep ℝ m (cBlade ℝ m T) (Pi.single ∅ 1) S = if T = S then 1 else 0 := by
        intro T; change bladeRepr ℝ m (cBlade ℝ m T) S = _; rw [bladeRepr_cBlade]
        simp [Pi.single_apply, eq_comm]
      simp only [hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [h3] at h1
    have hpow : (-1 : ℝ) ^ S.card = -1 := hS.neg_one_pow
    rw [hpow] at h1
    linarith
  have hzero : ∀ S : Finset (Fin m), S ≠ ∅ → coeff S = 0 := by
    intro S hSne
    by_cases hcard : Even S.card
    · obtain ⟨r, hrS⟩ := Finset.nonempty_iff_ne_empty.mpr hSne
      let U : Finset (Fin m) := symmDiff {r} S
      have hcomm_r : cGen ℝ m r * X - X * cGen ℝ m r = 0 := sub_eq_zero.mpr (hcomm r)
      have hdiff : cGen ℝ m r * X - X * cGen ℝ m r =
          ∑ T : Finset (Fin m), coeff T • (cGen ℝ m r * cBlade ℝ m T - cBlade ℝ m T * cGen ℝ m r) := by
        conv_lhs => rw [hX]
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
      have hterm : ∀ T : Finset (Fin m),
          ∃ α : ℝ, (cGen ℝ m r * cBlade ℝ m T - cBlade ℝ m T * cGen ℝ m r) =
            α • cBlade ℝ m (symmDiff {r} T) ∧
            (T = S → α ≠ 0) := by
        intro T
        rcases cGen_mul_cBlade_eq_pm m r T with ⟨ε, hε, hmul⟩
        have hswap := cGen_mul_cBlade ℝ m r T
        let sg : ℝ := (-1 : ℝ) ^ (T.card + if r ∈ T then 1 else 0)
        have hcb : cGen ℝ m r * cBlade ℝ m T - cBlade ℝ m T * cGen ℝ m r =
            ((1 - sg) * ε) • cBlade ℝ m (symmDiff {r} T) := by
          have h1 : cBlade ℝ m T * cGen ℝ m r = sg • (cGen ℝ m r * cBlade ℝ m T) := by
            rw [hswap, smul_smul]
            have hsg2 : sg * sg = 1 := by
              dsimp [sg]; rw [← pow_add, ← two_mul, pow_mul]; simp
            rw [hsg2, one_smul]
          rw [h1]
          conv_lhs => arg 1; rw [← one_smul ℝ (cGen ℝ m r * cBlade ℝ m T)]
          rw [← sub_smul, hmul, smul_smul]
        refine ⟨(1 - sg) * ε, hcb, fun hTS => ?_⟩
        subst hTS
        have hsg : sg = -1 := by
          dsimp [sg]
          simp only [hrS, ↓reduceIte]
          rcases hcard with ⟨k, hk⟩
          rw [hk, ← two_mul]
          exact Odd.neg_one_pow ⟨k, rfl⟩
        rw [hsg]
        rcases hε with rfl | rfl <;> norm_num
      choose α hα hα_ne using hterm
      have hsum_eq : cGen ℝ m r * X - X * cGen ℝ m r =
          ∑ T : Finset (Fin m), (coeff T * α T) • cBlade ℝ m (symmDiff {r} T) := by
        rw [hdiff]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [hα T, smul_smul]
      have hrepU : bladeRepr ℝ m (cGen ℝ m r * X - X * cGen ℝ m r) U = coeff S * α S := by
        rw [hsum_eq]
        simp only [bladeRepr, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        have hb : ∀ T : Finset (Fin m),
            cliffordEndRep ℝ m (cBlade ℝ m (symmDiff {r} T)) (Pi.single ∅ 1) U =
              if T = S then 1 else 0 := by
          intro T
          change bladeRepr ℝ m (cBlade ℝ m (symmDiff {r} T)) U = _
          rw [bladeRepr_cBlade]
          have heq_iff : symmDiff {r} T = U ↔ T = S := by
            constructor
            · intro h
              calc
                T = symmDiff {r} (symmDiff {r} T) := (symmDiff_symmDiff_cancel_left {r} T).symm
                _ = symmDiff {r} U := by rw [h]
                _ = S := symmDiff_symmDiff_cancel_left {r} S
            · intro h; subst h; rfl
          by_cases hTS : T = S
          · subst hTS; simp [U]
          · have hneU : symmDiff {r} T ≠ U := fun h => hTS (heq_iff.mp h)
            simp [Pi.single_apply, hTS, hneU.symm]
        simp only [hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have h0 : coeff S * α S = 0 := by
        rw [← hrepU, hcomm_r]
        simp [bladeRepr]
      exact (mul_eq_zero.mp h0).resolve_right (hα_ne S rfl)
    · exact hodd S (Nat.not_even_iff_odd.mp hcard)
  have hscalar : X = coeff ∅ • 1 := by
    rw [hX, Finset.sum_eq_single ∅]
    · simp [cBlade_empty]
    · intro S _ hSne
      rw [hzero S hSne, zero_smul]
    · intro h; exact False.elim (h (Finset.mem_univ ∅))
  have hmul1 : CliffordAlgebra.reverse X * X = 1 :=
    (spinGroup_reverse_mul_self_eq_one (cliffordNegSqForm ℝ m) g).1
  have hsq : coeff ∅ ^ 2 = 1 := by
    have h1 := congrArg (fun Y => bladeRepr ℝ m Y ∅) hmul1
    have hrev : CliffordAlgebra.reverse X = coeff ∅ • 1 := by
      rw [hscalar, map_smul, CliffordAlgebra.reverse.map_one]
    rw [hrev, hscalar, smul_mul_smul_comm, one_mul, ← sq] at h1
    have hL : bladeRepr ℝ m (coeff ∅ ^ 2 • (1 : CliffordAlgebra (cliffordNegSqForm ℝ m))) ∅ =
        coeff ∅ ^ 2 := by
      rw [← cBlade_empty ℝ m, bladeRepr, map_smul, LinearMap.smul_apply, Pi.smul_apply,
        smul_eq_mul]
      change coeff ∅ ^ 2 * bladeRepr ℝ m (cBlade ℝ m ∅) ∅ = coeff ∅ ^ 2
      rw [bladeRepr_cBlade]
      simp
    have hR : bladeRepr ℝ m (1 : CliffordAlgebra (cliffordNegSqForm ℝ m)) ∅ = 1 := by
      rw [← cBlade_empty ℝ m, bladeRepr_cBlade]; simp
    rw [hL, hR] at h1
    exact h1
  rcases sq_eq_one_iff.mp hsq with h1 | h1
  · left; change X = 1; rw [hscalar, h1, one_smul]
  · right; change X = -1; rw [hscalar, h1, neg_one_smul]

theorem spinorRepC_spinCEmbed_injective (n : ℕ) [NeZero n] :
    Function.Injective (fun p : SpinC (2 * n) =>
      spinorRepC n (spinCEmbed (cliffordNegSqForm ℝ (2 * n))
        (exists_isUnit_cliffordNegSqForm (2 * n)) p)) := by
  let φ : SpinC (2 * n) →* (Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)))ˣ :=
    (Units.map (spinorRepC n).toMonoidHom).comp
      (spinCEmbed (cliffordNegSqForm ℝ (2 * n)) (exists_isUnit_cliffordNegSqForm (2 * n)))
  suffices Function.Injective φ by
    intro p₁ p₂ hp
    apply this
    exact Units.ext hp
  rw [injective_iff_map_eq_one]
  intro p hp
  induction p using QuotientGroup.induction_on with
  | H q =>
    rcases q with ⟨g, z⟩
    let gC : CliffordAlgebra (cliffordNegSqForm ℝ (2 * n)) := g
    have hval : ((z : ℂ) • spinorRepC n ((1 : ℂ) ⊗ₜ[ℝ] gC)) = 1 := by
      have hp' := congrArg Units.val hp
      change spinorRepC n ((z : ℂ) ⊗ₜ[ℝ] gC) = 1 at hp'
      have hsm : ((z : ℂ) ⊗ₜ[ℝ] gC) = (z : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] gC) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hsm, map_smul] at hp'
      exact hp'
    have hcomm_rep : ∀ v : Fin (2 * n) → ℝ,
        spinorRepC n ((1 : ℂ) ⊗ₜ[ℝ] gC) * spinorCliffordMap n v =
          spinorCliffordMap n v * spinorRepC n ((1 : ℂ) ⊗ₜ[ℝ] gC) := by
      intro v
      have hinv : spinorRepC n ((1 : ℂ) ⊗ₜ[ℝ] gC) =
          ((z⁻¹ : Circle) : ℂ) • (1 : Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ))) := by
        have hm := congrArg (fun T => ((z⁻¹ : Circle) : ℂ) • T) hval
        rw [smul_smul, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_smul] at hm
        exact hm
      rw [hinv, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    have hiso1 : spinGroupToIsometryHom (cliffordNegSqForm ℝ (2 * n)) g = 1 := by
      apply DFunLike.ext; intro v
      apply spinorCliffordMap_injective n
      rw [← spinorRepC_rotor_sandwich g v, hcomm_rep v, mul_assoc]
      have hmul_rev :
          spinorRepC n ((1 : ℂ) ⊗ₜ[ℝ] gC) *
            spinorRepC n ((1 : ℂ) ⊗ₜ[ℝ] CliffordAlgebra.reverse gC) = 1 := by
        let u := _root_.spinGroup.toUnits g
        have hu : CliffordAlgebra.reverse gC * (u : CliffordAlgebra (cliffordNegSqForm ℝ (2 * n))) = 1 :=
          (spinGroup_reverse_mul_self_eq_one (cliffordNegSqForm ℝ (2 * n)) g).1
        have hrev_inv : CliffordAlgebra.reverse gC = (u⁻¹ : _) := by
          calc
            CliffordAlgebra.reverse gC
                = CliffordAlgebra.reverse gC * ((u : _) * (u⁻¹ : _)) := by simp
            _ = (CliffordAlgebra.reverse gC * (u : _)) * (u⁻¹ : _) := (mul_assoc _ _ _).symm
            _ = (u⁻¹ : _) := by rw [hu, one_mul]
        have hg_rev : gC * CliffordAlgebra.reverse gC = 1 := by
          change (u : CliffordAlgebra (cliffordNegSqForm ℝ (2 * n))) * CliffordAlgebra.reverse gC = 1
          rw [hrev_inv, Units.mul_inv]
        have htmul : ((1 : ℂ) ⊗ₜ[ℝ] gC) *
            ((1 : ℂ) ⊗ₜ[ℝ] CliffordAlgebra.reverse gC) = 1 := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hg_rev, Algebra.TensorProduct.one_def]
        rw [← map_mul, htmul, map_one]
      rw [hmul_rev, mul_one]
      rfl
    have hcomm_cgen : ∀ r : Fin (2 * n), cGen ℝ (2 * n) r * gC = gC * cGen ℝ (2 * n) r := by
      intro r
      have hr := congrArg (fun f => f (Pi.single r (1 : ℝ))) hiso1
      have hsand := ι_spinGroupIsometryEquiv (Q := cliffordNegSqForm ℝ (2 * n)) g (Pi.single r 1)
      rw [show spinGroupIsometryEquiv (cliffordNegSqForm ℝ (2 * n)) g (Pi.single r 1) =
          spinGroupToIsometryHom (cliffordNegSqForm ℝ (2 * n)) g (Pi.single r 1) from rfl, hr]
        at hsand
      have hmul := congrArg (fun x => x * gC) hsand
      rw [mul_assoc, (spinGroup_reverse_mul_self_eq_one _ g).1, mul_one] at hmul
      exact hmul
    rcases spinGroup_commutes_cGen_imp_scalar g hcomm_cgen with hg1 | hgneg
    · have hz1 : (z : ℂ) = 1 := by
        rw [show gC = 1 from hg1] at hval
        have h1 : spinorRepC n ((1 : ℂ) ⊗ₜ[ℝ] (1 : CliffordAlgebra (cliffordNegSqForm ℝ (2 * n)))) = 1 := by
          rw [← Algebra.TensorProduct.one_def, map_one]
        rw [h1] at hval
        have h11 := congrArg (fun T : Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) => T 1) hval
        simp only [LinearMap.smul_apply, Module.End.one_apply, Algebra.smul_def, mul_one] at h11
        have heq := congrArg ExteriorAlgebra.algebraMapInv h11
        simpa [ExteriorAlgebra.algebraMap_leftInverse _] using heq
      have hz' : z = 1 := Circle.ext hz1
      have hg' : g = 1 := Subtype.ext hg1
      rw [QuotientGroup.eq_one_iff]
      left; exact Prod.ext hg' hz'
    · have hzneg : (z : ℂ) = -1 := by
        rw [show gC = -1 from hgneg] at hval
        have hneg : spinorRepC n ((1 : ℂ) ⊗ₜ[ℝ] (-1 : CliffordAlgebra (cliffordNegSqForm ℝ (2 * n)))) = -1 := by
          rw [TensorProduct.tmul_neg, map_neg, ← Algebra.TensorProduct.one_def, map_one]
        rw [hneg] at hval
        have h11 := congrArg (fun T : Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) => T 1) hval
        simp only [LinearMap.smul_apply, LinearMap.neg_apply, Module.End.one_apply] at h11
        have h11' : -(algebraMap ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) (z : ℂ)) = 1 := by
          simpa [smul_neg, Algebra.smul_def, mul_one] using h11
        have heq := congrArg ExteriorAlgebra.algebraMapInv h11'
        rw [map_neg, ExteriorAlgebra.algebraMap_leftInverse _ _,
          ← map_one (algebraMap ℂ (ExteriorAlgebra ℂ (Fin n → ℂ))),
          ExteriorAlgebra.algebraMap_leftInverse _ _] at heq
        exact neg_eq_iff_eq_neg.mp heq
      have hz' : z = -1 := Circle.ext (by simpa using hzneg)
      have hg' : g = negOneSpinGroup (cliffordNegSqForm ℝ (2 * n))
          (exists_isUnit_cliffordNegSqForm (2 * n)) := Subtype.ext hgneg
      rw [QuotientGroup.eq_one_iff]
      right; exact Prod.ext hg' hz'

/-! #### `U(n)` Spinor Representation & Complex Householder Decomposition -/

/-- `Λ^{0,*}`-bundle representation of `U(n)` on `ExteriorAlgebra ℂ (Fin n → ℂ)`:
`U ↦ (det U) • Λ^*(Ū)` (multiplicative group homomorphism into `(End_ℂ(Λ^* ℂⁿ))ˣ`). -/
def unitarySpinorAction (n : ℕ) :
    Matrix.unitaryGroup (Fin n) ℂ →*
      (Module.End ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)))ˣ where
  toFun U :=
    { val := (U.1.det) • (ExteriorAlgebra.map (Matrix.toLin' (U.1.map star))).toLinearMap
      inv := ((U⁻¹).1.det) • (ExteriorAlgebra.map (Matrix.toLin' ((U⁻¹).1.map star))).toLinearMap
      val_inv := by
        apply LinearMap.ext; intro ω
        have hdet : U.1.det * (U⁻¹).1.det = 1 := by
          rw [← Matrix.det_mul, ← Submonoid.coe_mul, mul_inv_cancel,
            Submonoid.coe_one, Matrix.det_one]
        have hcomp : ((ExteriorAlgebra.map (Matrix.toLin' (U.1.map star))).comp
            (ExteriorAlgebra.map (Matrix.toLin' ((U⁻¹).1.map star)))) =
            AlgHom.id ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) := by
          rw [ExteriorAlgebra.map_comp_map, ← Matrix.toLin'_mul]
          have hmul : U.1.map star * (U⁻¹).1.map star = 1 := by
            have h1 : U.1 * (U⁻¹).1 = 1 := by
              rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]
            ext i j
            have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => star (M i j)) h1
            simpa [Matrix.mul_apply, star_sum, star_mul', mul_comm, Matrix.one_apply] using hij
          rw [hmul, Matrix.toLin'_one, ExteriorAlgebra.map_id]
        simp only [Module.End.mul_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
          Module.End.one_apply]
        rw [map_smul, smul_smul, hdet, one_smul]
        exact congrArg (fun f : ExteriorAlgebra ℂ (Fin n → ℂ) →ₐ[ℂ] _ => f ω) hcomp
      inv_val := by
        apply LinearMap.ext; intro ω
        have hdet : (U⁻¹).1.det * U.1.det = 1 := by
          rw [← Matrix.det_mul, ← Submonoid.coe_mul, inv_mul_cancel,
            Submonoid.coe_one, Matrix.det_one]
        have hcomp : ((ExteriorAlgebra.map (Matrix.toLin' ((U⁻¹).1.map star))).comp
            (ExteriorAlgebra.map (Matrix.toLin' (U.1.map star)))) =
            AlgHom.id ℂ (ExteriorAlgebra ℂ (Fin n → ℂ)) := by
          rw [ExteriorAlgebra.map_comp_map, ← Matrix.toLin'_mul]
          have hmul : (U⁻¹).1.map star * U.1.map star = 1 := by
            have h1 : (U⁻¹).1 * U.1 = 1 := by
              rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
            ext i j
            have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => star (M i j)) h1
            simpa [Matrix.mul_apply, star_sum, star_mul', mul_comm, Matrix.one_apply] using hij
          rw [hmul, Matrix.toLin'_one, ExteriorAlgebra.map_id]
        simp only [Module.End.mul_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
          Module.End.one_apply]
        rw [map_smul, smul_smul, hdet, one_smul]
        exact congrArg (fun f : ExteriorAlgebra ℂ (Fin n → ℂ) →ₐ[ℂ] _ => f ω) hcomp }
  map_one' := Units.ext <| by
    apply LinearMap.ext; intro ω
    have h1 : ((1 : Matrix (Fin n) (Fin n) ℂ).map star) = 1 := by
      ext i j; simp [Matrix.one_apply]
    simp [h1, Matrix.toLin'_one, ExteriorAlgebra.map_id]
  map_mul' U₁ U₂ := Units.ext <| by
    apply LinearMap.ext; intro ω
    simp only [Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply,
      AlgHom.toLinearMap_apply, Submonoid.coe_mul, Matrix.det_mul, map_smul, smul_smul]
    congr 1
    · exact mul_comm _ _
    · have hmul : (U₁.1 * U₂.1).map star = U₁.1.map star * U₂.1.map star := by
        ext i j; simp [Matrix.mul_apply, star_sum, star_mul', mul_comm]
      rw [hmul, Matrix.toLin'_mul, ← ExteriorAlgebra.map_comp_map]
      rfl

/-- Complex Householder reflection `I + (ζ - 1) v v* ∈ U(n)` along unit vector `v`. -/
def complexHouseholder {n : ℕ} (v : Fin n → ℂ) (hv : v ⬝ᵥ star v = 1) (ζ : Circle) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨1 + ((ζ : ℂ) - 1) • Matrix.vecMulVec v (star v), by
    rw [Matrix.mem_unitaryGroup_iff]
    let P : Matrix (Fin n) (Fin n) ℂ := Matrix.vecMulVec v (star v)
    have hPstar : star P = P := by
      ext i j
      simp only [P, Matrix.star_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply,
        Pi.star_apply, star_mul', star_star, mul_comm]
    have hPsq : P * P = P := by
      ext i j
      simp only [P, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
      calc
        ∑ k : Fin n, v i * star (v k) * (v k * star (v j))
            = v i * (∑ k : Fin n, v k * star (v k)) * star (v j) := by
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun k _ => by ring
        _ = v i * (v ⬝ᵥ star v) * star (v j) := rfl
        _ = v i * star (v j) := by rw [hv, mul_one]
    have hstar : star (1 + ((ζ : ℂ) - 1) • P) = 1 + (star (ζ : ℂ) - 1) • P := by
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
        Matrix.conjTranspose_smul, star_sub, star_one]
      rw [← Matrix.star_eq_conjTranspose, hPstar]
    rw [hstar]
    have hζ : (ζ : ℂ) * star (ζ : ℂ) = 1 := by
      rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel,
        Circle.coe_one]
    calc
      (1 + ((ζ : ℂ) - 1) • P) * (1 + (star (ζ : ℂ) - 1) • P)
          = 1 + (((ζ : ℂ) - 1) + (star (ζ : ℂ) - 1) + ((ζ : ℂ) - 1) * (star (ζ : ℂ) - 1)) • P := by
            simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
              smul_smul, hPsq]
            module
      _ = 1 + ((ζ : ℂ) * star (ζ : ℂ) - 1) • P := by
            congr 2; ring
      _ = 1 := by rw [hζ, sub_self, zero_smul, add_zero]⟩

theorem complexHouseholder_mulVec {n : ℕ} (v : Fin n → ℂ) (hv : v ⬝ᵥ star v = 1) (ζ : Circle)
    (w : Fin n → ℂ) :
    (complexHouseholder v hv ζ).1 *ᵥ w = w + (((ζ : ℂ) - 1) * (star v ⬝ᵥ w)) • v := by
  ext i
  simp only [complexHouseholder, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem complexHouseholder_det {n : ℕ} (v : Fin n → ℂ) (hv : v ⬝ᵥ star v = 1) (ζ : Circle) :
    (complexHouseholder v hv ζ).1.det = (ζ : ℂ) := by
  have hv_ne : v ≠ 0 := by
    intro h0; rw [h0, zero_dotProduct] at hv; exact zero_ne_one hv
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv_ne
  let H := (complexHouseholder v hv ζ).1
  let B : Matrix (Fin n) (Fin n) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).updateCol i₀ v
  have hBdet : B.det = v i₀ := by
    have hc := Matrix.det_updateCol_sum (1 : Matrix (Fin n) (Fin n) ℂ) i₀ v
    have hcol : (fun k => ∑ i : Fin n, v i • (1 : Matrix (Fin n) (Fin n) ℂ) k i) = v := by
      ext k; simp [Matrix.one_apply]
    rw [hcol] at hc
    simpa [B] using hc
  let C : Matrix (Fin n) (Fin n) ℂ :=
    (1 : Matrix (Fin n) (Fin n) ℂ).updateRow i₀
      (fun j => if j = i₀ then (ζ : ℂ) else ((ζ : ℂ) - 1) * star (v j))
  have hCdet : C.det = (ζ : ℂ) := by
    rw [Matrix.det_apply']
    have hzero : ∀ σ ∈ Finset.univ, σ ≠ (1 : Equiv.Perm (Fin n)) →
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin n, C (σ i) i = 0 := by
      intro σ _ hσ
      have hne : ∃ i : Fin n, σ i ≠ i := by
        by_contra hall
        push_neg at hall
        exact hσ (Equiv.ext hall)
      rcases hne with ⟨i, hi⟩
      suffices hprod : (∏ j : Fin n, C (σ j) j) = 0 by simp [hprod]
      by_cases hsi : σ i = i₀
      · refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
        have hii₀ : i ≠ i₀ := fun h => hi (hsi.trans h.symm)
        have hsi₀ : σ i₀ ≠ i₀ := fun h => hii₀ (σ.injective (hsi.trans h.symm))
        simp [C, Matrix.updateRow_apply, hsi₀, Matrix.one_apply]
      · refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        simp [C, Matrix.updateRow_apply, hsi, Matrix.one_apply, hi]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n)) hzero (fun h => absurd (Finset.mem_univ 1) h)]
    simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, Equiv.Perm.coe_one, id_eq, one_mul]
    rw [← Finset.mul_prod_erase Finset.univ (fun i => C i i) (Finset.mem_univ i₀)]
    have hi₀_val : C i₀ i₀ = (ζ : ℂ) := by simp [C, Matrix.updateRow_apply]
    have hrest : ∀ i ∈ Finset.univ.erase i₀, C i i = 1 := by
      intro i hi
      have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
      simp [C, Matrix.updateRow_apply, hne, Matrix.one_apply]
    rw [hi₀_val, Finset.prod_congr rfl hrest, Finset.prod_const_one, mul_one]
  have hHB : H * B = B * C := by
    ext i j
    by_cases hj : j = i₀
    · rw [hj]
      have hv_col : (H * B) i i₀ = (H *ᵥ v) i := by
        simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [B, Matrix.updateCol_apply]
      have hstar : star v ⬝ᵥ v = 1 := by rw [dotProduct_comm, hv]
      have hHv : (H *ᵥ v) i = (ζ : ℂ) * v i := by
        rw [complexHouseholder_mulVec, hstar, mul_one]
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hBC : (B * C) i i₀ = (ζ : ℂ) * v i := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
        · simp [B, C, Matrix.updateCol_apply, Matrix.updateRow_apply, mul_comm]
        · intro k _ hk
          simp [C, Matrix.updateRow_apply, hk, Matrix.one_apply]
        · intro hmem; exact absurd (Finset.mem_univ i₀) hmem
      rw [hv_col, hHv, hBC]
    · have hLHS : (H * B) i j = H i j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single j]
        · simp [B, Matrix.updateCol_apply, hj, Matrix.one_apply]
        · intro k _ hk
          simp [B, Matrix.updateCol_apply, hj, Matrix.one_apply, hk]
        · intro hmem; exact absurd (Finset.mem_univ j) hmem
      have hRHS : (B * C) i j =
          B i i₀ * C i₀ j + B i j * C j j := by
        rw [Matrix.mul_apply, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀)]
        congr 1
        rw [Finset.sum_eq_single j]
        · intro k hk hkj
          have hk0 : k ≠ i₀ := (Finset.mem_erase.mp hk).1
          simp [C, Matrix.updateRow_apply, hk0, Matrix.one_apply, hkj]
        · intro hmem
          exact absurd (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) hmem
      rw [hLHS, hRHS]
      simp [H, complexHouseholder, B, C, Matrix.updateCol_apply, Matrix.updateRow_apply,
        hj, Matrix.one_apply, Matrix.vecMulVec_apply]
      ring
  have hdet_eq := congrArg Matrix.det hHB
  rw [Matrix.det_mul, Matrix.det_mul, hBdet, hCdet] at hdet_eq
  exact mul_right_cancel₀ hi₀ (by simpa [mul_comm] using hdet_eq)

end UnitaryToSpinC

end SpinCGroupSection

end InfoGeometry.Geometry.SpinCAndSeibergWittenQuadratic
