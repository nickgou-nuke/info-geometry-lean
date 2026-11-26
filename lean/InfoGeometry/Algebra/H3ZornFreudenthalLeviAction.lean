/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornFreudenthalQuartic
import InfoGeometry.Exceptional.FreudenthalChargeLinear
import InfoGeometry.Algebra.H3ZornStructureGroup
import InfoGeometry.Algebra.H3ZornMinusculeCFSGBridge
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Levi `Str₀(H₃(𝕆_s)) = E₆(6)` Action on 56D Freudenthal Charge Space

This module realizes the block-diagonal Levi action of the reduced structure group
`h3zornReducedStructureGroup` (`Str₀(H₃(𝕆_s))`) and its Chevalley subgroup
`h3zornChevalleyE6` on the 56-dimensional split-Albert Freudenthal charge space
`Charge := FreudenthalCharge (H3Zorn ℝ)`.

For `g : h3zornReducedStructureGroup`, the action is defined by
`g · ⟨α, β, x, y⟩ := ⟨α, β, g.1 x, h3zornTraceInverseAdjoint g.1 y⟩`.

Main results:
1. `chargeCoordinateLinearEquiv` and `finrank_charge : Module.finrank ℝ Charge = 56`.
2. Adjoint-quadratic intertwining and group laws for `h3zornTraceInverseAdjoint` on
   `h3zornReducedStructureGroup`, including `h3zornTraceInverseAdjointReduced`.
3. Group homomorphisms `leviChargeEquiv`, `leviChargeGL`, subgroup `leviChargeSubgroup`,
   and restrictions `chevalleyE6ChargeEquiv`, `chevalleyE6ChargeGL`,
   `chevalleyE6ChargeSubgroup ≤ leviChargeSubgroup`, all proved injective.
4. Kernel-checked invariance of both `symplecticForm` and `quarticInvariant`, packaged into
   `leviInvariantAction : InvariantAction h3zornReducedStructureGroup` and
   `chevalleyE6InvariantAction : InvariantAction h3zornChevalleyE6`.
5. Concrete non-triviality and non-commutativity witnesses from the Chevalley torus,
   non-commuting simple Weyl reflections, and a quadratic Jordan `U`-element.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Algebra.H3ZornFreudenthal

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Exceptional.Freudenthal

section CarrierDimension

/-- Linear equivalence identifying the 56D Freudenthal charge space with
`ℝ × ℝ × H3Zorn ℝ × H3Zorn ℝ`. -/
def chargeCoordinateLinearEquiv :
    Charge ≃ₗ[ℝ] (ℝ × ℝ × H3Zorn ℝ × H3Zorn ℝ) where
  __ := coordinateAddEquiv (J := H3Zorn ℝ)
  map_smul' _ _ := rfl

@[simp] theorem chargeCoordinateLinearEquiv_apply (Q : Charge) :
    chargeCoordinateLinearEquiv Q = (Q.alpha, Q.beta, Q.x, Q.y) := rfl

/-- The split-Albert Freudenthal charge space has real dimension `56 = 1 + 1 + 27 + 27`. -/
theorem finrank_charge : Module.finrank ℝ Charge = 56 := by
  rw [LinearEquiv.finrank_eq chargeCoordinateLinearEquiv,
    Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_self, finrank_h3zorn]

end CarrierDimension

section ReducedStructureIntertwining

/-- For `g ∈ Str₀(H₃(𝕆_s))`, `(g x)# = (g⁻¹)† (x#)`. -/
theorem adjointQuad_reducedStructure (g : h3zornReducedStructureGroup) (x : H3Zorn ℝ) :
    H3Zorn.adjointQuad (g.1 x) =
      h3zornTraceInverseAdjoint g.1 (H3Zorn.adjointQuad x) := by
  simpa using h3zorn_adjointQuad_similitude_intertwines g.1 1
    (fun z => by simpa using g.2 z) x

/-- For `g ∈ Str₀(H₃(𝕆_s))`, `((g⁻¹)† y)# = g (y#)`. -/
theorem adjointQuad_traceInverseAdjoint_reducedStructure
    (g : h3zornReducedStructureGroup) (y : H3Zorn ℝ) :
    H3Zorn.adjointQuad (h3zornTraceInverseAdjoint g.1 y) =
      g.1 (H3Zorn.adjointQuad y) := by
  have h := h3zorn_traceInverseAdjoint_crossProduct_intertwines g.1 1
    (fun z => by simpa using g.2 z) y y
  rw [Units.val_one, one_smul, H3Zorn.crossProduct_self,
    H3Zorn.crossProduct_self, map_smul] at h
  have hhalf := congrArg (fun W : H3Zorn ℝ => (1 / 2 : ℝ) • W) h
  simpa [smul_smul] using hhalf

/-- The inverse trace-adjoint `(g⁻¹)†` preserves the split-Albert cubic norm. -/
theorem normCubic_traceInverseAdjoint_reducedStructure
    (g : h3zornReducedStructureGroup) (y : H3Zorn ℝ) :
    H3Zorn.normCubic (h3zornTraceInverseAdjoint g.1 y) = H3Zorn.normCubic y := by
  have h1 := H3Zorn.mccrimmon_identity_13 (h3zornTraceInverseAdjoint g.1 y)
  have h2 := H3Zorn.mccrimmon_identity_13 y
  rw [adjointQuad_traceInverseAdjoint_reducedStructure, H3Zorn.traceBilin_symm,
    h3zornTraceInverseAdjoint_traceBilin, H3Zorn.traceBilin_symm, h2] at h1
  linarith

/-- Package `(h3zornTraceAdjointEquiv g.1).symm` as an element of
`h3zornReducedStructureGroup`. -/
def h3zornTraceInverseAdjointReduced
    (g : h3zornReducedStructureGroup) : h3zornReducedStructureGroup :=
  ⟨(h3zornTraceAdjointEquiv g.1).symm, normCubic_traceInverseAdjoint_reducedStructure g⟩

@[simp] theorem h3zornTraceInverseAdjointReduced_apply
    (g : h3zornReducedStructureGroup) (y : H3Zorn ℝ) :
    (h3zornTraceInverseAdjointReduced g).1 y = h3zornTraceInverseAdjoint g.1 y := rfl

@[simp] theorem h3zornTraceInverseAdjoint_one (y : H3Zorn ℝ) :
    h3zornTraceInverseAdjoint (1 : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) y = y := by
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro z
  simpa using h3zornTraceInverseAdjoint_traceBilin
    (1 : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) y z

theorem h3zornTraceInverseAdjoint_mul
    (e₁ e₂ : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (y : H3Zorn ℝ) :
    h3zornTraceInverseAdjoint (e₁ * e₂) y =
      h3zornTraceInverseAdjoint e₁ (h3zornTraceInverseAdjoint e₂ y) := by
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro z
  obtain ⟨w, rfl⟩ := (e₁ * e₂).surjective z
  rw [h3zornTraceInverseAdjoint_traceBilin (e₁ * e₂) y w]
  change _ = H3Zorn.traceBilin (h3zornTraceInverseAdjoint e₁ (h3zornTraceInverseAdjoint e₂ y))
    (e₁ (e₂ w))
  rw [h3zornTraceInverseAdjoint_traceBilin e₁, h3zornTraceInverseAdjoint_traceBilin e₂]

theorem traceBilin_reducedStructure_pair
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (x y : H3Zorn ℝ) :
    H3Zorn.traceBilin (e x) (h3zornTraceInverseAdjoint e y) =
      H3Zorn.traceBilin x y := by
  rw [H3Zorn.traceBilin_symm (e x), h3zornTraceInverseAdjoint_traceBilin,
    H3Zorn.traceBilin_symm]

end ReducedStructureIntertwining

section LeviActionDefinition

/-- Block-diagonal Levi linear equivalence on `Charge` induced by `g ∈ Str₀(H₃(𝕆_s))`:
`⟨α, β, x, y⟩ ↦ ⟨α, β, g.1 x, (g.1⁻¹)† y⟩`. -/
def leviChargeLinearEquiv (g : h3zornReducedStructureGroup) : Charge ≃ₗ[ℝ] Charge where
  toFun Q :=
    { alpha := Q.alpha
      beta := Q.beta
      x := g.1 Q.x
      y := h3zornTraceInverseAdjoint g.1 Q.y }
  invFun Q :=
    { alpha := Q.alpha
      beta := Q.beta
      x := g.1.symm Q.x
      y := h3zornTraceAdjointEquiv g.1 Q.y }
  left_inv Q := by
    apply FreudenthalCharge.ext
    · rfl
    · rfl
    · exact g.1.symm_apply_apply Q.x
    · exact (h3zornTraceAdjointEquiv g.1).apply_symm_apply Q.y
  right_inv Q := by
    apply FreudenthalCharge.ext
    · rfl
    · rfl
    · exact g.1.apply_symm_apply Q.x
    · exact (h3zornTraceAdjointEquiv g.1).symm_apply_apply Q.y
  map_add' Q₁ Q₂ := by
    apply FreudenthalCharge.ext <;> simp
  map_smul' r Q := by
    apply FreudenthalCharge.ext <;> simp

@[simp] theorem leviChargeLinearEquiv_alpha (g : h3zornReducedStructureGroup) (Q : Charge) :
    (leviChargeLinearEquiv g Q).alpha = Q.alpha := rfl

@[simp] theorem leviChargeLinearEquiv_beta (g : h3zornReducedStructureGroup) (Q : Charge) :
    (leviChargeLinearEquiv g Q).beta = Q.beta := rfl

@[simp] theorem leviChargeLinearEquiv_x (g : h3zornReducedStructureGroup) (Q : Charge) :
    (leviChargeLinearEquiv g Q).x = g.1 Q.x := rfl

@[simp] theorem leviChargeLinearEquiv_y (g : h3zornReducedStructureGroup) (Q : Charge) :
    (leviChargeLinearEquiv g Q).y = h3zornTraceInverseAdjoint g.1 Q.y := rfl

/-- Group homomorphism from `Str₀(H₃(𝕆_s))` to `Charge ≃ₗ[ℝ] Charge`. -/
def leviChargeEquiv : h3zornReducedStructureGroup →* (Charge ≃ₗ[ℝ] Charge) where
  toFun := leviChargeLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro Q
    apply FreudenthalCharge.ext <;> simp
  map_mul' g₁ g₂ := by
    apply LinearEquiv.ext
    intro Q
    apply FreudenthalCharge.ext
    · rfl
    · rfl
    · rfl
    · exact h3zornTraceInverseAdjoint_mul g₁.1 g₂.1 Q.y

@[simp] theorem leviChargeEquiv_apply (g : h3zornReducedStructureGroup) (Q : Charge) :
    leviChargeEquiv g Q = leviChargeLinearEquiv g Q := rfl

/-- The Levi representation of `Str₀(H₃(𝕆_s))` on `Charge` is faithful. -/
theorem leviChargeEquiv_injective : Function.Injective leviChargeEquiv := by
  intro g₁ g₂ h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hx := congrArg (fun e : Charge ≃ₗ[ℝ] Charge => (e (electricCharge 0 x)).x) h
  simpa [electricCharge] using hx

/-- Group homomorphism embedding `Str₀(H₃(𝕆_s))` into `GL(Charge) ≅ GL₅₆(ℝ)`. -/
def leviChargeGL :
    h3zornReducedStructureGroup →* LinearMap.GeneralLinearGroup ℝ Charge :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ Charge).symm.toMonoidHom.comp
    leviChargeEquiv

theorem leviChargeGL_injective : Function.Injective leviChargeGL :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ Charge).symm.injective.comp
    leviChargeEquiv_injective

/-- The `Str₀(H₃(𝕆_s))` Levi subgroup inside `LinearMap.GeneralLinearGroup ℝ Charge`. -/
def leviChargeSubgroup : Subgroup (LinearMap.GeneralLinearGroup ℝ Charge) :=
  leviChargeGL.range

/-- Restriction of the 56D Levi representation to `h3zornChevalleyE6`. -/
def chevalleyE6ChargeEquiv : h3zornChevalleyE6 →* (Charge ≃ₗ[ℝ] Charge) :=
  leviChargeEquiv.comp h3zornChevalleyE6.subtype

@[simp] theorem chevalleyE6ChargeEquiv_apply (g : h3zornChevalleyE6) (Q : Charge) :
    chevalleyE6ChargeEquiv g Q = leviChargeEquiv g.1 Q := rfl

theorem chevalleyE6ChargeEquiv_injective : Function.Injective chevalleyE6ChargeEquiv :=
  leviChargeEquiv_injective.comp Subtype.coe_injective

/-- Embedding of `h3zornChevalleyE6` into `LinearMap.GeneralLinearGroup ℝ Charge`. -/
def chevalleyE6ChargeGL :
    h3zornChevalleyE6 →* LinearMap.GeneralLinearGroup ℝ Charge :=
  leviChargeGL.comp h3zornChevalleyE6.subtype

theorem chevalleyE6ChargeGL_injective : Function.Injective chevalleyE6ChargeGL :=
  leviChargeGL_injective.comp Subtype.coe_injective

/-- The `E₆(6)` Chevalley subgroup inside `LinearMap.GeneralLinearGroup ℝ Charge`. -/
def chevalleyE6ChargeSubgroup : Subgroup (LinearMap.GeneralLinearGroup ℝ Charge) :=
  chevalleyE6ChargeGL.range

theorem chevalleyE6ChargeSubgroup_le_leviChargeSubgroup :
    chevalleyE6ChargeSubgroup ≤ leviChargeSubgroup := by
  rintro _ ⟨g, rfl⟩
  exact ⟨g.1, rfl⟩

end LeviActionDefinition

section InvarianceAndPackaging

/-- The 56D Levi action of `Str₀(H₃(𝕆_s))` preserves the Freudenthal symplectic pairing. -/
theorem leviChargeEquiv_symplecticForm
    (g : h3zornReducedStructureGroup) (Q₁ Q₂ : Charge) :
    symplecticForm (leviChargeEquiv g Q₁) (leviChargeEquiv g Q₂) =
      symplecticForm Q₁ Q₂ := by
  rw [symplecticForm_expanded, symplecticForm_expanded]
  simp only [leviChargeEquiv_apply, leviChargeLinearEquiv_alpha, leviChargeLinearEquiv_beta,
    leviChargeLinearEquiv_x, leviChargeLinearEquiv_y]
  rw [traceBilin_reducedStructure_pair g.1 Q₁.x Q₂.y,
    h3zornTraceInverseAdjoint_traceBilin]

/-- The 56D Levi action of `Str₀(H₃(𝕆_s))` preserves the Freudenthal quartic invariant. -/
theorem leviChargeEquiv_quarticInvariant
    (g : h3zornReducedStructureGroup) (Q : Charge) :
    quarticInvariant (leviChargeEquiv g Q) = quarticInvariant Q := by
  rw [quarticInvariant_expanded, quarticInvariant_expanded]
  simp only [leviChargeEquiv_apply, leviChargeLinearEquiv_alpha, leviChargeLinearEquiv_beta,
    leviChargeLinearEquiv_x, leviChargeLinearEquiv_y]
  rw [traceBilin_reducedStructure_pair g.1 Q.x Q.y,
    g.2 Q.x,
    normCubic_traceInverseAdjoint_reducedStructure g Q.y,
    adjointQuad_reducedStructure g Q.x,
    adjointQuad_traceInverseAdjoint_reducedStructure g Q.y,
    h3zornTraceInverseAdjoint_traceBilin]

/-- Theorem-safe `InvariantAction` packaging of `Str₀(H₃(𝕆_s))` on `Charge`. -/
def leviInvariantAction : InvariantAction h3zornReducedStructureGroup where
  act g Q := leviChargeEquiv g Q
  act_one := by
    funext Q
    simp
  act_mul g₁ g₂ := by
    funext Q
    simp
  preserves_symplecticForm := leviChargeEquiv_symplecticForm
  preserves_quarticInvariant := leviChargeEquiv_quarticInvariant
  preserves_zeroCharge g := by
    have hz : zeroCharge (H3Zorn ℝ) = (0 : Charge) := by
      ext <;> rfl
    rw [hz]
    exact (leviChargeEquiv g).map_zero

/-- Theorem-safe `InvariantAction` packaging of `h3zornChevalleyE6` on `Charge`. -/
def chevalleyE6InvariantAction : InvariantAction h3zornChevalleyE6 where
  act g Q := chevalleyE6ChargeEquiv g Q
  act_one := by
    funext Q
    simp
  act_mul g₁ g₂ := by
    funext Q
    simp
  preserves_symplecticForm g Q₁ Q₂ :=
    leviChargeEquiv_symplecticForm g.1 Q₁ Q₂
  preserves_quarticInvariant g Q :=
    leviChargeEquiv_quarticInvariant g.1 Q
  preserves_zeroCharge g := leviInvariantAction.preserves_zeroCharge g.1

end InvarianceAndPackaging

section NonTrivialityWitnesses

/-- Non-trivial Chevalley torus witness: `h₀(2) ∈ h3zornChevalleyE6` acts non-trivially
on `electricCharge 1 (h3ZornBasis 0)` while preserving `quarticInvariant` and
`symplecticForm`. -/
theorem chevalleyE6_torus_nontrivial_witness :
    let t2 : ℝˣ := Units.mk0 (2 : ℝ) (by norm_num)
    let gT : h3zornChevalleyE6 :=
      ⟨h3zornTorusElt 0 t2, h3zornTorusElt_mem_chevalleyE6 0 t2⟩
    let Q₀ : Charge := electricCharge 1 (h3ZornBasis 0)
    chevalleyE6ChargeEquiv gT Q₀ ≠ Q₀ ∧ chevalleyE6ChargeEquiv gT ≠ 1 := by
  intro t2 gT Q₀
  have happly :
      (chevalleyE6ChargeEquiv gT Q₀).x = (2 : ℝ) • h3ZornBasis 0 := by
    rw [chevalleyE6ChargeEquiv_apply, leviChargeEquiv_apply, leviChargeLinearEquiv_x]
    dsimp only [gT, Q₀, electricCharge]
    rw [h3zornTorusElt_apply_basis 0 t2 0]
    have hw : h3zornWeight 0 0 = 1 := by decide
    rw [hw, zpow_one]
    simp only [t2, Units.val_mk0]
  have hne_vec : (2 : ℝ) • h3ZornBasis 0 ≠ h3ZornBasis 0 := by
    intro heq
    have hsub : ((2 : ℝ) - 1) • h3ZornBasis 0 = 0 := by
      rw [sub_smul, one_smul, heq, sub_self]
    have hc : (2 : ℝ) - 1 ≠ 0 := by norm_num
    exact h3ZornBasis.ne_zero 0 ((smul_eq_zero.mp hsub).resolve_left hc)
  have hne_charge : chevalleyE6ChargeEquiv gT Q₀ ≠ Q₀ := by
    intro hQ
    apply hne_vec
    rw [← happly]
    exact congrArg FreudenthalCharge.x hQ
  refine ⟨hne_charge, ?_⟩
  intro hone
  apply hne_charge
  have hQ := congrArg (fun e : Charge ≃ₗ[ℝ] Charge => e Q₀) hone
  exact hQ

/-- Non-commuting (non-diagonal) Chevalley Weyl witness in `Charge ≃ₗ[ℝ] Charge` and
`LinearMap.GeneralLinearGroup ℝ Charge`. -/
theorem chevalleyE6_weyl_noncomm_witness :
    let w0 : h3zornChevalleyE6 :=
      ⟨h3zornWeylElt 0 1, h3zornWeylElt_mem_chevalleyE6 0 1⟩
    let w2 : h3zornChevalleyE6 :=
      ⟨h3zornWeylElt 2 1, h3zornWeylElt_mem_chevalleyE6 2 1⟩
    chevalleyE6ChargeEquiv w0 * chevalleyE6ChargeEquiv w2 ≠
      chevalleyE6ChargeEquiv w2 * chevalleyE6ChargeEquiv w0 ∧
    chevalleyE6ChargeGL w0 * chevalleyE6ChargeGL w2 ≠
      chevalleyE6ChargeGL w2 * chevalleyE6ChargeGL w0 := by
  intro w0 w2
  have hw : w0 * w2 ≠ w2 * w0 := by
    intro h
    apply h3zornWeylElt_noncomm_witness
    exact congrArg Subtype.val h
  refine ⟨?_, ?_⟩
  · intro h
    apply hw
    apply chevalleyE6ChargeEquiv_injective
    simpa [map_mul] using h
  · intro h
    apply hw
    apply chevalleyE6ChargeGL_injective
    simpa [map_mul] using h

/-- Non-trivial `Str₀(H₃(𝕆_s))` quadratic-`U` witness using `diagCartan 2 (1 / 2) 1`,
acting non-trivially on `electricCharge 1 1` while preserving its quartic invariant `-4`. -/
theorem levi_diagCartan_U_nontrivial_witness :
    let d : H3Zorn ℝ := H3Zorn.diagCartan 2 (1 / 2 : ℝ) 1
    have hd_norm : H3Zorn.normCubic d = 1 := by
      have h := H3Zorn.diagCartan_quadratic_U_peirce_laplace_mellin_and_semigroup
        (R := ℝ) 2 (1 / 2 : ℝ) 1 1 1 1 1
      rw [h.2.1]
      norm_num
    have hd_ne : H3Zorn.normCubic d ≠ 0 := by
      rw [hd_norm]
      norm_num
    let uDiag : h3zornReducedStructureGroup :=
      ⟨h3zornULinearEquiv d hd_ne,
        h3zornULinearEquiv_mem_reducedStructureGroup d hd_ne (Or.inl hd_norm)⟩
    (leviChargeEquiv uDiag (electricCharge 1 1)).x =
        H3Zorn.diagCartan 4 (1 / 4 : ℝ) 1 ∧
      leviChargeEquiv uDiag (electricCharge 1 1) ≠ electricCharge 1 1 ∧
      quarticInvariant (leviChargeEquiv uDiag (electricCharge 1 1)) = -4 := by
  intro d hd_norm hd_ne uDiag
  have hU1 : (leviChargeEquiv uDiag (electricCharge 1 1)).x =
      H3Zorn.diagCartan 4 (1 / 4 : ℝ) 1 := by
    rw [leviChargeEquiv_apply, leviChargeLinearEquiv_x]
    dsimp [uDiag, electricCharge]
    rw [h3zornULinearEquiv_apply]
    have h := (H3Zorn.diagCartan_quadratic_U_peirce_laplace_mellin_and_semigroup
      (R := ℝ) 2 (1 / 2 : ℝ) 1 1 1 1 (1 : H3Zorn ℝ)).2.2.1
    rw [h]
    apply H3Zorn.ext_h3
    · change (2 : ℝ) * 2 * 1 = 4
      norm_num
    · change (1 / 2 : ℝ) * (1 / 2) * 1 = 1 / 4
      norm_num
    · change (1 : ℝ) * 1 * 1 = 1
      norm_num
    · change ZornVectorMatrix.smul (2 * (1 / 2 : ℝ)) ZornVectorMatrix.zero = ZornVectorMatrix.zero
      simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · change ZornVectorMatrix.smul ((1 / 2 : ℝ) * 1) ZornVectorMatrix.zero = ZornVectorMatrix.zero
      simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · change ZornVectorMatrix.smul (2 * (1 : ℝ)) ZornVectorMatrix.zero = ZornVectorMatrix.zero
      simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  refine ⟨hU1, ?_, ?_⟩
  · intro heq
    have hx := congrArg FreudenthalCharge.x heq
    rw [hU1] at hx
    have hα₁ := congrArg H3Zorn.α₁ hx
    change (4 : ℝ) = 1 at hα₁
    norm_num at hα₁
  · rw [leviChargeEquiv_quarticInvariant, unit_electric_quartic]

end NonTrivialityWitnesses

end InfoGeometry.Algebra.H3ZornFreudenthal
