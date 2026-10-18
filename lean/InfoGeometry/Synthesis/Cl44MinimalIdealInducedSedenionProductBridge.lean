/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl44MinimalIdealSplitSedenionEquivBridge
import InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
import InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
import InfoGeometry.Synthesis.Cl44PrimitiveIdempotentIdeal
import InfoGeometry.Synthesis.Cl44InducedSplitSedenionAlgebra

/-!
# `AddCommGroup` / `Module` Structure on `ZornSplitOctonion R`, `LinearEquiv` Promotion, $\mathbb{R}$-Bilinearity of `idealSedenionMul`, Conjugate-Norm Identity, and Transported 14-Parameter $G_2$ Derivations

This module closes the module-structure and $\mathbb{R}$-bilinearity gap identified in §4 of
`docs/SPLIT_SEDENION_CL44_GROUND_TRUTH_CONTRACT.md` on top of
`InfoGeometry.Synthesis.Cl44MinimalIdealSplitSedenionEquivBridge`:

1. **Section 1 — `AddCommGroup` and `Module R` Instance Stack on `ZornSplitOctonion R` & `LinearEquiv` Promotion**:
   - Equips `ZornSplitOctonion R` with `AddCommGroup (ZornSplitOctonion R)` and
     `Module R (ZornSplitOctonion R)` over any `CommRing R` (which automatically induces
     `AddCommGroup (SplitSedenion R)` and `Module R (SplitSedenion R)` via `Prod`).
   - Proves `spinor16ToSplitSedenion_smul` and promotes `spinor16SplitSedenionEquiv` and
     `cl44MatrixLeftIdealSplitSedenionEquiv` to genuine $\mathbb{R}$-linear equivalences
     `spinor16SplitSedenionLinearEquiv : (Fin 16 → ℝ) ≃ₗ[ℝ] SplitSedenion ℝ` and
     `cl44MatrixLeftIdealSplitSedenionLinearEquiv : LeftIdeal primIdem ≃ₗ[ℝ] SplitSedenion ℝ`.

2. **Section 2 — Proved $\mathbb{R}$-Bilinearity of `sedenionMul` and `idealSedenionMul`**:
   - Reuses the operation definitions owned by
     `Cl44InducedSplitSedenionAlgebra.lean` on `LeftIdeal primIdem`.
   - Proves `sedenionMul_add_left`, `sedenionMul_add_right`, `sedenionMul_smul_left`, and
     `sedenionMul_smul_right` on `SplitSedenion ℝ`.
   - Transports these across `cl44MatrixLeftIdealSplitSedenionLinearEquiv` to prove
     `idealSedenionMul_add_left`, `idealSedenionMul_add_right`, `idealSedenionMul_smul_left`,
     and `idealSedenionMul_smul_right` on `LeftIdeal primIdem`.

3. **Section 3 — Quadratic Conjugate-Norm Identity & Transported 14-Parameter $G_2$ Star-Derivations on `LeftIdeal primIdem`**:
   - Proves `sedenionMul_sedenionConj`, `sedenionNorm_eq_zero_iff_sedenionMul_sedenionConj_eq_zero`,
     and `idealSedenion_norm_zero_iff_mul_conj_zero`.
   - Proves `exists_idealSedenion_zero_divisors` and `exists_idealSedenion_nonzero_associator`.
   - Defines `idealG2Derivation (p : Params) : LeftIdeal primIdem → LeftIdeal primIdem` and
     proves `idealG2Derivation_leibniz`, `idealG2Derivation_conj`, `idealG2Derivation_ell_zero`,
     `readIdealG2Params_idealG2Derivation`, and `idealG2Derivation_injective`.

4. **Section 4 — Transported Split-Sedenion Operations on the 16-Component Spinor Carrier `Fin 16 → ℝ`**:
   - Defines `idealMul`, `idealConj`, `idealNorm`, and `idealAssociator` on `Fin 16 → ℝ`.
   - Proves `ideal_product_is_non_associative` and `ideal_norm_zero_iff_mul_conj_zero`.
-/

set_option autoImplicit false
noncomputable section

namespace InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridge

open InfoGeometry.Cl44IdempotentIdeal
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.Cl44MinimalIdealSplitSedenionEquivBridge
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Synthesis.Cl44InducedSplitSedenionAlgebra

/-!
## Section 1: `AddCommGroup` and `Module R` Instance Stack on `ZornSplitOctonion R` & `LinearEquiv` Promotion
-/

section ZornModuleInstances

variable {R : Type*} [CommRing R]

instance instAddZornSplitOctonion : Add (ZornSplitOctonion R) :=
  ⟨zornAdd⟩

instance instZeroZornSplitOctonion : Zero (ZornSplitOctonion R) :=
  ⟨zornZero⟩

instance instNegZornSplitOctonion : Neg (ZornSplitOctonion R) :=
  ⟨fun x => ⟨-x.a, -x.u, -x.v, -x.b⟩⟩

instance instSubZornSplitOctonion : Sub (ZornSplitOctonion R) :=
  ⟨zornSub⟩

instance instSMulZornSplitOctonion {S : Type*} [SMul S R] : SMul S (ZornSplitOctonion R) :=
  ⟨fun r x => ⟨r • x.a, fun k => r • x.u k, fun k => r • x.v k, r • x.b⟩⟩

@[simp] theorem ZornSplitOctonion.add_a (x y : ZornSplitOctonion R) :
    (x + y).a = x.a + y.a := rfl

@[simp] theorem ZornSplitOctonion.add_u (x y : ZornSplitOctonion R) (k : Fin 3) :
    (x + y).u k = x.u k + y.u k := rfl

@[simp] theorem ZornSplitOctonion.add_v (x y : ZornSplitOctonion R) (k : Fin 3) :
    (x + y).v k = x.v k + y.v k := rfl

@[simp] theorem ZornSplitOctonion.add_b (x y : ZornSplitOctonion R) :
    (x + y).b = x.b + y.b := rfl

@[simp] theorem ZornSplitOctonion.zero_a :
    (0 : ZornSplitOctonion R).a = 0 := rfl

@[simp] theorem ZornSplitOctonion.zero_u (k : Fin 3) :
    (0 : ZornSplitOctonion R).u k = 0 := rfl

@[simp] theorem ZornSplitOctonion.zero_v (k : Fin 3) :
    (0 : ZornSplitOctonion R).v k = 0 := rfl

@[simp] theorem ZornSplitOctonion.zero_b :
    (0 : ZornSplitOctonion R).b = 0 := rfl

@[simp] theorem ZornSplitOctonion.neg_a (x : ZornSplitOctonion R) :
    (-x).a = -x.a := rfl

@[simp] theorem ZornSplitOctonion.neg_u (x : ZornSplitOctonion R) (k : Fin 3) :
    (-x).u k = -x.u k := rfl

@[simp] theorem ZornSplitOctonion.neg_v (x : ZornSplitOctonion R) (k : Fin 3) :
    (-x).v k = -x.v k := rfl

@[simp] theorem ZornSplitOctonion.neg_b (x : ZornSplitOctonion R) :
    (-x).b = -x.b := rfl

@[simp] theorem ZornSplitOctonion.sub_a (x y : ZornSplitOctonion R) :
    (x - y).a = x.a - y.a := rfl

@[simp] theorem ZornSplitOctonion.sub_u (x y : ZornSplitOctonion R) (k : Fin 3) :
    (x - y).u k = x.u k - y.u k := rfl

@[simp] theorem ZornSplitOctonion.sub_v (x y : ZornSplitOctonion R) (k : Fin 3) :
    (x - y).v k = x.v k - y.v k := rfl

@[simp] theorem ZornSplitOctonion.sub_b (x y : ZornSplitOctonion R) :
    (x - y).b = x.b - y.b := rfl

omit [CommRing R] in
@[simp] theorem ZornSplitOctonion.smul_a {S : Type*} [SMul S R] (r : S) (x : ZornSplitOctonion R) :
    (r • x).a = r • x.a := rfl

omit [CommRing R] in
@[simp] theorem ZornSplitOctonion.smul_u {S : Type*} [SMul S R] (r : S) (x : ZornSplitOctonion R)
    (k : Fin 3) : (r • x).u k = r • x.u k := rfl

omit [CommRing R] in
@[simp] theorem ZornSplitOctonion.smul_v {S : Type*} [SMul S R] (r : S) (x : ZornSplitOctonion R)
    (k : Fin 3) : (r • x).v k = r • x.v k := rfl

omit [CommRing R] in
@[simp] theorem ZornSplitOctonion.smul_b {S : Type*} [SMul S R] (r : S) (x : ZornSplitOctonion R) :
    (r • x).b = r • x.b := rfl

instance instAddCommGroupZornSplitOctonion : AddCommGroup (ZornSplitOctonion R) where
  add := (· + ·)
  add_assoc a b c := by ext k <;> exact add_assoc _ _ _
  zero := 0
  zero_add a := by ext k <;> exact zero_add _
  add_zero a := by ext k <;> exact add_zero _
  nsmul n z := n • z
  nsmul_zero z := by ext k <;> exact zero_smul ℕ _
  nsmul_succ n z := by ext k <;> exact succ_nsmul _ n
  neg := Neg.neg
  sub := Sub.sub
  sub_eq_add_neg a b := by ext k <;> exact sub_eq_add_neg _ _
  zsmul n z := n • z
  zsmul_zero' z := by ext k <;> exact zero_smul ℤ _
  zsmul_succ' n z := by ext k <;> exact SubNegMonoid.zsmul_succ' n _
  zsmul_neg' n z := by ext k <;> exact SubNegMonoid.zsmul_neg' n _
  neg_add_cancel a := by ext k <;> exact neg_add_cancel _
  add_comm a b := by ext k <;> exact add_comm _ _

instance instModuleZornSplitOctonion : Module R (ZornSplitOctonion R) where
  smul := (· • ·)
  one_smul z := by ext k <;> exact one_smul R _
  mul_smul r s z := by ext k <;> exact mul_smul r s _
  smul_zero r := by ext k <;> exact smul_zero r
  smul_add r z₁ z₂ := by ext k <;> exact smul_add r _ _
  add_smul r s z := by ext k <;> exact add_smul r s _
  zero_smul z := by ext k <;> exact zero_smul R _

end ZornModuleInstances

/-- `spinor16ToSplitSedenion` is homogeneous with respect to scalar multiplication. -/
theorem spinor16ToSplitSedenion_smul (c : ℝ) (v : Fin 16 → ℝ) :
    spinor16ToSplitSedenion (c • v) = c • spinor16ToSplitSedenion v := by
  apply Prod.ext
  · exact fin8ToZorn_smul c (fun k => v (evenStateIndex k))
  · exact fin8ToZorn_smul c (fun k => v (oddStateIndex k))

/-- Genuine `ℝ`-linear equivalence `(Fin 16 → ℝ) ≃ₗ[ℝ] SplitSedenion ℝ` promoting
`spinor16SplitSedenionEquiv`. -/
def spinor16SplitSedenionLinearEquiv : (Fin 16 → ℝ) ≃ₗ[ℝ] SplitSedenion ℝ where
  toEquiv := spinor16SplitSedenionEquiv
  map_add' u v := spinor16ToSplitSedenion_add u v
  map_smul' c v := spinor16ToSplitSedenion_smul c v

/-- Genuine `ℝ`-linear equivalence `LeftIdeal primIdem ≃ₗ[ℝ] SplitSedenion ℝ` promoting
`cl44MatrixLeftIdealSplitSedenionEquiv`. -/
def cl44MatrixLeftIdealSplitSedenionLinearEquiv :
    LeftIdeal primIdem ≃ₗ[ℝ] SplitSedenion ℝ :=
  leftIdealEquiv.trans spinor16SplitSedenionLinearEquiv

@[simp] theorem cl44MatrixLeftIdealSplitSedenionLinearEquiv_apply (A : LeftIdeal primIdem) :
    cl44MatrixLeftIdealSplitSedenionLinearEquiv A =
      cl44MatrixLeftIdealSplitSedenionEquiv A :=
  rfl

@[simp] theorem cl44MatrixLeftIdealSplitSedenionLinearEquiv_symm_apply (X : SplitSedenion ℝ) :
    cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm X =
      cl44MatrixLeftIdealSplitSedenionEquiv.symm X :=
  rfl

/-!
## Section 2: Proved $\mathbb{R}$-Bilinearity of `sedenionMul` and `idealSedenionMul`
-/

/-- The transported conjugation `idealSedenionConj` is involutive. -/
@[simp] theorem idealSedenionConj_involutive (A : LeftIdeal primIdem) :
    idealSedenionConj (idealSedenionConj A) = A := by
  apply cl44MatrixLeftIdealSplitSedenionEquiv.injective
  simp [idealSedenionConj, sedenionConj, zornConj, zornSmul]

/-- The existing non-zero split-sedenion zero-divisor pair transfers to `idealSedenionMul`
on `LeftIdeal primIdem`. -/
theorem exists_idealSedenion_zero_divisors :
    ∃ A B : LeftIdeal primIdem,
      A ≠ 0 ∧ B ≠ 0 ∧ idealSedenionMul A B = 0 := by
  obtain ⟨hXY, hX, hY, _hNull⟩ := splitSedenion_explicit_zero_divisors_and_null_norm
  let X : SplitSedenion ℝ := (zornE0, zornZero)
  let Y : SplitSedenion ℝ := (zornE1, zornZero)
  refine ⟨cl44MatrixLeftIdealSplitSedenionEquiv.symm X,
    cl44MatrixLeftIdealSplitSedenionEquiv.symm Y, ?_, ?_, ?_⟩
  · intro h
    apply hX
    have hm := congrArg cl44MatrixLeftIdealSplitSedenionLinearEquiv h
    rw [cl44MatrixLeftIdealSplitSedenionLinearEquiv.map_zero,
        cl44MatrixLeftIdealSplitSedenionLinearEquiv_apply,
        cl44MatrixLeftIdealSplitSedenionEquiv.apply_symm_apply] at hm
    exact hm
  · intro h
    apply hY
    have hm := congrArg cl44MatrixLeftIdealSplitSedenionLinearEquiv h
    rw [cl44MatrixLeftIdealSplitSedenionLinearEquiv.map_zero,
        cl44MatrixLeftIdealSplitSedenionLinearEquiv_apply,
        cl44MatrixLeftIdealSplitSedenionEquiv.apply_symm_apply] at hm
    exact hm
  · apply cl44MatrixLeftIdealSplitSedenionLinearEquiv.injective
    rw [cl44MatrixLeftIdealSplitSedenionLinearEquiv.map_zero,
        cl44MatrixLeftIdealSplitSedenionLinearEquiv_apply]
    unfold idealSedenionMul
    rw [cl44MatrixLeftIdealSplitSedenionEquiv.apply_symm_apply,
        cl44MatrixLeftIdealSplitSedenionEquiv.apply_symm_apply,
        cl44MatrixLeftIdealSplitSedenionEquiv.apply_symm_apply]
    exact hXY

/-- The split-sedenion non-associativity witness transfers to `idealSedenionMul` on
`LeftIdeal primIdem`. -/
theorem exists_idealSedenion_nonzero_associator :
    ∃ A B C : LeftIdeal primIdem,
      idealSedenionMul (idealSedenionMul A B) C ≠
        idealSedenionMul A (idealSedenionMul B C) := by
  obtain ⟨_hAssocCl, hPair⟩ := cl44_associative_vs_splitSedenion_nonAssociative
  obtain ⟨X, Y, Z, hXYZ⟩ := hPair
  refine ⟨cl44MatrixLeftIdealSplitSedenionEquiv.symm X,
    cl44MatrixLeftIdealSplitSedenionEquiv.symm Y,
    cl44MatrixLeftIdealSplitSedenionEquiv.symm Z, ?_⟩
  intro h
  have hm := congrArg cl44MatrixLeftIdealSplitSedenionEquiv h
  apply hXYZ
  simpa [idealSedenionMul] using hm

private theorem zornConj_add (x y : ZornSplitOctonion ℝ) :
    zornConj (zornAdd x y) = zornAdd (zornConj x) (zornConj y) := by
  ext k <;> simp [zornConj, zornAdd] <;> abel_nf

private theorem zornConj_smul (c : ℝ) (x : ZornSplitOctonion ℝ) :
    zornConj (zornSmul c x) = zornSmul c (zornConj x) := by
  ext k <;> simp [zornConj, zornSmul] <;> ring_nf

/-- Left additivity of the split-sedenion pair product `sedenionMul`. -/
theorem sedenionMul_add_left (X₁ X₂ Y : SplitSedenion ℝ) :
    sedenionMul (X₁ + X₂) Y = sedenionMul X₁ Y + sedenionMul X₂ Y := by
  rcases X₁ with ⟨a₁, b₁⟩
  rcases X₂ with ⟨a₂, b₂⟩
  rcases Y with ⟨c, d⟩
  change (zornAdd (zornMul (zornAdd a₁ a₂) c)
      (zornMul (zornConj d) (zornAdd b₁ b₂)),
    zornAdd (zornMul d (zornAdd a₁ a₂))
      (zornMul (zornAdd b₁ b₂) (zornConj c))) = _
  rw [zornMul_add_left, zornMul_add_right, zornMul_add_right, zornMul_add_left]
  apply Prod.ext <;> ext k <;> simp [sedenionMul, zornAdd] <;> abel_nf

/-- Right additivity of the split-sedenion pair product `sedenionMul`. -/
theorem sedenionMul_add_right (X Y₁ Y₂ : SplitSedenion ℝ) :
    sedenionMul X (Y₁ + Y₂) = sedenionMul X Y₁ + sedenionMul X Y₂ := by
  rcases X with ⟨a, b⟩
  rcases Y₁ with ⟨c₁, d₁⟩
  rcases Y₂ with ⟨c₂, d₂⟩
  change (zornAdd (zornMul a (zornAdd c₁ c₂))
      (zornMul (zornConj (zornAdd d₁ d₂)) b),
    zornAdd (zornMul (zornAdd d₁ d₂) a)
      (zornMul b (zornConj (zornAdd c₁ c₂)))) = _
  rw [zornMul_add_right, zornConj_add, zornMul_add_left,
      zornMul_add_left, zornConj_add, zornMul_add_right]
  apply Prod.ext <;> ext k <;> simp [sedenionMul, zornAdd] <;> abel_nf

/-- Left $\mathbb{R}$-homogeneity of the split-sedenion pair product `sedenionMul`. -/
theorem sedenionMul_smul_left (c : ℝ) (X Y : SplitSedenion ℝ) :
    sedenionMul (c • X) Y = c • sedenionMul X Y := by
  change (zornAdd (zornMul (zornSmul c X.1) Y.1)
      (zornMul (zornConj Y.2) (zornSmul c X.2)),
    zornAdd (zornMul Y.2 (zornSmul c X.1))
      (zornMul (zornSmul c X.2) (zornConj Y.1))) =
    (zornSmul c (zornAdd (zornMul X.1 Y.1) (zornMul (zornConj Y.2) X.2)),
      zornSmul c (zornAdd (zornMul Y.2 X.1) (zornMul X.2 (zornConj Y.1))))
  rw [zornMul_smul_left, zornMul_smul_right, zornMul_smul_left, zornMul_smul_right]
  apply Prod.ext <;> ext k <;> simp [zornAdd, zornSmul] <;> ring_nf

/-- Right $\mathbb{R}$-homogeneity of the split-sedenion pair product `sedenionMul`. -/
theorem sedenionMul_smul_right (c : ℝ) (X Y : SplitSedenion ℝ) :
    sedenionMul X (c • Y) = c • sedenionMul X Y := by
  change (zornAdd (zornMul X.1 (zornSmul c Y.1))
      (zornMul (zornConj (zornSmul c Y.2)) X.2),
    zornAdd (zornMul (zornSmul c Y.2) X.1)
      (zornMul X.2 (zornConj (zornSmul c Y.1)))) =
    (zornSmul c (zornAdd (zornMul X.1 Y.1) (zornMul (zornConj Y.2) X.2)),
      zornSmul c (zornAdd (zornMul Y.2 X.1) (zornMul X.2 (zornConj Y.1))))
  simp only [zornMul_smul_left, zornMul_smul_right, zornConj_smul]
  apply Prod.ext <;> ext k <;> simp [zornAdd, zornSmul] <;> ring_nf

/-- Left additivity of the transported product `idealSedenionMul` on `LeftIdeal primIdem`. -/
theorem idealSedenionMul_add_left (A₁ A₂ B : LeftIdeal primIdem) :
    idealSedenionMul (A₁ + A₂) B =
      idealSedenionMul A₁ B + idealSedenionMul A₂ B := by
  change cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionMul (cl44MatrixLeftIdealSplitSedenionLinearEquiv (A₁ + A₂))
        (cl44MatrixLeftIdealSplitSedenionLinearEquiv B)) =
    cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionMul (cl44MatrixLeftIdealSplitSedenionLinearEquiv A₁)
        (cl44MatrixLeftIdealSplitSedenionLinearEquiv B)) +
    cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionMul (cl44MatrixLeftIdealSplitSedenionLinearEquiv A₂)
        (cl44MatrixLeftIdealSplitSedenionLinearEquiv B))
  rw [cl44MatrixLeftIdealSplitSedenionLinearEquiv.map_add,
      sedenionMul_add_left,
      cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm.map_add]

/-- Right additivity of the transported product `idealSedenionMul` on `LeftIdeal primIdem`. -/
theorem idealSedenionMul_add_right (A B₁ B₂ : LeftIdeal primIdem) :
    idealSedenionMul A (B₁ + B₂) =
      idealSedenionMul A B₁ + idealSedenionMul A B₂ := by
  change cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionMul (cl44MatrixLeftIdealSplitSedenionLinearEquiv A)
        (cl44MatrixLeftIdealSplitSedenionLinearEquiv (B₁ + B₂))) =
    cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionMul (cl44MatrixLeftIdealSplitSedenionLinearEquiv A)
        (cl44MatrixLeftIdealSplitSedenionLinearEquiv B₁)) +
    cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionMul (cl44MatrixLeftIdealSplitSedenionLinearEquiv A)
        (cl44MatrixLeftIdealSplitSedenionLinearEquiv B₂))
  rw [cl44MatrixLeftIdealSplitSedenionLinearEquiv.map_add,
      sedenionMul_add_right,
      cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm.map_add]

/-- Left $\mathbb{R}$-homogeneity of the transported product `idealSedenionMul` on `LeftIdeal primIdem`. -/
theorem idealSedenionMul_smul_left (c : ℝ) (A B : LeftIdeal primIdem) :
    idealSedenionMul (c • A) B = c • idealSedenionMul A B := by
  change cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionMul (cl44MatrixLeftIdealSplitSedenionLinearEquiv (c • A))
        (cl44MatrixLeftIdealSplitSedenionLinearEquiv B)) =
    c • cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionMul (cl44MatrixLeftIdealSplitSedenionLinearEquiv A)
        (cl44MatrixLeftIdealSplitSedenionLinearEquiv B))
  rw [cl44MatrixLeftIdealSplitSedenionLinearEquiv.map_smul,
      sedenionMul_smul_left,
      cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm.map_smul]

/-- Right $\mathbb{R}$-homogeneity of the transported product `idealSedenionMul` on `LeftIdeal primIdem`. -/
theorem idealSedenionMul_smul_right (c : ℝ) (A B : LeftIdeal primIdem) :
    idealSedenionMul A (c • B) = c • idealSedenionMul A B := by
  change cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionMul (cl44MatrixLeftIdealSplitSedenionLinearEquiv A)
        (cl44MatrixLeftIdealSplitSedenionLinearEquiv (c • B))) =
    c • cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionMul (cl44MatrixLeftIdealSplitSedenionLinearEquiv A)
        (cl44MatrixLeftIdealSplitSedenionLinearEquiv B))
  rw [cl44MatrixLeftIdealSplitSedenionLinearEquiv.map_smul,
      sedenionMul_smul_right,
      cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm.map_smul]

/-!
## Section 3: Quadratic Conjugate-Norm Identity & Transported 14-Parameter $G_2$ Star-Derivations on `LeftIdeal primIdem`
-/

/-- **Split-Sedenion Quadratic Conjugate-Norm Identity**:
For every `X : SplitSedenion ℝ`, multiplying `X` by its Cayley–Dickson conjugate `sedenionConj X`
yields `(zornSmul (sedenionNorm X) zornOne, zornZero)`. -/
theorem sedenionMul_sedenionConj (X : SplitSedenion ℝ) :
    sedenionMul X (sedenionConj X) = (zornSmul (sedenionNorm X) zornOne, zornZero) := by
  apply Prod.ext
  · ext k
    · dsimp [sedenionMul, sedenionConj, sedenionNorm, zornAdd, zornMul, zornConj,
        zornNorm, zornSmul, zornOne, vec3Dot, vec3Cross]
      ring
    · fin_cases k <;>
        (dsimp [sedenionMul, sedenionConj, sedenionNorm, zornAdd, zornMul, zornConj,
          zornNorm, zornSmul, zornOne, vec3Dot, vec3Cross]; ring)
    · fin_cases k <;>
        (dsimp [sedenionMul, sedenionConj, sedenionNorm, zornAdd, zornMul, zornConj,
          zornNorm, zornSmul, zornOne, vec3Dot, vec3Cross]; ring)
    · dsimp [sedenionMul, sedenionConj, sedenionNorm, zornAdd, zornMul, zornConj,
        zornNorm, zornSmul, zornOne, vec3Dot, vec3Cross]
      ring
  · ext k
    · dsimp [sedenionMul, sedenionConj, zornAdd, zornMul, zornConj,
        zornSmul, zornZero, vec3Dot, vec3Cross]
      ring
    · fin_cases k <;>
        (dsimp [sedenionMul, sedenionConj, zornAdd, zornMul, zornConj,
          zornSmul, zornZero, vec3Dot, vec3Cross]; ring)
    · fin_cases k <;>
        (dsimp [sedenionMul, sedenionConj, zornAdd, zornMul, zornConj,
          zornSmul, zornZero, vec3Dot, vec3Cross]; ring)
    · dsimp [sedenionMul, sedenionConj, zornAdd, zornMul, zornConj,
        zornSmul, zornZero, vec3Dot, vec3Cross]
      ring

/-- The split-sedenion quadratic expression `sedenionNorm X` vanishes if and only if
`sedenionMul X (sedenionConj X) = sedenionZero`. -/
theorem sedenionNorm_eq_zero_iff_sedenionMul_sedenionConj_eq_zero (X : SplitSedenion ℝ) :
    sedenionNorm X = 0 ↔ sedenionMul X (sedenionConj X) = sedenionZero := by
  rw [sedenionMul_sedenionConj]
  constructor
  · intro h
    rw [h]
    apply Prod.ext
    · exact zornSmul_zero_zornOne
    · rfl
  · intro h
    have ha : (zornSmul (sedenionNorm X) (zornOne : ZornSplitOctonion ℝ)).a =
        (zornZero : ZornSplitOctonion ℝ).a :=
      congrArg (fun Y : SplitSedenion ℝ => Y.1.a) h
    dsimp [zornSmul, zornOne, zornZero] at ha
    linarith

/-- Associator of the transported product `idealSedenionMul` on `LeftIdeal primIdem`. -/
def idealSedenionAssociator (A B C : LeftIdeal primIdem) : LeftIdeal primIdem :=
  idealSedenionMul (idealSedenionMul A B) C - idealSedenionMul A (idealSedenionMul B C)

/-- Transported split-sedenion multiplicative unit in `LeftIdeal primIdem`. -/
def idealSedenionOne : LeftIdeal primIdem :=
  cl44MatrixLeftIdealSplitSedenionEquiv.symm sedenionOne

/-- Transported Cayley–Dickson doubling generator $\ell = (0, 1)$ in `LeftIdeal primIdem`. -/
def idealSedenionEll : LeftIdeal primIdem :=
  cl44MatrixLeftIdealSplitSedenionEquiv.symm sedenionEll

/-- The transported doubling unit `idealSedenionEll` squares to `idealSedenionOne` under
`idealSedenionMul`. -/
@[simp] theorem idealSedenionEll_sq_eq_one :
    idealSedenionMul idealSedenionEll idealSedenionEll = idealSedenionOne := by
  unfold idealSedenionMul idealSedenionEll idealSedenionOne
  rw [cl44MatrixLeftIdealSplitSedenionEquiv.apply_symm_apply,
      (splitSedenion_chiral_sheet_shift_laws (zornZero : ZornSplitOctonion ℝ) zornZero).2.2]

/-- On `LeftIdeal primIdem`, `idealSedenionNorm A = 0` if and only if
`idealSedenionMul A (idealSedenionConj A) = 0`. -/
theorem idealSedenion_norm_zero_iff_mul_conj_zero (A : LeftIdeal primIdem) :
    idealSedenionNorm A = 0 ↔
      idealSedenionMul A (idealSedenionConj A) = 0 := by
  unfold idealSedenionNorm idealSedenionMul idealSedenionConj
  rw [cl44MatrixLeftIdealSplitSedenionEquiv.apply_symm_apply,
      ← cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm.map_zero]
  change sedenionNorm (cl44MatrixLeftIdealSplitSedenionEquiv A) = 0 ↔
    cl44MatrixLeftIdealSplitSedenionEquiv.symm
      (sedenionMul (cl44MatrixLeftIdealSplitSedenionEquiv A)
        (sedenionConj (cl44MatrixLeftIdealSplitSedenionEquiv A))) =
    cl44MatrixLeftIdealSplitSedenionEquiv.symm sedenionZero
  rw [cl44MatrixLeftIdealSplitSedenionEquiv.symm.injective.eq_iff]
  exact sedenionNorm_eq_zero_iff_sedenionMul_sedenionConj_eq_zero
    (cl44MatrixLeftIdealSplitSedenionEquiv A)

/-- The 14-parameter $G_2$ derivation family transported to `LeftIdeal primIdem` across
`cl44MatrixLeftIdealSplitSedenionEquiv`. -/
def idealG2Derivation (p : Params) (A : LeftIdeal primIdem) : LeftIdeal primIdem :=
  cl44MatrixLeftIdealSplitSedenionEquiv.symm
    (sedenionG2Derivation p (cl44MatrixLeftIdealSplitSedenionEquiv A))

/-- The fixed-parameter split-sedenion `G₂` derivation, viewed as a real-linear
endomorphism of the standard module on `SplitSedenion ℝ`. -/
def sedenionG2DerivationLinear (p : Params) :
    SplitSedenion ℝ →ₗ[ℝ] SplitSedenion ℝ where
  toFun := sedenionG2Derivation p
  map_add' X Y := by
    change sedenionG2Derivation p (sedenionAdd X Y) =
      sedenionAdd (sedenionG2Derivation p X) (sedenionG2Derivation p Y)
    exact sedenionG2Derivation_add p X Y
  map_smul' r X := by
    have hz (x : ZornSplitOctonion ℝ) : zornSmul r x = r • x := by
      ext <;> simp [zornSmul]
    rcases X with ⟨x, y⟩
    change (zornG2Derivation p (r • x), zornG2Derivation p (r • y)) =
      (r • zornG2Derivation p x, r • zornG2Derivation p y)
    apply Prod.ext
    · calc
        zornG2Derivation p (r • x) = zornG2Derivation p (zornSmul r x) := by rw [hz]
        _ = zornSmul r (zornG2Derivation p x) := zornG2Derivation_smul p r x
        _ = r • zornG2Derivation p x := hz _
    · calc
        zornG2Derivation p (r • y) = zornG2Derivation p (zornSmul r y) := by rw [hz]
        _ = zornSmul r (zornG2Derivation p y) := zornG2Derivation_smul p r y
        _ = r • zornG2Derivation p y := hz _

/-- `idealG2Derivation p` satisfies the Leibniz derivation law for `idealSedenionMul` and
submodule addition `+` on `LeftIdeal primIdem`. -/
theorem idealG2Derivation_leibniz (p : Params) (A B : LeftIdeal primIdem) :
    idealG2Derivation p (idealSedenionMul A B) =
      idealSedenionMul (idealG2Derivation p A) B +
        idealSedenionMul A (idealG2Derivation p B) := by
  change cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionG2Derivation p
        (cl44MatrixLeftIdealSplitSedenionEquiv (idealSedenionMul A B))) =
    cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionMul
        (cl44MatrixLeftIdealSplitSedenionEquiv (idealG2Derivation p A))
        (cl44MatrixLeftIdealSplitSedenionEquiv B)) +
    cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm
      (sedenionMul
        (cl44MatrixLeftIdealSplitSedenionEquiv A)
        (cl44MatrixLeftIdealSplitSedenionEquiv (idealG2Derivation p B)))
  rw [← cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm.map_add]
  unfold idealG2Derivation idealSedenionMul
  simp only [cl44MatrixLeftIdealSplitSedenionLinearEquiv_symm_apply,
    Equiv.apply_symm_apply, sedenionG2Derivation_leibniz]
  rfl

/-- `idealG2Derivation p` commutes with the transported involution `idealSedenionConj`. -/
@[simp] theorem idealG2Derivation_conj (p : Params) (A : LeftIdeal primIdem) :
    idealG2Derivation p (idealSedenionConj A) =
      idealSedenionConj (idealG2Derivation p A) := by
  unfold idealG2Derivation idealSedenionConj
  simp only [Equiv.apply_symm_apply, sedenionG2Derivation_conj]

/-- `idealG2Derivation p` annihilates the transported doubling generator `idealSedenionEll`. -/
@[simp] theorem idealG2Derivation_ell_zero (p : Params) :
    idealG2Derivation p idealSedenionEll = 0 := by
  unfold idealG2Derivation idealSedenionEll
  rw [cl44MatrixLeftIdealSplitSedenionEquiv.apply_symm_apply,
      sedenionG2Derivation_sedenionEll_zero]
  exact cl44MatrixLeftIdealSplitSedenionLinearEquiv.symm.map_zero

/-- Canonical 14-coordinate parameter readout from a self-map `G : LeftIdeal primIdem → LeftIdeal primIdem`. -/
def readIdealG2Params (G : LeftIdeal primIdem → LeftIdeal primIdem) : Params :=
  readSedenionG2Params (fun X =>
    cl44MatrixLeftIdealSplitSedenionEquiv
      (G (cl44MatrixLeftIdealSplitSedenionEquiv.symm X)))

/-- Reading the 14 canonical coordinates from `idealG2Derivation p` recovers `p` identically. -/
@[simp] theorem readIdealG2Params_idealG2Derivation (p : Params) :
    readIdealG2Params (idealG2Derivation p) = p := by
  unfold readIdealG2Params idealG2Derivation
  have hfun :
      (fun X : SplitSedenion ℝ =>
        cl44MatrixLeftIdealSplitSedenionEquiv
          (cl44MatrixLeftIdealSplitSedenionEquiv.symm
            (sedenionG2Derivation p
              (cl44MatrixLeftIdealSplitSedenionEquiv
                (cl44MatrixLeftIdealSplitSedenionEquiv.symm X))))) =
      sedenionG2Derivation p := by
    funext X
    simp only [Equiv.apply_symm_apply]
  rw [hfun]
  exact readSedenionG2Params_sedenionG2Derivation p

/-- The transported 14-parameter $G_2$ derivation family `idealG2Derivation` on `LeftIdeal primIdem`
is injective. -/
theorem idealG2Derivation_injective :
    Function.Injective idealG2Derivation := by
  intro p q hpq
  have h := congrArg readIdealG2Params hpq
  rw [readIdealG2Params_idealG2Derivation p,
      readIdealG2Params_idealG2Derivation q] at h
  exact h

/-!
## Section 4: Transported Split-Sedenion Operations on the 16-Component Spinor Carrier `Fin 16 → ℝ`
-/

/-- Transported split-sedenion multiplication on `Fin 16 → ℝ` induced by `spinor16SplitSedenionEquiv`. -/
def idealMul (ψ₁ ψ₂ : Fin 16 → ℝ) : Fin 16 → ℝ :=
  spinor16SplitSedenionEquiv.symm
    (sedenionMul (spinor16SplitSedenionEquiv ψ₁) (spinor16SplitSedenionEquiv ψ₂))

/-- Transported Cayley–Dickson involution on `Fin 16 → ℝ` induced by `spinor16SplitSedenionEquiv`. -/
def idealConj (ψ : Fin 16 → ℝ) : Fin 16 → ℝ :=
  spinor16SplitSedenionEquiv.symm (sedenionConj (spinor16SplitSedenionEquiv ψ))

/-- Transported split-sedenion quadratic expression on `Fin 16 → ℝ`. -/
def idealNorm (ψ : Fin 16 → ℝ) : ℝ :=
  sedenionNorm (spinor16SplitSedenionEquiv ψ)

/-- Associator of the transported product `idealMul` on `Fin 16 → ℝ`. -/
def idealAssociator (ψ₁ ψ₂ ψ₃ : Fin 16 → ℝ) : Fin 16 → ℝ :=
  idealMul (idealMul ψ₁ ψ₂) ψ₃ - idealMul ψ₁ (idealMul ψ₂ ψ₃)

/-- `spinor16SplitSedenionEquiv.symm` maps `sedenionZero` to the zero vector `0 : Fin 16 → ℝ`. -/
@[simp] theorem spinor16SplitSedenionEquiv_symm_sedenionZero :
    spinor16SplitSedenionEquiv.symm sedenionZero = (0 : Fin 16 → ℝ) :=
  spinor16SplitSedenionLinearEquiv.symm.map_zero

/-- `spinor16SplitSedenionEquiv.symm X = 0` if and only if `X = sedenionZero`. -/
theorem spinor16SplitSedenionEquiv_symm_eq_zero_iff (X : SplitSedenion ℝ) :
    spinor16SplitSedenionEquiv.symm X = 0 ↔ X = sedenionZero := by
  rw [← spinor16SplitSedenionEquiv_symm_sedenionZero]
  exact spinor16SplitSedenionEquiv.symm.injective.eq_iff

/-- The transported product `idealMul` on `Fin 16 → ℝ` has a non-vanishing associator. -/
theorem ideal_product_is_non_associative :
    ∃ ψ₁ ψ₂ ψ₃ : Fin 16 → ℝ, idealAssociator ψ₁ ψ₂ ψ₃ ≠ 0 := by
  rcases cl44_associative_vs_splitSedenion_nonAssociative.2 with ⟨X, Y, Z, hne⟩
  refine ⟨spinor16SplitSedenionEquiv.symm X,
    spinor16SplitSedenionEquiv.symm Y,
    spinor16SplitSedenionEquiv.symm Z, ?_⟩
  unfold idealAssociator
  rw [sub_ne_zero]
  intro heq
  apply hne
  have h1 := congrArg spinor16SplitSedenionEquiv heq
  unfold idealMul at h1
  simp only [Equiv.apply_symm_apply] at h1
  exact h1

/-- On `Fin 16 → ℝ`, `idealNorm ψ = 0` if and only if `idealMul ψ (idealConj ψ) = 0`. -/
theorem ideal_norm_zero_iff_mul_conj_zero (ψ : Fin 16 → ℝ) :
    idealNorm ψ = 0 ↔ idealMul ψ (idealConj ψ) = 0 := by
  unfold idealNorm idealMul idealConj
  rw [spinor16SplitSedenionEquiv.apply_symm_apply,
      spinor16SplitSedenionEquiv_symm_eq_zero_iff]
  exact sedenionNorm_eq_zero_iff_sedenionMul_sedenionConj_eq_zero
    (spinor16SplitSedenionEquiv ψ)

end InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridge
