/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.Semisimple.Basic
import InfoGeometry.Algebra.CompactOctonionG2Derivations
import InfoGeometry.Algebra.H3OctonionLieAlgebra
import InfoGeometry.Algebra.H3OctonionTKKLieAlgebra
import InfoGeometry.Algebra.H3OctonionSimplicity
import InfoGeometry.Algebra.MagicSquareTitsBracket
import InfoGeometry.Algebra.SplitE8Simplicity
import InfoGeometry.Exceptional.GenericGradedJacobiClosure

/-!
# Compact `𝔈₈(-248)` and Quaternionic `𝔈₈(-24)` via the Tits Magic Square

This module formalizes the real exceptional Lie algebras of type `E₈` via the factored
Freudenthal–Tits Magic Square `(1/3, -2, 1)` and `(3, -6, 1)` `ad`-invariant bilinear form:

1. **Generic Factored Magic Square Engine (`MagicSquareLie O J`)**:
   Constructs `LieRing`, `LieAlgebra ℝ`, 27-cell `GlobalLeibniz` via
   `GenericGradedJacobiClosure.global_leibniz_of_homogeneous`, and the `(3, -6, 1)`
   `ad`-invariant bilinear form `magicInvBilin` once for arbitrary `(O : OctonionMagicDatum)`
   and `(J : JordanMagicDatum)`.
2. **Concrete Carriers (`CompactE8Lie`, `QuaternionicE8Lie`, `SplitE8Lie` invariant form)**:
   - `CompactE8Lie` (`𝔈₈(-248)` from `CompactOctonion ℝ × H3Octonion ℝ`, `finrank = 248`)
   - `QuaternionicE8Lie` (`𝔈₈(-24)` from `CompactOctonion ℝ × H3Zorn ℝ`, `finrank = 248`)
   - `splitE8InvBilin` & `splitE8InvBilin_lieInvariant` on `SplitE8Lie` (`𝔈₈(+8)`).
3. **Simplicity via Complexification**:
   Proves `complexSplitE8Lie_isSimple : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] SplitE8Lie)`,
   constructs diamond-free complexification equivalences `compactE8BaseChangeEquiv` and
   `quaternionicE8BaseChangeEquiv`, and descends via `LieEquiv.isSimple` and
   `isSimple_of_isSimple_extendScalars` to `compactE8Lie_isSimple` and
   `quaternionicE8Lie_isSimple`.
4. **Cartan Involutions, `IsKilling ℝ`, & Signature Separation (`-248` vs `-24` vs `+8`)**:
   Defines `sigmaO` on `ZornVectorMatrix ℝ`, `sigmaJ` on `H3Zorn ℝ`, and the three Cartan
   involutions (`id`, `(id, σ_J)`, `(σ_O, σ_J)`), proving `IsKilling ℝ`, Killing form
   definiteness on `k` and `p`, exact signatures `-248`, `-24`, `+8`, and unconditional
   pairwise non-isomorphism `IsEmpty (L₁ ≃ₗ⁅ℝ⁆ L₂)` among all three real forms.
-/

noncomputable section

namespace InfoGeometry.Algebra

open scoped TensorProduct BigOperators
open InfoGeometry.Exceptional
open InfoGeometry.Canonical.NativeTitsE8Carrier

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-! ## 1. Generic Factored Tits `(1/3, -2, 1)` Magic Square & `(3, -6, 1)` Invariant Form -/

section GenericMagicSquare

/-- Decoupled 7-dimensional octonionic data and identities for the Tits Magic Square,
together with the `ad`-invariant trace pairing on `G₂`. -/
structure OctonionMagicDatum (O₀ G₂ : Type) [AddCommGroup O₀] [Module ℝ O₀]
    [LieRing G₂] [LieAlgebra ℝ G₂] where
  bilin₀ : O₀ →ₗ[ℝ] O₀ →ₗ[ℝ] ℝ
  comm₀ : O₀ →ₗ[ℝ] O₀ →ₗ[ℝ] O₀
  assoc₀ : O₀ → O₀ → O₀ → O₀
  act : G₂ →ₗ[ℝ] O₀ →ₗ[ℝ] O₀
  inner : O₀ →ₗ[ℝ] O₀ →ₗ[ℝ] G₂
  g2Bilin : G₂ →ₗ[ℝ] G₂ →ₗ[ℝ] ℝ
  bilin_symm : ∀ a b, bilin₀ a b = bilin₀ b a
  comm_skew : ∀ a b, comm₀ b a = -comm₀ a b
  bilin_deriv_skew : ∀ D a b, bilin₀ (act D a) b + bilin₀ a (act D b) = 0
  bilin_comm_cyclic : ∀ a b c, bilin₀ a (comm₀ b c) = bilin₀ b (comm₀ c a)
  g2_covariant : ∀ (D : G₂) (a b : O₀), ⁅D, inner a b⁆ = inner (act D a) b + inner a (act D b)
  inner_skew : ∀ a b, inner b a = -inner a b
  act_lie : ∀ (D E : G₂) (a : O₀), act ⁅D, E⁆ a = act D (act E a) - act E (act D a)
  act_comm : ∀ D a b, act D (comm₀ a b) = comm₀ (act D a) b + comm₀ a (act D b)
  inner_comm_cyclic_zero : ∀ a b c,
    inner a (comm₀ b c) + inner b (comm₀ c a) + inner c (comm₀ a b) = 0
  comm_double_identity : ∀ a b c,
    comm₀ b (comm₀ c a) - comm₀ c (comm₀ a b) + (6 : ℝ) • (bilin₀ b c • a) =
      (2 : ℝ) • (bilin₀ b c • a + bilin₀ c a • b + bilin₀ a b • c)
  comm_jacobi_eq_neg_six_assoc : ∀ a b c,
    comm₀ a (comm₀ b c) + comm₀ b (comm₀ c a) + comm₀ c (comm₀ a b) = (-6 : ℝ) • assoc₀ a b c
  assoc_cycle : ∀ a b c, assoc₀ b c a = assoc₀ a b c
  kleinfeld_combo : ∀ a b c,
    -assoc₀ a b c - (1 / 3 : ℝ) • comm₀ a (comm₀ b c) - (1 / 3 : ℝ) • act (inner b c) a = 0
  g2Bilin_symm : ∀ D₁ D₂, g2Bilin D₁ D₂ = g2Bilin D₂ D₁
  g2Bilin_lie_skew : ∀ (D₁ D₂ D₃ : G₂), g2Bilin ⁅D₁, D₂⁆ D₃ + g2Bilin D₂ ⁅D₁, D₃⁆ = 0
  g2Bilin_inner_eq : ∀ D a b, g2Bilin (inner a b) D = 6 * bilin₀ a (act D b)

/-- Decoupled 26-dimensional traceless Jordan data and identities for the Tits Magic Square,
together with the `ad`-invariant trace pairing on `F₄`. -/
structure JordanMagicDatum (J₀ F₄ : Type) [AddCommGroup J₀] [Module ℝ J₀]
    [LieRing F₄] [LieAlgebra ℝ F₄] where
  traceBilin₀ : J₀ →ₗ[ℝ] J₀ →ₗ[ℝ] ℝ
  mul₀ : J₀ →ₗ[ℝ] J₀ →ₗ[ℝ] J₀
  act : F₄ →ₗ[ℝ] J₀ →ₗ[ℝ] J₀
  inner : J₀ →ₗ[ℝ] J₀ →ₗ[ℝ] F₄
  f4Bilin : F₄ →ₗ[ℝ] F₄ →ₗ[ℝ] ℝ
  traceBilin_symm : ∀ x y, traceBilin₀ x y = traceBilin₀ y x
  mul_comm : ∀ x y, mul₀ x y = mul₀ y x
  traceBilin_deriv_skew : ∀ F x y, traceBilin₀ (act F x) y + traceBilin₀ x (act F y) = 0
  traceBilin_mul_cyclic : ∀ x y z, traceBilin₀ x (mul₀ y z) = traceBilin₀ y (mul₀ z x)
  f4_covariant : ∀ (F : F₄) (x y : J₀), ⁅F, inner x y⁆ = inner (act F x) y + inner x (act F y)
  inner_skew : ∀ x y, inner y x = -inner x y
  act_lie : ∀ (F G : F₄) (x : J₀), act ⁅F, G⁆ x = act F (act G x) - act G (act F x)
  act_mul : ∀ F x y, act F (mul₀ x y) = mul₀ (act F x) y + mul₀ x (act F y)
  inner_mul_cyclic_zero : ∀ x y z,
    inner x (mul₀ y z) + inner y (mul₀ z x) + inner z (mul₀ x y) = 0
  mul_assoc_decompose : ∀ x y z,
    mul₀ x (mul₀ y z) =
      (1 / 6 : ℝ) • (traceBilin₀ y z • x + traceBilin₀ z x • y + traceBilin₀ x y • z) +
      (1 / 3 : ℝ) • (act (inner x y) z - act (inner z x) y) -
      ((1 / 3 : ℝ) * traceBilin₀ y z) • x
  inner_self_cyclic_zero : ∀ x y z,
    act (inner y z) x + act (inner z x) y + act (inner x y) z = 0
  f4Bilin_symm : ∀ F₁ F₂, f4Bilin F₁ F₂ = f4Bilin F₂ F₁
  f4Bilin_lie_skew : ∀ (F₁ F₂ F₃ : F₄), f4Bilin ⁅F₁, F₂⁆ F₃ + f4Bilin F₂ ⁅F₁, F₃⁆ = 0
  f4Bilin_inner_eq : ∀ F x y, f4Bilin (inner x y) F = -3 * traceBilin₀ x (act F y)

/-- Factored Tits Magic Square Lie algebra carrier `G₂ ⊕ (O₀ ⊗ J₀) ⊕ F₄`. -/
@[ext]
structure MagicSquareLie {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) where
  g2 : G₂
  mixed : O₀ ⊗[ℝ] J₀
  f4 : F₄

section MagicSquareInstances

variable {O₀ G₂ J₀ F₄ : Type}
  [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
  [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
  {O : OctonionMagicDatum O₀ G₂} {J : JordanMagicDatum J₀ F₄}

instance : Zero (MagicSquareLie O J) := ⟨⟨0, 0, 0⟩⟩
instance : Add (MagicSquareLie O J) :=
  ⟨fun X Y => ⟨X.g2 + Y.g2, X.mixed + Y.mixed, X.f4 + Y.f4⟩⟩
instance : Neg (MagicSquareLie O J) := ⟨fun X => ⟨-X.g2, -X.mixed, -X.f4⟩⟩
instance : Sub (MagicSquareLie O J) :=
  ⟨fun X Y => ⟨X.g2 - Y.g2, X.mixed - Y.mixed, X.f4 - Y.f4⟩⟩
instance : SMul ℝ (MagicSquareLie O J) :=
  ⟨fun r X => ⟨r • X.g2, r • X.mixed, r • X.f4⟩⟩

@[simp] theorem MagicSquareLie.zero_g2 : (0 : MagicSquareLie O J).g2 = 0 := rfl
@[simp] theorem MagicSquareLie.zero_mixed : (0 : MagicSquareLie O J).mixed = 0 := rfl
@[simp] theorem MagicSquareLie.zero_f4 : (0 : MagicSquareLie O J).f4 = 0 := rfl
@[simp] theorem MagicSquareLie.add_g2 (X Y : MagicSquareLie O J) :
    (X + Y).g2 = X.g2 + Y.g2 := rfl
@[simp] theorem MagicSquareLie.add_mixed (X Y : MagicSquareLie O J) :
    (X + Y).mixed = X.mixed + Y.mixed := rfl
@[simp] theorem MagicSquareLie.add_f4 (X Y : MagicSquareLie O J) :
    (X + Y).f4 = X.f4 + Y.f4 := rfl
@[simp] theorem MagicSquareLie.neg_g2 (X : MagicSquareLie O J) : (-X).g2 = -X.g2 := rfl
@[simp] theorem MagicSquareLie.neg_mixed (X : MagicSquareLie O J) : (-X).mixed = -X.mixed := rfl
@[simp] theorem MagicSquareLie.neg_f4 (X : MagicSquareLie O J) : (-X).f4 = -X.f4 := rfl
@[simp] theorem MagicSquareLie.sub_g2 (X Y : MagicSquareLie O J) :
    (X - Y).g2 = X.g2 - Y.g2 := rfl
@[simp] theorem MagicSquareLie.sub_mixed (X Y : MagicSquareLie O J) :
    (X - Y).mixed = X.mixed - Y.mixed := rfl
@[simp] theorem MagicSquareLie.sub_f4 (X Y : MagicSquareLie O J) :
    (X - Y).f4 = X.f4 - Y.f4 := rfl
@[simp] theorem MagicSquareLie.smul_g2 (r : ℝ) (X : MagicSquareLie O J) :
    (r • X).g2 = r • X.g2 := rfl
@[simp] theorem MagicSquareLie.smul_mixed (r : ℝ) (X : MagicSquareLie O J) :
    (r • X).mixed = r • X.mixed := rfl
@[simp] theorem MagicSquareLie.smul_f4 (r : ℝ) (X : MagicSquareLie O J) :
    (r • X).f4 = r • X.f4 := rfl

instance : AddCommGroup (MagicSquareLie O J) where
  add_assoc _ _ _ := by ext <;> exact add_assoc _ _ _
  zero_add _ := by ext <;> exact zero_add _
  add_zero _ := by ext <;> exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel _ := by ext <;> exact neg_add_cancel _
  add_comm _ _ := by ext <;> exact add_comm _ _
  sub_eq_add_neg _ _ := by ext <;> exact sub_eq_add_neg _ _

instance : Module ℝ (MagicSquareLie O J) where
  one_smul _ := by ext <;> exact one_smul ℝ _
  mul_smul r s _ := by ext <;> exact mul_smul r s _
  smul_zero r := by ext <;> exact smul_zero r
  smul_add r _ _ := by ext <;> exact smul_add r _ _
  add_smul r s _ := by ext <;> exact add_smul r s _
  zero_smul _ := by ext <;> exact zero_smul ℝ _

/-- Linear equivalence `MagicSquareLie O J ≃ₗ[ℝ] G₂ × (O₀ ⊗[ℝ] J₀) × F₄`. -/
def magicSquareLinearEquiv (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    MagicSquareLie O J ≃ₗ[ℝ] (G₂ × (O₀ ⊗[ℝ] J₀) × F₄) where
  toFun X := (X.g2, X.mixed, X.f4)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Lift of `O.act` onto `O₀ ⊗[ℝ] J₀`. -/
def magicG2MixedActLM (O : OctonionMagicDatum O₀ G₂) {J₀ : Type}
    [AddCommGroup J₀] [Module ℝ J₀] :
    G₂ →ₗ[ℝ] (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] (O₀ ⊗[ℝ] J₀) where
  toFun D := TensorProduct.map (O.act D) LinearMap.id
  map_add' D₁ D₂ := by
    apply TensorProduct.ext'; intro a x
    simp [map_add, TensorProduct.add_tmul]
  map_smul' r D := by
    apply TensorProduct.ext'; intro a x
    simp [map_smul, TensorProduct.smul_tmul]

@[simp] theorem magicG2MixedActLM_tmul (O : OctonionMagicDatum O₀ G₂) {J₀ : Type}
    [AddCommGroup J₀] [Module ℝ J₀] (D : G₂) (a : O₀) (x : J₀) :
    magicG2MixedActLM O D (a ⊗ₜ[ℝ] x) = (O.act D a) ⊗ₜ[ℝ] x := rfl

/-- Lift of `J.act` onto `O₀ ⊗[ℝ] J₀`. -/
def magicF4MixedActLM {O₀ : Type} [AddCommGroup O₀] [Module ℝ O₀]
    (J : JordanMagicDatum J₀ F₄) :
    F₄ →ₗ[ℝ] (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] (O₀ ⊗[ℝ] J₀) where
  toFun F := TensorProduct.map LinearMap.id (J.act F)
  map_add' F₁ F₂ := by
    apply TensorProduct.ext'; intro a x
    simp [map_add, TensorProduct.tmul_add]
  map_smul' r F := by
    apply TensorProduct.ext'; intro a x
    simp [map_smul, TensorProduct.smul_tmul']

@[simp] theorem magicF4MixedActLM_tmul {O₀ : Type} [AddCommGroup O₀] [Module ℝ O₀]
    (J : JordanMagicDatum J₀ F₄) (F : F₄) (a : O₀) (x : J₀) :
    magicF4MixedActLM J F (a ⊗ₜ[ℝ] x) = a ⊗ₜ[ℝ] (J.act F x) := rfl

private def magicBilLift {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Φ : O₀ →ₗ[ℝ] J₀ →ₗ[ℝ] O₀ →ₗ[ℝ] J₀ →ₗ[ℝ] E) :
    (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] E :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun x => TensorProduct.lift (Φ a x)
          map_add' := fun _ _ => by apply TensorProduct.ext'; intro b y; simp
          map_smul' := fun _ _ => by apply TensorProduct.ext'; intro b y; simp }
      map_add' := fun _ _ => by
        apply LinearMap.ext; intro x; apply TensorProduct.ext'; intro b y; simp
      map_smul' := fun _ _ => by
        apply LinearMap.ext; intro x; apply TensorProduct.ext'; intro b y; simp }

@[simp] private theorem magicBilLift_tmul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Φ : O₀ →ₗ[ℝ] J₀ →ₗ[ℝ] O₀ →ₗ[ℝ] J₀ →ₗ[ℝ] E)
    (a b : O₀) (x y : J₀) :
    magicBilLift Φ (a ⊗ₜ[ℝ] x) (b ⊗ₜ[ℝ] y) = Φ a x b y := by
  simp [magicBilLift]

/-- Mixed-to-`G₂` Magic Square bracket component: `(1/3) * ⟨x, y⟩ • inner a b`. -/
def magicMixedToG2LM (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] G₂ :=
  magicBilLift
    { toFun := fun a =>
        { toFun := fun x =>
            { toFun := fun b =>
                { toFun := fun y => ((1 / 3 : ℝ) * J.traceBilin₀ x y) • O.inner a b
                  map_add' := fun y₁ y₂ => by simp [map_add, mul_add, add_smul]
                  map_smul' := fun r y => by simp [map_smul]; module }
              map_add' := fun b₁ b₂ => by
                apply LinearMap.ext; intro y
                simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, smul_add]
              map_smul' := fun r b => by
                apply LinearMap.ext; intro y
                simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
                  RingHom.id_apply]
                module }
          map_add' := fun x₁ x₂ => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, mul_add,
              add_smul]
          map_smul' := fun r x => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
              RingHom.id_apply, smul_eq_mul]
            module }
      map_add' := fun a₁ a₂ => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, smul_add]
      map_smul' := fun r a => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
          RingHom.id_apply]
        module }

@[simp] theorem magicMixedToG2LM_tmul (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (a b : O₀) (x y : J₀) :
    magicMixedToG2LM O J (a ⊗ₜ[ℝ] x) (b ⊗ₜ[ℝ] y) =
      ((1 / 3 : ℝ) * J.traceBilin₀ x y) • O.inner a b := by
  simp [magicMixedToG2LM]

/-- Mixed-to-`F₄` Magic Square bracket component: `(-2) * ⟨a, b⟩ • inner x y`. -/
def magicMixedToF4LM (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] F₄ :=
  magicBilLift
    { toFun := fun a =>
        { toFun := fun x =>
            { toFun := fun b =>
                { toFun := fun y => ((-2 : ℝ) * O.bilin₀ a b) • J.inner x y
                  map_add' := fun y₁ y₂ => by simp [map_add, smul_add]
                  map_smul' := fun r y => by simp [map_smul]; module }
              map_add' := fun b₁ b₂ => by
                apply LinearMap.ext; intro y
                simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, mul_add,
                  add_smul]
              map_smul' := fun r b => by
                apply LinearMap.ext; intro y
                simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
                  RingHom.id_apply, smul_eq_mul]
                module }
          map_add' := fun x₁ x₂ => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, smul_add]
          map_smul' := fun r x => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
              RingHom.id_apply]
            module }
      map_add' := fun a₁ a₂ => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, mul_add,
          add_smul]
      map_smul' := fun r a => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
          RingHom.id_apply, smul_eq_mul]
        module }

@[simp] theorem magicMixedToF4LM_tmul (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (a b : O₀) (x y : J₀) :
    magicMixedToF4LM O J (a ⊗ₜ[ℝ] x) (b ⊗ₜ[ℝ] y) =
      ((-2 : ℝ) * O.bilin₀ a b) • J.inner x y := by
  simp [magicMixedToF4LM]

/-- Mixed-to-Mixed Magic Square bracket component: `(comm₀ a b) ⊗ (mul₀ x y)`. -/
def magicMixedToMixedLM (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] (O₀ ⊗[ℝ] J₀) :=
  magicBilLift
    { toFun := fun a =>
        { toFun := fun x =>
            { toFun := fun b =>
                { toFun := fun y => (O.comm₀ a b) ⊗ₜ[ℝ] (J.mul₀ x y)
                  map_add' := fun y₁ y₂ => by simp [map_add, TensorProduct.tmul_add]
                  map_smul' := fun r y => by simp [map_smul, TensorProduct.tmul_smul] }
              map_add' := fun b₁ b₂ => by
                apply LinearMap.ext; intro y
                simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add,
                  TensorProduct.add_tmul]
              map_smul' := fun r b => by
                apply LinearMap.ext; intro y
                simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
                  TensorProduct.smul_tmul, TensorProduct.tmul_smul, RingHom.id_apply] }
          map_add' := fun x₁ x₂ => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add,
              TensorProduct.tmul_add]
          map_smul' := fun r x => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
              TensorProduct.tmul_smul, RingHom.id_apply] }
      map_add' := fun a₁ a₂ => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add,
          TensorProduct.add_tmul]
      map_smul' := fun r a => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
          TensorProduct.smul_tmul, TensorProduct.tmul_smul, RingHom.id_apply] }

@[simp] theorem magicMixedToMixedLM_tmul (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (a b : O₀) (x y : J₀) :
    magicMixedToMixedLM O J (a ⊗ₜ[ℝ] x) (b ⊗ₜ[ℝ] y) =
      (O.comm₀ a b) ⊗ₜ[ℝ] (J.mul₀ x y) := by
  simp [magicMixedToMixedLM]

/-- Full bilinear Magic Square bracket on `MagicSquareLie O J`. -/
def magicSquareBracketLM (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    MagicSquareLie O J →ₗ[ℝ] MagicSquareLie O J →ₗ[ℝ] MagicSquareLie O J where
  toFun X :=
    { toFun := fun Y =>
        { g2 := ⁅X.g2, Y.g2⁆ + magicMixedToG2LM O J X.mixed Y.mixed
          mixed := magicG2MixedActLM O X.g2 Y.mixed - magicG2MixedActLM O Y.g2 X.mixed +
            magicF4MixedActLM J X.f4 Y.mixed - magicF4MixedActLM J Y.f4 X.mixed +
            magicMixedToMixedLM O J X.mixed Y.mixed
          f4 := ⁅X.f4, Y.f4⁆ + magicMixedToF4LM O J X.mixed Y.mixed }
      map_add' Y₁ Y₂ := by
        apply MagicSquareLie.ext <;>
          simp only [MagicSquareLie.add_g2, MagicSquareLie.add_mixed, MagicSquareLie.add_f4,
            lie_add, map_add, LinearMap.add_apply] <;> abel
      map_smul' r Y := by
        apply MagicSquareLie.ext <;>
          simp only [MagicSquareLie.smul_g2, MagicSquareLie.smul_mixed, MagicSquareLie.smul_f4,
            lie_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply] <;> module }
  map_add' X₁ X₂ := by
    apply LinearMap.ext; intro Y; apply MagicSquareLie.ext <;>
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
        MagicSquareLie.add_g2, MagicSquareLie.add_mixed, MagicSquareLie.add_f4,
        add_lie, map_add] <;> abel
  map_smul' r X := by
    apply LinearMap.ext; intro Y; apply MagicSquareLie.ext <;>
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
        MagicSquareLie.smul_g2, MagicSquareLie.smul_mixed, MagicSquareLie.smul_f4,
        smul_lie, map_smul, RingHom.id_apply] <;> module

private theorem magicMixedToG2LM_antisymm (m₁ m₂ : O₀ ⊗[ℝ] J₀) :
    magicMixedToG2LM O J m₂ m₁ = -magicMixedToG2LM O J m₁ m₂ := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ => simp [ih₁, ih₂]; abel
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ => simp [ih₁, ih₂]; abel
    | tmul b y =>
      simp only [magicMixedToG2LM_tmul, J.traceBilin_symm y x, O.inner_skew a b, smul_neg]

private theorem magicMixedToF4LM_antisymm (m₁ m₂ : O₀ ⊗[ℝ] J₀) :
    magicMixedToF4LM O J m₂ m₁ = -magicMixedToF4LM O J m₁ m₂ := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ => simp [ih₁, ih₂]; abel
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ => simp [ih₁, ih₂]; abel
    | tmul b y =>
      simp only [magicMixedToF4LM_tmul, O.bilin_symm b a, J.inner_skew x y, smul_neg]

private theorem magicMixedToMixedLM_antisymm (m₁ m₂ : O₀ ⊗[ℝ] J₀) :
    magicMixedToMixedLM O J m₂ m₁ = -magicMixedToMixedLM O J m₁ m₂ := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ => simp [ih₁, ih₂]; abel
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ => simp [ih₁, ih₂]; abel
    | tmul b y =>
      simp only [magicMixedToMixedLM_tmul, O.comm_skew a b, J.mul_comm y x,
        TensorProduct.neg_tmul]

theorem magicSquareBracketLM_antisymm (X Y : MagicSquareLie O J) :
    magicSquareBracketLM O J Y X = -magicSquareBracketLM O J X Y := by
  apply MagicSquareLie.ext
  · simp only [magicSquareBracketLM, LinearMap.coe_mk, AddHom.coe_mk, MagicSquareLie.neg_g2,
      magicMixedToG2LM_antisymm X.mixed Y.mixed]
    rw [← lie_skew X.g2 Y.g2]
    abel
  · simp only [magicSquareBracketLM, LinearMap.coe_mk, AddHom.coe_mk, MagicSquareLie.neg_mixed,
      magicMixedToMixedLM_antisymm X.mixed Y.mixed]
    abel
  · simp only [magicSquareBracketLM, LinearMap.coe_mk, AddHom.coe_mk, MagicSquareLie.neg_f4,
      magicMixedToF4LM_antisymm X.mixed Y.mixed]
    rw [← lie_skew X.f4 Y.f4]
    abel

theorem magicSquareBracketLM_self (X : MagicSquareLie O J) :
    magicSquareBracketLM O J X X = 0 := by
  have h := magicSquareBracketLM_antisymm X X
  have h2 : (2 : ℝ) • magicSquareBracketLM O J X X = 0 := by
    rw [two_smul]
    nth_rw 2 [h]
    exact add_neg_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Embedding `G₂ →ₗ[ℝ] MagicSquareLie O J`. -/
def msEmbedG2LM (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    G₂ →ₗ[ℝ] MagicSquareLie O J where
  toFun D := ⟨D, 0, 0⟩
  map_add' _ _ := by apply MagicSquareLie.ext <;> simp
  map_smul' _ _ := by apply MagicSquareLie.ext <;> simp

@[simp] private theorem msEmbedG2LM_g2 (D : G₂) : (msEmbedG2LM O J D).g2 = D := rfl
@[simp] private theorem msEmbedG2LM_mixed (D : G₂) : (msEmbedG2LM O J D).mixed = 0 := rfl
@[simp] private theorem msEmbedG2LM_f4 (D : G₂) : (msEmbedG2LM O J D).f4 = 0 := rfl

/-- Embedding `(O₀ ⊗[ℝ] J₀) →ₗ[ℝ] MagicSquareLie O J`. -/
def msEmbedMixed (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] MagicSquareLie O J where
  toFun m := ⟨0, m, 0⟩
  map_add' _ _ := by apply MagicSquareLie.ext <;> simp
  map_smul' _ _ := by apply MagicSquareLie.ext <;> simp

@[simp] private theorem msEmbedMixed_g2 (m : O₀ ⊗[ℝ] J₀) :
    (msEmbedMixed O J m).g2 = 0 := rfl
@[simp] private theorem msEmbedMixed_mixed (m : O₀ ⊗[ℝ] J₀) :
    (msEmbedMixed O J m).mixed = m := rfl
@[simp] private theorem msEmbedMixed_f4 (m : O₀ ⊗[ℝ] J₀) :
    (msEmbedMixed O J m).f4 = 0 := rfl

/-- Embedding `F₄ →ₗ[ℝ] MagicSquareLie O J`. -/
def msEmbedF4LM (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    F₄ →ₗ[ℝ] MagicSquareLie O J where
  toFun F := ⟨0, 0, F⟩
  map_add' _ _ := by apply MagicSquareLie.ext <;> simp
  map_smul' _ _ := by apply MagicSquareLie.ext <;> simp

@[simp] private theorem msEmbedF4LM_g2 (F : F₄) : (msEmbedF4LM O J F).g2 = 0 := rfl
@[simp] private theorem msEmbedF4LM_mixed (F : F₄) : (msEmbedF4LM O J F).mixed = 0 := rfl
@[simp] private theorem msEmbedF4LM_f4 (F : F₄) : (msEmbedF4LM O J F).f4 = F := rfl

/-- Bilinear pure-tensor embedding `a ↦ x ↦ msEmbedMixed O J (a ⊗ₜ[ℝ] x)`. -/
def msEmbedTensor (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    O₀ →ₗ[ℝ] J₀ →ₗ[ℝ] MagicSquareLie O J :=
  LinearMap.mk₂ ℝ (fun a x => msEmbedMixed O J (a ⊗ₜ[ℝ] x))
    (fun _ _ _ => by simp [TensorProduct.add_tmul])
    (fun _ _ _ => by simp [TensorProduct.smul_tmul])
    (fun _ _ _ => by simp [TensorProduct.tmul_add])
    (fun _ _ _ => by simp [TensorProduct.tmul_smul])

@[simp] theorem msEmbedTensor_apply (a : O₀) (x : J₀) :
    msEmbedTensor O J a x = msEmbedMixed O J (a ⊗ₜ[ℝ] x) := rfl

private inductive MSGrade : Type
  | g2 | mixed | f4
  deriving DecidableEq, Inhabited

private instance : Fintype MSGrade where
  elems := {.g2, .mixed, .f4}
  complete g := by cases g <;> simp

private def msGradeProj (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    MSGrade → MagicSquareLie O J →ₗ[ℝ] MagicSquareLie O J
  | .g2 =>
    { toFun := fun X => msEmbedG2LM O J X.g2
      map_add' := fun X Y => by simp [map_add]
      map_smul' := fun r X => by simp [map_smul] }
  | .mixed =>
    { toFun := fun X => msEmbedMixed O J X.mixed
      map_add' := fun X Y => by simp [map_add]
      map_smul' := fun r X => by simp [map_smul] }
  | .f4 =>
    { toFun := fun X => msEmbedF4LM O J X.f4
      map_add' := fun X Y => by simp [map_add]
      map_smul' := fun r X => by simp [map_smul] }

private theorem msGradeProj_sum (X : MagicSquareLie O J) :
    (∑ i : MSGrade, msGradeProj O J i X) = X := by
  have huniv : (Finset.univ : Finset MSGrade) = {.g2, .mixed, .f4} := by
    ext g; cases g <;> simp
  rw [huniv]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, or_self, Finset.sum_singleton, msGradeProj, LinearMap.coe_mk,
    AddHom.coe_mk]
  apply MagicSquareLie.ext <;> simp

private theorem msBracket_g2_g2 (D₁ D₂ : G₂) :
    magicSquareBracketLM O J (msEmbedG2LM O J D₁) (msEmbedG2LM O J D₂) =
      msEmbedG2LM O J ⁅D₁, D₂⁆ := by
  apply MagicSquareLie.ext <;> simp [magicSquareBracketLM, msEmbedG2LM]

private theorem msBracket_f4_f4 (F₁ F₂ : F₄) :
    magicSquareBracketLM O J (msEmbedF4LM O J F₁) (msEmbedF4LM O J F₂) =
      msEmbedF4LM O J ⁅F₁, F₂⁆ := by
  apply MagicSquareLie.ext <;> simp [magicSquareBracketLM, msEmbedF4LM]

private theorem msBracket_g2_f4 (D : G₂) (F : F₄) :
    magicSquareBracketLM O J (msEmbedG2LM O J D) (msEmbedF4LM O J F) = 0 := by
  apply MagicSquareLie.ext <;> simp [magicSquareBracketLM, msEmbedG2LM, msEmbedF4LM]

private theorem msBracket_f4_g2 (F : F₄) (D : G₂) :
    magicSquareBracketLM O J (msEmbedF4LM O J F) (msEmbedG2LM O J D) = 0 := by
  apply MagicSquareLie.ext <;> simp [magicSquareBracketLM, msEmbedG2LM, msEmbedF4LM]

private theorem msBracket_g2_mixed (D : G₂) (m : O₀ ⊗[ℝ] J₀) :
    magicSquareBracketLM O J (msEmbedG2LM O J D) (msEmbedMixed O J m) =
      msEmbedMixed O J (magicG2MixedActLM O D m) := by
  apply MagicSquareLie.ext <;> simp [magicSquareBracketLM, msEmbedG2LM, msEmbedMixed]

private theorem msBracket_mixed_g2 (m : O₀ ⊗[ℝ] J₀) (D : G₂) :
    magicSquareBracketLM O J (msEmbedMixed O J m) (msEmbedG2LM O J D) =
      msEmbedMixed O J (-magicG2MixedActLM O D m) := by
  rw [magicSquareBracketLM_antisymm, msBracket_g2_mixed, map_neg]

private theorem msBracket_f4_mixed (F : F₄) (m : O₀ ⊗[ℝ] J₀) :
    magicSquareBracketLM O J (msEmbedF4LM O J F) (msEmbedMixed O J m) =
      msEmbedMixed O J (magicF4MixedActLM J F m) := by
  apply MagicSquareLie.ext <;> simp [magicSquareBracketLM, msEmbedF4LM, msEmbedMixed]

private theorem msBracket_mixed_f4 (m : O₀ ⊗[ℝ] J₀) (F : F₄) :
    magicSquareBracketLM O J (msEmbedMixed O J m) (msEmbedF4LM O J F) =
      msEmbedMixed O J (-magicF4MixedActLM J F m) := by
  rw [magicSquareBracketLM_antisymm, msBracket_f4_mixed, map_neg]

private theorem msBracket_mixed_mixed (m₁ m₂ : O₀ ⊗[ℝ] J₀) :
    magicSquareBracketLM O J (msEmbedMixed O J m₁) (msEmbedMixed O J m₂) =
      msEmbedG2LM O J (magicMixedToG2LM O J m₁ m₂) +
      msEmbedMixed O J (magicMixedToMixedLM O J m₁ m₂) +
      msEmbedF4LM O J (magicMixedToF4LM O J m₁ m₂) := by
  apply MagicSquareLie.ext <;> simp [magicSquareBracketLM, msEmbedG2LM, msEmbedMixed, msEmbedF4LM]

private theorem msDefect_swap₁₂ (x y z : MagicSquareLie O J) :
    leibnizDefect (magicSquareBracketLM O J) y x z =
      -leibnizDefect (magicSquareBracketLM O J) x y z := by
  simp only [leibnizDefect]
  rw [magicSquareBracketLM_antisymm x y, map_neg, LinearMap.neg_apply]
  abel

private theorem msDefect_swap₂₃ (x y z : MagicSquareLie O J) :
    leibnizDefect (magicSquareBracketLM O J) x z y =
      -leibnizDefect (magicSquareBracketLM O J) x y z := by
  simp only [leibnizDefect]
  rw [magicSquareBracketLM_antisymm y z,
    magicSquareBracketLM_antisymm (magicSquareBracketLM O J x z) y,
    map_neg, magicSquareBracketLM_antisymm z (magicSquareBracketLM O J x y)]
  abel

private theorem msDefect_cycle (x y z : MagicSquareLie O J) :
    leibnizDefect (magicSquareBracketLM O J) y z x =
      leibnizDefect (magicSquareBracketLM O J) x y z := by
  rw [msDefect_swap₂₃ y x z, msDefect_swap₁₂ x y z, neg_neg]

private theorem msDefect_g2_g2_g2 (D₁ D₂ D₃ : G₂) :
    leibnizDefect (magicSquareBracketLM O J)
      (msEmbedG2LM O J D₁) (msEmbedG2LM O J D₂) (msEmbedG2LM O J D₃) = 0 := by
  have hz : ⁅D₁, ⁅D₂, D₃⁆⁆ - ⁅⁅D₁, D₂⁆, D₃⁆ - ⁅D₂, ⁅D₁, D₃⁆⁆ = 0 := by
    rw [leibniz_lie D₁ D₂ D₃]; abel
  rw [leibnizDefect, msBracket_g2_g2, msBracket_g2_g2, msBracket_g2_g2,
    msBracket_g2_g2, msBracket_g2_g2, msBracket_g2_g2, ← map_sub, ← map_sub, hz, map_zero]

private theorem msDefect_f4_f4_f4 (F₁ F₂ F₃ : F₄) :
    leibnizDefect (magicSquareBracketLM O J)
      (msEmbedF4LM O J F₁) (msEmbedF4LM O J F₂) (msEmbedF4LM O J F₃) = 0 := by
  have hz : ⁅F₁, ⁅F₂, F₃⁆⁆ - ⁅⁅F₁, F₂⁆, F₃⁆ - ⁅F₂, ⁅F₁, F₃⁆⁆ = 0 := by
    rw [leibniz_lie F₁ F₂ F₃]; abel
  rw [leibnizDefect, msBracket_f4_f4, msBracket_f4_f4, msBracket_f4_f4,
    msBracket_f4_f4, msBracket_f4_f4, msBracket_f4_f4, ← map_sub, ← map_sub, hz, map_zero]

private theorem msDefect_g2_g2_f4 (D₁ D₂ : G₂) (F : F₄) :
    leibnizDefect (magicSquareBracketLM O J)
      (msEmbedG2LM O J D₁) (msEmbedG2LM O J D₂) (msEmbedF4LM O J F) = 0 := by
  simp only [leibnizDefect, msBracket_g2_f4, msBracket_g2_g2, map_zero, sub_self]

private theorem msDefect_g2_f4_f4 (D : G₂) (F₁ F₂ : F₄) :
    leibnizDefect (magicSquareBracketLM O J)
      (msEmbedG2LM O J D) (msEmbedF4LM O J F₁) (msEmbedF4LM O J F₂) = 0 := by
  simp only [leibnizDefect, msBracket_g2_f4, msBracket_f4_f4, map_zero, LinearMap.zero_apply,
    sub_self]

private theorem msDefect_g2_g2_mixed (D₁ D₂ : G₂) (m : O₀ ⊗[ℝ] J₀) :
    leibnizDefect (magicSquareBracketLM O J)
      (msEmbedG2LM O J D₁) (msEmbedG2LM O J D₂) (msEmbedMixed O J m) = 0 := by
  induction m using TensorProduct.inductionOn with
  | add m₁ m₂ ih₁ ih₂ => rw [map_add, leibnizDefect_add_right, ih₁, ih₂, add_zero]
  | tmul a x =>
    simp only [leibnizDefect, msBracket_g2_mixed, msBracket_g2_g2, magicG2MixedActLM_tmul,
      O.act_lie]
    apply MagicSquareLie.ext
    · simp only [MagicSquareLie.sub_g2, MagicSquareLie.zero_g2, msEmbedMixed_g2]; abel
    · simp only [MagicSquareLie.sub_mixed, MagicSquareLie.zero_mixed, msEmbedMixed_mixed,
        TensorProduct.sub_tmul]; abel
    · simp only [MagicSquareLie.sub_f4, MagicSquareLie.zero_f4, msEmbedMixed_f4]; abel

private theorem msDefect_f4_f4_mixed (F₁ F₂ : F₄) (m : O₀ ⊗[ℝ] J₀) :
    leibnizDefect (magicSquareBracketLM O J)
      (msEmbedF4LM O J F₁) (msEmbedF4LM O J F₂) (msEmbedMixed O J m) = 0 := by
  induction m using TensorProduct.inductionOn with
  | add m₁ m₂ ih₁ ih₂ => rw [map_add, leibnizDefect_add_right, ih₁, ih₂, add_zero]
  | tmul a x =>
    simp only [leibnizDefect, msBracket_f4_mixed, msBracket_f4_f4, magicF4MixedActLM_tmul,
      J.act_lie]
    apply MagicSquareLie.ext
    · simp only [MagicSquareLie.sub_g2, MagicSquareLie.zero_g2, msEmbedMixed_g2]; abel
    · simp only [MagicSquareLie.sub_mixed, MagicSquareLie.zero_mixed, msEmbedMixed_mixed,
        TensorProduct.tmul_sub]; abel
    · simp only [MagicSquareLie.sub_f4, MagicSquareLie.zero_f4, msEmbedMixed_f4]; abel

private theorem msDefect_g2_f4_mixed (D : G₂) (F : F₄) (m : O₀ ⊗[ℝ] J₀) :
    leibnizDefect (magicSquareBracketLM O J)
      (msEmbedG2LM O J D) (msEmbedF4LM O J F) (msEmbedMixed O J m) = 0 := by
  induction m using TensorProduct.inductionOn with
  | add m₁ m₂ ih₁ ih₂ => rw [map_add, leibnizDefect_add_right, ih₁, ih₂, add_zero]
  | tmul a x =>
    simp only [leibnizDefect, msBracket_f4_mixed, msBracket_g2_f4, msBracket_g2_mixed,
      map_zero, LinearMap.zero_apply, sub_zero, magicG2MixedActLM_tmul, magicF4MixedActLM_tmul]
    exact sub_self _

private theorem msDefect_g2_mixed_mixed (D : G₂) (m₁ m₂ : O₀ ⊗[ℝ] J₀) :
    leibnizDefect (magicSquareBracketLM O J)
      (msEmbedG2LM O J D) (msEmbedMixed O J m₁) (msEmbedMixed O J m₂) = 0 := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ => rw [map_add, leibnizDefect_add_mid, ih₁, ih₂, add_zero]
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ => rw [map_add, leibnizDefect_add_right, ih₁, ih₂, add_zero]
    | tmul b y =>
      simp only [leibnizDefect, msBracket_mixed_mixed, msBracket_g2_mixed,
        magicG2MixedActLM_tmul, map_add, msBracket_g2_g2, msBracket_g2_f4,
        magicMixedToG2LM_tmul, magicMixedToMixedLM_tmul, magicMixedToF4LM_tmul, add_zero]
      apply MagicSquareLie.ext
      · simp only [MagicSquareLie.sub_g2, MagicSquareLie.add_g2, MagicSquareLie.zero_g2,
          msEmbedG2LM_g2, msEmbedMixed_g2, msEmbedF4LM_g2, lie_smul, O.g2_covariant, smul_add]
        abel
      · simp only [MagicSquareLie.sub_mixed, MagicSquareLie.add_mixed, MagicSquareLie.zero_mixed,
          msEmbedG2LM_mixed, msEmbedMixed_mixed, msEmbedF4LM_mixed, O.act_comm,
          TensorProduct.add_tmul]
        abel
      · simp only [MagicSquareLie.sub_f4, MagicSquareLie.add_f4, MagicSquareLie.zero_f4,
          msEmbedG2LM_f4, msEmbedMixed_f4, msEmbedF4LM_f4]
        have hskew := O.bilin_deriv_skew D a b
        have hc : (-2 : ℝ) * O.bilin₀ (O.act D a) b +
            (-2 : ℝ) * O.bilin₀ a (O.act D b) = 0 := by linarith
        have hsum : ((-2 : ℝ) * O.bilin₀ (O.act D a) b) • J.inner x y +
            ((-2 : ℝ) * O.bilin₀ a (O.act D b)) • J.inner x y = 0 := by
          rw [← add_smul, hc, zero_smul]
        have hre :
            (0 + 0 - (0 + 0 + ((-2 : ℝ) * O.bilin₀ (O.act D a) b) • J.inner x y) -
              (0 + 0 + ((-2 : ℝ) * O.bilin₀ a (O.act D b)) • J.inner x y)) =
            -(((-2 : ℝ) * O.bilin₀ (O.act D a) b) • J.inner x y +
              ((-2 : ℝ) * O.bilin₀ a (O.act D b)) • J.inner x y) := by abel
        rw [hre, hsum, neg_zero]

private theorem msDefect_f4_mixed_mixed (F : F₄) (m₁ m₂ : O₀ ⊗[ℝ] J₀) :
    leibnizDefect (magicSquareBracketLM O J)
      (msEmbedF4LM O J F) (msEmbedMixed O J m₁) (msEmbedMixed O J m₂) = 0 := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ => rw [map_add, leibnizDefect_add_mid, ih₁, ih₂, add_zero]
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ => rw [map_add, leibnizDefect_add_right, ih₁, ih₂, add_zero]
    | tmul b y =>
      simp only [leibnizDefect, msBracket_mixed_mixed, msBracket_f4_mixed,
        magicF4MixedActLM_tmul, map_add, msBracket_f4_g2, msBracket_f4_f4,
        magicMixedToG2LM_tmul, magicMixedToMixedLM_tmul, magicMixedToF4LM_tmul, zero_add]
      apply MagicSquareLie.ext
      · simp only [MagicSquareLie.sub_g2, MagicSquareLie.add_g2, MagicSquareLie.zero_g2,
          msEmbedG2LM_g2, msEmbedMixed_g2, msEmbedF4LM_g2]
        have hskew := J.traceBilin_deriv_skew F x y
        have hc : (1 / 3 : ℝ) * J.traceBilin₀ (J.act F x) y +
            (1 / 3 : ℝ) * J.traceBilin₀ x (J.act F y) = 0 := by linarith
        have hsum : ((1 / 3 : ℝ) * J.traceBilin₀ (J.act F x) y) • O.inner a b +
            ((1 / 3 : ℝ) * J.traceBilin₀ x (J.act F y)) • O.inner a b = 0 := by
          rw [← add_smul, hc, zero_smul]
        have hre :
            (0 + 0 - (((1 / 3 : ℝ) * J.traceBilin₀ (J.act F x) y) • O.inner a b + 0 + 0) -
              (((1 / 3 : ℝ) * J.traceBilin₀ x (J.act F y)) • O.inner a b + 0 + 0)) =
            -(((1 / 3 : ℝ) * J.traceBilin₀ (J.act F x) y) • O.inner a b +
              ((1 / 3 : ℝ) * J.traceBilin₀ x (J.act F y)) • O.inner a b) := by abel
        rw [hre, hsum, neg_zero]
      · simp only [MagicSquareLie.sub_mixed, MagicSquareLie.add_mixed, MagicSquareLie.zero_mixed,
          msEmbedG2LM_mixed, msEmbedMixed_mixed, msEmbedF4LM_mixed, J.act_mul,
          TensorProduct.tmul_add]
        abel
      · simp only [MagicSquareLie.sub_f4, MagicSquareLie.add_f4, MagicSquareLie.zero_f4,
          msEmbedG2LM_f4, msEmbedMixed_f4, msEmbedF4LM_f4, lie_smul, J.f4_covariant, smul_add]
        abel

private theorem msDefect_mixed_mixed_mixed_tmul
    (a b c : O₀) (x y z : J₀) :
    leibnizDefect (magicSquareBracketLM O J)
      (msEmbedTensor O J a x) (msEmbedTensor O J b y) (msEmbedTensor O J c z) = 0 := by
  have hdef : leibnizDefect (magicSquareBracketLM O J)
        (msEmbedTensor O J a x) (msEmbedTensor O J b y) (msEmbedTensor O J c z) =
      magicSquareBracketLM O J (msEmbedTensor O J a x)
        (magicSquareBracketLM O J (msEmbedTensor O J b y) (msEmbedTensor O J c z)) +
      magicSquareBracketLM O J (msEmbedTensor O J b y)
        (magicSquareBracketLM O J (msEmbedTensor O J c z) (msEmbedTensor O J a x)) +
      magicSquareBracketLM O J (msEmbedTensor O J c z)
        (magicSquareBracketLM O J (msEmbedTensor O J a x) (msEmbedTensor O J b y)) := by
    simp only [leibnizDefect]
    rw [magicSquareBracketLM_antisymm (msEmbedTensor O J c z) (msEmbedTensor O J a x),
      magicSquareBracketLM_antisymm
        (magicSquareBracketLM O J (msEmbedTensor O J a x) (msEmbedTensor O J b y))
        (msEmbedTensor O J c z),
      map_neg]
    abel
  rw [hdef]
  have hterm (u v w : O₀) (p q r : J₀) :
      magicSquareBracketLM O J (msEmbedTensor O J u p)
          (magicSquareBracketLM O J (msEmbedTensor O J v q) (msEmbedTensor O J w r)) =
        msEmbedG2LM O J (((1 / 3 : ℝ) * J.traceBilin₀ p (J.mul₀ q r)) • O.inner u (O.comm₀ v w)) +
        msEmbedF4LM O J (((-2 : ℝ) * O.bilin₀ u (O.comm₀ v w)) • J.inner p (J.mul₀ q r)) +
        msEmbedMixed O J (
          (-((1 / 3 : ℝ) * J.traceBilin₀ q r) • O.act (O.inner v w) u) ⊗ₜ[ℝ] p +
          u ⊗ₜ[ℝ] (-((-2 : ℝ) * O.bilin₀ v w) • J.act (J.inner q r) p) +
          (O.comm₀ u (O.comm₀ v w)) ⊗ₜ[ℝ] (J.mul₀ p (J.mul₀ q r))) := by
    simp only [msEmbedTensor_apply, msBracket_mixed_mixed, map_add,
      msBracket_mixed_g2, msBracket_mixed_f4,
      magicMixedToG2LM_tmul, magicMixedToF4LM_tmul, magicMixedToMixedLM_tmul,
      map_smul, magicG2MixedActLM_tmul, magicF4MixedActLM_tmul,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    apply MagicSquareLie.ext
    · simp
    · simp only [MagicSquareLie.add_mixed, MagicSquareLie.neg_mixed, MagicSquareLie.smul_mixed,
        msEmbedG2LM_mixed, msEmbedF4LM_mixed, msEmbedMixed_mixed, neg_smul, smul_neg,
        zero_add, add_zero, smul_zero]
      abel
    · simp
  rw [hterm a b c x y z, hterm b c a y z x, hterm c a b z x y]
  apply MagicSquareLie.ext
  · simp only [MagicSquareLie.add_g2, MagicSquareLie.zero_g2, msEmbedG2LM_g2, msEmbedF4LM_g2,
      msEmbedMixed_g2, add_zero]
    rw [J.traceBilin_mul_cyclic y z x, J.traceBilin_mul_cyclic z x y]
    rw [← smul_add, ← smul_add, O.inner_comm_cyclic_zero a b c, smul_zero]
  · simp only [MagicSquareLie.add_mixed, MagicSquareLie.zero_mixed, msEmbedG2LM_mixed,
      msEmbedF4LM_mixed, msEmbedMixed_mixed, zero_add, add_zero]
    rw [J.mul_assoc_decompose x y z, J.mul_assoc_decompose y z x, J.mul_assoc_decompose z x y]
    simp only [TensorProduct.tmul_add, TensorProduct.tmul_sub, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul]
    have hP0_cyc :
        O.comm₀ a (O.comm₀ b c) + O.comm₀ b (O.comm₀ c a) + O.comm₀ c (O.comm₀ a b) =
          (-6 : ℝ) • O.assoc₀ a b c :=
      O.comm_jacobi_eq_neg_six_assoc a b c
    have hK (u v w : O₀) (r : ℝ) (p : J₀) :
        -((1 / 3 : ℝ) * r) • (O.act (O.inner v w) u) ⊗ₜ[ℝ] p +
          ((1 / 6 : ℝ) * r) • (((-6 : ℝ) • O.assoc₀ u v w) ⊗ₜ[ℝ] p) -
          ((1 / 3 : ℝ) * r) • (O.comm₀ u (O.comm₀ v w)) ⊗ₜ[ℝ] p = 0 := by
      have hvec : -((1 / 3 : ℝ) * r) • O.act (O.inner v w) u - r • O.assoc₀ u v w -
          ((1 / 3 : ℝ) * r) • O.comm₀ u (O.comm₀ v w) = 0 := by
        have hsub : -((1 / 3 : ℝ) * r) • O.act (O.inner v w) u - r • O.assoc₀ u v w -
            ((1 / 3 : ℝ) * r) • O.comm₀ u (O.comm₀ v w) =
            r • (-O.assoc₀ u v w - (1 / 3 : ℝ) • O.comm₀ u (O.comm₀ v w) -
              (1 / 3 : ℝ) • O.act (O.inner v w) u) := by
          simp only [smul_sub, smul_smul]
          module
        rw [hsub, O.kleinfeld_combo u v w, smul_zero]
      have htmul :
          (-((1 / 3 : ℝ) * r) • O.act (O.inner v w) u - r • O.assoc₀ u v w -
            ((1 / 3 : ℝ) * r) • O.comm₀ u (O.comm₀ v w)) ⊗ₜ[ℝ] p = 0 := by
        rw [hvec, TensorProduct.zero_tmul]
      simp only [TensorProduct.sub_tmul, TensorProduct.smul_tmul, TensorProduct.tmul_smul] at htmul
      have hre :
          -((1 / 3 : ℝ) * r) • (O.act (O.inner v w) u) ⊗ₜ[ℝ] p +
            ((1 / 6 : ℝ) * r) • (((-6 : ℝ) • O.assoc₀ u v w) ⊗ₜ[ℝ] p) -
            ((1 / 3 : ℝ) * r) • (O.comm₀ u (O.comm₀ v w)) ⊗ₜ[ℝ] p =
          -((1 / 3 : ℝ) * r) • (O.act (O.inner v w) u) ⊗ₜ[ℝ] p -
            r • (O.assoc₀ u v w) ⊗ₜ[ℝ] p -
            ((1 / 3 : ℝ) * r) • (O.comm₀ u (O.comm₀ v w)) ⊗ₜ[ℝ] p := by
        rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul,
          show ((1 / 6 : ℝ) * r) * (-6 : ℝ) = -r from by ring]
        module
      rw [hre]
      simpa [neg_smul] using htmul
    have hKa := hK a b c (J.traceBilin₀ y z) x
    have hKb := hK b c a (J.traceBilin₀ z x) y
    have hKc := hK c a b (J.traceBilin₀ x y) z
    have hK_assoc_b : O.assoc₀ b c a = O.assoc₀ a b c := O.assoc_cycle a b c
    have hK_assoc_c : O.assoc₀ c a b = O.assoc₀ a b c :=
      (O.assoc_cycle b c a).trans (O.assoc_cycle a b c)
    let C0 (u v w : O₀) : O₀ :=
      (1 / 3 : ℝ) • (O.comm₀ v (O.comm₀ w u) - O.comm₀ w (O.comm₀ u v)) +
        (2 * O.bilin₀ v w) • u
    have hC0_eq (u v w : O₀) :
        C0 u v w = (2 / 3 : ℝ) •
          (O.bilin₀ v w • u + O.bilin₀ w u • v + O.bilin₀ u v • w) := by
      have hid := O.comm_double_identity u v w
      have hid3 := congrArg (fun s : O₀ => (1 / 3 : ℝ) • s) hid
      simp only [smul_add, smul_smul, ← mul_assoc] at hid3
      have h36 : (1 / 3 : ℝ) * (6 : ℝ) = 2 := by norm_num
      have h32 : (1 / 3 : ℝ) * (2 : ℝ) = 2 / 3 := by norm_num
      rw [h36, h32] at hid3
      simpa [C0, smul_add, smul_sub, smul_smul] using hid3
    have hC_symm_b : C0 b c a = C0 a b c := by rw [hC0_eq, hC0_eq]; congr 1; abel
    have hC_symm_c : C0 c a b = C0 a b c := by rw [hC0_eq, hC0_eq]; congr 1; abel
    have hDJor_cyc : J.act (J.inner y z) x + J.act (J.inner z x) y + J.act (J.inner x y) z = 0 :=
      J.inner_self_cyclic_zero x y z
    have hC_vanish :
        (C0 a b c) ⊗ₜ[ℝ] (J.act (J.inner y z) x) +
        (C0 b c a) ⊗ₜ[ℝ] (J.act (J.inner z x) y) +
        (C0 c a b) ⊗ₜ[ℝ] (J.act (J.inner x y) z) = 0 := by
      rw [hC_symm_b, hC_symm_c, ← TensorProduct.tmul_add, ← TensorProduct.tmul_add, hDJor_cyc,
        TensorProduct.tmul_zero]
    have hP0_expand :
        (1 / 6 : ℝ) • ((O.comm₀ a (O.comm₀ b c) + O.comm₀ b (O.comm₀ c a) +
          O.comm₀ c (O.comm₀ a b)) ⊗ₜ[ℝ]
            (J.traceBilin₀ y z • x + J.traceBilin₀ z x • y + J.traceBilin₀ x y • z)) =
        (1 / 6 : ℝ) • (((-6 : ℝ) • O.assoc₀ a b c) ⊗ₜ[ℝ]
            (J.traceBilin₀ y z • x + J.traceBilin₀ z x • y + J.traceBilin₀ x y • z)) := by
      rw [hP0_cyc]
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, smul_add] at hP0_expand
    simp only [C0, TensorProduct.add_tmul, TensorProduct.sub_tmul, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul] at hC_vanish
    rw [hK_assoc_b] at hKb
    rw [hK_assoc_c] at hKc
    simp only [← mul_smul] at hKa hKb hKc hP0_expand hC_vanish ⊢
    have hP0_diff :
        ((((1 / 6 * J.traceBilin₀ y z) • O.comm₀ a (O.comm₀ b c) ⊗ₜ[ℝ] x +
            (1 / 6 * J.traceBilin₀ z x) • O.comm₀ a (O.comm₀ b c) ⊗ₜ[ℝ] y +
            (1 / 6 * J.traceBilin₀ x y) • O.comm₀ a (O.comm₀ b c) ⊗ₜ[ℝ] z) +
          ((1 / 6 * J.traceBilin₀ y z) • O.comm₀ b (O.comm₀ c a) ⊗ₜ[ℝ] x +
            (1 / 6 * J.traceBilin₀ z x) • O.comm₀ b (O.comm₀ c a) ⊗ₜ[ℝ] y +
            (1 / 6 * J.traceBilin₀ x y) • O.comm₀ b (O.comm₀ c a) ⊗ₜ[ℝ] z)) +
          ((1 / 6 * J.traceBilin₀ y z) • O.comm₀ c (O.comm₀ a b) ⊗ₜ[ℝ] x +
            (1 / 6 * J.traceBilin₀ z x) • O.comm₀ c (O.comm₀ a b) ⊗ₜ[ℝ] y +
            (1 / 6 * J.traceBilin₀ x y) • O.comm₀ c (O.comm₀ a b) ⊗ₜ[ℝ] z)) -
        ((1 / 6 * -6 * J.traceBilin₀ y z) • (O.assoc₀ a b c) ⊗ₜ[ℝ] x +
          (1 / 6 * -6 * J.traceBilin₀ z x) • (O.assoc₀ a b c) ⊗ₜ[ℝ] y +
          (1 / 6 * -6 * J.traceBilin₀ x y) • (O.assoc₀ a b c) ⊗ₜ[ℝ] z) = 0 := by
      have hp := sub_eq_zero.mpr hP0_expand
      simp only [show ∀ t : ℝ, (1 / 6 : ℝ) * (t * -6) = 1 / 6 * -6 * t from fun _ => by ring] at hp
      have hre :
          ((((1 / 6 * J.traceBilin₀ y z) • O.comm₀ a (O.comm₀ b c) ⊗ₜ[ℝ] x +
              (1 / 6 * J.traceBilin₀ z x) • O.comm₀ a (O.comm₀ b c) ⊗ₜ[ℝ] y +
              (1 / 6 * J.traceBilin₀ x y) • O.comm₀ a (O.comm₀ b c) ⊗ₜ[ℝ] z) +
            ((1 / 6 * J.traceBilin₀ y z) • O.comm₀ b (O.comm₀ c a) ⊗ₜ[ℝ] x +
              (1 / 6 * J.traceBilin₀ z x) • O.comm₀ b (O.comm₀ c a) ⊗ₜ[ℝ] y +
              (1 / 6 * J.traceBilin₀ x y) • O.comm₀ b (O.comm₀ c a) ⊗ₜ[ℝ] z)) +
            ((1 / 6 * J.traceBilin₀ y z) • O.comm₀ c (O.comm₀ a b) ⊗ₜ[ℝ] x +
              (1 / 6 * J.traceBilin₀ z x) • O.comm₀ c (O.comm₀ a b) ⊗ₜ[ℝ] y +
              (1 / 6 * J.traceBilin₀ x y) • O.comm₀ c (O.comm₀ a b) ⊗ₜ[ℝ] z)) =
          (((1 / 6 * J.traceBilin₀ y z) • O.comm₀ a (O.comm₀ b c) ⊗ₜ[ℝ] x +
              (1 / 6 * J.traceBilin₀ y z) • O.comm₀ b (O.comm₀ c a) ⊗ₜ[ℝ] x +
              (1 / 6 * J.traceBilin₀ y z) • O.comm₀ c (O.comm₀ a b) ⊗ₜ[ℝ] x) +
            ((1 / 6 * J.traceBilin₀ z x) • O.comm₀ a (O.comm₀ b c) ⊗ₜ[ℝ] y +
              (1 / 6 * J.traceBilin₀ z x) • O.comm₀ b (O.comm₀ c a) ⊗ₜ[ℝ] y +
              (1 / 6 * J.traceBilin₀ z x) • O.comm₀ c (O.comm₀ a b) ⊗ₜ[ℝ] y)) +
            ((1 / 6 * J.traceBilin₀ x y) • O.comm₀ a (O.comm₀ b c) ⊗ₜ[ℝ] z +
              (1 / 6 * J.traceBilin₀ x y) • O.comm₀ b (O.comm₀ c a) ⊗ₜ[ℝ] z +
              (1 / 6 * J.traceBilin₀ x y) • O.comm₀ c (O.comm₀ a b) ⊗ₜ[ℝ] z) := by
        abel
      rw [hre]
      exact hp
    simp only [← TensorProduct.smul_tmul', smul_smul] at hKa hKb hKc
    have hzero : ∀ {u v : O₀ ⊗[ℝ] J₀}, u = 0 → v = 0 → u + v = 0 := by
      rintro u v rfl rfl; exact add_zero 0
    have hcomb := hzero (hzero (hzero hKa hKb) (hzero hKc hC_vanish)) hP0_diff
    refine Eq.trans ?_ hcomb
    module
  · simp only [MagicSquareLie.add_f4, MagicSquareLie.zero_f4, msEmbedG2LM_f4, msEmbedF4LM_f4,
      msEmbedMixed_f4, add_zero, zero_add]
    rw [O.bilin_comm_cyclic a b c, O.bilin_comm_cyclic b c a]
    rw [← smul_add, ← smul_add, J.inner_mul_cyclic_zero x y z, smul_zero]

private theorem msDefect_mixed_mixed_mixed (m₁ m₂ m₃ : O₀ ⊗[ℝ] J₀) :
    leibnizDefect (magicSquareBracketLM O J)
      (msEmbedMixed O J m₁) (msEmbedMixed O J m₂) (msEmbedMixed O J m₃) = 0 := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ => rw [map_add, leibnizDefect_add_left, ih₁, ih₂, add_zero]
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ => rw [map_add, leibnizDefect_add_mid, ih₁, ih₂, add_zero]
    | tmul b y =>
      induction m₃ using TensorProduct.inductionOn with
      | add w₁ w₂ ih₁ ih₂ => rw [map_add, leibnizDefect_add_right, ih₁, ih₂, add_zero]
      | tmul c z => exact msDefect_mixed_mixed_mixed_tmul a b c x y z

private theorem msDefect_all_cells (i j k : MSGrade) (X Y Z : MagicSquareLie O J) :
    leibnizDefect (magicSquareBracketLM O J)
      (msGradeProj O J i X) (msGradeProj O J j Y) (msGradeProj O J k Z) = 0 := by
  cases i <;> cases j <;> cases k <;>
    simp only [msGradeProj, LinearMap.coe_mk, AddHom.coe_mk]
  · exact msDefect_g2_g2_g2 _ _ _
  · exact msDefect_g2_g2_mixed _ _ _
  · exact msDefect_g2_g2_f4 _ _ _
  · rw [msDefect_swap₂₃, msDefect_g2_g2_mixed, neg_zero]
  · exact msDefect_g2_mixed_mixed _ _ _
  · rw [msDefect_swap₂₃, msDefect_g2_f4_mixed, neg_zero]
  · rw [msDefect_swap₂₃, msDefect_g2_g2_f4, neg_zero]
  · exact msDefect_g2_f4_mixed _ _ _
  · exact msDefect_g2_f4_f4 _ _ _
  · rw [← msDefect_cycle, msDefect_g2_g2_mixed]
  · rw [msDefect_swap₁₂, msDefect_g2_mixed_mixed, neg_zero]
  · rw [msDefect_swap₁₂, msDefect_swap₂₃, msDefect_g2_f4_mixed, neg_zero, neg_zero]
  · rw [msDefect_cycle, msDefect_g2_mixed_mixed]
  · exact msDefect_mixed_mixed_mixed _ _ _
  · rw [msDefect_cycle, msDefect_f4_mixed_mixed]
  · rw [msDefect_cycle, msDefect_swap₂₃, msDefect_g2_f4_mixed, neg_zero]
  · rw [msDefect_swap₁₂, msDefect_f4_mixed_mixed, neg_zero]
  · rw [← msDefect_cycle, msDefect_f4_f4_mixed]
  · rw [← msDefect_cycle, msDefect_g2_g2_f4]
  · rw [msDefect_swap₁₂, msDefect_g2_f4_mixed, neg_zero]
  · rw [msDefect_swap₁₂, msDefect_swap₂₃, msDefect_g2_f4_f4, neg_zero, neg_zero]
  · rw [msDefect_cycle, msDefect_g2_f4_mixed]
  · exact msDefect_f4_mixed_mixed _ _ _
  · rw [msDefect_swap₂₃, msDefect_f4_f4_mixed, neg_zero]
  · rw [msDefect_cycle, msDefect_g2_f4_f4]
  · exact msDefect_f4_f4_mixed _ _ _
  · exact msDefect_f4_f4_f4 _ _ _

theorem magicSquareBracketLM_leibniz (X Y Z : MagicSquareLie O J) :
    magicSquareBracketLM O J X (magicSquareBracketLM O J Y Z) =
      magicSquareBracketLM O J (magicSquareBracketLM O J X Y) Z +
        magicSquareBracketLM O J Y (magicSquareBracketLM O J X Z) := by
  have h := global_leibniz_of_homogeneous (magicSquareBracketLM O J)
    (msGradeProj O J) msGradeProj_sum msDefect_all_cells X Y Z
  dsimp [leibnizDefect] at h
  have hsub : magicSquareBracketLM O J X (magicSquareBracketLM O J Y Z) -
      magicSquareBracketLM O J (magicSquareBracketLM O J X Y) Z =
      magicSquareBracketLM O J Y (magicSquareBracketLM O J X Z) := sub_eq_zero.mp h
  rw [eq_add_of_sub_eq' hsub, add_comm]

instance instLieRingMagicSquareLie : LieRing (MagicSquareLie O J) where
  bracket X Y := magicSquareBracketLM O J X Y
  add_lie X₁ X₂ Y := by
    change magicSquareBracketLM O J (X₁ + X₂) Y =
      magicSquareBracketLM O J X₁ Y + magicSquareBracketLM O J X₂ Y
    simp [map_add]
  lie_add X Y₁ Y₂ := by
    change magicSquareBracketLM O J X (Y₁ + Y₂) =
      magicSquareBracketLM O J X Y₁ + magicSquareBracketLM O J X Y₂
    simp [map_add]
  lie_self X := magicSquareBracketLM_self X
  leibniz_lie X Y Z := by
    change magicSquareBracketLM O J X (magicSquareBracketLM O J Y Z) =
      magicSquareBracketLM O J (magicSquareBracketLM O J X Y) Z +
        magicSquareBracketLM O J Y (magicSquareBracketLM O J X Z)
    exact magicSquareBracketLM_leibniz X Y Z

instance instLieAlgebraMagicSquareLie : LieAlgebra ℝ (MagicSquareLie O J) where
  lie_smul r X Y := by
    change magicSquareBracketLM O J X (r • Y) = r • magicSquareBracketLM O J X Y
    simp [map_smul]

/-- Mixed bilinear pairing `(a₁ ⊗ x₁, a₂ ⊗ x₂) ↦ bilin₀ a₁ a₂ * traceBilin₀ x₁ x₂`. -/
def magicMixedBilin (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] ℝ :=
  magicBilLift
    { toFun := fun a =>
        { toFun := fun x =>
            { toFun := fun b =>
                { toFun := fun y => O.bilin₀ a b * J.traceBilin₀ x y
                  map_add' := fun y₁ y₂ => by simp [map_add, mul_add]
                  map_smul' := fun r y => by simp [map_smul]; ring }
              map_add' := fun b₁ b₂ => by
                apply LinearMap.ext; intro y
                simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, add_mul]
              map_smul' := fun r b => by
                apply LinearMap.ext; intro y
                simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
                  RingHom.id_apply, smul_eq_mul]
                ring }
          map_add' := fun x₁ x₂ => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, mul_add]
          map_smul' := fun r x => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
              RingHom.id_apply, smul_eq_mul]
            ring }
      map_add' := fun a₁ a₂ => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, add_mul]
      map_smul' := fun r a => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
          RingHom.id_apply, smul_eq_mul]
        ring }

@[simp] theorem magicMixedBilin_tmul (a b : O₀) (x y : J₀) :
    magicMixedBilin O J (a ⊗ₜ[ℝ] x) (b ⊗ₜ[ℝ] y) = O.bilin₀ a b * J.traceBilin₀ x y := by
  simp [magicMixedBilin]

theorem magicMixedBilin_symm (m₁ m₂ : O₀ ⊗[ℝ] J₀) :
    magicMixedBilin O J m₁ m₂ = magicMixedBilin O J m₂ m₁ := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
    | tmul b y => simp [O.bilin_symm a b, J.traceBilin_symm x y]

/-- `(3, -6, 1)` `ad`-invariant symmetric bilinear form on `MagicSquareLie O J`:
`B(X, Y) = 3 * Tr_O(X.g2 ∘ Y.g2) - 6 * ⟨X.mixed, Y.mixed⟩ + Tr_J(X.f4 ∘ Y.f4)`. -/
def magicInvBilin (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    MagicSquareLie O J →ₗ[ℝ] MagicSquareLie O J →ₗ[ℝ] ℝ where
  toFun X :=
    { toFun := fun Y =>
        3 * O.g2Bilin X.g2 Y.g2 - 6 * magicMixedBilin O J X.mixed Y.mixed +
          J.f4Bilin X.f4 Y.f4
      map_add' := fun Y₁ Y₂ => by
        simp only [MagicSquareLie.add_g2, MagicSquareLie.add_mixed, MagicSquareLie.add_f4,
          map_add]
        ring
      map_smul' := fun r Y => by
        simp only [MagicSquareLie.smul_g2, MagicSquareLie.smul_mixed, MagicSquareLie.smul_f4,
          map_smul, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' X₁ X₂ := by
    apply LinearMap.ext; intro Y
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      MagicSquareLie.add_g2, MagicSquareLie.add_mixed, MagicSquareLie.add_f4,
      map_add, LinearMap.add_apply]
    ring
  map_smul' r X := by
    apply LinearMap.ext; intro Y
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      MagicSquareLie.smul_g2, MagicSquareLie.smul_mixed, MagicSquareLie.smul_f4,
      map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem magicInvBilin_apply (X Y : MagicSquareLie O J) :
    magicInvBilin O J X Y =
      3 * O.g2Bilin X.g2 Y.g2 - 6 * magicMixedBilin O J X.mixed Y.mixed +
        J.f4Bilin X.f4 Y.f4 := rfl

theorem magicInvBilin_symm (X Y : MagicSquareLie O J) :
    magicInvBilin O J X Y = magicInvBilin O J Y X := by
  simp only [magicInvBilin_apply, O.g2Bilin_symm X.g2 Y.g2,
    magicMixedBilin_symm X.mixed Y.mixed, J.f4Bilin_symm X.f4 Y.f4]

private theorem magicInvBilin_lieInvariant_g2 (D : G₂) (X Y : MagicSquareLie O J) :
    magicInvBilin O J ⁅msEmbedG2LM O J D, X⁆ Y +
      magicInvBilin O J X ⁅msEmbedG2LM O J D, Y⁆ = 0 := by
  have hg2 : O.g2Bilin ⁅D, X.g2⁆ Y.g2 + O.g2Bilin X.g2 ⁅D, Y.g2⁆ = 0 :=
    O.g2Bilin_lie_skew D X.g2 Y.g2
  have hmix : ∀ m₁ m₂ : O₀ ⊗[ℝ] J₀,
      magicMixedBilin O J (magicG2MixedActLM O D m₁) m₂ +
        magicMixedBilin O J m₁ (magicG2MixedActLM O D m₂) = 0 := by
    intro m₁ m₂
    induction m₁ using TensorProduct.inductionOn with
    | add u₁ u₂ ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply] at ih₁ ih₂ ⊢; linarith
    | tmul a x =>
      induction m₂ using TensorProduct.inductionOn with
      | add v₁ v₂ ih₁ ih₂ =>
        simp only [map_add] at ih₁ ih₂ ⊢; linarith
      | tmul b y =>
        simp only [magicG2MixedActLM_tmul, magicMixedBilin_tmul]
        rw [J.traceBilin_symm x y]
        have hsk := O.bilin_deriv_skew D a b
        calc O.bilin₀ (O.act D a) b * J.traceBilin₀ y x +
              O.bilin₀ a (O.act D b) * J.traceBilin₀ y x
            = (O.bilin₀ (O.act D a) b + O.bilin₀ a (O.act D b)) * J.traceBilin₀ y x := by ring
          _ = 0 := by rw [hsk, zero_mul]
  have hm := hmix X.mixed Y.mixed
  change magicInvBilin O J (magicSquareBracketLM O J (msEmbedG2LM O J D) X) Y +
    magicInvBilin O J X (magicSquareBracketLM O J (msEmbedG2LM O J D) Y) = 0
  simp only [magicInvBilin_apply, magicSquareBracketLM, msEmbedG2LM, LinearMap.coe_mk,
    AddHom.coe_mk, zero_lie, add_zero, map_zero, LinearMap.zero_apply, sub_zero]
  linarith

private theorem magicInvBilin_lieInvariant_f4 (F : F₄) (X Y : MagicSquareLie O J) :
    magicInvBilin O J ⁅msEmbedF4LM O J F, X⁆ Y +
      magicInvBilin O J X ⁅msEmbedF4LM O J F, Y⁆ = 0 := by
  have hf4 : J.f4Bilin ⁅F, X.f4⁆ Y.f4 + J.f4Bilin X.f4 ⁅F, Y.f4⁆ = 0 :=
    J.f4Bilin_lie_skew F X.f4 Y.f4
  have hmix : ∀ m₁ m₂ : O₀ ⊗[ℝ] J₀,
      magicMixedBilin O J (magicF4MixedActLM J F m₁) m₂ +
        magicMixedBilin O J m₁ (magicF4MixedActLM J F m₂) = 0 := by
    intro m₁ m₂
    induction m₁ using TensorProduct.inductionOn with
    | add u₁ u₂ ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply] at ih₁ ih₂ ⊢; linarith
    | tmul a x =>
      induction m₂ using TensorProduct.inductionOn with
      | add v₁ v₂ ih₁ ih₂ =>
        simp only [map_add] at ih₁ ih₂ ⊢; linarith
      | tmul b y =>
        simp only [magicF4MixedActLM_tmul, magicMixedBilin_tmul]
        have hsk := J.traceBilin_deriv_skew F x y
        calc O.bilin₀ a b * J.traceBilin₀ (J.act F x) y +
              O.bilin₀ a b * J.traceBilin₀ x (J.act F y)
            = O.bilin₀ a b * (J.traceBilin₀ (J.act F x) y + J.traceBilin₀ x (J.act F y)) := by
              ring
          _ = 0 := by rw [hsk, mul_zero]
  have hm := hmix X.mixed Y.mixed
  change magicInvBilin O J (magicSquareBracketLM O J (msEmbedF4LM O J F) X) Y +
    magicInvBilin O J X (magicSquareBracketLM O J (msEmbedF4LM O J F) Y) = 0
  simp only [magicInvBilin_apply, magicSquareBracketLM, msEmbedF4LM, LinearMap.coe_mk,
    AddHom.coe_mk, zero_lie, zero_add, add_zero, map_zero, LinearMap.zero_apply, sub_zero]
  linarith

private theorem magicInvBilin_lieInvariant_mixed_tmul
    (c : O₀) (z : J₀) (X Y : MagicSquareLie O J) :
    magicInvBilin O J ⁅msEmbedTensor O J c z, X⁆ Y +
      magicInvBilin O J X ⁅msEmbedTensor O J c z, Y⁆ = 0 := by
  have hsplit : ∀ W : MagicSquareLie O J,
      W = msEmbedG2LM O J W.g2 + msEmbedMixed O J W.mixed + msEmbedF4LM O J W.f4 := by
    intro W; apply MagicSquareLie.ext <;> simp
  have h1 : ∀ (D : G₂) (m : O₀ ⊗[ℝ] J₀),
      magicInvBilin O J ⁅msEmbedTensor O J c z, msEmbedMixed O J m⁆ (msEmbedG2LM O J D) +
        magicInvBilin O J (msEmbedMixed O J m) ⁅msEmbedTensor O J c z, msEmbedG2LM O J D⁆ = 0 := by
    intro D m
    induction m using TensorProduct.inductionOn with
    | add u₁ u₂ ih₁ ih₂ =>
      simp only [map_add, lie_add, LinearMap.add_apply] at ih₁ ih₂ ⊢; linarith
    | tmul a x =>
      change magicInvBilin O J (magicSquareBracketLM O J (msEmbedMixed O J (c ⊗ₜ[ℝ] z))
          (msEmbedMixed O J (a ⊗ₜ[ℝ] x))) (msEmbedG2LM O J D) +
        magicInvBilin O J (msEmbedMixed O J (a ⊗ₜ[ℝ] x))
          (magicSquareBracketLM O J (msEmbedMixed O J (c ⊗ₜ[ℝ] z)) (msEmbedG2LM O J D)) = 0
      rw [msBracket_mixed_mixed, msBracket_mixed_g2]
      simp only [magicMixedToG2LM_tmul, magicMixedToMixedLM_tmul, magicMixedToF4LM_tmul,
        magicG2MixedActLM_tmul, map_add, map_neg, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, magicInvBilin_apply,
        msEmbedG2LM_g2, msEmbedG2LM_mixed, msEmbedG2LM_f4,
        msEmbedMixed_g2, msEmbedMixed_mixed, msEmbedMixed_f4,
        msEmbedF4LM_g2, msEmbedF4LM_mixed, msEmbedF4LM_f4,
        map_zero, LinearMap.zero_apply, magicMixedBilin_tmul,
        O.g2Bilin_inner_eq D c a]
      have hsk := O.bilin_deriv_skew D c a
      have hsym : O.bilin₀ a (O.act D c) = O.bilin₀ (O.act D c) a := O.bilin_symm _ _
      have htsym : J.traceBilin₀ x z = J.traceBilin₀ z x := J.traceBilin_symm _ _
      rw [hsym, htsym]
      have hmul : (O.bilin₀ (O.act D c) a + O.bilin₀ c (O.act D a)) * J.traceBilin₀ z x = 0 := by
        rw [hsk, zero_mul]
      linarith [hmul]
  have h2 : ∀ (F : F₄) (m : O₀ ⊗[ℝ] J₀),
      magicInvBilin O J ⁅msEmbedTensor O J c z, msEmbedMixed O J m⁆ (msEmbedF4LM O J F) +
        magicInvBilin O J (msEmbedMixed O J m) ⁅msEmbedTensor O J c z, msEmbedF4LM O J F⁆ = 0 := by
    intro F m
    induction m using TensorProduct.inductionOn with
    | add u₁ u₂ ih₁ ih₂ =>
      simp only [map_add, lie_add, LinearMap.add_apply] at ih₁ ih₂ ⊢; linarith
    | tmul a x =>
      change magicInvBilin O J (magicSquareBracketLM O J (msEmbedMixed O J (c ⊗ₜ[ℝ] z))
          (msEmbedMixed O J (a ⊗ₜ[ℝ] x))) (msEmbedF4LM O J F) +
        magicInvBilin O J (msEmbedMixed O J (a ⊗ₜ[ℝ] x))
          (magicSquareBracketLM O J (msEmbedMixed O J (c ⊗ₜ[ℝ] z)) (msEmbedF4LM O J F)) = 0
      rw [msBracket_mixed_mixed, msBracket_mixed_f4]
      simp only [magicMixedToG2LM_tmul, magicMixedToMixedLM_tmul, magicMixedToF4LM_tmul,
        magicF4MixedActLM_tmul, map_add, map_neg, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, magicInvBilin_apply,
        msEmbedG2LM_g2, msEmbedG2LM_mixed, msEmbedG2LM_f4,
        msEmbedMixed_g2, msEmbedMixed_mixed, msEmbedMixed_f4,
        msEmbedF4LM_g2, msEmbedF4LM_mixed, msEmbedF4LM_f4,
        map_zero, LinearMap.zero_apply, magicMixedBilin_tmul,
        J.f4Bilin_inner_eq F z x]
      have hsk := J.traceBilin_deriv_skew F z x
      have hsym : J.traceBilin₀ x (J.act F z) = J.traceBilin₀ (J.act F z) x :=
        J.traceBilin_symm _ _
      have hobsym : O.bilin₀ a c = O.bilin₀ c a := O.bilin_symm _ _
      rw [hsym, hobsym]
      have hmul : O.bilin₀ c a * (J.traceBilin₀ (J.act F z) x + J.traceBilin₀ z (J.act F x)) = 0 := by
        rw [hsk, mul_zero]
      linarith [hmul]
  have h3 : ∀ m₁ m₂ : O₀ ⊗[ℝ] J₀,
      magicInvBilin O J ⁅msEmbedTensor O J c z, msEmbedMixed O J m₁⁆ (msEmbedMixed O J m₂) +
        magicInvBilin O J (msEmbedMixed O J m₁) ⁅msEmbedTensor O J c z, msEmbedMixed O J m₂⁆ = 0 := by
    intro m₁ m₂
    induction m₁ using TensorProduct.inductionOn with
    | add u₁ u₂ ih₁ ih₂ =>
      simp only [map_add, lie_add, LinearMap.add_apply] at ih₁ ih₂ ⊢; linarith
    | tmul a x =>
      induction m₂ using TensorProduct.inductionOn with
      | add v₁ v₂ ih₁ ih₂ =>
        simp only [map_add, lie_add] at ih₁ ih₂ ⊢; linarith
      | tmul b y =>
        change magicInvBilin O J (magicSquareBracketLM O J (msEmbedMixed O J (c ⊗ₜ[ℝ] z))
            (msEmbedMixed O J (a ⊗ₜ[ℝ] x))) (msEmbedMixed O J (b ⊗ₜ[ℝ] y)) +
          magicInvBilin O J (msEmbedMixed O J (a ⊗ₜ[ℝ] x))
            (magicSquareBracketLM O J (msEmbedMixed O J (c ⊗ₜ[ℝ] z))
              (msEmbedMixed O J (b ⊗ₜ[ℝ] y))) = 0
        rw [msBracket_mixed_mixed, msBracket_mixed_mixed]
        simp only [magicMixedToG2LM_tmul, magicMixedToMixedLM_tmul, magicMixedToF4LM_tmul,
          magicInvBilin_apply, map_add, LinearMap.add_apply,
          msEmbedG2LM_g2, msEmbedG2LM_mixed, msEmbedG2LM_f4,
          msEmbedMixed_g2, msEmbedMixed_mixed, msEmbedMixed_f4,
          msEmbedF4LM_g2, msEmbedF4LM_mixed, msEmbedF4LM_f4,
          map_zero, LinearMap.zero_apply, magicMixedBilin_tmul]
        have hcycO : O.bilin₀ (O.comm₀ c a) b + O.bilin₀ a (O.comm₀ c b) = 0 := by
          have hc1 := O.bilin_comm_cyclic b c a
          have hs1 : O.bilin₀ b (O.comm₀ c a) = O.bilin₀ (O.comm₀ c a) b := O.bilin_symm _ _
          have hc3 : O.bilin₀ c (O.comm₀ a b) = O.bilin₀ a (O.comm₀ b c) :=
            O.bilin_comm_cyclic c a b
          have hsk2 : O.comm₀ b c = -O.comm₀ c b := O.comm_skew c b
          rw [hsk2, map_neg] at hc3
          linarith [hs1, hc1, hc3]
        have hcycJ : J.traceBilin₀ (J.mul₀ z x) y = J.traceBilin₀ x (J.mul₀ z y) := by
          have hc1 := J.traceBilin_mul_cyclic y z x
          have hs1 : J.traceBilin₀ y (J.mul₀ z x) = J.traceBilin₀ (J.mul₀ z x) y :=
            J.traceBilin_symm _ _
          rw [← hs1, hc1, J.traceBilin_mul_cyclic z x y, J.mul_comm z y]
        rw [hcycJ]
        have hmul : (O.bilin₀ (O.comm₀ c a) b + O.bilin₀ a (O.comm₀ c b)) *
            J.traceBilin₀ x (J.mul₀ z y) = 0 := by
          rw [hcycO, zero_mul]
        linarith [hmul]
  have h1' : ∀ (D : G₂) (m : O₀ ⊗[ℝ] J₀),
      magicInvBilin O J ⁅msEmbedTensor O J c z, msEmbedG2LM O J D⁆ (msEmbedMixed O J m) +
        magicInvBilin O J (msEmbedG2LM O J D) ⁅msEmbedTensor O J c z, msEmbedMixed O J m⁆ = 0 := by
    intro D m
    rw [magicInvBilin_symm _ (msEmbedMixed O J m), magicInvBilin_symm (msEmbedG2LM O J D) _]
    linarith [h1 D m]
  have h2' : ∀ (F : F₄) (m : O₀ ⊗[ℝ] J₀),
      magicInvBilin O J ⁅msEmbedTensor O J c z, msEmbedF4LM O J F⁆ (msEmbedMixed O J m) +
        magicInvBilin O J (msEmbedF4LM O J F) ⁅msEmbedTensor O J c z, msEmbedMixed O J m⁆ = 0 := by
    intro F m
    rw [magicInvBilin_symm _ (msEmbedMixed O J m), magicInvBilin_symm (msEmbedF4LM O J F) _]
    linarith [h2 F m]
  have h0_gg : ∀ (D₁ D₂ : G₂),
      magicInvBilin O J ⁅msEmbedTensor O J c z, msEmbedG2LM O J D₁⁆ (msEmbedG2LM O J D₂) +
        magicInvBilin O J (msEmbedG2LM O J D₁) ⁅msEmbedTensor O J c z, msEmbedG2LM O J D₂⁆ = 0 := by
    intro D₁ D₂
    change magicInvBilin O J (magicSquareBracketLM O J (msEmbedMixed O J (c ⊗ₜ[ℝ] z))
        (msEmbedG2LM O J D₁)) (msEmbedG2LM O J D₂) +
      magicInvBilin O J (msEmbedG2LM O J D₁)
        (magicSquareBracketLM O J (msEmbedMixed O J (c ⊗ₜ[ℝ] z)) (msEmbedG2LM O J D₂)) = 0
    simp [msBracket_mixed_g2, magicInvBilin_apply]
  have h0_gf : ∀ (D : G₂) (F : F₄),
      magicInvBilin O J ⁅msEmbedTensor O J c z, msEmbedG2LM O J D⁆ (msEmbedF4LM O J F) +
        magicInvBilin O J (msEmbedG2LM O J D) ⁅msEmbedTensor O J c z, msEmbedF4LM O J F⁆ = 0 := by
    intro D F
    change magicInvBilin O J (magicSquareBracketLM O J (msEmbedMixed O J (c ⊗ₜ[ℝ] z))
        (msEmbedG2LM O J D)) (msEmbedF4LM O J F) +
      magicInvBilin O J (msEmbedG2LM O J D)
        (magicSquareBracketLM O J (msEmbedMixed O J (c ⊗ₜ[ℝ] z)) (msEmbedF4LM O J F)) = 0
    simp [msBracket_mixed_g2, msBracket_mixed_f4, magicInvBilin_apply]
  have h0_fg : ∀ (F : F₄) (D : G₂),
      magicInvBilin O J ⁅msEmbedTensor O J c z, msEmbedF4LM O J F⁆ (msEmbedG2LM O J D) +
        magicInvBilin O J (msEmbedF4LM O J F) ⁅msEmbedTensor O J c z, msEmbedG2LM O J D⁆ = 0 := by
    intro F D
    rw [magicInvBilin_symm _ (msEmbedG2LM O J D), magicInvBilin_symm (msEmbedF4LM O J F) _]
    linarith [h0_gf D F]
  have h0_ff : ∀ (F₁ F₂ : F₄),
      magicInvBilin O J ⁅msEmbedTensor O J c z, msEmbedF4LM O J F₁⁆ (msEmbedF4LM O J F₂) +
        magicInvBilin O J (msEmbedF4LM O J F₁) ⁅msEmbedTensor O J c z, msEmbedF4LM O J F₂⁆ = 0 := by
    intro F₁ F₂
    change magicInvBilin O J (magicSquareBracketLM O J (msEmbedMixed O J (c ⊗ₜ[ℝ] z))
        (msEmbedF4LM O J F₁)) (msEmbedF4LM O J F₂) +
      magicInvBilin O J (msEmbedF4LM O J F₁)
        (magicSquareBracketLM O J (msEmbedMixed O J (c ⊗ₜ[ℝ] z)) (msEmbedF4LM O J F₂)) = 0
    simp [msBracket_mixed_f4, magicInvBilin_apply]
  conv_lhs => rw [hsplit X, hsplit Y]
  simp only [lie_add, map_add, LinearMap.add_apply]
  linarith [h0_gg X.g2 Y.g2, h1' X.g2 Y.mixed, h0_gf X.g2 Y.f4,
    h1 Y.g2 X.mixed, h3 X.mixed Y.mixed, h2 Y.f4 X.mixed,
    h0_fg X.f4 Y.g2, h2' X.f4 Y.mixed, h0_ff X.f4 Y.f4]

/-- `ad`-invariance of the `(3, -6, 1)` bilinear form `magicInvBilin O J`. -/
theorem magicInvBilin_lieInvariant (Z X Y : MagicSquareLie O J) :
    magicInvBilin O J ⁅Z, X⁆ Y + magicInvBilin O J X ⁅Z, Y⁆ = 0 := by
  have hZ : Z = msEmbedG2LM O J Z.g2 + msEmbedMixed O J Z.mixed + msEmbedF4LM O J Z.f4 := by
    apply MagicSquareLie.ext <;> simp
  have hmix : ∀ m : O₀ ⊗[ℝ] J₀,
      magicInvBilin O J ⁅msEmbedMixed O J m, X⁆ Y +
        magicInvBilin O J X ⁅msEmbedMixed O J m, Y⁆ = 0 := by
    intro m
    induction m using TensorProduct.inductionOn with
    | add u₁ u₂ ih₁ ih₂ =>
      simp only [map_add, add_lie, LinearMap.add_apply] at ih₁ ih₂ ⊢; linarith
    | tmul c z => exact magicInvBilin_lieInvariant_mixed_tmul c z X Y
  rw [hZ]
  simp only [add_lie, map_add, LinearMap.add_apply]
  linarith [magicInvBilin_lieInvariant_g2 Z.g2 X Y, hmix Z.mixed,
    magicInvBilin_lieInvariant_f4 Z.f4 X Y]

end MagicSquareInstances

end GenericMagicSquare

/-! ## 2. Concrete Magic Data, `CompactE8Lie`, `QuaternionicE8Lie`, and `SplitE8Lie` Invariant Form -/

section ConcreteDataAndCarriers

section H3Octonion26D

open H3Octonion

/-- Trace-zero projection `H3Octonion ℝ →ₗ[ℝ] h3OctonionTraceZero`. -/
def h3OctProj0 : H3Octonion ℝ →ₗ[ℝ] h3OctonionTraceZero where
  toFun x := ⟨x - ((1 / 3 : ℝ) * linearTrace x) • (1 : H3Octonion ℝ), by
    change linearTrace (x - ((1 / 3 : ℝ) * linearTrace x) • (1 : H3Octonion ℝ)) = 0
    rw [linearTrace_sub, linearTrace_smul, linearTrace_one]
    ring⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, linearTrace_add]
    module
  map_smul' r x := by
    apply Subtype.ext
    simp only [SetLike.val_smul, linearTrace_smul, RingHom.id_apply]
    module

@[simp] theorem h3OctProj0_coe (x : H3Octonion ℝ) :
    (h3OctProj0 x : H3Octonion ℝ) = x - ((1 / 3 : ℝ) * linearTrace x) • (1 : H3Octonion ℝ) := rfl

theorem h3OctProj0_of_mem (x : h3OctonionTraceZero) : h3OctProj0 x.1 = x := by
  apply Subtype.ext
  have hx : linearTrace x.1 = 0 := x.2
  simp [hx]

theorem h3OctProj0_smul_one (r : ℝ) : h3OctProj0 (r • (1 : H3Octonion ℝ)) = 0 := by
  apply Subtype.ext
  simp only [h3OctProj0_coe, linearTrace_smul, linearTrace_one, Submodule.coe_zero]
  module

/-- Traceless Jordan product `x *₀ y` on `h3OctonionTraceZero`. -/
def h3OctMul0 (x y : h3OctonionTraceZero) : h3OctonionTraceZero :=
  ⟨x.1 * y.1 - ((1 / 3 : ℝ) * traceBilin x.1 y.1) • (1 : H3Octonion ℝ), by
    change linearTrace (x.1 * y.1 - ((1 / 3 : ℝ) * traceBilin x.1 y.1) • (1 : H3Octonion ℝ)) = 0
    rw [linearTrace_sub, linearTrace_smul, linearTrace_one, linearTrace_jordanMul]
    ring⟩

@[simp] theorem h3OctMul0_coe (x y : h3OctonionTraceZero) :
    (h3OctMul0 x y : H3Octonion ℝ) =
      x.1 * y.1 - ((1 / 3 : ℝ) * traceBilin x.1 y.1) • (1 : H3Octonion ℝ) := rfl

theorem h3OctMul0_eq_proj0 (x y : h3OctonionTraceZero) :
    h3OctMul0 x y = h3OctProj0 (x.1 * y.1) := by
  apply Subtype.ext
  simp [h3OctMul0_coe, h3OctProj0_coe, linearTrace_jordanMul]

def h3OctMul0LM : h3OctonionTraceZero →ₗ[ℝ] h3OctonionTraceZero →ₗ[ℝ] h3OctonionTraceZero :=
  LinearMap.mk₂ ℝ h3OctMul0
    (fun _ _ _ => by apply Subtype.ext; simp only [h3OctMul0_coe, Submodule.coe_add, add_mul,
      traceBilin_add_left]; module)
    (fun _ _ _ => by apply Subtype.ext; simp only [h3OctMul0_coe, SetLike.val_smul, smul_mul_assoc,
      traceBilin_smul_left]; module)
    (fun _ _ _ => by apply Subtype.ext; simp only [h3OctMul0_coe, Submodule.coe_add, mul_add,
      traceBilin_add_right]; module)
    (fun _ _ _ => by apply Subtype.ext; simp only [h3OctMul0_coe, SetLike.val_smul, mul_smul_comm,
      traceBilin_smul_right]; module)

theorem h3OctMul0_comm (x y : h3OctonionTraceZero) : h3OctMul0 x y = h3OctMul0 y x := by
  apply Subtype.ext
  simp only [h3OctMul0_coe, H3Octonion.mul_comm x.1 y.1, H3Octonion.traceBilin_symm x.1 y.1]

/-- Action of `H3OctonionF4Derivations` on `h3OctonionTraceZero`. -/
def h3OctF4Act (D : H3OctonionF4Derivations) (x : h3OctonionTraceZero) : h3OctonionTraceZero :=
  ⟨D.1 x.1, h3Octonion_derivation_linearTrace_zero D x.1⟩

@[simp] theorem h3OctF4Act_coe (D : H3OctonionF4Derivations) (x : h3OctonionTraceZero) :
    (h3OctF4Act D x : H3Octonion ℝ) = D.1 x.1 := rfl

def h3OctF4ActLM :
    H3OctonionF4Derivations →ₗ[ℝ] h3OctonionTraceZero →ₗ[ℝ] h3OctonionTraceZero :=
  LinearMap.mk₂ ℝ h3OctF4Act
    (fun _ _ _ => by apply Subtype.ext; rfl)
    (fun _ _ _ => by apply Subtype.ext; rfl)
    (fun D x₁ x₂ => by apply Subtype.ext; exact D.1.map_add x₁.1 x₂.1)
    (fun r D x => by apply Subtype.ext; exact D.1.map_smul r x.1)

/-- Inner Jordan derivation `[L_x, L_y]` in `H3OctonionF4Derivations`. -/
def h3OctF4Inner (x y : h3OctonionTraceZero) : H3OctonionF4Derivations :=
  h3OctonionJordanInnerDerivation x.1 y.1

def h3OctF4InnerLM :
    h3OctonionTraceZero →ₗ[ℝ] h3OctonionTraceZero →ₗ[ℝ] H3OctonionF4Derivations :=
  LinearMap.mk₂ ℝ h3OctF4Inner
    (fun x₁ x₂ y => by
      apply Subtype.ext; apply LinearMap.ext; intro z
      change (x₁.1 + x₂.1) * (y.1 * z) - y.1 * ((x₁.1 + x₂.1) * z) =
        (x₁.1 * (y.1 * z) - y.1 * (x₁.1 * z)) + (x₂.1 * (y.1 * z) - y.1 * (x₂.1 * z))
      simp only [add_mul, mul_add]; abel)
    (fun r x y => by
      apply Subtype.ext; apply LinearMap.ext; intro z
      change (r • x.1) * (y.1 * z) - y.1 * ((r • x.1) * z) =
        r • (x.1 * (y.1 * z) - y.1 * (x.1 * z))
      simp only [smul_mul_assoc, mul_smul_comm]; module)
    (fun x y₁ y₂ => by
      apply Subtype.ext; apply LinearMap.ext; intro z
      change x.1 * ((y₁.1 + y₂.1) * z) - (y₁.1 + y₂.1) * (x.1 * z) =
        (x.1 * (y₁.1 * z) - y₁.1 * (x.1 * z)) + (x.1 * (y₂.1 * z) - y₂.1 * (x.1 * z))
      simp only [mul_add, add_mul]; abel)
    (fun r x y => by
      apply Subtype.ext; apply LinearMap.ext; intro z
      change x.1 * ((r • y.1) * z) - (r • y.1) * (x.1 * z) =
        r • (x.1 * (y.1 * z) - y.1 * (x.1 * z))
      simp only [mul_smul_comm, smul_mul_assoc]; module)

theorem h3OctF4Inner_antisymm (x y : h3OctonionTraceZero) :
    h3OctF4Inner y x = -h3OctF4Inner x y := by
  apply Subtype.ext; apply LinearMap.ext; intro z
  change y.1 * (x.1 * z) - x.1 * (y.1 * z) = -(x.1 * (y.1 * z) - y.1 * (x.1 * z))
  abel

def h3OctTraceBilin0LM : h3OctonionTraceZero →ₗ[ℝ] h3OctonionTraceZero →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => traceBilin x.1 y.1)
    (fun x₁ x₂ y => traceBilin_add_left x₁.1 x₂.1 y.1)
    (fun r x y => traceBilin_smul_left r x.1 y.1)
    (fun x y₁ y₂ => traceBilin_add_right x.1 y₁.1 y₂.1)
    (fun r x y => traceBilin_smul_right r x.1 y.1)

theorem h3Oct_traceBilin_mul_cyclic (x y z : h3OctonionTraceZero) :
    traceBilin x.1 (h3OctMul0 y z).1 = traceBilin y.1 (h3OctMul0 z x).1 := by
  have hsimp : ∀ u v w : h3OctonionTraceZero,
      traceBilin u.1 (h3OctMul0 v w).1 = traceBilin u.1 (v.1 * w.1) := by
    intro u v w
    simp only [h3OctMul0_coe, traceBilin_sub_right, traceBilin_smul_right, traceBilin_one]
    have hu : linearTrace u.1 = 0 := u.2
    rw [hu]; ring
  rw [hsimp x y z, hsimp y z x]
  calc traceBilin x.1 (y.1 * z.1)
      = traceBilin (y.1 * z.1) x.1 := H3Octonion.traceBilin_symm _ _
    _ = traceBilin z.1 (y.1 * x.1) := h3Octonion_traceBilin_jordanLmul_assoc y.1 z.1 x.1
    _ = traceBilin (y.1 * x.1) z.1 := H3Octonion.traceBilin_symm _ _
    _ = traceBilin (x.1 * y.1) z.1 := by rw [H3Octonion.mul_comm y.1 x.1]
    _ = traceBilin y.1 (x.1 * z.1) := h3Octonion_traceBilin_jordanLmul_assoc x.1 y.1 z.1
    _ = traceBilin y.1 (z.1 * x.1) := by rw [H3Octonion.mul_comm x.1 z.1]

theorem h3OctF4Act_mul0 (D : H3OctonionF4Derivations) (x y : h3OctonionTraceZero) :
    h3OctF4Act D (h3OctMul0 x y) = h3OctMul0 (h3OctF4Act D x) y + h3OctMul0 x (h3OctF4Act D y) := by
  apply Subtype.ext
  simp only [h3OctF4Act_coe, h3OctMul0_coe, Submodule.coe_add]
  have h1 : D.1 (1 : H3Octonion ℝ) = 0 := h3Octonion_derivation_apply_one_eq_zero D
  have htb := h3Octonion_derivation_traceBilin_skew D x.1 y.1
  rw [D.1.map_sub, D.2 x.1 y.1, map_smul, h1, smul_zero, sub_zero]
  have hcoef : ((1 / 3 : ℝ) * traceBilin (D.1 x.1) y.1 +
      (1 / 3 : ℝ) * traceBilin x.1 (D.1 y.1)) = 0 := by linarith
  have hzero : (((1 / 3 : ℝ) * traceBilin (D.1 x.1) y.1) • (1 : H3Octonion ℝ) +
      ((1 / 3 : ℝ) * traceBilin x.1 (D.1 y.1)) • (1 : H3Octonion ℝ)) = 0 := by
    rw [← add_smul, hcoef, zero_smul]
  have hsub : D.1 x.1 * y.1 - ((1 / 3 : ℝ) * traceBilin (D.1 x.1) y.1) • (1 : H3Octonion ℝ) +
      (x.1 * D.1 y.1 - ((1 / 3 : ℝ) * traceBilin x.1 (D.1 y.1)) • (1 : H3Octonion ℝ)) =
      D.1 x.1 * y.1 + x.1 * D.1 y.1 -
        (((1 / 3 : ℝ) * traceBilin (D.1 x.1) y.1) • (1 : H3Octonion ℝ) +
          ((1 / 3 : ℝ) * traceBilin x.1 (D.1 y.1)) • (1 : H3Octonion ℝ)) := by abel
  rw [hsub, hzero, sub_zero]

theorem h3OctF4_covariant (D : H3OctonionF4Derivations) (x y : h3OctonionTraceZero) :
    ⁅D, h3OctF4Inner x y⁆ = h3OctF4Inner (h3OctF4Act D x) y + h3OctF4Inner x (h3OctF4Act D y) := by
  apply Subtype.ext; apply LinearMap.ext; intro z
  have h1' : D.1 (x.1 * z) - x.1 * D.1 z = D.1 x.1 * z :=
    congrArg (fun f : Module.End ℝ (H3Octonion ℝ) => f z)
      (lie_derivation_jordanLmul D.1 D.2 x.1)
  have h2' : D.1 (y.1 * z) - y.1 * D.1 z = D.1 y.1 * z :=
    congrArg (fun f : Module.End ℝ (H3Octonion ℝ) => f z)
      (lie_derivation_jordanLmul D.1 D.2 y.1)
  have h3' : D.1 (x.1 * (y.1 * z)) - x.1 * D.1 (y.1 * z) = D.1 x.1 * (y.1 * z) :=
    congrArg (fun f : Module.End ℝ (H3Octonion ℝ) => f (y.1 * z))
      (lie_derivation_jordanLmul D.1 D.2 x.1)
  have h4' : D.1 (y.1 * (x.1 * z)) - y.1 * D.1 (x.1 * z) = D.1 y.1 * (x.1 * z) :=
    congrArg (fun f : Module.End ℝ (H3Octonion ℝ) => f (x.1 * z))
      (lie_derivation_jordanLmul D.1 D.2 y.1)
  have h1mul : y.1 * (D.1 (x.1 * z) - x.1 * D.1 z) = y.1 * (D.1 x.1 * z) :=
    congrArg (fun w => y.1 * w) h1'
  have h2mul : x.1 * (D.1 (y.1 * z) - y.1 * D.1 z) = x.1 * (D.1 y.1 * z) :=
    congrArg (fun w => x.1 * w) h2'
  rw [mul_sub] at h1mul h2mul
  have hDx : D.1 (x.1 * (y.1 * z)) = D.1 x.1 * (y.1 * z) + x.1 * D.1 (y.1 * z) :=
    eq_add_of_sub_eq' (by rw [← h3']; abel)
  have hDy : D.1 (y.1 * (x.1 * z)) = D.1 y.1 * (x.1 * z) + y.1 * D.1 (x.1 * z) :=
    eq_add_of_sub_eq' (by rw [← h4']; abel)
  have hxy : x.1 * (y.1 * D.1 z) = x.1 * D.1 (y.1 * z) - x.1 * (D.1 y.1 * z) :=
    eq_sub_of_add_eq (by rw [← h2mul]; abel)
  have hyx : y.1 * (x.1 * D.1 z) = y.1 * D.1 (x.1 * z) - y.1 * (D.1 x.1 * z) :=
    eq_sub_of_add_eq (by rw [← h1mul]; abel)
  change D.1 (x.1 * (y.1 * z) - y.1 * (x.1 * z)) -
      (x.1 * (y.1 * D.1 z) - y.1 * (x.1 * D.1 z)) =
    (D.1 x.1 * (y.1 * z) - y.1 * (D.1 x.1 * z)) +
      (x.1 * (D.1 y.1 * z) - D.1 y.1 * (x.1 * z))
  rw [D.1.map_sub, hDx, hDy, hxy, hyx]; abel

theorem h3OctF4Inner_mul_cyclic_zero (x y z : h3OctonionTraceZero) :
    h3OctF4Inner x (h3OctMul0 y z) + h3OctF4Inner y (h3OctMul0 z x) +
      h3OctF4Inner z (h3OctMul0 x y) = 0 := by
  apply Subtype.ext; apply LinearMap.ext; intro w
  have hone (a : H3Octonion ℝ) :
      (h3OctonionJordanInnerDerivation a 1 : Module.End ℝ (H3Octonion ℝ)) w = 0 := by
    simp only [h3OctonionJordanInnerDerivation_apply, one_mul_h3Octonion, sub_self]
  have hdrop (u v p : h3OctonionTraceZero) :
      (h3OctF4Inner u (h3OctMul0 v p) : Module.End ℝ (H3Octonion ℝ)) w =
        (h3OctonionJordanInnerDerivation u.1 (v.1 * p.1) : Module.End ℝ (H3Octonion ℝ)) w := by
    change u.1 * ((v.1 * p.1 - ((1 / 3 : ℝ) * traceBilin v.1 p.1) • (1 : H3Octonion ℝ)) * w) -
        (v.1 * p.1 - ((1 / 3 : ℝ) * traceBilin v.1 p.1) • (1 : H3Octonion ℝ)) * (u.1 * w) =
      u.1 * (v.1 * p.1 * w) - (v.1 * p.1) * (u.1 * w)
    rw [sub_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
    have hw := hone u.1
    simp only [h3OctonionJordanInnerDerivation_apply] at hw
    have hsub :
        (u.1 * (v.1 * p.1 * w) - ((1 / 3 : ℝ) * traceBilin v.1 p.1) • (u.1 * (1 * w))) -
          (v.1 * p.1 * (u.1 * w) - ((1 / 3 : ℝ) * traceBilin v.1 p.1) • (1 * (u.1 * w))) =
        (u.1 * (v.1 * p.1 * w) - v.1 * p.1 * (u.1 * w)) -
          ((1 / 3 : ℝ) * traceBilin v.1 p.1) • (u.1 * (1 * w) - 1 * (u.1 * w)) := by module
    rw [hsub, hw, smul_zero, sub_zero]
  change (h3OctF4Inner x (h3OctMul0 y z) : Module.End ℝ (H3Octonion ℝ)) w +
      (h3OctF4Inner y (h3OctMul0 z x) : Module.End ℝ (H3Octonion ℝ)) w +
      (h3OctF4Inner z (h3OctMul0 x y) : Module.End ℝ (H3Octonion ℝ)) w = 0
  rw [hdrop x y z, hdrop y z x, hdrop z x y]
  have hJ := two_nsmul_lie_lmul_lmul_add_add_eq_zero x.1 y.1 z.1
  rw [two_nsmul] at hJ
  have hJw := congrArg (fun f : AddMonoid.End (H3Octonion ℝ) => f w) hJ
  change (x.1 * ((y.1 * z.1) * w) - (y.1 * z.1) * (x.1 * w) +
      (y.1 * ((z.1 * x.1) * w) - (z.1 * x.1) * (y.1 * w)) +
      (z.1 * ((x.1 * y.1) * w) - (x.1 * y.1) * (z.1 * w))) +
      (x.1 * ((y.1 * z.1) * w) - (y.1 * z.1) * (x.1 * w) +
      (y.1 * ((z.1 * x.1) * w) - (z.1 * x.1) * (y.1 * w)) +
      (z.1 * ((x.1 * y.1) * w) - (x.1 * y.1) * (z.1 * w))) = 0 at hJw
  have h2r : (2 : ℝ) •
      ((x.1 * (y.1 * z.1 * w) - (y.1 * z.1) * (x.1 * w)) +
        (y.1 * (z.1 * x.1 * w) - (z.1 * x.1) * (y.1 * w)) +
        (z.1 * (x.1 * y.1 * w) - (x.1 * y.1) * (z.1 * w))) = 0 := by
    rw [two_smul]; exact hJw
  exact (smul_eq_zero.mp h2r).resolve_left (by norm_num)

theorem h3OctProj0_cube (w : h3OctonionTraceZero) :
    h3OctProj0 (w.1 * (w.1 * w.1)) = ((1 / 2 : ℝ) * traceBilin w.1 w.1) • w := by
  have hw : linearTrace w.1 = 0 := w.2
  have hsq : w.1 * w.1 =
      ((1 / 2 : ℝ) * traceBilin w.1 w.1) • (1 : H3Octonion ℝ) + adjointQuad w.1 := by
    have h1 := h3octonion_mul_self_eq_adjoint w.1
    have hm := mccrimmon_identity_16 w.1 w.1
    rw [hw, zero_mul, zero_sub, crossProduct_self, linearTrace_smul] at hm
    have hadj : linearTrace (adjointQuad w.1) = -(1 / 2 : ℝ) * traceBilin w.1 w.1 := by linarith
    rw [hw, zero_smul, zero_sub, hadj] at h1
    rw [h1]; module
  have hcube : w.1 * (w.1 * w.1) =
      ((1 / 2 : ℝ) * traceBilin w.1 w.1) • w.1 + normCubic w.1 • (1 : H3Octonion ℝ) := by
    rw [hsq, mul_add, mul_smul_comm, h3Octonion_mul_one, h3octonion_jordan_mul_adjoint_eq_norm_one]
  rw [hcube, map_add, h3OctProj0_smul_one, add_zero, map_smul, h3OctProj0_of_mem w]

private theorem symmetric_trilinear_h3OctonionTraceZero_eq_zero
    (F : h3OctonionTraceZero →ₗ[ℝ] h3OctonionTraceZero →ₗ[ℝ]
      h3OctonionTraceZero →ₗ[ℝ] h3OctonionTraceZero)
    (h12 : ∀ x y z, F x y z = F y x z)
    (h23 : ∀ x y z, F x y z = F x z y)
    (hdiag : ∀ w, F w w w = 0) (x y z : h3OctonionTraceZero) : F x y z = 0 := by
  have h13 (a b c : h3OctonionTraceZero) : F a b c = F c b a := by rw [h12, h23, h12]
  have hpol : (6 : ℝ) • F x y z =
      F (x + y + z) (x + y + z) (x + y + z) -
      F (x + y) (x + y) (x + y) - F (x + z) (x + z) (x + z) -
      F (y + z) (y + z) (y + z) + F x x x + F y y y + F z z z := by
    simp only [map_add, LinearMap.add_apply]
    rw [h12 y x x, h23 x x y, h23 y y x, h12 y x y,
      h12 z x x, h23 x x z, h23 z z x, h12 z x z,
      h12 z y y, h23 y y z, h23 z z y, h12 z y z,
      h23 y z x, h12 y x z, h12 z x y, h23 x z y,
      h13 z y x]
    module
  rw [hdiag, hdiag, hdiag, hdiag, hdiag, hdiag, hdiag] at hpol
  simp only [sub_zero, add_zero] at hpol
  exact (smul_eq_zero.mp hpol).resolve_left (by norm_num)

theorem h3OctProj0_cyclic_cube_polarized (x y z : h3OctonionTraceZero) :
    (1 / 3 : ℝ) • h3OctProj0 (x.1 * (y.1 * z.1) + y.1 * (z.1 * x.1) + z.1 * (x.1 * y.1)) =
      (1 / 6 : ℝ) • (traceBilin y.1 z.1 • x + traceBilin z.1 x.1 • y +
        traceBilin x.1 y.1 • z) := by
  let qFun (a b c : h3OctonionTraceZero) : h3OctonionTraceZero :=
    (1 / 3 : ℝ) • h3OctProj0 (a.1 * (b.1 * c.1) + b.1 * (c.1 * a.1) + c.1 * (a.1 * b.1)) -
      (1 / 6 : ℝ) • (traceBilin b.1 c.1 • a + traceBilin c.1 a.1 • b + traceBilin a.1 b.1 • c)
  have h3Proj0_val_add : ∀ u v : H3Octonion ℝ,
      ((h3OctProj0 (u + v) : h3OctonionTraceZero) : H3Octonion ℝ) =
        (h3OctProj0 u : H3Octonion ℝ) + (h3OctProj0 v : H3Octonion ℝ) :=
    fun u v => congrArg Subtype.val (h3OctProj0.map_add u v)
  have h3Proj0_val_smul : ∀ (r : ℝ) (u : H3Octonion ℝ),
      ((h3OctProj0 (r • u) : h3OctonionTraceZero) : H3Octonion ℝ) = r • (h3OctProj0 u : H3Octonion ℝ) :=
    fun r u => congrArg Subtype.val (h3OctProj0.map_smul r u)
  let Q : h3OctonionTraceZero →ₗ[ℝ] h3OctonionTraceZero →ₗ[ℝ]
      h3OctonionTraceZero →ₗ[ℝ] h3OctonionTraceZero :=
    { toFun := fun a =>
        { toFun := fun b =>
            { toFun := fun c => qFun a b c
              map_add' := fun c₁ c₂ => by
                apply Subtype.ext
                simp only [qFun, Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul,
                  mul_add, add_mul, traceBilin_add_right, traceBilin_add_left]
                have hlin : a.1 * (b.1 * c₁.1) + a.1 * (b.1 * c₂.1) +
                    (b.1 * (c₁.1 * a.1) + b.1 * (c₂.1 * a.1)) +
                    (c₁.1 * (a.1 * b.1) + c₂.1 * (a.1 * b.1)) =
                    (a.1 * (b.1 * c₁.1) + b.1 * (c₁.1 * a.1) + c₁.1 * (a.1 * b.1)) +
                    (a.1 * (b.1 * c₂.1) + b.1 * (c₂.1 * a.1) + c₂.1 * (a.1 * b.1)) := by abel
                rw [hlin, h3Proj0_val_add]; module
              map_smul' := fun r c => by
                apply Subtype.ext
                simp only [qFun, Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul,
                  RingHom.id_apply, mul_smul_comm, smul_mul_assoc,
                  traceBilin_smul_right, traceBilin_smul_left]
                have hlin : r • (a.1 * (b.1 * c.1)) + r • (b.1 * (c.1 * a.1)) +
                    r • (c.1 * (a.1 * b.1)) =
                    r • (a.1 * (b.1 * c.1) + b.1 * (c.1 * a.1) + c.1 * (a.1 * b.1)) := by module
                rw [hlin, h3Proj0_val_smul]; module }
          map_add' := fun b₁ b₂ => by
            apply LinearMap.ext; intro c; apply Subtype.ext
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, qFun,
              Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul,
              mul_add, add_mul, traceBilin_add_left, traceBilin_add_right]
            have hlin : a.1 * (b₁.1 * c.1) + a.1 * (b₂.1 * c.1) +
                (b₁.1 * (c.1 * a.1) + b₂.1 * (c.1 * a.1)) +
                (c.1 * (a.1 * b₁.1) + c.1 * (a.1 * b₂.1)) =
                (a.1 * (b₁.1 * c.1) + b₁.1 * (c.1 * a.1) + c.1 * (a.1 * b₁.1)) +
                (a.1 * (b₂.1 * c.1) + b₂.1 * (c.1 * a.1) + c.1 * (a.1 * b₂.1)) := by abel
            rw [hlin, h3Proj0_val_add]; module
          map_smul' := fun r b => by
            apply LinearMap.ext; intro c; apply Subtype.ext
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, qFun,
              Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul, RingHom.id_apply,
              mul_smul_comm, smul_mul_assoc, traceBilin_smul_left, traceBilin_smul_right]
            have hlin : r • (a.1 * (b.1 * c.1)) + r • (b.1 * (c.1 * a.1)) +
                r • (c.1 * (a.1 * b.1)) =
                r • (a.1 * (b.1 * c.1) + b.1 * (c.1 * a.1) + c.1 * (a.1 * b.1)) := by module
            rw [hlin, h3Proj0_val_smul]; module }
      map_add' := fun a₁ a₂ => by
        apply LinearMap.ext; intro b; apply LinearMap.ext; intro c; apply Subtype.ext
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, qFun,
          Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul,
          add_mul, mul_add, traceBilin_add_right, traceBilin_add_left]
        have hlin : a₁.1 * (b.1 * c.1) + a₂.1 * (b.1 * c.1) +
            (b.1 * (c.1 * a₁.1) + b.1 * (c.1 * a₂.1)) +
            (c.1 * (a₁.1 * b.1) + c.1 * (a₂.1 * b.1)) =
            (a₁.1 * (b.1 * c.1) + b.1 * (c.1 * a₁.1) + c.1 * (a₁.1 * b.1)) +
            (a₂.1 * (b.1 * c.1) + b.1 * (c.1 * a₂.1) + c.1 * (a₂.1 * b.1)) := by abel
        rw [hlin, h3Proj0_val_add]; module
      map_smul' := fun r a => by
        apply LinearMap.ext; intro b; apply LinearMap.ext; intro c; apply Subtype.ext
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, qFun,
          Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul, RingHom.id_apply,
          smul_mul_assoc, mul_smul_comm, traceBilin_smul_right, traceBilin_smul_left]
        have hlin : r • (a.1 * (b.1 * c.1)) + r • (b.1 * (c.1 * a.1)) +
            r • (c.1 * (a.1 * b.1)) =
            r • (a.1 * (b.1 * c.1) + b.1 * (c.1 * a.1) + c.1 * (a.1 * b.1)) := by module
        rw [hlin, h3Proj0_val_smul]; module }
  have hQ12 (a b c : h3OctonionTraceZero) : Q a b c = Q b a c := by
    change qFun a b c = qFun b a c
    dsimp [qFun]
    have hP : a.1 * (b.1 * c.1) + b.1 * (c.1 * a.1) + c.1 * (a.1 * b.1) =
        b.1 * (a.1 * c.1) + a.1 * (c.1 * b.1) + c.1 * (b.1 * a.1) := by
      rw [H3Octonion.mul_comm b.1 c.1, H3Octonion.mul_comm c.1 a.1, H3Octonion.mul_comm a.1 b.1]
      abel
    have hR : traceBilin b.1 c.1 • a + traceBilin c.1 a.1 • b + traceBilin a.1 b.1 • c =
        traceBilin a.1 c.1 • b + traceBilin c.1 b.1 • a + traceBilin b.1 a.1 • c := by
      rw [traceBilin_symm a.1 b.1, traceBilin_symm c.1 a.1, traceBilin_symm c.1 b.1]; abel
    rw [hP, hR]
  have hQ23 (a b c : h3OctonionTraceZero) : Q a b c = Q a c b := by
    change qFun a b c = qFun a c b
    dsimp [qFun]
    have hP : a.1 * (b.1 * c.1) + b.1 * (c.1 * a.1) + c.1 * (a.1 * b.1) =
        a.1 * (c.1 * b.1) + c.1 * (b.1 * a.1) + b.1 * (a.1 * c.1) := by
      rw [H3Octonion.mul_comm b.1 c.1, H3Octonion.mul_comm c.1 a.1, H3Octonion.mul_comm a.1 b.1]
      abel
    have hR : traceBilin b.1 c.1 • a + traceBilin c.1 a.1 • b + traceBilin a.1 b.1 • c =
        traceBilin c.1 b.1 • a + traceBilin b.1 a.1 • c + traceBilin a.1 c.1 • b := by
      rw [traceBilin_symm b.1 c.1, traceBilin_symm c.1 a.1, traceBilin_symm a.1 b.1]; abel
    rw [hP, hR]
  have hQdiag (w : h3OctonionTraceZero) : Q w w w = 0 := by
    change qFun w w w = 0
    dsimp [qFun]
    have h1 : w.1 * (w.1 * w.1) + w.1 * (w.1 * w.1) + w.1 * (w.1 * w.1) =
        (3 : ℝ) • (w.1 * (w.1 * w.1)) := by module
    have h2 : traceBilin w.1 w.1 • w + traceBilin w.1 w.1 • w + traceBilin w.1 w.1 • w =
        (3 : ℝ) • (traceBilin w.1 w.1 • w) := by module
    rw [h1, h2, map_smul, h3OctProj0_cube w]; module
  exact sub_eq_zero.mp (symmetric_trilinear_h3OctonionTraceZero_eq_zero Q hQ12 hQ23 hQdiag x y z)

theorem h3OctMul0_assoc_decompose (x y z : h3OctonionTraceZero) :
    h3OctMul0 x (h3OctMul0 y z) =
      (1 / 6 : ℝ) • (traceBilin y.1 z.1 • x + traceBilin z.1 x.1 • y +
        traceBilin x.1 y.1 • z) +
      (1 / 3 : ℝ) • (h3OctF4Act (h3OctF4Inner x y) z - h3OctF4Act (h3OctF4Inner z x) y) -
      ((1 / 3 : ℝ) * traceBilin y.1 z.1) • x := by
  rw [← h3OctProj0_cyclic_cube_polarized x y z]
  apply Subtype.ext
  have hdrop : (h3OctMul0 x (h3OctMul0 y z) : H3Octonion ℝ) =
      (h3OctProj0 (x.1 * (y.1 * z.1)) : H3Octonion ℝ) -
        ((1 / 3 : ℝ) * traceBilin y.1 z.1) • x.1 := by
    rw [h3OctMul0_eq_proj0 x (h3OctMul0 y z)]
    simp only [h3OctMul0_coe, mul_sub, mul_smul_comm, map_sub, map_smul, Submodule.coe_sub,
      SetLike.val_smul, h3Octonion_mul_one, h3OctProj0_of_mem x]
  have hf4 : (h3OctF4Act (h3OctF4Inner x y) z - h3OctF4Act (h3OctF4Inner z x) y :
        H3Octonion ℝ) =
      (h3OctProj0 ((3 : ℝ) • (x.1 * (y.1 * z.1)) -
        (x.1 * (y.1 * z.1) + y.1 * (z.1 * x.1) + z.1 * (x.1 * y.1))) : H3Octonion ℝ) := by
    have h_inner : ((h3OctF4Act (h3OctF4Inner x y) z -
          h3OctF4Act (h3OctF4Inner z x) y : h3OctonionTraceZero) : H3Octonion ℝ) =
        (3 : ℝ) • (x.1 * (y.1 * z.1)) -
          (x.1 * (y.1 * z.1) + y.1 * (z.1 * x.1) + z.1 * (x.1 * y.1)) := by
      simp only [Submodule.coe_sub, h3OctF4Act_coe, h3OctF4Inner,
        h3OctonionJordanInnerDerivation_apply]
      rw [H3Octonion.mul_comm x.1 z.1, H3Octonion.mul_comm z.1 y.1]
      module
    have hproj := congrArg Subtype.val
      (h3OctProj0_of_mem (h3OctF4Act (h3OctF4Inner x y) z - h3OctF4Act (h3OctF4Inner z x) y))
    simp only [Submodule.coe_sub] at hproj h_inner
    rw [← hproj, h_inner]
  rw [hdrop]
  simp only [Submodule.coe_sub, Submodule.coe_add, SetLike.val_smul]
  rw [hf4, map_sub, map_smul]
  simp only [Submodule.coe_sub, SetLike.val_smul]
  module

end H3Octonion26D

section ConcreteMagicData

private def compactOctAssoc0 (a b c : CompactOctonionTraceZero) : CompactOctonionTraceZero :=
  ⟨compactOctAssociator a.1 b.1 c.1, by
    change CompactOctonion.trace (compactOctAssociator a.1 b.1 c.1) = 0
    rw [compactOctAssociator, CompactOctonion.trace_sub, CompactOctonion.trace_mul_assoc,
      sub_self]⟩

private def compactOctG2BilinLM :
    CompactOctonionDerivations →ₗ[ℝ] CompactOctonionDerivations →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun D₁ D₂ => LinearMap.trace ℝ (CompactOctonion ℝ) (D₁.1 * D₂.1))
    (fun D₁ D₂ E => by
      change LinearMap.trace ℝ (CompactOctonion ℝ) ((D₁.1 + D₂.1) * E.1) = _
      simp only [add_mul, map_add])
    (fun r D E => by simp only [SetLike.val_smul, smul_mul_assoc, map_smul, smul_eq_mul])
    (fun D E₁ E₂ => by
      change LinearMap.trace ℝ (CompactOctonion ℝ) (D.1 * (E₁.1 + E₂.1)) = _
      simp only [mul_add, map_add])
    (fun r D E => by simp only [SetLike.val_smul, mul_smul_comm, map_smul, smul_eq_mul])

/-- Concrete `OctonionMagicDatum` for the compact octonions `CompactOctonion ℝ` (`𝕆`, `𝔤₂(-14)`). -/
def compactOctonionDatum :
    OctonionMagicDatum CompactOctonionTraceZero CompactOctonionDerivations where
  bilin₀ := compactOctBilin0LM
  comm₀ := compactOctComm0LM
  assoc₀ := compactOctAssoc0
  act := compactG2ActLM
  inner := compactG2InnerLM
  g2Bilin := compactOctG2BilinLM
  bilin_symm a b := compactOctonion_bilin_symm a.1 b.1
  comm_skew := compactOctComm0_antisymm
  bilin_deriv_skew := compactOctBilin_deriv_skew
  bilin_comm_cyclic := compactOctBilin_comm_cyclic
  g2_covariant := compactG2_covariant
  inner_skew := compactG2Inner_antisymm
  act_lie := compactG2Act_lie
  act_comm := compactG2Act_comm0
  inner_comm_cyclic_zero := compactOct_stanDer_comm_cyclic_zero
  comm_double_identity a b c := by
    apply Subtype.ext
    simpa [compactOctComm0_coe, compactOctBilin0LM_apply] using
      compactOct_comm_double_identity a b c
  comm_jacobi_eq_neg_six_assoc a b c := by
    apply Subtype.ext
    exact compactOct_jacobiator_eq_neg_six_assoc a.1 b.1 c.1
  assoc_cycle a b c := by
    apply Subtype.ext
    have h1 : compactOctAssociator b.1 c.1 a.1 = compactOctAssociator a.1 b.1 c.1 := by
      have hid := compactOct_kleinfeld_traceZero_combo a b c
      have hsub : (compactG2Inner b c).1 a.1 =
          (CompactOctonion.mul (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1 -
            CompactOctonion.mul a.1
              (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1)) -
            (3 : ℕ) • compactOctAssociator b.1 c.1 a.1 :=
        compactOctStanDer_normal_form b.1 c.1 a.1
      have hcomm_flip : CompactOctonion.mul a.1
            (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) -
          CompactOctonion.mul
            (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1 =
          -(CompactOctonion.mul (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1 -
            CompactOctonion.mul a.1
              (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1)) := by abel
      have h3 : (3 : ℕ) • compactOctAssociator b.1 c.1 a.1 =
          (3 : ℝ) • compactOctAssociator b.1 c.1 a.1 := by module
      change -compactOctAssociator a.1 b.1 c.1 -
          (1 / 3 : ℝ) • (CompactOctonion.mul a.1
              (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) -
            CompactOctonion.mul
              (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1) -
          (1 / 3 : ℝ) • (compactG2Inner b c).1 a.1 = 0 at hid
      rw [hsub, h3, hcomm_flip] at hid
      simp only [smul_neg, smul_sub, smul_smul] at hid
      norm_num at hid
      have hsum : -compactOctAssociator a.1 b.1 c.1 + compactOctAssociator b.1 c.1 a.1 = 0 := by
        rw [← hid]; module
      exact eq_of_sub_eq_zero (by rw [← hsum]; abel)
    exact h1
  kleinfeld_combo a b c := by
    apply Subtype.ext
    exact compactOct_kleinfeld_traceZero_combo a b c
  g2Bilin_symm D₁ D₂ := LinearMap.trace_mul_comm ℝ D₁.1 D₂.1
  g2Bilin_lie_skew D₁ D₂ D₃ := by
    change LinearMap.trace ℝ (CompactOctonion ℝ) ((D₁.1 * D₂.1 - D₂.1 * D₁.1) * D₃.1) +
      LinearMap.trace ℝ (CompactOctonion ℝ) (D₂.1 * (D₁.1 * D₃.1 - D₃.1 * D₁.1)) = 0
    simp only [sub_mul, mul_sub, map_sub]
    have h1 : LinearMap.trace ℝ (CompactOctonion ℝ) ((D₁.1 * D₂.1) * D₃.1) =
        LinearMap.trace ℝ (CompactOctonion ℝ) (D₂.1 * (D₃.1 * D₁.1)) := by
      rw [mul_assoc, LinearMap.trace_mul_comm, mul_assoc]
    have h2 : LinearMap.trace ℝ (CompactOctonion ℝ) ((D₂.1 * D₁.1) * D₃.1) =
        LinearMap.trace ℝ (CompactOctonion ℝ) (D₂.1 * (D₁.1 * D₃.1)) := by
      rw [mul_assoc]
    linarith
  g2Bilin_inner_eq D a b := by
    change LinearMap.trace ℝ (CompactOctonion ℝ) ((compactG2Inner a b).1 * D.1) =
      6 * CompactOctonion.bilin a.1 (D.1 b.1)
    exact compactOct_trace_stanDer_comp a b D

private def h3OctF4BilinLM :
    H3OctonionF4Derivations →ₗ[ℝ] H3OctonionF4Derivations →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun F₁ F₂ => LinearMap.trace ℝ (H3Octonion ℝ) (F₁.1 * F₂.1))
    (fun F₁ F₂ G => by
      change LinearMap.trace ℝ (H3Octonion ℝ) ((F₁.1 + F₂.1) * G.1) = _
      simp only [add_mul, map_add])
    (fun _ _ _ => by simp only [SetLike.val_smul, smul_mul_assoc, map_smul, smul_eq_mul])
    (fun F G₁ G₂ => by
      change LinearMap.trace ℝ (H3Octonion ℝ) (F.1 * (G₁.1 + G₂.1)) = _
      simp only [mul_add, map_add])
    (fun _ _ _ => by simp only [SetLike.val_smul, mul_smul_comm, map_smul, smul_eq_mul])

/-- Concrete `JordanMagicDatum` for the compact Euclidean Albert algebra `H3Octonion ℝ` (`H₃(𝕆)`). -/
def h3OctonionJordanDatum :
    JordanMagicDatum h3OctonionTraceZero H3OctonionF4Derivations where
  traceBilin₀ := h3OctTraceBilin0LM
  mul₀ := h3OctMul0LM
  act := h3OctF4ActLM
  inner := h3OctF4InnerLM
  f4Bilin := h3OctF4BilinLM
  traceBilin_symm x y := H3Octonion.traceBilin_symm x.1 y.1
  mul_comm := h3OctMul0_comm
  traceBilin_deriv_skew F x y := h3Octonion_derivation_traceBilin_skew F x.1 y.1
  traceBilin_mul_cyclic := h3Oct_traceBilin_mul_cyclic
  f4_covariant := h3OctF4_covariant
  inner_skew := h3OctF4Inner_antisymm
  act_lie _ _ _ := by apply Subtype.ext; rfl
  act_mul := h3OctF4Act_mul0
  inner_mul_cyclic_zero := h3OctF4Inner_mul_cyclic_zero
  mul_assoc_decompose := h3OctMul0_assoc_decompose
  inner_self_cyclic_zero x y z := by
    apply Subtype.ext
    change (h3OctF4Act (h3OctF4Inner y z) x).1 + (h3OctF4Act (h3OctF4Inner z x) y).1 +
        (h3OctF4Act (h3OctF4Inner x y) z).1 = 0
    simp only [h3OctF4Act_coe, h3OctF4Inner, h3OctonionJordanInnerDerivation_apply]
    rw [H3Octonion.mul_comm y.1 z.1, H3Octonion.mul_comm z.1 x.1, H3Octonion.mul_comm x.1 y.1]
    abel
  f4Bilin_symm F₁ F₂ := LinearMap.trace_mul_comm ℝ F₁.1 F₂.1
  f4Bilin_lie_skew F₁ F₂ F₃ := by
    change LinearMap.trace ℝ (H3Octonion ℝ) ((F₁.1 * F₂.1 - F₂.1 * F₁.1) * F₃.1) +
      LinearMap.trace ℝ (H3Octonion ℝ) (F₂.1 * (F₁.1 * F₃.1 - F₃.1 * F₁.1)) = 0
    simp only [sub_mul, mul_sub, map_sub]
    have h1 : LinearMap.trace ℝ (H3Octonion ℝ) ((F₁.1 * F₂.1) * F₃.1) =
        LinearMap.trace ℝ (H3Octonion ℝ) (F₂.1 * (F₃.1 * F₁.1)) := by
      rw [mul_assoc, LinearMap.trace_mul_comm, mul_assoc]
    have h2 : LinearMap.trace ℝ (H3Octonion ℝ) ((F₂.1 * F₁.1) * F₃.1) =
        LinearMap.trace ℝ (H3Octonion ℝ) (F₂.1 * (F₁.1 * F₃.1)) := by
      rw [mul_assoc]
    linarith
  f4Bilin_inner_eq F x y := by
    change LinearMap.trace ℝ (H3Octonion ℝ)
        ((h3OctonionJordanInnerDerivation x.1 y.1 : Module.End ℝ (H3Octonion ℝ)) * F.1) =
      -3 * H3Octonion.traceBilin x.1 (F.1 y.1)
    rw [LinearMap.trace_mul_comm, h3Octonion_deriv_innerDeriv_trace F x.1 y.1]
    have hsk := h3Octonion_derivation_traceBilin_skew F x.1 y.1
    linarith

section H3ZornOperatorTrace

open H3Zorn

private theorem candidateJordanMulOctℂ_add_left (x₁ x₂ y : H3Octonion ℂ) :
    candidateJordanMulOctℂ (x₁ + x₂) y =
      candidateJordanMulOctℂ x₁ y + candidateJordanMulOctℂ x₂ y := by
  simp [candidateJordanMulOctℂ, H3Octonion.T_add_left, smul_add]

private theorem candidateJordanMulOctℂ_add_right (x y₁ y₂ : H3Octonion ℂ) :
    candidateJordanMulOctℂ x (y₁ + y₂) =
      candidateJordanMulOctℂ x y₁ + candidateJordanMulOctℂ x y₂ := by
  simp [candidateJordanMulOctℂ, H3Octonion.T_add_outer, smul_add]

private theorem candidateJordanMulOctℂ_smul_left (c : ℂ) (x y : H3Octonion ℂ) :
    candidateJordanMulOctℂ (c • x) y = c • candidateJordanMulOctℂ x y := by
  rw [candidateJordanMulOctℂ, candidateJordanMulOctℂ, H3Octonion.T_smul_left,
    smul_comm c (1 / 2 : ℂ)]

private theorem candidateJordanMulOctℂ_smul_right (c : ℂ) (x y : H3Octonion ℂ) :
    candidateJordanMulOctℂ x (c • y) = c • candidateJordanMulOctℂ x y := by
  rw [candidateJordanMulOctℂ, candidateJordanMulOctℂ, H3Octonion.T_smul_outer,
    smul_comm c (1 / 2 : ℂ)]

private theorem candidateJordanMulZornℂ_add_right (X Y₁ Y₂ : H3Zorn ℂ) :
    candidateJordanMulZornℂ X (Y₁ + Y₂) =
      candidateJordanMulZornℂ X Y₁ + candidateJordanMulZornℂ X Y₂ := by
  simp [candidateJordanMulZornℂ, H3Zorn.T_add_right, smul_add]

private theorem candidateJordanMulZornℂ_smul_right (c : ℂ) (X Y : H3Zorn ℂ) :
    candidateJordanMulZornℂ X (c • Y) = c • candidateJordanMulZornℂ X Y := by
  rw [candidateJordanMulZornℂ, candidateJordanMulZornℂ, H3Zorn.T_smul_right,
    smul_comm c (1 / 2 : ℂ)]

private theorem ofRealH3Octonion_linearTrace (x : H3Octonion ℝ) :
    H3Octonion.linearTrace (ofRealH3Octonion x) = ((H3Octonion.linearTrace x : ℝ) : ℂ) := by
  dsimp [ofRealH3Octonion, H3Octonion.linearTrace]
  push_cast
  rfl

private theorem ofRealH3Zorn_linearTrace (X : H3Zorn ℝ) :
    H3Zorn.linearTrace (ofRealH3Zorn X) = ((H3Zorn.linearTrace X : ℝ) : ℂ) := by
  dsimp [ofRealH3Zorn, H3Zorn.linearTrace]
  push_cast
  rfl

private def jordanLmulH3Zorn (a : H3Zorn ℝ) : Module.End ℝ (H3Zorn ℝ) where
  toFun z := a * z
  map_add' z₁ z₂ := mul_add a z₁ z₂
  map_smul' r z := mul_smul_comm r a z

private def jordanLmulH3Octℂ (u : H3Octonion ℂ) : Module.End ℂ (H3Octonion ℂ) where
  toFun z := candidateJordanMulOctℂ u z
  map_add' z₁ z₂ := candidateJordanMulOctℂ_add_right u z₁ z₂
  map_smul' c z := candidateJordanMulOctℂ_smul_right c u z

private def jordanLmulH3Zornℂ (u : H3Zorn ℂ) : Module.End ℂ (H3Zorn ℂ) where
  toFun z := candidateJordanMulZornℂ u z
  map_add' z₁ z₂ := candidateJordanMulZornℂ_add_right u z₁ z₂
  map_smul' c z := candidateJordanMulZornℂ_smul_right c u z

private theorem trace_jordanLmul_h3Octℂ_ofReal (a b : H3Octonion ℝ) :
    LinearMap.trace ℂ (H3Octonion ℂ)
        (jordanLmulH3Octℂ (ofRealH3Octonion a) * jordanLmulH3Octℂ (ofRealH3Octonion b)) =
      (LinearMap.trace ℝ (H3Octonion ℝ)
        (jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) b) : ℂ) := by
  let _free : Module.Free ℝ (H3Octonion ℝ) := Module.Free.of_divisionRing ℝ (H3Octonion ℝ)
  let _fin : Module.Finite ℝ (H3Octonion ℝ) := instModuleFiniteH3Octonion
  have hconj : jordanLmulH3Octℂ (ofRealH3Octonion a) * jordanLmulH3Octℂ (ofRealH3Octonion b) =
      tensorEquivH3Octonion.conj
        ((jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) b).baseChange ℂ) := by
    apply LinearMap.ext; intro z
    rw [← ofReal_rePart_add_I_imPart_H3Octonion z]
    have hreal : ∀ w : H3Octonion ℝ,
        (jordanLmulH3Octℂ (ofRealH3Octonion a) * jordanLmulH3Octℂ (ofRealH3Octonion b))
            (ofRealH3Octonion w) =
          tensorEquivH3Octonion.conj
            ((jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) b).baseChange ℂ)
            (ofRealH3Octonion w) := by
      intro w
      have hsym : tensorEquivH3Octonion.symm (ofRealH3Octonion w) = (1 : ℂ) ⊗ₜ[ℝ] w := by
        apply tensorEquivH3Octonion.injective
        simp
      rw [LinearEquiv.conj_apply_apply, hsym, LinearMap.baseChange_tmul,
        tensorEquivH3Octonion_tmul, one_smul]
      change candidateJordanMulOctℂ (ofRealH3Octonion a)
          (candidateJordanMulOctℂ (ofRealH3Octonion b) (ofRealH3Octonion w)) =
        ofRealH3Octonion (a * (b * w))
      rw [← ofRealH3Octonion_jordanMul, ← ofRealH3Octonion_jordanMul]
    simp only [map_add, map_smul, hreal]
  rw [hconj, LinearMap.trace_conj', LinearMap.trace_baseChange]
  rfl

private theorem trace_jordanLmul_h3Octℂ (u v : H3Octonion ℂ) :
    LinearMap.trace ℂ (H3Octonion ℂ) (jordanLmulH3Octℂ u * jordanLmulH3Octℂ v) =
      3 * H3Octonion.traceBilin u v + 2 * H3Octonion.linearTrace u * H3Octonion.linearTrace v := by
  have hreal : ∀ a b : H3Octonion ℝ,
      LinearMap.trace ℂ (H3Octonion ℂ)
          (jordanLmulH3Octℂ (ofRealH3Octonion a) * jordanLmulH3Octℂ (ofRealH3Octonion b)) =
        3 * H3Octonion.traceBilin (ofRealH3Octonion a) (ofRealH3Octonion b) +
          2 * H3Octonion.linearTrace (ofRealH3Octonion a) *
            H3Octonion.linearTrace (ofRealH3Octonion b) := by
    intro a b
    rw [trace_jordanLmul_h3Octℂ_ofReal, h3Octonion_jordanLmul_trace_mul,
      ofRealH3Octonion_traceBilin, ofRealH3Octonion_linearTrace, ofRealH3Octonion_linearTrace]
    push_cast; ring
  have haddL : ∀ u₁ u₂ v : H3Octonion ℂ,
      jordanLmulH3Octℂ (u₁ + u₂) * jordanLmulH3Octℂ v =
        jordanLmulH3Octℂ u₁ * jordanLmulH3Octℂ v + jordanLmulH3Octℂ u₂ * jordanLmulH3Octℂ v := by
    intro u₁ u₂ v; apply LinearMap.ext; intro z
    exact candidateJordanMulOctℂ_add_left u₁ u₂ (candidateJordanMulOctℂ v z)
  have hsmulL : ∀ (c : ℂ) (u v : H3Octonion ℂ),
      jordanLmulH3Octℂ (c • u) * jordanLmulH3Octℂ v =
        c • (jordanLmulH3Octℂ u * jordanLmulH3Octℂ v) := by
    intro c u v; apply LinearMap.ext; intro z
    exact candidateJordanMulOctℂ_smul_left c u (candidateJordanMulOctℂ v z)
  have haddR : ∀ u v₁ v₂ : H3Octonion ℂ,
      jordanLmulH3Octℂ u * jordanLmulH3Octℂ (v₁ + v₂) =
        jordanLmulH3Octℂ u * jordanLmulH3Octℂ v₁ + jordanLmulH3Octℂ u * jordanLmulH3Octℂ v₂ := by
    intro u v₁ v₂; apply LinearMap.ext; intro z
    change candidateJordanMulOctℂ u (candidateJordanMulOctℂ (v₁ + v₂) z) =
      candidateJordanMulOctℂ u (candidateJordanMulOctℂ v₁ z) +
        candidateJordanMulOctℂ u (candidateJordanMulOctℂ v₂ z)
    rw [candidateJordanMulOctℂ_add_left, candidateJordanMulOctℂ_add_right]
  have hsmulR : ∀ (c : ℂ) (u v : H3Octonion ℂ),
      jordanLmulH3Octℂ u * jordanLmulH3Octℂ (c • v) =
        c • (jordanLmulH3Octℂ u * jordanLmulH3Octℂ v) := by
    intro c u v; apply LinearMap.ext; intro z
    change candidateJordanMulOctℂ u (candidateJordanMulOctℂ (c • v) z) =
      c • candidateJordanMulOctℂ u (candidateJordanMulOctℂ v z)
    rw [candidateJordanMulOctℂ_smul_left, candidateJordanMulOctℂ_smul_right]
  rw [← ofReal_rePart_add_I_imPart_H3Octonion u, ← ofReal_rePart_add_I_imPart_H3Octonion v]
  simp only [haddL, haddR, hsmulL, hsmulR, map_add, map_smul, smul_eq_mul,
    H3Octonion.traceBilin_add_left, H3Octonion.traceBilin_add_right,
    H3Octonion.traceBilin_smul_left, H3Octonion.traceBilin_smul_right,
    H3Octonion.linearTrace_add, H3Octonion.linearTrace_smul]
  rw [hreal (rePartH3Octonion u) (rePartH3Octonion v),
    hreal (rePartH3Octonion u) (imPartH3Octonion v),
    hreal (imPartH3Octonion u) (rePartH3Octonion v),
    hreal (imPartH3Octonion u) (imPartH3Octonion v)]
  ring

private theorem trace_jordanLmul_h3Zornℂ (U V : H3Zorn ℂ) :
    LinearMap.trace ℂ (H3Zorn ℂ) (jordanLmulH3Zornℂ U * jordanLmulH3Zornℂ V) =
      3 * H3Zorn.traceBilin U V + 2 * H3Zorn.linearTrace U * H3Zorn.linearTrace V := by
  obtain ⟨u, rfl⟩ := h3OctonionComplexEquiv.surjective U
  obtain ⟨v, rfl⟩ := h3OctonionComplexEquiv.surjective V
  have hconj : jordanLmulH3Zornℂ (h3OctonionComplexEquiv u) *
        jordanLmulH3Zornℂ (h3OctonionComplexEquiv v) =
      h3OctonionComplexEquiv.conj (jordanLmulH3Octℂ u * jordanLmulH3Octℂ v) := by
    apply LinearMap.ext; intro Z
    obtain ⟨z, rfl⟩ := h3OctonionComplexEquiv.surjective Z
    simp only [Module.End.mul_apply, LinearEquiv.conj_apply_apply]
    simp only [jordanLmulH3Zornℂ, jordanLmulH3Octℂ, LinearMap.coe_mk, AddHom.coe_mk,
      ← h3OctonionComplexEquiv_jordanMul, LinearEquiv.symm_apply_apply]
  rw [hconj, LinearMap.trace_conj', trace_jordanLmul_h3Octℂ,
    h3OctonionComplexEquiv_traceBilin, h3OctonionComplexEquiv_linearTrace,
    h3OctonionComplexEquiv_linearTrace]

theorem h3Zorn_jordanLmul_trace_mul (a b : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmulH3Zorn a * jordanLmulH3Zorn b) =
      3 * traceBilin a b + 2 * linearTrace a * linearTrace b := by
  let _free : Module.Free ℝ (H3Zorn ℝ) := Module.Free.of_divisionRing ℝ (H3Zorn ℝ)
  let _fin : Module.Finite ℝ (H3Zorn ℝ) := h3ZornBasis.finiteDimensional_of_finite
  have hconj : jordanLmulH3Zornℂ (ofRealH3Zorn a) * jordanLmulH3Zornℂ (ofRealH3Zorn b) =
      tensorEquivH3Zorn.conj ((jordanLmulH3Zorn a * jordanLmulH3Zorn b).baseChange ℂ) := by
    apply LinearMap.ext; intro Z
    rw [← ofReal_rePart_add_I_imPart_H3Zorn Z]
    have hreal : ∀ W : H3Zorn ℝ,
        (jordanLmulH3Zornℂ (ofRealH3Zorn a) * jordanLmulH3Zornℂ (ofRealH3Zorn b))
            (ofRealH3Zorn W) =
          tensorEquivH3Zorn.conj ((jordanLmulH3Zorn a * jordanLmulH3Zorn b).baseChange ℂ)
            (ofRealH3Zorn W) := by
      intro W
      have hsym : tensorEquivH3Zorn.symm (ofRealH3Zorn W) = (1 : ℂ) ⊗ₜ[ℝ] W := by
        apply tensorEquivH3Zorn.injective; simp
      rw [LinearEquiv.conj_apply_apply, hsym, LinearMap.baseChange_tmul,
        tensorEquivH3Zorn_tmul, one_smul]
      change candidateJordanMulZornℂ (ofRealH3Zorn a)
          (candidateJordanMulZornℂ (ofRealH3Zorn b) (ofRealH3Zorn W)) =
        ofRealH3Zorn (a * (b * W))
      rw [← ofRealH3Zorn_jordanMul, ← ofRealH3Zorn_jordanMul]
    simp only [map_add, map_smul, hreal]
  have hC : (LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmulH3Zorn a * jordanLmulH3Zorn b) : ℂ) =
      (3 * traceBilin a b + 2 * linearTrace a * linearTrace b : ℝ) := by
    calc (LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmulH3Zorn a * jordanLmulH3Zorn b) : ℂ)
        = LinearMap.trace ℂ (H3Zorn ℂ)
            (jordanLmulH3Zornℂ (ofRealH3Zorn a) * jordanLmulH3Zornℂ (ofRealH3Zorn b)) := by
          rw [hconj, LinearMap.trace_conj', LinearMap.trace_baseChange]; rfl
      _ = 3 * H3Zorn.traceBilin (ofRealH3Zorn a) (ofRealH3Zorn b) +
            2 * H3Zorn.linearTrace (ofRealH3Zorn a) * H3Zorn.linearTrace (ofRealH3Zorn b) :=
          trace_jordanLmul_h3Zornℂ _ _
      _ = (3 * traceBilin a b + 2 * linearTrace a * linearTrace b : ℝ) := by
          rw [ofRealH3Zorn_traceBilin, ofRealH3Zorn_linearTrace, ofRealH3Zorn_linearTrace]
          push_cast; ring
  exact Complex.ofReal_injective hC

theorem h3Zorn_deriv_innerDeriv_trace (D : F4DerivationCarrier) (u v : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ)
        (D.1 * (h3ZornJordanInnerDerivation u v : Module.End ℝ (H3Zorn ℝ))) =
      3 * traceBilin (D.1 u) v := by
  have hinner : (h3ZornJordanInnerDerivation u v : Module.End ℝ (H3Zorn ℝ)) =
      jordanLmulH3Zorn u * jordanLmulH3Zorn v - jordanLmulH3Zorn v * jordanLmulH3Zorn u := by
    apply LinearMap.ext; intro z; rfl
  have hDL : D.1 * jordanLmulH3Zorn u - jordanLmulH3Zorn u * D.1 = jordanLmulH3Zorn (D.1 u) := by
    apply LinearMap.ext; intro z
    change D.1 (u * z) - u * D.1 z = D.1 u * z
    rw [D.2 u z]; abel
  have hcyc : LinearMap.trace ℝ (H3Zorn ℝ) (D.1 * (jordanLmulH3Zorn v * jordanLmulH3Zorn u)) =
      LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmulH3Zorn u * D.1 * jordanLmulH3Zorn v) := by
    rw [← mul_assoc, LinearMap.trace_mul_cycle, mul_assoc]
  rw [hinner, mul_sub, map_sub, hcyc, ← mul_assoc, ← map_sub, ← sub_mul, hDL,
    h3Zorn_jordanLmul_trace_mul, h3ZornF4_derivation_linearTrace_zero D u]
  ring

end H3ZornOperatorTrace

private def h3ZornF4BilinLM :
    F4DerivationCarrier →ₗ[ℝ] F4DerivationCarrier →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun F₁ F₂ => LinearMap.trace ℝ (H3Zorn ℝ) (F₁.1 * F₂.1))
    (fun F₁ F₂ G => by
      change LinearMap.trace ℝ (H3Zorn ℝ) ((F₁.1 + F₂.1) * G.1) = _
      simp only [add_mul, map_add])
    (fun _ _ _ => by simp only [SetLike.val_smul, smul_mul_assoc, map_smul, smul_eq_mul])
    (fun F G₁ G₂ => by
      change LinearMap.trace ℝ (H3Zorn ℝ) (F.1 * (G₁.1 + G₂.1)) = _
      simp only [mul_add, map_add])
    (fun _ _ _ => by simp only [SetLike.val_smul, mul_smul_comm, map_smul, smul_eq_mul])

/-- Concrete `JordanMagicDatum` for the split Albert algebra `H3Zorn ℝ` (`H₃(𝕆_s)`),
reusing all 26D identities from `MagicSquareTitsBracket`. -/
def h3ZornJordanDatum : JordanMagicDatum h3TraceZero F4DerivationCarrier where
  traceBilin₀ := MagicSquareTitsBracket.traceBilin0LM
  mul₀ := MagicSquareTitsBracket.h3Mul0LM
  act := MagicSquareTitsBracket.f4ActLM
  inner := MagicSquareTitsBracket.f4InnerLM
  f4Bilin := h3ZornF4BilinLM
  traceBilin_symm x y := H3Zorn.traceBilin_symm x.1 y.1
  mul_comm := MagicSquareTitsBracket.h3Mul0_comm
  traceBilin_deriv_skew := MagicSquareTitsBracket.f4_derivation_traceBilin_skew0
  traceBilin_mul_cyclic := MagicSquareTitsBracket.h3_traceBilin_mul_cyclic
  f4_covariant := MagicSquareTitsBracket.f4_covariant
  inner_skew := MagicSquareTitsBracket.f4Inner_antisymm
  act_lie := MagicSquareTitsBracket.f4Act_lie
  act_mul := MagicSquareTitsBracket.f4Act_h3Mul0
  inner_mul_cyclic_zero := MagicSquareTitsBracket.f4Inner_mul_cyclic_zero
  mul_assoc_decompose := MagicSquareTitsBracket.h3Mul0_assoc_decompose
  inner_self_cyclic_zero x y z := by
    apply Subtype.ext
    change (MagicSquareTitsBracket.f4Act (MagicSquareTitsBracket.f4Inner y z) x).1 +
        (MagicSquareTitsBracket.f4Act (MagicSquareTitsBracket.f4Inner z x) y).1 +
        (MagicSquareTitsBracket.f4Act (MagicSquareTitsBracket.f4Inner x y) z).1 = 0
    simp only [MagicSquareTitsBracket.f4Act_coe, MagicSquareTitsBracket.f4Inner,
      h3ZornJordanInnerDerivation_apply]
    rw [_root_.mul_comm y.1 z.1, _root_.mul_comm z.1 x.1, _root_.mul_comm x.1 y.1]
    abel
  f4Bilin_symm F₁ F₂ := LinearMap.trace_mul_comm ℝ F₁.1 F₂.1
  f4Bilin_lie_skew F₁ F₂ F₃ := by
    change LinearMap.trace ℝ (H3Zorn ℝ) ((F₁.1 * F₂.1 - F₂.1 * F₁.1) * F₃.1) +
      LinearMap.trace ℝ (H3Zorn ℝ) (F₂.1 * (F₁.1 * F₃.1 - F₃.1 * F₁.1)) = 0
    simp only [sub_mul, mul_sub, map_sub]
    have h1 : LinearMap.trace ℝ (H3Zorn ℝ) ((F₁.1 * F₂.1) * F₃.1) =
        LinearMap.trace ℝ (H3Zorn ℝ) (F₂.1 * (F₃.1 * F₁.1)) := by
      rw [mul_assoc, LinearMap.trace_mul_comm, mul_assoc]
    have h2 : LinearMap.trace ℝ (H3Zorn ℝ) ((F₂.1 * F₁.1) * F₃.1) =
        LinearMap.trace ℝ (H3Zorn ℝ) (F₂.1 * (F₁.1 * F₃.1)) := by
      rw [mul_assoc]
    linarith
  f4Bilin_inner_eq F x y := by
    change LinearMap.trace ℝ (H3Zorn ℝ)
        ((h3ZornJordanInnerDerivation x.1 y.1 : Module.End ℝ (H3Zorn ℝ)) * F.1) =
      -3 * H3Zorn.traceBilin x.1 (F.1 y.1)
    rw [LinearMap.trace_mul_comm, h3Zorn_deriv_innerDeriv_trace F x.1 y.1]
    have hsk := MagicSquareTitsBracket.f4_derivation_traceBilin_skew0 F x y
    simp only [MagicSquareTitsBracket.f4Act_coe] at hsk
    linarith

/-- The 248-dimensional compact real Lie algebra `𝔈₈(-248)` via the Tits Magic Square on
`CompactOctonion ℝ × H3Octonion ℝ`. -/
abbrev CompactE8Lie := MagicSquareLie compactOctonionDatum h3OctonionJordanDatum

/-- The 248-dimensional quaternionic real Lie algebra `𝔈₈(-24)` via the Tits Magic Square on
`CompactOctonion ℝ × H3Zorn ℝ`. -/
abbrev QuaternionicE8Lie := MagicSquareLie compactOctonionDatum h3ZornJordanDatum

instance instModuleFiniteCompactE8Lie : Module.Finite ℝ CompactE8Lie :=
  let _free1 : Module.Free ℝ CompactOctonionDerivations :=
    Module.Free.of_divisionRing ℝ CompactOctonionDerivations
  let _fin1 : Module.Finite ℝ CompactOctonionDerivations :=
    Module.finite_of_finrank_pos (by rw [finrank_compactOctonionDerivations]; norm_num)
  let _free2 : Module.Free ℝ CompactOctonionTraceZero :=
    Module.Free.of_divisionRing ℝ CompactOctonionTraceZero
  let _fin2 : Module.Finite ℝ CompactOctonionTraceZero :=
    Module.finite_of_finrank_pos (by rw [finrank_compactOctonionTraceZero]; norm_num)
  let _free3 : Module.Free ℝ h3OctonionTraceZero :=
    Module.Free.of_divisionRing ℝ h3OctonionTraceZero
  let _fin3 : Module.Finite ℝ h3OctonionTraceZero :=
    Module.finite_of_finrank_pos (by rw [finrank_h3OctonionTraceZero]; norm_num)
  let _free4 : Module.Free ℝ H3OctonionF4Derivations :=
    Module.Free.of_divisionRing ℝ H3OctonionF4Derivations
  let _fin4 : Module.Finite ℝ H3OctonionF4Derivations :=
    Module.finite_of_finrank_pos (by rw [finrank_H3OctonionF4Derivations]; norm_num)
  Module.Finite.equiv (magicSquareLinearEquiv compactOctonionDatum h3OctonionJordanDatum).symm

/-- `CompactE8Lie` (`𝔈₈(-248)`) has exact real dimension `248 = 14 + 7 * 26 + 52`. -/
theorem finrank_compactE8Lie : Module.finrank ℝ CompactE8Lie = 248 := by
  let _free1 : Module.Free ℝ CompactOctonionTraceZero :=
    Module.Free.of_divisionRing ℝ CompactOctonionTraceZero
  let _free2 : Module.Free ℝ h3OctonionTraceZero :=
    Module.Free.of_divisionRing ℝ h3OctonionTraceZero
  let _fin1 : Module.Finite ℝ CompactOctonionTraceZero :=
    Module.finite_of_finrank_pos (by rw [finrank_compactOctonionTraceZero]; norm_num)
  let _fin2 : Module.Finite ℝ h3OctonionTraceZero :=
    Module.finite_of_finrank_pos (by rw [finrank_h3OctonionTraceZero]; norm_num)
  let _finG2 : Module.Finite ℝ CompactOctonionDerivations :=
    Module.finite_of_finrank_pos (by rw [finrank_compactOctonionDerivations]; norm_num)
  let _finMix : Module.Finite ℝ (CompactOctonionTraceZero ⊗[ℝ] h3OctonionTraceZero) :=
    inferInstance
  let _finF4 : Module.Finite ℝ H3OctonionF4Derivations :=
    Module.finite_of_finrank_pos (by rw [finrank_H3OctonionF4Derivations]; norm_num)
  rw [(magicSquareLinearEquiv compactOctonionDatum h3OctonionJordanDatum).finrank_eq,
    Module.finrank_prod, Module.finrank_prod, Module.finrank_tensorProduct,
    finrank_compactOctonionDerivations, finrank_compactOctonionTraceZero,
    finrank_h3OctonionTraceZero, finrank_H3OctonionF4Derivations]

instance instModuleFiniteQuaternionicE8Lie : Module.Finite ℝ QuaternionicE8Lie :=
  let _free1 : Module.Free ℝ CompactOctonionDerivations :=
    Module.Free.of_divisionRing ℝ CompactOctonionDerivations
  let _fin1 : Module.Finite ℝ CompactOctonionDerivations :=
    Module.finite_of_finrank_pos (by rw [finrank_compactOctonionDerivations]; norm_num)
  let _free2 : Module.Free ℝ CompactOctonionTraceZero :=
    Module.Free.of_divisionRing ℝ CompactOctonionTraceZero
  let _fin2 : Module.Finite ℝ CompactOctonionTraceZero :=
    Module.finite_of_finrank_pos (by rw [finrank_compactOctonionTraceZero]; norm_num)
  let _free3 : Module.Free ℝ h3TraceZero := Module.Free.of_divisionRing ℝ h3TraceZero
  let _fin3 : Module.Finite ℝ h3TraceZero :=
    Module.finite_of_finrank_pos (by rw [finrank_h3TraceZero]; norm_num)
  let _free4 : Module.Free ℝ F4DerivationCarrier := Module.Free.of_divisionRing ℝ F4DerivationCarrier
  let _fin4 : Module.Finite ℝ F4DerivationCarrier :=
    Module.finite_of_finrank_pos (by rw [finrank_f4DerivationCarrier]; norm_num)
  Module.Finite.equiv (magicSquareLinearEquiv compactOctonionDatum h3ZornJordanDatum).symm

/-- `QuaternionicE8Lie` (`𝔈₈(-24)`) has exact real dimension `248 = 14 + 7 * 26 + 52`. -/
theorem finrank_quaternionicE8Lie : Module.finrank ℝ QuaternionicE8Lie = 248 := by
  let _free1 : Module.Free ℝ CompactOctonionTraceZero :=
    Module.Free.of_divisionRing ℝ CompactOctonionTraceZero
  let _free2 : Module.Free ℝ h3TraceZero := Module.Free.of_divisionRing ℝ h3TraceZero
  let _fin1 : Module.Finite ℝ CompactOctonionTraceZero :=
    Module.finite_of_finrank_pos (by rw [finrank_compactOctonionTraceZero]; norm_num)
  let _fin2 : Module.Finite ℝ h3TraceZero :=
    Module.finite_of_finrank_pos (by rw [finrank_h3TraceZero]; norm_num)
  let _finG2 : Module.Finite ℝ CompactOctonionDerivations :=
    Module.finite_of_finrank_pos (by rw [finrank_compactOctonionDerivations]; norm_num)
  let _finMix : Module.Finite ℝ (CompactOctonionTraceZero ⊗[ℝ] h3TraceZero) := inferInstance
  let _finF4 : Module.Finite ℝ F4DerivationCarrier :=
    Module.finite_of_finrank_pos (by rw [finrank_f4DerivationCarrier]; norm_num)
  rw [(magicSquareLinearEquiv compactOctonionDatum h3ZornJordanDatum).finrank_eq,
    Module.finrank_prod, Module.finrank_prod, Module.finrank_tensorProduct,
    finrank_compactOctonionDerivations, finrank_compactOctonionTraceZero,
    finrank_h3TraceZero, finrank_f4DerivationCarrier]

section SplitE8InvariantForm

open MagicSquareTitsBracket
open InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear

private def zornMulLeftEnd (x : ZornVectorMatrix ℝ) : Module.End ℝ (ZornVectorMatrix ℝ) where
  toFun y := ZornVectorMatrix.mul x y
  map_add' y₁ y₂ := ZornVectorMatrix.mul_add x y₁ y₂
  map_smul' r y := by
    ext i <;> (try fin_cases i) <;>
      simp [ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

private def zornMulRightEnd (x : ZornVectorMatrix ℝ) : Module.End ℝ (ZornVectorMatrix ℝ) where
  toFun y := ZornVectorMatrix.mul y x
  map_add' y₁ y₂ := ZornVectorMatrix.add_mul y₁ y₂ x
  map_smul' r y := by
    ext i <;> (try fin_cases i) <;>
      simp [ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

private theorem zorn_operatorTrace_eq_sum (A : Module.End ℝ (ZornVectorMatrix ℝ)) :
    LinearMap.trace ℝ (ZornVectorMatrix ℝ) A =
      (A (zorn_basis 0)).a + (A (zorn_basis 1)).v 0 + (A (zorn_basis 2)).v 1 +
      (A (zorn_basis 3)).v 2 + (A (zorn_basis 4)).w 0 + (A (zorn_basis 5)).w 1 +
      (A (zorn_basis 6)).w 2 + (A (zorn_basis 7)).b := by
  rw [LinearMap.trace_eq_matrix_trace ℝ zornCoordinateBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    zornCoordinateBasis_apply, Fin.sum_univ_eight]
  have hrepr : ∀ k : Fin 8, ∀ X : ZornVectorMatrix ℝ,
      zornCoordinateBasis.repr X k = match k with
        | 0 => X.a | 1 => X.v 0 | 2 => X.v 1 | 3 => X.v 2
        | 4 => X.w 0 | 5 => X.w 1 | 6 => X.w 2 | 7 => X.b := by
    intro k X
    have hd := zorn_basis_decomposition X
    have h0 := congrArg zornCoordinateBasis.repr hd
    rw [map_sum] at h0
    simp only [map_smul] at h0
    have h1 := congrArg (fun f : Fin 8 →₀ ℝ => f k) h0
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul] at h1
    have hs : ∀ i : Fin 8, (zornCoordinateBasis.repr (zorn_basis i)) k = if i = k then 1 else 0 := by
      intro i
      rw [← zornCoordinateBasis_apply i, zornCoordinateBasis.repr_self, Finsupp.single_apply]
    simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      at h1
    fin_cases k <;> exact h1.symm
  simp only [hrepr]

private theorem zorn_trace_mulLeft_mulLeft (x y : splitOctonionTraceZero) :
    LinearMap.trace ℝ (ZornVectorMatrix ℝ) (zornMulLeftEnd x.1 * zornMulLeftEnd y.1) =
      -4 * zornBilin x.1 y.1 := by
  rw [zorn_operatorTrace_eq_sum]
  have hx0 : x.1.a + x.1.b = 0 := x.2
  have hy0 : y.1.a + y.1.b = 0 := y.2
  have hxb : x.1.b = -x.1.a := eq_neg_of_add_eq_zero_right hx0
  have hyb : y.1.b = -y.1.a := eq_neg_of_add_eq_zero_right hy0
  simp [Module.End.mul_apply, zornMulLeftEnd, zorn_basis, zornBilin, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot, ZornVec3.cross,
    Fin.sum_univ_three, hxb, hyb]
  ring

private theorem zorn_trace_mulRight_mulLeft (x y : splitOctonionTraceZero) :
    LinearMap.trace ℝ (ZornVectorMatrix ℝ) (zornMulRightEnd x.1 * zornMulLeftEnd y.1) =
      2 * zornBilin x.1 y.1 := by
  rw [zorn_operatorTrace_eq_sum]
  have hx0 : x.1.a + x.1.b = 0 := x.2
  have hy0 : y.1.a + y.1.b = 0 := y.2
  have hxb : x.1.b = -x.1.a := eq_neg_of_add_eq_zero_right hx0
  have hyb : y.1.b = -y.1.a := eq_neg_of_add_eq_zero_right hy0
  simp [Module.End.mul_apply, zornMulLeftEnd, zornMulRightEnd, zorn_basis, zornBilin,
    ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot,
    ZornVec3.cross, Fin.sum_univ_three, hxb, hyb]
  ring

private theorem zorn_trace_mulRight_mulRight (x y : splitOctonionTraceZero) :
    LinearMap.trace ℝ (ZornVectorMatrix ℝ) (zornMulRightEnd x.1 * zornMulRightEnd y.1) =
      -4 * zornBilin x.1 y.1 := by
  rw [zorn_operatorTrace_eq_sum]
  have hx0 : x.1.a + x.1.b = 0 := x.2
  have hy0 : y.1.a + y.1.b = 0 := y.2
  have hxb : x.1.b = -x.1.a := eq_neg_of_add_eq_zero_right hx0
  have hyb : y.1.b = -y.1.a := eq_neg_of_add_eq_zero_right hy0
  simp [Module.End.mul_apply, zornMulRightEnd, zorn_basis, zornBilin, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot, ZornVec3.cross,
    Fin.sum_univ_three, hxb, hyb]
  ring

private theorem zorn_trace_comm_comp_eq (X Y D : Module.End ℝ (ZornVectorMatrix ℝ)) :
    LinearMap.trace ℝ (ZornVectorMatrix ℝ) ((X * Y - Y * X) * D) =
      LinearMap.trace ℝ (ZornVectorMatrix ℝ) (Y * (D * X - X * D)) := by
  rw [sub_mul, map_sub, mul_sub, map_sub]
  have h1 : LinearMap.trace ℝ (ZornVectorMatrix ℝ) ((X * Y) * D) =
      LinearMap.trace ℝ (ZornVectorMatrix ℝ) (Y * (D * X)) := by
    have hc := LinearMap.trace_mul_comm ℝ X (Y * D)
    rw [mul_assoc X Y D, hc, mul_assoc Y D X]
  rw [h1, mul_assoc Y X D]

private theorem zorn_trace_stanDer_comp (a b : splitOctonionTraceZero) (D : G2DerivationCarrier) :
    LinearMap.trace ℝ (ZornVectorMatrix ℝ)
        ((vDerEquivZornDerivations (g2Inner a b)).1 * (vDerEquivZornDerivations D).1) =
      6 * zornBilin a.1 ((vDerEquivZornDerivations D).1 b.1) := by
  let D' := vDerEquivZornDerivations D
  have hdecomp : (vDerEquivZornDerivations (g2Inner a b)).1 =
      (zornMulLeftEnd a.1 * zornMulLeftEnd b.1 - zornMulLeftEnd b.1 * zornMulLeftEnd a.1) +
      (zornMulLeftEnd a.1 * zornMulRightEnd b.1 - zornMulRightEnd b.1 * zornMulLeftEnd a.1) +
      (zornMulRightEnd a.1 * zornMulRightEnd b.1 - zornMulRightEnd b.1 * zornMulRightEnd a.1) := by
    apply LinearMap.ext; intro x
    change stanDerMap (R := ℝ) a.1 b.1 x = _
    simp only [stanDerMap, L_map, R_map,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      Module.End.mul_apply, zornMulLeftEnd, zornMulRightEnd, LinearMap.coe_mk, AddHom.coe_mk]
    rfl
  have hcommL : D'.1 * zornMulLeftEnd a.1 - zornMulLeftEnd a.1 * D'.1 =
      zornMulLeftEnd (D'.1 a.1) := by
    apply LinearMap.ext; intro x
    change D'.1 (ZornVectorMatrix.mul a.1 x) - ZornVectorMatrix.mul a.1 (D'.1 x) =
      ZornVectorMatrix.mul (D'.1 a.1) x
    rw [D'.2 a.1 x]
    change ZornVectorMatrix.mul (D'.1 a.1) x + ZornVectorMatrix.mul a.1 (D'.1 x) -
      ZornVectorMatrix.mul a.1 (D'.1 x) = _
    abel
  have hcommR : D'.1 * zornMulRightEnd a.1 - zornMulRightEnd a.1 * D'.1 =
      zornMulRightEnd (D'.1 a.1) := by
    apply LinearMap.ext; intro x
    change D'.1 (ZornVectorMatrix.mul x a.1) - ZornVectorMatrix.mul (D'.1 x) a.1 =
      ZornVectorMatrix.mul x (D'.1 a.1)
    rw [D'.2 x a.1]
    change ZornVectorMatrix.mul (D'.1 x) a.1 + ZornVectorMatrix.mul x (D'.1 a.1) -
      ZornVectorMatrix.mul (D'.1 x) a.1 = _
    abel
  rw [hdecomp, add_mul, add_mul, map_add, map_add,
    zorn_trace_comm_comp_eq, zorn_trace_comm_comp_eq, zorn_trace_comm_comp_eq,
    hcommL, hcommR]
  let Da : splitOctonionTraceZero := ⟨D'.1 a.1,
    InfoGeometry.Lie.SplitDerivationCoordinates.every_derivation_trace_zero D a.1⟩
  change LinearMap.trace ℝ (ZornVectorMatrix ℝ) (zornMulLeftEnd b.1 * zornMulLeftEnd Da.1) +
      LinearMap.trace ℝ (ZornVectorMatrix ℝ) (zornMulRightEnd b.1 * zornMulLeftEnd Da.1) +
      LinearMap.trace ℝ (ZornVectorMatrix ℝ) (zornMulRightEnd b.1 * zornMulRightEnd Da.1) =
    6 * zornBilin a.1 (D'.1 b.1)
  rw [zorn_trace_mulLeft_mulLeft b Da, zorn_trace_mulRight_mulLeft b Da,
    zorn_trace_mulRight_mulRight b Da]
  have hsk := zornBilin_deriv_skew D a b
  have hsym : zornBilin b.1 (D'.1 a.1) = zornBilin (D'.1 a.1) b.1 := zornBilin_symm _ _
  change -4 * zornBilin b.1 (D'.1 a.1) + 2 * zornBilin b.1 (D'.1 a.1) +
      -4 * zornBilin b.1 (D'.1 a.1) = 6 * zornBilin a.1 (D'.1 b.1)
  have hsk' : zornBilin (D'.1 a.1) b.1 + zornBilin a.1 (D'.1 b.1) = 0 := hsk
  linarith [hsk', hsym]

private def splitOctG2BilinLM : G2DerivationCarrier →ₗ[ℝ] G2DerivationCarrier →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun D₁ D₂ => LinearMap.trace ℝ (ZornVectorMatrix ℝ)
      ((vDerEquivZornDerivations D₁).1 * (vDerEquivZornDerivations D₂).1))
    (fun D₁ D₂ E => by
      rw [map_add]
      change LinearMap.trace ℝ (ZornVectorMatrix ℝ)
          (((vDerEquivZornDerivations D₁).1 + (vDerEquivZornDerivations D₂).1) *
            (vDerEquivZornDerivations E).1) = _
      simp only [add_mul, map_add])
    (fun r D E => by
      simp only [map_smul, SetLike.val_smul, smul_mul_assoc, smul_eq_mul])
    (fun D E₁ E₂ => by
      rw [map_add]
      change LinearMap.trace ℝ (ZornVectorMatrix ℝ)
          ((vDerEquivZornDerivations D).1 *
            ((vDerEquivZornDerivations E₁).1 + (vDerEquivZornDerivations E₂).1)) = _
      simp only [mul_add, map_add])
    (fun r D E => by
      simp only [map_smul, SetLike.val_smul, mul_smul_comm, smul_eq_mul])

/-- Concrete `OctonionMagicDatum` for the split octonions `ZornVectorMatrix ℝ` (`𝕆_s`, `𝔤₂(2)`). -/
def splitOctonionDatum : OctonionMagicDatum splitOctonionTraceZero G2DerivationCarrier where
  bilin₀ := zornBilin0LM
  comm₀ := zornComm0LM
  assoc₀ a b c := ⟨_root_.associator a.1 b.1 c.1, ZornVectorMatrix.trace_associator a.1 b.1 c.1⟩
  act := g2ActLM
  inner := g2InnerLM
  g2Bilin := splitOctG2BilinLM
  bilin_symm a b := zornBilin_symm a.1 b.1
  comm_skew := zornComm0_antisymm
  bilin_deriv_skew := zornBilin_deriv_skew
  bilin_comm_cyclic := zornBilin_comm_cyclic
  g2_covariant := g2_covariant
  inner_skew := g2Inner_antisymm
  act_lie := g2Act_lie
  act_comm := g2Act_zornComm0
  inner_comm_cyclic_zero := stanDer_comm_cyclic_zero
  comm_double_identity a b c := by
    apply Subtype.ext
    simpa only [zornComm0LM, LinearMap.mk₂_apply, zornComm0_coe, zornBilin0LM_apply,
      Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul] using
      octonion_comm_double_identity a b c
  comm_jacobi_eq_neg_six_assoc a b c := by
    apply Subtype.ext
    exact ZornVectorMatrix.zornJacobiator_eq_neg_six_smul_zornAssociator a.1 b.1 c.1
  assoc_cycle a b c := by
    apply Subtype.ext
    exact alternative_associator_cycle zorn_left_alternative zorn_right_alternative a.1 b.1 c.1
  kleinfeld_combo a b c := by
    apply Subtype.ext
    exact kleinfeld_traceZero_combo a b c
  g2Bilin_symm D₁ D₂ := LinearMap.trace_mul_comm ℝ _ _
  g2Bilin_lie_skew D₁ D₂ D₃ := by
    change LinearMap.trace ℝ (ZornVectorMatrix ℝ)
        ((vDerEquivZornDerivations ⁅D₁, D₂⁆).1 * (vDerEquivZornDerivations D₃).1) +
      LinearMap.trace ℝ (ZornVectorMatrix ℝ)
        ((vDerEquivZornDerivations D₂).1 * (vDerEquivZornDerivations ⁅D₁, D₃⁆).1) = 0
    rw [LieEquiv.map_lie, LieEquiv.map_lie]
    set A := (vDerEquivZornDerivations D₁).1
    set B := (vDerEquivZornDerivations D₂).1
    set C := (vDerEquivZornDerivations D₃).1
    change LinearMap.trace ℝ (ZornVectorMatrix ℝ) ((A * B - B * A) * C) +
      LinearMap.trace ℝ (ZornVectorMatrix ℝ) (B * (A * C - C * A)) = 0
    simp only [sub_mul, mul_sub, map_sub]
    have h1 : LinearMap.trace ℝ (ZornVectorMatrix ℝ) ((A * B) * C) =
        LinearMap.trace ℝ (ZornVectorMatrix ℝ) (B * (C * A)) := by
      rw [mul_assoc, LinearMap.trace_mul_comm, mul_assoc]
    have h2 : LinearMap.trace ℝ (ZornVectorMatrix ℝ) ((B * A) * C) =
        LinearMap.trace ℝ (ZornVectorMatrix ℝ) (B * (A * C)) := by
      rw [mul_assoc]
    linarith
  g2Bilin_inner_eq D a b := by
    change LinearMap.trace ℝ (ZornVectorMatrix ℝ)
        ((vDerEquivZornDerivations (g2Inner a b)).1 * (vDerEquivZornDerivations D).1) =
      6 * zornBilin a.1 ((vDerEquivZornDerivations D).1 b.1)
    exact zorn_trace_stanDer_comp a b D

/-- Lie algebra isomorphism `SplitE8Lie ≃ₗ⁅ℝ⁆ MagicSquareLie splitOctonionDatum h3ZornJordanDatum`. -/
def splitE8EquivMagicSquare :
    SplitE8Lie ≃ₗ⁅ℝ⁆ MagicSquareLie splitOctonionDatum h3ZornJordanDatum where
  toFun X := ⟨X.g2, X.mixed, X.f4⟩
  invFun X := ⟨X.g2, X.mixed, X.f4⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {X Y} := by
    apply MagicSquareLie.ext <;> rfl

/-- The `(3, -6, 1)` `ad`-invariant symmetric bilinear form on `SplitE8Lie` (`𝔈₈(+8)`). -/
def splitE8InvBilin : SplitE8Lie →ₗ[ℝ] SplitE8Lie →ₗ[ℝ] ℝ :=
  LinearMap.compl₁₂ (magicInvBilin splitOctonionDatum h3ZornJordanDatum)
    splitE8EquivMagicSquare.toLinearEquiv.toLinearMap
    splitE8EquivMagicSquare.toLinearEquiv.toLinearMap

@[simp] theorem splitE8InvBilin_apply (X Y : SplitE8Lie) :
    splitE8InvBilin X Y =
      magicInvBilin splitOctonionDatum h3ZornJordanDatum
        (splitE8EquivMagicSquare X) (splitE8EquivMagicSquare Y) := rfl

theorem splitE8InvBilin_symm (X Y : SplitE8Lie) :
    splitE8InvBilin X Y = splitE8InvBilin Y X :=
  magicInvBilin_symm _ _

theorem splitE8InvBilin_lieInvariant (Z X Y : SplitE8Lie) :
    splitE8InvBilin ⁅Z, X⁆ Y + splitE8InvBilin X ⁅Z, Y⁆ = 0 := by
  simp only [splitE8InvBilin_apply, LieEquiv.map_lie]
  exact magicInvBilin_lieInvariant _ _ _

end SplitE8InvariantForm

end ConcreteMagicData

end ConcreteDataAndCarriers

/-! ## 3. Simplicity via Complexification (`SplitE8Lie`, `QuaternionicE8Lie`, `CompactE8Lie`) -/

section ComplexificationSimplicity

open MagicSquareTitsBracket
open InfoGeometry.Exceptional.CFSGPort.Chevalley

section ComplexSplitE8Simplicity

private def e8SimpleHℂ (i : Fin 8) : ℂ ⊗[ℝ] SplitE8Lie :=
  (1 : ℂ) ⊗ₜ[ℝ] e8SimpleH i

private def e8SimpleEℂ (i : Fin 8) : ℂ ⊗[ℝ] SplitE8Lie :=
  (1 : ℂ) ⊗ₜ[ℝ] e8SimpleE i

private def e8SimpleFℂ (i : Fin 8) : ℂ ⊗[ℝ] SplitE8Lie :=
  (1 : ℂ) ⊗ₜ[ℝ] e8SimpleF i

private def e8RootVecℂ (r : Fin 240) : ℂ ⊗[ℝ] SplitE8Lie :=
  (1 : ℂ) ⊗ₜ[ℝ] e8RootVec r

private def e8ChevalleyBasisℂ : Module.Basis (Fin 8 ⊕ Fin 240) ℂ (ℂ ⊗[ℝ] SplitE8Lie) :=
  e8ChevalleyBasis.baseChange ℂ

private theorem e8ChevalleyBasisℂ_inl (i : Fin 8) :
    e8ChevalleyBasisℂ (Sum.inl i) = e8SimpleHℂ i := by
  simp [e8ChevalleyBasisℂ, e8ChevalleyBasis, e8SimpleHℂ]

private theorem e8ChevalleyBasisℂ_inr (r : Fin 240) :
    e8ChevalleyBasisℂ (Sum.inr r) = e8RootVecℂ r := by
  simp [e8ChevalleyBasisℂ, e8ChevalleyBasis, e8RootVecℂ]

private theorem e8SimpleHℂ_comm (i j : Fin 8) : ⁅e8SimpleHℂ i, e8SimpleHℂ j⁆ = 0 := by
  rw [e8SimpleHℂ, e8SimpleHℂ, LieAlgebra.ExtendScalars.bracket_tmul,
    e8SimpleH_comm i j, TensorProduct.tmul_zero]

private theorem e8RootVecℂ_bracket_H (i : Fin 8) (r : Fin 240) :
    ⁅e8SimpleHℂ i, e8RootVecℂ r⁆ = (e8RootEigenvalue i r : ℂ) • e8RootVecℂ r := by
  rw [e8SimpleHℂ, e8RootVecℂ, LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
    e8RootVec_bracket_H, TensorProduct.tmul_smul,
    ← IsScalarTower.algebraMap_smul ℂ (e8RootEigenvalue i r : ℝ), map_intCast]

private theorem e8Simpleℂ_bracket_HE (i j : Fin 8) :
    ⁅e8SimpleHℂ i, e8SimpleEℂ j⁆ = ((Tag.cartan .E8 i j : ℤ) : ℂ) • e8SimpleEℂ j := by
  rw [e8SimpleHℂ, e8SimpleEℂ, LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
    e8Simple_bracket_HE, TensorProduct.tmul_smul,
    ← IsScalarTower.algebraMap_smul ℂ ((Tag.cartan .E8 i j : ℤ) : ℝ), map_intCast]

private theorem e8Simpleℂ_bracket_EF_same (i : Fin 8) :
    ⁅e8SimpleEℂ i, e8SimpleFℂ i⁆ = e8SimpleHℂ i := by
  rw [e8SimpleEℂ, e8SimpleFℂ, e8SimpleHℂ, LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
    e8Simple_bracket_EF_same]

private theorem e8RootVecℂ_bracket_neg_ne_zero (r : Fin 240) :
    ⁅e8RootVecℂ r, e8RootVecℂ (e8RootNeg r)⁆ ≠ 0 := by
  rw [e8RootVecℂ, e8RootVecℂ, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  let _free : Module.Free ℝ SplitE8Lie := Module.Free.of_divisionRing ℝ SplitE8Lie
  have hinj : Function.Injective (fun x : SplitE8Lie => (1 : ℂ) ⊗ₜ[ℝ] x) := by
    intro x y hxy
    have hx := congrArg (e8ChevalleyBasis.baseChange ℂ).repr hxy
    have hcoeff : ∀ k : Fin 8 ⊕ Fin 240, e8ChevalleyBasis.repr x k = e8ChevalleyBasis.repr y k := by
      intro k
      have hk := congrArg (fun f : (Fin 8 ⊕ Fin 240) →₀ ℂ => f k) hx
      simp only [Module.Basis.baseChange_repr_tmul, Complex.real_smul, mul_one] at hk
      exact Complex.ofReal_injective hk
    have hx' := e8ChevalleyBasis.sum_repr x
    have hy' := e8ChevalleyBasis.sum_repr y
    rw [← hx', ← hy']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcoeff k]
  intro h0
  apply e8RootVec_bracket_neg_ne_zero r
  exact hinj (by simpa using h0)

private theorem e8RootVecℂ_opp_mem_cartan (r : Fin 240) :
    ⁅e8RootVecℂ r, e8RootVecℂ (e8RootNeg r)⁆ ∈ Submodule.span ℂ (Set.range e8SimpleHℂ) := by
  rw [e8RootVecℂ, e8RootVecℂ, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  have hopp : e8RootCoord r + e8RootCoord (e8RootNeg r) = 0 := by
    rw [e8RootCoord_neg, add_neg_cancel]
  have hmem : ⁅e8RootVec r, e8RootVec (e8RootNeg r)⁆ ∈ Submodule.span ℝ (Set.range e8SimpleH) := by
    rw [← splitE8Cartan_eq_span_e8SimpleH]
    exact e8RootVec_opposite_bracket_mem_cartan hopp
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  rw [← ha, TensorProduct.tmul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul ℂ (a i)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem e8_cartan_transpose_mulVec_ne_zero_complex {c : Fin 8 → ℂ}
    (hc : (∑ i : Fin 8, c i • e8SimpleHℂ i) ≠ 0) :
    ∃ j : Fin 8, ∑ i : Fin 8, c i * ((Tag.cartan .E8 i j : ℤ) : ℂ) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let invC : Matrix (Fin 8) (Fin 8) ℤ := !![
     4,  5,  7, 10,  8,  6,  4,  2;
     5,  8, 10, 15, 12,  9,  6,  3;
     7, 10, 14, 20, 16, 12,  8,  4;
    10, 15, 20, 30, 24, 18, 12,  6;
     8, 12, 16, 24, 20, 15, 10,  5;
     6,  9, 12, 18, 15, 12,  8,  4;
     4,  6,  8, 12, 10,  8,  6,  3;
     2,  3,  4,  6,  5,  4,  3,  2]
  have hinv : ∀ k i : Fin 8,
      ∑ j : Fin 8, Tag.cartan .E8 i j * invC k j = if i = k then 1 else 0 := by
    intro k i; fin_cases k <;> fin_cases i <;> decide
  have hc0 : ∀ k : Fin 8, c k = 0 := by
    intro k
    have hsum0 : ∑ j : Fin 8, (invC k j : ℂ) *
        (∑ i : Fin 8, c i * ((Tag.cartan .E8 i j : ℤ) : ℂ)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hcon j, mul_zero]
    have hswap : ∑ j : Fin 8, (invC k j : ℂ) *
        (∑ i : Fin 8, c i * ((Tag.cartan .E8 i j : ℤ) : ℂ)) = c k := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hinner : ∀ i : Fin 8,
          ∑ j : Fin 8, (invC k j : ℂ) * (c i * ((Tag.cartan .E8 i j : ℤ) : ℂ)) =
            c i * ((if i = k then (1 : ℤ) else 0 : ℤ) : ℂ) := by
        intro i
        calc ∑ j : Fin 8, (invC k j : ℂ) * (c i * ((Tag.cartan .E8 i j : ℤ) : ℂ))
            = c i * ∑ j : Fin 8, ((Tag.cartan .E8 i j * invC k j : ℤ) : ℂ) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun j _ => ?_
                push_cast; ring
          _ = c i * ((if i = k then (1 : ℤ) else 0 : ℤ) : ℂ) := by
                rw [← Int.cast_sum, hinv k i]
      simp_rw [hinner]
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hik
        simp [hik]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [hswap] at hsum0
    exact hsum0
  apply hc
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hc0 i, zero_smul]

/-- **Complexified Split `E₈(ℂ)` Simplicity**:
`ℂ ⊗[ℝ] SplitE8Lie` is a simple complex Lie algebra. -/
theorem complexSplitE8Lie_isSimple : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] SplitE8Lie) where
  eq_bot_or_eq_top I := by
    by_cases hbot : I = ⊥
    · exact Or.inl hbot
    · right
      have hne : ∃ x ∈ I, x ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hbot
        rw [eq_bot_iff]
        intro x hx
        exact hall x hx
      obtain ⟨x, hxI, hxne⟩ := hne
      have hrep := e8ChevalleyBasisℂ.sum_repr x
      rw [Fintype.sum_sum_type] at hrep
      simp_rw [e8ChevalleyBasisℂ_inl, e8ChevalleyBasisℂ_inr] at hrep
      let hpart : ℂ ⊗[ℝ] SplitE8Lie :=
        ∑ i : Fin 8, e8ChevalleyBasisℂ.repr x (Sum.inl i) • e8SimpleHℂ i
      have hhmem : hpart ∈ Submodule.span ℂ (Set.range e8SimpleHℂ) :=
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hkill := cartan_weight_kill_mem_generic e8SimpleHℂ e8RootVecℂ e8RootEigenvalue
        e8SimpleHℂ_comm e8RootVecℂ_bracket_H e8RootEigenvalue_ne_zero e8RootEigenvalue_eq_imp
        I.toSubmodule (fun i y hy => I.lie_mem hy) Finset.univ hpart hhmem
        (fun r => e8ChevalleyBasisℂ.repr x (Sum.inr r)) (by rw [hrep]; exact hxI)
      have hcartan_nz : ∃ c : Fin 8 → ℂ,
          (∑ i : Fin 8, c i • e8SimpleHℂ i) ∈ I ∧ (∑ i : Fin 8, c i • e8SimpleHℂ i) ≠ 0 := by
        by_cases hp0 : hpart = 0
        · have hex : ∃ r : Fin 240, e8ChevalleyBasisℂ.repr x (Sum.inr r) ≠ 0 := by
            by_contra hall
            push Not at hall
            have hs0 : (∑ r : Fin 240, e8ChevalleyBasisℂ.repr x (Sum.inr r) • e8RootVecℂ r) = 0 :=
              Finset.sum_eq_zero fun r _ => by rw [hall r, zero_smul]
            apply hxne
            rw [← hrep, show (∑ i : Fin 8, e8ChevalleyBasisℂ.repr x (Sum.inl i) • e8SimpleHℂ i) =
              hpart from rfl, hp0, hs0, add_zero]
          obtain ⟨r, hr⟩ := hex
          have hrI : e8RootVecℂ r ∈ I := by
            have hs := I.smul_mem (e8ChevalleyBasisℂ.repr x (Sum.inr r))⁻¹
              (hkill.2 r (Finset.mem_univ r))
            rw [smul_smul, inv_mul_cancel₀ hr, one_smul] at hs
            exact hs
          have hbrI : ⁅e8RootVecℂ r, e8RootVecℂ (e8RootNeg r)⁆ ∈ I := by
            rw [← lie_skew]; exact I.neg_mem (I.lie_mem hrI)
          obtain ⟨c, hc⟩ :=
            (Submodule.mem_span_range_iff_exists_fun ℂ).mp (e8RootVecℂ_opp_mem_cartan r)
          refine ⟨c, ?_, ?_⟩
          · rw [hc]; exact hbrI
          · rw [hc]; exact e8RootVecℂ_bracket_neg_ne_zero r
        · exact ⟨fun i => e8ChevalleyBasisℂ.repr x (Sum.inl i), hkill.1, hp0⟩
      obtain ⟨c, hcI, hcne⟩ := hcartan_nz
      obtain ⟨j₀, hj₀⟩ := e8_cartan_transpose_mulVec_ne_zero_complex hcne
      have hej₀ : e8SimpleEℂ j₀ ∈ I := by
        have hbr : ⁅∑ i : Fin 8, c i • e8SimpleHℂ i, e8SimpleEℂ j₀⁆ ∈ I := by
          rw [← lie_skew]
          exact I.neg_mem (I.lie_mem hcI)
        have heq : ⁅∑ i : Fin 8, c i • e8SimpleHℂ i, e8SimpleEℂ j₀⁆ =
            (∑ i : Fin 8, c i * ((Tag.cartan .E8 i j₀ : ℤ) : ℂ)) • e8SimpleEℂ j₀ := by
          rw [sum_lie, Finset.sum_smul]
          refine Finset.sum_congr rfl fun i _ => ?_
          have h1 := smul_lie (c i) (e8SimpleHℂ i) (e8SimpleEℂ j₀)
          rw [h1, e8Simpleℂ_bracket_HE, smul_smul]
        rw [heq] at hbr
        have hs := I.smul_mem (∑ i : Fin 8, c i * ((Tag.cartan .E8 i j₀ : ℤ) : ℂ))⁻¹ hbr
        rw [smul_smul, inv_mul_cancel₀ hj₀, one_smul] at hs
        exact hs
      have he_to_h : ∀ i : Fin 8, e8SimpleEℂ i ∈ I → e8SimpleHℂ i ∈ I := fun i hi => by
        rw [← e8Simpleℂ_bracket_EF_same i, ← lie_skew]
        exact I.neg_mem (I.lie_mem hi)
      have hstep : ∀ a b : Fin 8, Tag.cartan .E8 a b = -1 →
          e8SimpleHℂ a ∈ I → e8SimpleHℂ b ∈ I := by
        intro a b hab haI
        have hbr : ⁅e8SimpleHℂ a, e8SimpleEℂ b⁆ ∈ I := by
          rw [← lie_skew]; exact I.neg_mem (I.lie_mem haI)
        rw [e8Simpleℂ_bracket_HE, hab] at hbr
        have heb : e8SimpleEℂ b ∈ I := by
          simpa using I.neg_mem hbr
        exact he_to_h b heb
      have hh_j₀ : e8SimpleHℂ j₀ ∈ I := he_to_h j₀ hej₀
      have hc02 : Tag.cartan .E8 (0 : Fin 8) (2 : Fin 8) = -1 := by decide
      have hc20 : Tag.cartan .E8 (2 : Fin 8) (0 : Fin 8) = -1 := by decide
      have hc13 : Tag.cartan .E8 (1 : Fin 8) (3 : Fin 8) = -1 := by decide
      have hc31 : Tag.cartan .E8 (3 : Fin 8) (1 : Fin 8) = -1 := by decide
      have hc23 : Tag.cartan .E8 (2 : Fin 8) (3 : Fin 8) = -1 := by decide
      have hc32 : Tag.cartan .E8 (3 : Fin 8) (2 : Fin 8) = -1 := by decide
      have hc34 : Tag.cartan .E8 (3 : Fin 8) (4 : Fin 8) = -1 := by decide
      have hc43 : Tag.cartan .E8 (4 : Fin 8) (3 : Fin 8) = -1 := by decide
      have hc45 : Tag.cartan .E8 (4 : Fin 8) (5 : Fin 8) = -1 := by decide
      have hc54 : Tag.cartan .E8 (5 : Fin 8) (4 : Fin 8) = -1 := by decide
      have hc56 : Tag.cartan .E8 (5 : Fin 8) (6 : Fin 8) = -1 := by decide
      have hc65 : Tag.cartan .E8 (6 : Fin 8) (5 : Fin 8) = -1 := by decide
      have hc67 : Tag.cartan .E8 (6 : Fin 8) (7 : Fin 8) = -1 := by decide
      have hc76 : Tag.cartan .E8 (7 : Fin 8) (6 : Fin 8) = -1 := by decide
      have hh3 : e8SimpleHℂ 3 ∈ I := by
        fin_cases j₀
        · exact hstep 2 3 hc23 (hstep 0 2 hc02 hh_j₀)
        · exact hstep 1 3 hc13 hh_j₀
        · exact hstep 2 3 hc23 hh_j₀
        · exact hh_j₀
        · exact hstep 4 3 hc43 hh_j₀
        · exact hstep 4 3 hc43 (hstep 5 4 hc54 hh_j₀)
        · exact hstep 4 3 hc43 (hstep 5 4 hc54 (hstep 6 5 hc65 hh_j₀))
        · exact hstep 4 3 hc43 (hstep 5 4 hc54 (hstep 6 5 hc65 (hstep 7 6 hc76 hh_j₀)))
      have hh2 : e8SimpleHℂ 2 ∈ I := hstep 3 2 hc32 hh3
      have hh0 : e8SimpleHℂ 0 ∈ I := hstep 2 0 hc20 hh2
      have hh1 : e8SimpleHℂ 1 ∈ I := hstep 3 1 hc31 hh3
      have hh4 : e8SimpleHℂ 4 ∈ I := hstep 3 4 hc34 hh3
      have hh5 : e8SimpleHℂ 5 ∈ I := hstep 4 5 hc45 hh4
      have hh6 : e8SimpleHℂ 6 ∈ I := hstep 5 6 hc56 hh5
      have hh7 : e8SimpleHℂ 7 ∈ I := hstep 6 7 hc67 hh6
      have hh_all : ∀ i : Fin 8, e8SimpleHℂ i ∈ I := fun i => by
        fin_cases i
        · exact hh0
        · exact hh1
        · exact hh2
        · exact hh3
        · exact hh4
        · exact hh5
        · exact hh6
        · exact hh7
      have hr_all : ∀ r : Fin 240, e8RootVecℂ r ∈ I := fun r => by
        obtain ⟨i, hi⟩ := e8RootEigenvalue_ne_zero r
        have hbr : ⁅e8SimpleHℂ i, e8RootVecℂ r⁆ ∈ I := by
          rw [← lie_skew]; exact I.neg_mem (I.lie_mem (hh_all i))
        rw [e8RootVecℂ_bracket_H] at hbr
        have hnz : (e8RootEigenvalue i r : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hi
        have hs := I.smul_mem (e8RootEigenvalue i r : ℂ)⁻¹ hbr
        rw [smul_smul, inv_mul_cancel₀ hnz, one_smul] at hs
        exact hs
      rw [eq_top_iff]
      intro y _
      have hy := e8ChevalleyBasisℂ.sum_repr y
      rw [← hy, Fintype.sum_sum_type]
      refine I.add_mem (I.sum_mem fun i _ => I.smul_mem _ ?_)
        (I.sum_mem fun r _ => I.smul_mem _ ?_)
      · rw [e8ChevalleyBasisℂ_inl]; exact hh_all i
      · rw [e8ChevalleyBasisℂ_inr]; exact hr_all r
  non_abelian := by
    intro hab
    have h0 := hab.trivial (e8SimpleHℂ 0) (e8SimpleEℂ 0)
    rw [e8Simpleℂ_bracket_HE] at h0
    have hc : Tag.cartan .E8 (0 : Fin 8) (0 : Fin 8) = 2 := by decide
    rw [hc] at h0
    have hne : e8SimpleEℂ 0 ≠ 0 := by
      rw [e8SimpleEℂ, e8SimpleE_eq_rootVec, ← e8RootVecℂ, ← e8ChevalleyBasisℂ_inr]
      exact e8ChevalleyBasisℂ.ne_zero (Sum.inr (e8ESimpleIdx 0))
    have hsm := (smul_eq_zero.mp h0).resolve_right hne
    norm_num at hsm

end ComplexSplitE8Simplicity

section BaseChangeMagicSquare

private def extendScalarsLinear {E N : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup N] [Module ℝ N] [Module ℂ N] [IsScalarTower ℝ ℂ N]
    (g : E →ₗ[ℝ] N) : ℂ ⊗[ℝ] E →ₗ[ℂ] N :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun z =>
        { toFun := fun x => z • g x
          map_add' := fun a b => by rw [map_add, smul_add]
          map_smul' := fun r a => by
            simp only [RingHom.id_apply, map_smul, smul_comm z r] }
      map_add' := fun z₁ z₂ => by
        apply LinearMap.ext; intro x; simp [add_smul]
      map_smul' := fun c z => by
        apply LinearMap.ext; intro x; simp [mul_smul] }

@[simp] private theorem extendScalarsLinear_tmul {E N : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup N] [Module ℝ N] [Module ℂ N] [IsScalarTower ℝ ℂ N]
    (g : E →ₗ[ℝ] N) (z : ℂ) (x : E) :
    extendScalarsLinear g (z ⊗ₜ[ℝ] x) = z • g x := by
  simp [extendScalarsLinear]

private def extendScalarsBilin {E₁ E₂ N : Type}
    [AddCommGroup E₁] [Module ℝ E₁] [AddCommGroup E₂] [Module ℝ E₂]
    [AddCommGroup N] [Module ℝ N] [Module ℂ N] [IsScalarTower ℝ ℂ N]
    (M : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] N) : (ℂ ⊗[ℝ] E₁) →ₗ[ℂ] (ℂ ⊗[ℝ] E₂) →ₗ[ℂ] N :=
  extendScalarsLinear
    { toFun := fun x₁ => extendScalarsLinear (M x₁)
      map_add' := fun x₁ x₁' => by
        apply LinearMap.ext; intro w
        induction w using TensorProduct.inductionOn with
        | tmul z₂ x₂ =>
          simp only [LinearMap.add_apply, extendScalarsLinear_tmul, map_add, smul_add]
        | add a b ha hb =>
          simp only [LinearMap.add_apply] at ha hb ⊢
          rw [map_add (extendScalarsLinear (M (x₁ + x₁'))), ha, hb,
            map_add (extendScalarsLinear (M x₁)), map_add (extendScalarsLinear (M x₁'))]
          abel
      map_smul' := fun r x₁ => by
        apply LinearMap.ext; intro w
        induction w using TensorProduct.inductionOn with
        | tmul z₂ x₂ =>
          simp only [RingHom.id_apply, LinearMap.smul_apply, extendScalarsLinear_tmul,
            map_smul, smul_comm z₂ r]
        | add a b ha hb =>
          simp only [RingHom.id_apply, LinearMap.smul_apply] at ha hb ⊢
          rw [map_add (extendScalarsLinear (M (r • x₁))),
            ha, hb, map_add (extendScalarsLinear (M x₁)), smul_add] }

@[simp] private theorem extendScalarsBilin_tmul {E₁ E₂ N : Type}
    [AddCommGroup E₁] [Module ℝ E₁] [AddCommGroup E₂] [Module ℝ E₂]
    [AddCommGroup N] [Module ℝ N] [Module ℂ N] [IsScalarTower ℝ ℂ N]
    (M : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] N) (z₁ z₂ : ℂ) (x₁ : E₁) (x₂ : E₂) :
    extendScalarsBilin M (z₁ ⊗ₜ[ℝ] x₁) (z₂ ⊗ₜ[ℝ] x₂) = (z₁ * z₂) • M x₁ x₂ := by
  dsimp [extendScalarsBilin]
  rw [extendScalarsLinear_tmul]
  dsimp
  rw [extendScalarsLinear_tmul, smul_smul]

private def tensorMixToFun (O₀ J₀ : Type)
    [AddCommGroup O₀] [Module ℝ O₀] [AddCommGroup J₀] [Module ℝ J₀] :
    (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀) →ₗ[ℂ] ℂ ⊗[ℝ] (O₀ ⊗[ℝ] J₀) :=
  let M : O₀ →ₗ[ℝ] J₀ →ₗ[ℝ] ℂ ⊗[ℝ] (O₀ ⊗[ℝ] J₀) :=
    { toFun := fun a =>
        { toFun := fun x => (1 : ℂ) ⊗ₜ[ℝ] (a ⊗ₜ[ℝ] x)
          map_add' := fun x₁ x₂ => by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
          map_smul' := fun r x => by
            simp only [RingHom.id_apply, TensorProduct.tmul_smul] }
      map_add' := fun a₁ a₂ => by
        apply LinearMap.ext; intro x
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
          TensorProduct.add_tmul, TensorProduct.tmul_add]
      map_smul' := fun r a => by
        apply LinearMap.ext; intro x
        simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
          TensorProduct.smul_tmul, TensorProduct.tmul_smul] }
  TensorProduct.lift (extendScalarsBilin M)

private theorem tensorMixToFun_tmul {O₀ J₀ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [AddCommGroup J₀] [Module ℝ J₀]
    (z₁ z₂ : ℂ) (a : O₀) (x : J₀) :
    tensorMixToFun O₀ J₀ ((z₁ ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] (z₂ ⊗ₜ[ℝ] x)) =
      (z₁ * z₂) ⊗ₜ[ℝ] (a ⊗ₜ[ℝ] x) := by
  dsimp [tensorMixToFun]
  rw [extendScalarsBilin_tmul]
  dsimp
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private def tensorMixInvFun (O₀ J₀ : Type)
    [AddCommGroup O₀] [Module ℝ O₀] [AddCommGroup J₀] [Module ℝ J₀] :
    ℂ ⊗[ℝ] (O₀ ⊗[ℝ] J₀) →ₗ[ℂ] (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀) :=
  let g : (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀) :=
    TensorProduct.lift
      { toFun := fun a =>
          { toFun := fun x => ((1 : ℂ) ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℝ] x)
            map_add' := fun x₁ x₂ => by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
            map_smul' := fun r x => by
              simp only [RingHom.id_apply, TensorProduct.tmul_smul] }
        map_add' := fun a₁ a₂ => by
          apply LinearMap.ext; intro x
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
            TensorProduct.tmul_add, TensorProduct.add_tmul]
        map_smul' := fun r a => by
          apply LinearMap.ext; intro x
          simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
          rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul ℂ r ((1 : ℂ) ⊗ₜ[ℝ] a)]
          rw [← TensorProduct.smul_tmul' (algebraMap ℝ ℂ r) ((1 : ℂ) ⊗ₜ[ℝ] a) ((1 : ℂ) ⊗ₜ[ℝ] x),
            IsScalarTower.algebraMap_smul ℂ r] }
  extendScalarsLinear g

private theorem tensorMixInvFun_tmul {O₀ J₀ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [AddCommGroup J₀] [Module ℝ J₀]
    (z : ℂ) (a : O₀) (x : J₀) :
    tensorMixInvFun O₀ J₀ (z ⊗ₜ[ℝ] (a ⊗ₜ[ℝ] x)) =
      z • (((1 : ℂ) ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℝ] x)) := by
  dsimp [tensorMixInvFun]
  rw [extendScalarsLinear_tmul, TensorProduct.lift.tmul]
  rfl

private def tensorMixCollapse (O₀ J₀ : Type)
    [AddCommGroup O₀] [Module ℝ O₀] [AddCommGroup J₀] [Module ℝ J₀] :
    (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀) ≃ₗ[ℂ] ℂ ⊗[ℝ] (O₀ ⊗[ℝ] J₀) where
  toFun := tensorMixToFun O₀ J₀
  invFun := tensorMixInvFun O₀ J₀
  map_add' := (tensorMixToFun O₀ J₀).map_add'
  map_smul' := (tensorMixToFun O₀ J₀).map_smul'
  left_inv := fun w => by
    induction w using TensorProduct.inductionOn with
    | tmul u₁ u₂ =>
      induction u₁ using TensorProduct.inductionOn with
      | tmul z₁ a =>
        induction u₂ using TensorProduct.inductionOn with
        | tmul z₂ x =>
          rw [tensorMixToFun_tmul, tensorMixInvFun_tmul]
          rw [show (z₁ ⊗ₜ[ℝ] a) = z₁ • ((1 : ℂ) ⊗ₜ[ℝ] a) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
          rw [show (z₂ ⊗ₜ[ℝ] x) = z₂ • ((1 : ℂ) ⊗ₜ[ℝ] x) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
          rw [show (z₁ * z₂) • ((1 : ℂ) ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℝ] x) =
              (z₁ * z₂) • (((1 : ℂ) ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℝ] x)) from
            (TensorProduct.smul_tmul' (z₁ * z₂) ((1 : ℂ) ⊗ₜ[ℝ] a) ((1 : ℂ) ⊗ₜ[ℝ] x)).symm]
          rw [show (z₁ • ((1 : ℂ) ⊗ₜ[ℝ] a)) ⊗ₜ[ℂ] (z₂ • ((1 : ℂ) ⊗ₜ[ℝ] x)) =
              z₁ • (z₂ • (((1 : ℂ) ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℝ] x))) by
            rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_comm z₁ z₂]]
          rw [smul_smul]
        | add u v hu hv =>
          simp only [TensorProduct.tmul_add, map_add] at hu hv ⊢; rw [hu, hv]
      | add u v hu hv =>
        simp only [TensorProduct.add_tmul, map_add] at hu hv ⊢; rw [hu, hv]
    | add u v hu hv =>
      simp only [map_add] at hu hv ⊢; rw [hu, hv]
  right_inv := fun w => by
    induction w using TensorProduct.inductionOn with
    | tmul z m =>
      induction m using TensorProduct.inductionOn with
      | tmul a x =>
        rw [tensorMixInvFun_tmul, map_smul, tensorMixToFun_tmul]
        rw [one_mul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add u v hu hv =>
        simp only [TensorProduct.tmul_add, map_add] at hu hv ⊢; rw [hu, hv]
    | add u v hu hv =>
      simp only [map_add] at hu hv ⊢; rw [hu, hv]

private theorem tensorMixCollapse_tmul {O₀ J₀ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [AddCommGroup J₀] [Module ℝ J₀]
    (z₁ z₂ : ℂ) (a : O₀) (x : J₀) :
    tensorMixCollapse O₀ J₀ ((z₁ ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] (z₂ ⊗ₜ[ℝ] x)) =
      (z₁ * z₂) ⊗ₜ[ℝ] (a ⊗ₜ[ℝ] x) :=
  tensorMixToFun_tmul z₁ z₂ a x

private theorem tensorMixCollapse_symm_tmul {O₀ J₀ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [AddCommGroup J₀] [Module ℝ J₀]
    (z : ℂ) (a : O₀) (x : J₀) :
    (tensorMixCollapse O₀ J₀).symm (z ⊗ₜ[ℝ] (a ⊗ₜ[ℝ] x)) =
      z • (((1 : ℂ) ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℝ] x)) :=
  tensorMixInvFun_tmul z a x

private def magicSquareTensorSplit {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    ℂ ⊗[ℝ] MagicSquareLie O J ≃ₗ[ℂ]
      (ℂ ⊗[ℝ] G₂) × ((ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀)) × (ℂ ⊗[ℝ] F₄) :=
  let toFun : ℂ ⊗[ℝ] MagicSquareLie O J →ₗ[ℂ]
      (ℂ ⊗[ℝ] G₂) × (ℂ ⊗[ℝ] (O₀ ⊗[ℝ] J₀)) × (ℂ ⊗[ℝ] F₄) :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun z =>
          { toFun := fun X => (z ⊗ₜ[ℝ] X.g2, z ⊗ₜ[ℝ] X.mixed, z ⊗ₜ[ℝ] X.f4)
            map_add' := fun X Y => by
              ext <;> simp [TensorProduct.tmul_add]
            map_smul' := fun r X => by
              ext <;> simp only [RingHom.id_apply, MagicSquareLie.smul_g2,
                MagicSquareLie.smul_mixed, MagicSquareLie.smul_f4, Prod.smul_fst, Prod.smul_snd,
                TensorProduct.tmul_smul] }
        map_add' := fun z₁ z₂ => by
          ext X <;> simp [TensorProduct.add_tmul]
        map_smul' := fun c z => by
          ext X
          · simp [TensorProduct.smul_tmul']
          · simp [TensorProduct.smul_tmul']
          · simp [TensorProduct.smul_tmul'] }
  let invFun : (ℂ ⊗[ℝ] G₂) × (ℂ ⊗[ℝ] (O₀ ⊗[ℝ] J₀)) × (ℂ ⊗[ℝ] F₄) →ₗ[ℂ]
      ℂ ⊗[ℝ] MagicSquareLie O J :=
    { toFun := fun p =>
        (msEmbedG2LM O J).baseChange ℂ p.1 +
        (msEmbedMixed O J).baseChange ℂ p.2.1 +
        (msEmbedF4LM O J).baseChange ℂ p.2.2
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_add]
        congr 1
        · congr 1
          · exact ((msEmbedG2LM O J).baseChange ℂ).map_smul c p.1
          · exact ((msEmbedMixed O J).baseChange ℂ).map_smul c p.2.1
        · exact ((msEmbedF4LM O J).baseChange ℂ).map_smul c p.2.2 }
  let split1 : ℂ ⊗[ℝ] MagicSquareLie O J ≃ₗ[ℂ]
      (ℂ ⊗[ℝ] G₂) × (ℂ ⊗[ℝ] (O₀ ⊗[ℝ] J₀)) × (ℂ ⊗[ℝ] F₄) :=
    { toFun := toFun
      invFun := invFun
      map_add' := toFun.map_add'
      map_smul' := toFun.map_smul'
      left_inv := fun u => by
        induction u using TensorProduct.inductionOn with
        | tmul z X =>
          dsimp [toFun, invFun]
          simp only [← TensorProduct.tmul_add]
          congr 1
          apply MagicSquareLie.ext <;> simp
        | add u v hu hv =>
          simp only [map_add] at hu hv ⊢; rw [hu, hv]
      right_inv := fun p => by
        rcases p with ⟨g, m, f⟩
        have hg : ∀ x : ℂ ⊗[ℝ] G₂,
            toFun ((msEmbedG2LM O J).baseChange ℂ x) = (x, 0, 0) := fun x => by
          induction x using TensorProduct.inductionOn with
          | tmul z D => dsimp [toFun]; simp [TensorProduct.tmul_zero]
          | add a b ha hb => simp only [map_add] at ha hb ⊢; rw [ha, hb]; simp [Prod.mk_add_mk]
        have hm : ∀ x : ℂ ⊗[ℝ] (O₀ ⊗[ℝ] J₀),
            toFun ((msEmbedMixed O J).baseChange ℂ x) = (0, x, 0) := fun x => by
          induction x using TensorProduct.inductionOn with
          | tmul z mx => dsimp [toFun]; simp [TensorProduct.tmul_zero]
          | add a b ha hb => simp only [map_add] at ha hb ⊢; rw [ha, hb]; simp [Prod.mk_add_mk]
        have hf : ∀ x : ℂ ⊗[ℝ] F₄,
            toFun ((msEmbedF4LM O J).baseChange ℂ x) = (0, 0, x) := fun x => by
          induction x using TensorProduct.inductionOn with
          | tmul z F => dsimp [toFun]; simp [TensorProduct.tmul_zero]
          | add a b ha hb => simp only [map_add] at ha hb ⊢; rw [ha, hb]; simp [Prod.mk_add_mk]
        dsimp [invFun]
        simp only [map_add, hg, hm, hf]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp }
  split1.trans (LinearEquiv.prodCongr (LinearEquiv.refl ℂ _)
    (LinearEquiv.prodCongr (tensorMixCollapse O₀ J₀).symm (LinearEquiv.refl ℂ _)))

private theorem magicSquareTensorSplit_tmul {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (z : ℂ) (X : MagicSquareLie O J) :
    magicSquareTensorSplit O J (z ⊗ₜ[ℝ] X) =
      (z ⊗ₜ[ℝ] X.g2, (tensorMixCollapse O₀ J₀).symm (z ⊗ₜ[ℝ] X.mixed), z ⊗ₜ[ℝ] X.f4) := rfl

private theorem magicSquareTensorSplit_symm_g2 {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (d : ℂ ⊗[ℝ] G₂) :
    (magicSquareTensorSplit O J).symm (d, 0, 0) = (msEmbedG2LM O J).baseChange ℂ d := by
  dsimp [magicSquareTensorSplit]; simp

private theorem magicSquareTensorSplit_symm_mixed {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (m : (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀)) :
    (magicSquareTensorSplit O J).symm (0, m, 0) =
      (msEmbedMixed O J).baseChange ℂ (tensorMixCollapse O₀ J₀ m) := by
  dsimp [magicSquareTensorSplit]; simp

private theorem magicSquareTensorSplit_symm_f4 {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (f : ℂ ⊗[ℝ] F₄) :
    (magicSquareTensorSplit O J).symm (0, 0, f) = (msEmbedF4LM O J).baseChange ℂ f := by
  dsimp [magicSquareTensorSplit]; simp

private def msMapComplexEquiv {O₀ G₂ J₀ F₄ O₀' G₂' J₀' F₄' : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    [AddCommGroup O₀'] [Module ℝ O₀'] [LieRing G₂'] [LieAlgebra ℝ G₂']
    [AddCommGroup J₀'] [Module ℝ J₀'] [LieRing F₄'] [LieAlgebra ℝ F₄']
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (O' : OctonionMagicDatum O₀' G₂') (J' : JordanMagicDatum J₀' F₄')
    (ΦG2 : ℂ ⊗[ℝ] G₂ ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] G₂')
    (ΦO : ℂ ⊗[ℝ] O₀ ≃ₗ[ℂ] ℂ ⊗[ℝ] O₀')
    (ΦJ : ℂ ⊗[ℝ] J₀ ≃ₗ[ℂ] ℂ ⊗[ℝ] J₀')
    (ΦF4 : ℂ ⊗[ℝ] F₄ ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] F₄') :
    ℂ ⊗[ℝ] MagicSquareLie O J ≃ₗ[ℂ] ℂ ⊗[ℝ] MagicSquareLie O' J' :=
  (magicSquareTensorSplit O J).trans
    ((LinearEquiv.prodCongr ΦG2.toLinearEquiv
      (LinearEquiv.prodCongr (TensorProduct.congr ΦO ΦJ) ΦF4.toLinearEquiv)).trans
      (magicSquareTensorSplit O' J').symm)

private def magicBilinℂ {E : Type} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : (ℂ ⊗[ℝ] E) →ₗ[ℂ] (ℂ ⊗[ℝ] E) →ₗ[ℂ] ℂ :=
  extendScalarsBilin
    { toFun := fun x₁ => (Algebra.linearMap ℝ ℂ).comp (B x₁)
      map_add' := fun x₁ x₁' => by
        apply LinearMap.ext; intro x₂; simp [map_add]
      map_smul' := fun r x₁ => by
        apply LinearMap.ext; intro x₂; simp [map_smul] }

@[simp] private theorem magicBilinℂ_tmul {E : Type} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z₁ z₂ : ℂ) (x₁ x₂ : E) :
    magicBilinℂ B (z₁ ⊗ₜ[ℝ] x₁) (z₂ ⊗ₜ[ℝ] x₂) = z₁ * z₂ * (B x₁ x₂ : ℂ) := by
  dsimp [magicBilinℂ]
  rw [extendScalarsBilin_tmul]
  simp [smul_eq_mul]

private def magicMap2ℂ {E₁ E₂ : Type}
    [AddCommGroup E₁] [Module ℝ E₁] [AddCommGroup E₂] [Module ℝ E₂]
    (M : E₁ →ₗ[ℝ] E₁ →ₗ[ℝ] E₂) : (ℂ ⊗[ℝ] E₁) →ₗ[ℂ] (ℂ ⊗[ℝ] E₁) →ₗ[ℂ] (ℂ ⊗[ℝ] E₂) :=
  let embed1 : E₂ →ₗ[ℝ] ℂ ⊗[ℝ] E₂ :=
    { toFun := fun y => (1 : ℂ) ⊗ₜ[ℝ] y
      map_add' := fun y₁ y₂ => TensorProduct.tmul_add _ _ _
      map_smul' := fun r y => TensorProduct.tmul_smul r (1 : ℂ) y }
  extendScalarsBilin
    { toFun := fun x₁ => embed1.comp (M x₁)
      map_add' := fun x₁ x₁' => by
        apply LinearMap.ext; intro x₂; simp [map_add]
      map_smul' := fun r x₁ => by
        apply LinearMap.ext; intro x₂; simp [map_smul] }

@[simp] private theorem magicMap2ℂ_tmul {E₁ E₂ : Type}
    [AddCommGroup E₁] [Module ℝ E₁] [AddCommGroup E₂] [Module ℝ E₂]
    (M : E₁ →ₗ[ℝ] E₁ →ₗ[ℝ] E₂) (z₁ z₂ : ℂ) (x₁ x₂ : E₁) :
    magicMap2ℂ M (z₁ ⊗ₜ[ℝ] x₁) (z₂ ⊗ₜ[ℝ] x₂) = (z₁ * z₂) ⊗ₜ[ℝ] M x₁ x₂ := by
  dsimp [magicMap2ℂ]
  rw [extendScalarsBilin_tmul]
  dsimp
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private def magicActℂ {G E : Type}
    [AddCommGroup G] [Module ℝ G] [AddCommGroup E] [Module ℝ E]
    (A : G →ₗ[ℝ] E →ₗ[ℝ] E) : (ℂ ⊗[ℝ] G) →ₗ[ℂ] (ℂ ⊗[ℝ] E) →ₗ[ℂ] (ℂ ⊗[ℝ] E) :=
  let embed1 : E →ₗ[ℝ] ℂ ⊗[ℝ] E :=
    { toFun := fun y => (1 : ℂ) ⊗ₜ[ℝ] y
      map_add' := fun y₁ y₂ => TensorProduct.tmul_add _ _ _
      map_smul' := fun r y => TensorProduct.tmul_smul r (1 : ℂ) y }
  extendScalarsBilin
    { toFun := fun g => embed1.comp (A g)
      map_add' := fun g₁ g₂ => by
        apply LinearMap.ext; intro e; simp [map_add]
      map_smul' := fun r g => by
        apply LinearMap.ext; intro e; simp [map_smul] }

@[simp] private theorem magicActℂ_tmul {G E : Type}
    [AddCommGroup G] [Module ℝ G] [AddCommGroup E] [Module ℝ E]
    (A : G →ₗ[ℝ] E →ₗ[ℝ] E) (z₁ z₂ : ℂ) (g : G) (e : E) :
    magicActℂ A (z₁ ⊗ₜ[ℝ] g) (z₂ ⊗ₜ[ℝ] e) = (z₁ * z₂) ⊗ₜ[ℝ] A g e := by
  dsimp [magicActℂ]
  rw [extendScalarsBilin_tmul]
  dsimp
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem ms_lie_eq_bracketLM {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    {O : OctonionMagicDatum O₀ G₂} {J : JordanMagicDatum J₀ F₄}
    (X Y : MagicSquareLie O J) :
    ⁅X, Y⁆ = magicSquareBracketLM O J X Y := rfl

private theorem ext_lie_add {L : Type} [LieRing L] [LieAlgebra ℝ L] (x y z : ℂ ⊗[ℝ] L) :
    ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := lie_add x y z

private theorem ext_add_lie {L : Type} [LieRing L] [LieAlgebra ℝ L] (x y z : ℂ ⊗[ℝ] L) :
    ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := add_lie x y z

private theorem ext_lie_skew {L : Type} [LieRing L] [LieAlgebra ℝ L] (x y : ℂ ⊗[ℝ] L) :
    -⁅y, x⁆ = ⁅x, y⁆ := lie_skew x y

private theorem ms_split_bracket_g2_g2 {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (D₁ D₂ : ℂ ⊗[ℝ] G₂) :
    magicSquareTensorSplit O J
        ⁅(magicSquareTensorSplit O J).symm (D₁, 0, 0),
          (magicSquareTensorSplit O J).symm (D₂, 0, 0)⁆ =
      (⁅D₁, D₂⁆, 0, 0) := by
  induction D₁ using TensorProduct.inductionOn with
  | tmul z₁ d₁ =>
    induction D₂ using TensorProduct.inductionOn with
    | tmul z₂ d₂ =>
      rw [magicSquareTensorSplit_symm_g2, magicSquareTensorSplit_symm_g2,
        LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LieAlgebra.ExtendScalars.bracket_tmul, ms_lie_eq_bracketLM, msBracket_g2_g2,
        magicSquareTensorSplit_tmul]
      simp [LieAlgebra.ExtendScalars.bracket_tmul]
    | add u v hu hv =>
      have h : (u + v, (0 : (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀)), (0 : ℂ ⊗[ℝ] F₄)) =
          (u, 0, 0) + (v, 0, 0) := by
        refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp
      rw [h, map_add, ext_lie_add, map_add, hu, hv, ext_lie_add]
      simp [Prod.mk_add_mk]
  | add u v hu hv =>
    have h : (u + v, (0 : (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀)), (0 : ℂ ⊗[ℝ] F₄)) =
        (u, 0, 0) + (v, 0, 0) := by
      refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp
    rw [h, map_add, ext_add_lie, map_add, hu, hv, ext_add_lie]
    simp [Prod.mk_add_mk]

private theorem ms_split_bracket_f4_f4 {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (F₁ F₂ : ℂ ⊗[ℝ] F₄) :
    magicSquareTensorSplit O J
        ⁅(magicSquareTensorSplit O J).symm (0, 0, F₁),
          (magicSquareTensorSplit O J).symm (0, 0, F₂)⁆ =
      (0, 0, ⁅F₁, F₂⁆) := by
  induction F₁ using TensorProduct.inductionOn with
  | tmul z₁ f₁ =>
    induction F₂ using TensorProduct.inductionOn with
    | tmul z₂ f₂ =>
      rw [magicSquareTensorSplit_symm_f4, magicSquareTensorSplit_symm_f4,
        LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LieAlgebra.ExtendScalars.bracket_tmul, ms_lie_eq_bracketLM, msBracket_f4_f4,
        magicSquareTensorSplit_tmul]
      simp [LieAlgebra.ExtendScalars.bracket_tmul]
    | add u v hu hv =>
      have h : ((0 : ℂ ⊗[ℝ] G₂), (0 : (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀)), u + v) =
          (0, 0, u) + (0, 0, v) := by
        refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp
      rw [h, map_add, ext_lie_add, map_add, hu, hv, ext_lie_add]
      simp [Prod.mk_add_mk]
  | add u v hu hv =>
    have h : ((0 : ℂ ⊗[ℝ] G₂), (0 : (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀)), u + v) =
        (0, 0, u) + (0, 0, v) := by
      refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp
    rw [h, map_add, ext_add_lie, map_add, hu, hv, ext_add_lie]
    simp [Prod.mk_add_mk]

private theorem ms_split_bracket_g2_f4 {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (D : ℂ ⊗[ℝ] G₂) (F : ℂ ⊗[ℝ] F₄) :
    magicSquareTensorSplit O J
        ⁅(magicSquareTensorSplit O J).symm (D, 0, 0),
          (magicSquareTensorSplit O J).symm (0, 0, F)⁆ = 0 := by
  induction D using TensorProduct.inductionOn with
  | tmul z₁ d =>
    induction F using TensorProduct.inductionOn with
    | tmul z₂ f =>
      rw [magicSquareTensorSplit_symm_g2, magicSquareTensorSplit_symm_f4,
        LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LieAlgebra.ExtendScalars.bracket_tmul, ms_lie_eq_bracketLM, msBracket_g2_f4,
        TensorProduct.tmul_zero, map_zero]
    | add u v hu hv =>
      have h : ((0 : ℂ ⊗[ℝ] G₂), (0 : (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀)), u + v) =
          (0, 0, u) + (0, 0, v) := by
        refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp
      rw [h, map_add, ext_lie_add, map_add, hu, hv, add_zero]
  | add u v hu hv =>
    have h : (u + v, (0 : (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀)), (0 : ℂ ⊗[ℝ] F₄)) =
        (u, 0, 0) + (v, 0, 0) := by
      refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp
    rw [h, map_add, ext_add_lie, map_add, hu, hv, add_zero]

private theorem ms_split_bracket_g2_mixed {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (D : ℂ ⊗[ℝ] G₂) (u : ℂ ⊗[ℝ] O₀) (v : ℂ ⊗[ℝ] J₀) :
    magicSquareTensorSplit O J
        ⁅(magicSquareTensorSplit O J).symm (D, 0, 0),
          (magicSquareTensorSplit O J).symm (0, u ⊗ₜ[ℂ] v, 0)⁆ =
      (0, (magicActℂ O.act D u) ⊗ₜ[ℂ] v, 0) := by
  induction D using TensorProduct.inductionOn with
  | tmul z₁ d =>
    induction u using TensorProduct.inductionOn with
    | tmul z₂ a =>
      induction v using TensorProduct.inductionOn with
      | tmul z₃ x =>
        rw [magicSquareTensorSplit_symm_g2, magicSquareTensorSplit_symm_mixed,
          tensorMixCollapse_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
          LieAlgebra.ExtendScalars.bracket_tmul, ms_lie_eq_bracketLM, msBracket_g2_mixed,
          magicG2MixedActLM_tmul, magicSquareTensorSplit_tmul]
        simp only [msEmbedMixed_g2, msEmbedMixed_mixed, msEmbedMixed_f4, TensorProduct.tmul_zero,
          tensorMixCollapse_symm_tmul, magicActℂ_tmul]
        refine Prod.ext rfl (Prod.ext ?_ rfl)
        dsimp only
        rw [show ((z₁ * z₂) ⊗ₜ[ℝ] ((O.act d) a)) =
            (z₁ * z₂) • ((1 : ℂ) ⊗ₜ[ℝ] ((O.act d) a)) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
        rw [show (z₃ ⊗ₜ[ℝ] x) = z₃ • ((1 : ℂ) ⊗ₜ[ℝ] x) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
        rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
          smul_smul, mul_assoc]
      | add v₁ v₂ hv₁ hv₂ =>
        have h : ((0 : ℂ ⊗[ℝ] G₂), (z₂ ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] (v₁ + v₂), (0 : ℂ ⊗[ℝ] F₄)) =
            (0, (z₂ ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] v₁, 0) + (0, (z₂ ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] v₂, 0) := by
          refine Prod.ext ?_ (Prod.ext (TensorProduct.tmul_add _ _ _) ?_) <;> simp
        rw [h, map_add, ext_lie_add, map_add, hv₁, hv₂, TensorProduct.tmul_add]
        simp [Prod.mk_add_mk]
    | add u₁ u₂ hu₁ hu₂ =>
      have h : ((0 : ℂ ⊗[ℝ] G₂), (u₁ + u₂) ⊗ₜ[ℂ] v, (0 : ℂ ⊗[ℝ] F₄)) =
          (0, u₁ ⊗ₜ[ℂ] v, 0) + (0, u₂ ⊗ₜ[ℂ] v, 0) := by
        refine Prod.ext ?_ (Prod.ext (TensorProduct.add_tmul _ _ _) ?_) <;> simp
      rw [h, map_add, ext_lie_add, map_add, hu₁, hu₂, map_add, TensorProduct.add_tmul]
      simp [Prod.mk_add_mk]
  | add d₁ d₂ hd₁ hd₂ =>
    have h : (d₁ + d₂, (0 : (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀)), (0 : ℂ ⊗[ℝ] F₄)) =
        (d₁, 0, 0) + (d₂, 0, 0) := by
      refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp
    rw [h, map_add, ext_add_lie, map_add, hd₁, hd₂, map_add, LinearMap.add_apply,
      TensorProduct.add_tmul]
    simp [Prod.mk_add_mk]

private theorem ms_split_bracket_f4_mixed {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (F : ℂ ⊗[ℝ] F₄) (u : ℂ ⊗[ℝ] O₀) (v : ℂ ⊗[ℝ] J₀) :
    magicSquareTensorSplit O J
        ⁅(magicSquareTensorSplit O J).symm (0, 0, F),
          (magicSquareTensorSplit O J).symm (0, u ⊗ₜ[ℂ] v, 0)⁆ =
      (0, u ⊗ₜ[ℂ] (magicActℂ J.act F v), 0) := by
  induction F using TensorProduct.inductionOn with
  | tmul z₁ f =>
    induction u using TensorProduct.inductionOn with
    | tmul z₂ a =>
      induction v using TensorProduct.inductionOn with
      | tmul z₃ x =>
        rw [magicSquareTensorSplit_symm_f4, magicSquareTensorSplit_symm_mixed,
          tensorMixCollapse_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
          LieAlgebra.ExtendScalars.bracket_tmul, ms_lie_eq_bracketLM, msBracket_f4_mixed,
          magicF4MixedActLM_tmul, magicSquareTensorSplit_tmul]
        simp only [msEmbedMixed_g2, msEmbedMixed_mixed, msEmbedMixed_f4, TensorProduct.tmul_zero,
          tensorMixCollapse_symm_tmul, magicActℂ_tmul]
        refine Prod.ext rfl (Prod.ext ?_ rfl)
        dsimp only
        rw [show (z₂ ⊗ₜ[ℝ] a) = z₂ • ((1 : ℂ) ⊗ₜ[ℝ] a) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
        rw [show ((z₁ * z₃) ⊗ₜ[ℝ] ((J.act f) x)) =
            (z₁ * z₃) • ((1 : ℂ) ⊗ₜ[ℝ] ((J.act f) x)) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
        rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
          smul_smul, mul_left_comm]
      | add v₁ v₂ hv₁ hv₂ =>
        have h : ((0 : ℂ ⊗[ℝ] G₂), (z₂ ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] (v₁ + v₂), (0 : ℂ ⊗[ℝ] F₄)) =
            (0, (z₂ ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] v₁, 0) + (0, (z₂ ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] v₂, 0) := by
          refine Prod.ext ?_ (Prod.ext (TensorProduct.tmul_add _ _ _) ?_) <;> simp
        rw [h, map_add, ext_lie_add, map_add, hv₁, hv₂, map_add, TensorProduct.tmul_add]
        simp [Prod.mk_add_mk]
    | add u₁ u₂ hu₁ hu₂ =>
      have h : ((0 : ℂ ⊗[ℝ] G₂), (u₁ + u₂) ⊗ₜ[ℂ] v, (0 : ℂ ⊗[ℝ] F₄)) =
          (0, u₁ ⊗ₜ[ℂ] v, 0) + (0, u₂ ⊗ₜ[ℂ] v, 0) := by
        refine Prod.ext ?_ (Prod.ext (TensorProduct.add_tmul _ _ _) ?_) <;> simp
      rw [h, map_add, ext_lie_add, map_add, hu₁, hu₂, TensorProduct.add_tmul]
      simp [Prod.mk_add_mk]
  | add f₁ f₂ hf₁ hf₂ =>
    have h : ((0 : ℂ ⊗[ℝ] G₂), (0 : (ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀)), f₁ + f₂) =
        (0, 0, f₁) + (0, 0, f₂) := by
      refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp
    rw [h, map_add, ext_add_lie, map_add, hf₁, hf₂, map_add, LinearMap.add_apply,
      TensorProduct.tmul_add]
    simp [Prod.mk_add_mk]

private theorem ms_split_bracket_mixed_mixed {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (u₁ u₂ : ℂ ⊗[ℝ] O₀) (v₁ v₂ : ℂ ⊗[ℝ] J₀) :
    magicSquareTensorSplit O J
        ⁅(magicSquareTensorSplit O J).symm (0, u₁ ⊗ₜ[ℂ] v₁, 0),
          (magicSquareTensorSplit O J).symm (0, u₂ ⊗ₜ[ℂ] v₂, 0)⁆ =
      ((1 / 3 : ℂ) • (magicBilinℂ J.traceBilin₀ v₁ v₂ • magicMap2ℂ O.inner u₁ u₂),
        (magicMap2ℂ O.comm₀ u₁ u₂) ⊗ₜ[ℂ] (magicMap2ℂ J.mul₀ v₁ v₂),
        (-2 : ℂ) • (magicBilinℂ O.bilin₀ u₁ u₂ • magicMap2ℂ J.inner v₁ v₂)) := by
  induction u₁ using TensorProduct.inductionOn with
  | tmul z₁ a =>
    induction v₁ using TensorProduct.inductionOn with
    | tmul w₁ x =>
      induction u₂ using TensorProduct.inductionOn with
      | tmul z₂ b =>
        induction v₂ using TensorProduct.inductionOn with
        | tmul w₂ y =>
          rw [magicSquareTensorSplit_symm_mixed, magicSquareTensorSplit_symm_mixed,
            tensorMixCollapse_tmul, tensorMixCollapse_tmul,
            LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
            LieAlgebra.ExtendScalars.bracket_tmul, ms_lie_eq_bracketLM, msBracket_mixed_mixed,
            magicMixedToG2LM_tmul, magicMixedToMixedLM_tmul, magicMixedToF4LM_tmul,
            TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add]
          simp only [magicSquareTensorSplit_tmul, msEmbedG2LM_g2, msEmbedG2LM_mixed,
            msEmbedG2LM_f4, msEmbedMixed_g2, msEmbedMixed_mixed, msEmbedMixed_f4,
            msEmbedF4LM_g2, msEmbedF4LM_mixed, msEmbedF4LM_f4, TensorProduct.tmul_zero,
            tensorMixCollapse_symm_tmul, map_zero, magicBilinℂ_tmul, magicMap2ℂ_tmul,
            Prod.mk_add_mk, add_zero, zero_add]
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · dsimp only
            rw [TensorProduct.tmul_smul,
              show (z₁ * w₁ * (z₂ * w₂)) ⊗ₜ[ℝ] ((O.inner a) b) =
                  (z₁ * w₁ * (z₂ * w₂)) • ((1 : ℂ) ⊗ₜ[ℝ] ((O.inner a) b)) by
                rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
              show (z₁ * z₂) ⊗ₜ[ℝ] ((O.inner a) b) =
                  (z₁ * z₂) • ((1 : ℂ) ⊗ₜ[ℝ] ((O.inner a) b)) by
                rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
              ← IsScalarTower.algebraMap_smul ℂ (1 / 3 * (J.traceBilin₀ x) y)]
            simp only [smul_smul]
            congr 1; simp; ring
          · dsimp only
            rw [show ((z₁ * z₂) ⊗ₜ[ℝ] ((O.comm₀ a) b)) =
                  (z₁ * z₂) • ((1 : ℂ) ⊗ₜ[ℝ] ((O.comm₀ a) b)) by
                rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
              show ((w₁ * w₂) ⊗ₜ[ℝ] ((J.mul₀ x) y)) =
                  (w₁ * w₂) • ((1 : ℂ) ⊗ₜ[ℝ] ((J.mul₀ x) y)) by
                rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
              ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
            congr 1
            ring
          · dsimp only
            rw [TensorProduct.tmul_smul,
              show (z₁ * w₁ * (z₂ * w₂)) ⊗ₜ[ℝ] ((J.inner x) y) =
                  (z₁ * w₁ * (z₂ * w₂)) • ((1 : ℂ) ⊗ₜ[ℝ] ((J.inner x) y)) by
                rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
              show (w₁ * w₂) ⊗ₜ[ℝ] ((J.inner x) y) =
                  (w₁ * w₂) • ((1 : ℂ) ⊗ₜ[ℝ] ((J.inner x) y)) by
                rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
              ← IsScalarTower.algebraMap_smul ℂ (-2 * (O.bilin₀ a) b)]
            simp only [smul_smul]
            congr 1; simp; ring
        | add v₂' v₂'' hv₂' hv₂'' =>
          have h : ((0 : ℂ ⊗[ℝ] G₂), (z₂ ⊗ₜ[ℝ] b) ⊗ₜ[ℂ] (v₂' + v₂''), (0 : ℂ ⊗[ℝ] F₄)) =
              (0, (z₂ ⊗ₜ[ℝ] b) ⊗ₜ[ℂ] v₂', 0) + (0, (z₂ ⊗ₜ[ℝ] b) ⊗ₜ[ℂ] v₂'', 0) := by
            refine Prod.ext ?_ (Prod.ext (TensorProduct.tmul_add _ _ _) ?_) <;> simp
          rw [h, map_add, ext_lie_add, map_add, hv₂', hv₂'', map_add, map_add,
            TensorProduct.tmul_add]
          simp only [Prod.mk_add_mk, map_add, smul_add, add_smul]
      | add u₂' u₂'' hu₂' hu₂'' =>
        have h : ((0 : ℂ ⊗[ℝ] G₂), (u₂' + u₂'') ⊗ₜ[ℂ] v₂, (0 : ℂ ⊗[ℝ] F₄)) =
            (0, u₂' ⊗ₜ[ℂ] v₂, 0) + (0, u₂'' ⊗ₜ[ℂ] v₂, 0) := by
          refine Prod.ext ?_ (Prod.ext (TensorProduct.add_tmul _ _ _) ?_) <;> simp
        rw [h, map_add, ext_lie_add, map_add, hu₂', hu₂'', map_add, map_add,
          TensorProduct.add_tmul]
        simp only [Prod.mk_add_mk, map_add, smul_add, add_smul]
    | add v₁' v₁'' hv₁' hv₁'' =>
      have h : ((0 : ℂ ⊗[ℝ] G₂), (z₁ ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] (v₁' + v₁''), (0 : ℂ ⊗[ℝ] F₄)) =
          (0, (z₁ ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] v₁', 0) + (0, (z₁ ⊗ₜ[ℝ] a) ⊗ₜ[ℂ] v₁'', 0) := by
        refine Prod.ext ?_ (Prod.ext (TensorProduct.tmul_add _ _ _) ?_) <;> simp
      rw [h, map_add, ext_add_lie, map_add, hv₁', hv₁'', map_add, LinearMap.add_apply,
        map_add, LinearMap.add_apply, TensorProduct.tmul_add]
      simp only [Prod.mk_add_mk, map_add, LinearMap.add_apply, smul_add, add_smul]
  | add u₁' u₁'' hu₁' hu₁'' =>
    have h : ((0 : ℂ ⊗[ℝ] G₂), (u₁' + u₁'') ⊗ₜ[ℂ] v₁, (0 : ℂ ⊗[ℝ] F₄)) =
        (0, u₁' ⊗ₜ[ℂ] v₁, 0) + (0, u₁'' ⊗ₜ[ℂ] v₁, 0) := by
      refine Prod.ext ?_ (Prod.ext (TensorProduct.add_tmul _ _ _) ?_) <;> simp
    rw [h, map_add, ext_add_lie, map_add, hu₁', hu₁'', map_add, LinearMap.add_apply,
      map_add, LinearMap.add_apply, TensorProduct.add_tmul]
    simp only [Prod.mk_add_mk, map_add, LinearMap.add_apply, smul_add, add_smul]

private def mkMagicSquareComplexLieEquiv {O₀ G₂ J₀ F₄ O₀' G₂' J₀' F₄' : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    [AddCommGroup O₀'] [Module ℝ O₀'] [LieRing G₂'] [LieAlgebra ℝ G₂']
    [AddCommGroup J₀'] [Module ℝ J₀'] [LieRing F₄'] [LieAlgebra ℝ F₄']
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (O' : OctonionMagicDatum O₀' G₂') (J' : JordanMagicDatum J₀' F₄')
    (ΦG2 : ℂ ⊗[ℝ] G₂ ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] G₂')
    (ΦO : ℂ ⊗[ℝ] O₀ ≃ₗ[ℂ] ℂ ⊗[ℝ] O₀')
    (ΦJ : ℂ ⊗[ℝ] J₀ ≃ₗ[ℂ] ℂ ⊗[ℝ] J₀')
    (ΦF4 : ℂ ⊗[ℝ] F₄ ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] F₄')
    (hObilin : ∀ u₁ u₂, magicBilinℂ O'.bilin₀ (ΦO u₁) (ΦO u₂) = magicBilinℂ O.bilin₀ u₁ u₂)
    (hOcomm : ∀ u₁ u₂, ΦO (magicMap2ℂ O.comm₀ u₁ u₂) = magicMap2ℂ O'.comm₀ (ΦO u₁) (ΦO u₂))
    (hOact : ∀ D u, ΦO (magicActℂ O.act D u) = magicActℂ O'.act (ΦG2 D) (ΦO u))
    (hOinner : ∀ u₁ u₂, ΦG2 (magicMap2ℂ O.inner u₁ u₂) = magicMap2ℂ O'.inner (ΦO u₁) (ΦO u₂))
    (hJtrace : ∀ v₁ v₂, magicBilinℂ J'.traceBilin₀ (ΦJ v₁) (ΦJ v₂) =
      magicBilinℂ J.traceBilin₀ v₁ v₂)
    (hJmul : ∀ v₁ v₂, ΦJ (magicMap2ℂ J.mul₀ v₁ v₂) = magicMap2ℂ J'.mul₀ (ΦJ v₁) (ΦJ v₂))
    (hJact : ∀ F v, ΦJ (magicActℂ J.act F v) = magicActℂ J'.act (ΦF4 F) (ΦJ v))
    (hJinner : ∀ v₁ v₂, ΦF4 (magicMap2ℂ J.inner v₁ v₂) = magicMap2ℂ J'.inner (ΦJ v₁) (ΦJ v₂)) :
    ℂ ⊗[ℝ] MagicSquareLie O J ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] MagicSquareLie O' J' :=
  let s := magicSquareTensorSplit O J
  let s' := magicSquareTensorSplit O' J'
  let P : ((ℂ ⊗[ℝ] G₂) × (((ℂ ⊗[ℝ] O₀) ⊗[ℂ] (ℂ ⊗[ℝ] J₀)) × (ℂ ⊗[ℝ] F₄))) ≃ₗ[ℂ]
      ((ℂ ⊗[ℝ] G₂') × (((ℂ ⊗[ℝ] O₀') ⊗[ℂ] (ℂ ⊗[ℝ] J₀')) × (ℂ ⊗[ℝ] F₄'))) :=
    LinearEquiv.prodCongr ΦG2.toLinearEquiv
      (LinearEquiv.prodCongr (TensorProduct.congr ΦO ΦJ) ΦF4.toLinearEquiv)
  let Φ := s.trans (P.trans s'.symm)
  { toFun := Φ
    invFun := Φ.symm
    left_inv := Φ.left_inv
    right_inv := Φ.right_inv
    map_add' := Φ.map_add'
    map_smul' := Φ.map_smul'
    map_lie' := fun {X Y} => by
      have hmain : ∀ x y, P (s ⁅s.symm x, s.symm y⁆) = s' ⁅s'.symm (P x), s'.symm (P y)⁆ := by
        intro x y
        rcases x with ⟨xg, xm, xf⟩
        rcases y with ⟨yg, ym, yf⟩
        have hx : (xg, xm, xf) = (xg, 0, 0) + (0, xm, 0) + (0, 0, xf) := by
          refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
        have hy : (yg, ym, yf) = (yg, 0, 0) + (0, ym, 0) + (0, 0, yf) := by
          refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
        have h_gg : ∀ d₁ d₂,
            P (s ⁅s.symm (d₁, 0, 0), s.symm (d₂, 0, 0)⁆) =
              s' ⁅s'.symm (P (d₁, 0, 0)), s'.symm (P (d₂, 0, 0))⁆ := by
          intro d₁ d₂
          rw [ms_split_bracket_g2_g2]
          dsimp [P]
          simp only [map_zero]
          rw [ms_split_bracket_g2_g2, ΦG2.map_lie]
        have h_ff : ∀ f₁ f₂,
            P (s ⁅s.symm (0, 0, f₁), s.symm (0, 0, f₂)⁆) =
              s' ⁅s'.symm (P (0, 0, f₁)), s'.symm (P (0, 0, f₂))⁆ := by
          intro f₁ f₂
          rw [ms_split_bracket_f4_f4]
          dsimp [P]
          simp only [map_zero]
          rw [ms_split_bracket_f4_f4, ΦF4.map_lie]
        have h_gf : ∀ d f,
            P (s ⁅s.symm (d, 0, 0), s.symm (0, 0, f)⁆) =
              s' ⁅s'.symm (P (d, 0, 0)), s'.symm (P (0, 0, f))⁆ := by
          intro d f
          rw [ms_split_bracket_g2_f4]
          dsimp [P]
          simp only [map_zero]
          rw [ms_split_bracket_g2_f4]
          rfl
        have h_fg : ∀ f d,
            P (s ⁅s.symm (0, 0, f), s.symm (d, 0, 0)⁆) =
              s' ⁅s'.symm (P (0, 0, f)), s'.symm (P (d, 0, 0))⁆ := by
          intro f d
          rw [← ext_lie_skew (s.symm (0, 0, f)) (s.symm (d, 0, 0)), map_neg, map_neg, h_gf,
            ← map_neg, ← ext_lie_skew (s'.symm (P (0, 0, f))) (s'.symm (P (d, 0, 0))), map_neg]
        have h_gm : ∀ d m,
            P (s ⁅s.symm (d, 0, 0), s.symm (0, m, 0)⁆) =
              s' ⁅s'.symm (P (d, 0, 0)), s'.symm (P (0, m, 0))⁆ := by
          intro d m
          induction m using TensorProduct.inductionOn with
          | tmul u v =>
            rw [ms_split_bracket_g2_mixed]
            dsimp [P]
            simp only [map_zero]
            rw [ms_split_bracket_g2_mixed, hOact]
          | add m₁ m₂ hm₁ hm₂ =>
            have hadd : ((0 : ℂ ⊗[ℝ] G₂), m₁ + m₂, (0 : ℂ ⊗[ℝ] F₄)) =
                (0, m₁, 0) + (0, m₂, 0) := by
              refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
            rw [hadd, map_add, ext_lie_add, map_add, map_add, hm₁, hm₂]
            simp only [map_add, ext_lie_add]
        have h_mg : ∀ m d,
            P (s ⁅s.symm (0, m, 0), s.symm (d, 0, 0)⁆) =
              s' ⁅s'.symm (P (0, m, 0)), s'.symm (P (d, 0, 0))⁆ := by
          intro m d
          rw [← ext_lie_skew (s.symm (0, m, 0)) (s.symm (d, 0, 0)), map_neg, map_neg, h_gm,
            ← map_neg, ← ext_lie_skew (s'.symm (P (0, m, 0))) (s'.symm (P (d, 0, 0))), map_neg]
        have h_fm : ∀ f m,
            P (s ⁅s.symm (0, 0, f), s.symm (0, m, 0)⁆) =
              s' ⁅s'.symm (P (0, 0, f)), s'.symm (P (0, m, 0))⁆ := by
          intro f m
          induction m using TensorProduct.inductionOn with
          | tmul u v =>
            rw [ms_split_bracket_f4_mixed]
            dsimp [P]
            simp only [map_zero]
            rw [ms_split_bracket_f4_mixed, hJact]
          | add m₁ m₂ hm₁ hm₂ =>
            have hadd : ((0 : ℂ ⊗[ℝ] G₂), m₁ + m₂, (0 : ℂ ⊗[ℝ] F₄)) =
                (0, m₁, 0) + (0, m₂, 0) := by
              refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
            rw [hadd, map_add, ext_lie_add, map_add, map_add, hm₁, hm₂]
            simp only [map_add, ext_lie_add]
        have h_mf : ∀ m f,
            P (s ⁅s.symm (0, m, 0), s.symm (0, 0, f)⁆) =
              s' ⁅s'.symm (P (0, m, 0)), s'.symm (P (0, 0, f))⁆ := by
          intro m f
          rw [← ext_lie_skew (s.symm (0, m, 0)) (s.symm (0, 0, f)), map_neg, map_neg, h_fm,
            ← map_neg, ← ext_lie_skew (s'.symm (P (0, m, 0))) (s'.symm (P (0, 0, f))), map_neg]
        have h_mm : ∀ m₁ m₂,
            P (s ⁅s.symm (0, m₁, 0), s.symm (0, m₂, 0)⁆) =
              s' ⁅s'.symm (P (0, m₁, 0)), s'.symm (P (0, m₂, 0))⁆ := by
          intro m₁ m₂
          induction m₁ using TensorProduct.inductionOn with
          | tmul u₁ v₁ =>
            induction m₂ using TensorProduct.inductionOn with
            | tmul u₂ v₂ =>
              rw [ms_split_bracket_mixed_mixed]
              dsimp [P]
              simp only [map_zero, map_smul, hOinner, hOcomm, hJmul, hJinner]
              rw [← hJtrace, ← hObilin]
              rw [ms_split_bracket_mixed_mixed]
            | add a b ha hb =>
              have hadd : ((0 : ℂ ⊗[ℝ] G₂), a + b, (0 : ℂ ⊗[ℝ] F₄)) =
                  (0, a, 0) + (0, b, 0) := by
                refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
              rw [hadd, map_add, ext_lie_add, map_add, map_add, ha, hb]
              simp only [map_add, ext_lie_add]
          | add a b ha hb =>
            have hadd : ((0 : ℂ ⊗[ℝ] G₂), a + b, (0 : ℂ ⊗[ℝ] F₄)) =
                (0, a, 0) + (0, b, 0) := by
              refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
            rw [hadd, map_add, ext_add_lie, map_add, map_add, ha, hb]
            simp only [map_add, ext_add_lie]
        conv_lhs => rw [hx, hy]
        simp only [map_add, ext_add_lie, ext_lie_add, h_gg, h_gm, h_gf, h_mg, h_mm, h_mf,
          h_fg, h_fm, h_ff]
        conv_rhs => rw [hx, hy]
        simp only [map_add, ext_add_lie, ext_lie_add]
      apply s'.injective
      have h := hmain (s X) (s Y)
      simpa [Φ, LinearEquiv.trans_apply] using h }

section H3TraceZeroComplexEquiv

private def h3OctTraceLinearℂ : H3Octonion ℂ →ₗ[ℂ] ℂ where
  toFun := H3Octonion.linearTrace
  map_add' := H3Octonion.linearTrace_add
  map_smul' := H3Octonion.linearTrace_smul

private def h3ZornTraceLinearℂ : H3Zorn ℂ →ₗ[ℂ] ℂ where
  toFun := H3Zorn.linearTrace
  map_add' := H3Zorn.linearTrace_add
  map_smul' := H3Zorn.linearTrace_smul

private def h3OctonionTraceZeroℂ : Submodule ℂ (H3Octonion ℂ) :=
  LinearMap.ker h3OctTraceLinearℂ

private def h3TraceZeroℂ : Submodule ℂ (H3Zorn ℂ) :=
  LinearMap.ker h3ZornTraceLinearℂ

private def ofRealH3Oct0 : h3OctonionTraceZero →ₗ[ℝ] h3OctonionTraceZeroℂ where
  toFun x := ⟨ofRealH3Octonion x.1, by
    change H3Octonion.linearTrace (ofRealH3Octonion x.1) = 0
    rw [ofRealH3Octonion_linearTrace]
    have hx : H3Octonion.linearTrace x.1 = 0 := x.2
    rw [hx, Complex.ofReal_zero]⟩
  map_add' x y := by apply Subtype.ext; exact ofRealH3Octonion.map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    simp

private def rePartH3Oct0 : h3OctonionTraceZeroℂ →ₗ[ℝ] h3OctonionTraceZero where
  toFun x := ⟨rePartH3Octonion x.1, by
    change H3Octonion.linearTrace (rePartH3Octonion x.1) = 0
    have htr : H3Octonion.linearTrace (rePartH3Octonion x.1) =
        (H3Octonion.linearTrace x.1).re := by
      simp [H3Octonion.linearTrace, rePartH3Octonion]
    have hx : H3Octonion.linearTrace x.1 = 0 := x.2
    rw [htr, hx, Complex.zero_re]⟩
  map_add' x y := by apply Subtype.ext; exact rePartH3Octonion.map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    simp

private def imPartH3Oct0 : h3OctonionTraceZeroℂ →ₗ[ℝ] h3OctonionTraceZero where
  toFun x := ⟨imPartH3Octonion x.1, by
    change H3Octonion.linearTrace (imPartH3Octonion x.1) = 0
    have htr : H3Octonion.linearTrace (imPartH3Octonion x.1) =
        (H3Octonion.linearTrace x.1).im := by
      simp [H3Octonion.linearTrace, imPartH3Octonion]
    have hx : H3Octonion.linearTrace x.1 = 0 := x.2
    rw [htr, hx, Complex.zero_im]⟩
  map_add' x y := by apply Subtype.ext; exact imPartH3Octonion.map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    simp

private def ofRealH3Zorn0 : h3TraceZero →ₗ[ℝ] h3TraceZeroℂ where
  toFun x := ⟨ofRealH3Zorn x.1, by
    change H3Zorn.linearTrace (ofRealH3Zorn x.1) = 0
    rw [ofRealH3Zorn_linearTrace]
    have hx : H3Zorn.linearTrace x.1 = 0 := x.2
    rw [hx, Complex.ofReal_zero]⟩
  map_add' x y := by apply Subtype.ext; exact ofRealH3Zorn.map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    simp

private def rePartH3Zorn0 : h3TraceZeroℂ →ₗ[ℝ] h3TraceZero where
  toFun x := ⟨rePartH3Zorn x.1, by
    change H3Zorn.linearTrace (rePartH3Zorn x.1) = 0
    have htr : H3Zorn.linearTrace (rePartH3Zorn x.1) = (H3Zorn.linearTrace x.1).re := by
      simp [H3Zorn.linearTrace, rePartH3Zorn]
    have hx : H3Zorn.linearTrace x.1 = 0 := x.2
    rw [htr, hx, Complex.zero_re]⟩
  map_add' x y := by apply Subtype.ext; exact rePartH3Zorn.map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    simp

private def imPartH3Zorn0 : h3TraceZeroℂ →ₗ[ℝ] h3TraceZero where
  toFun x := ⟨imPartH3Zorn x.1, by
    change H3Zorn.linearTrace (imPartH3Zorn x.1) = 0
    have htr : H3Zorn.linearTrace (imPartH3Zorn x.1) = (H3Zorn.linearTrace x.1).im := by
      simp [H3Zorn.linearTrace, imPartH3Zorn]
    have hx : H3Zorn.linearTrace x.1 = 0 := x.2
    rw [htr, hx, Complex.zero_im]⟩
  map_add' x y := by apply Subtype.ext; exact imPartH3Zorn.map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    simp

private def tensorEquivH3OctonionTraceZeroℂ :
    ℂ ⊗[ℝ] h3OctonionTraceZero ≃ₗ[ℂ] h3OctonionTraceZeroℂ :=
  mkComplexTensorEquiv ofRealH3Oct0 rePartH3Oct0 imPartH3Oct0
    (fun a => Subtype.ext (rePartH3Octonion_ofReal a.1))
    (fun a => Subtype.ext (imPartH3Octonion_ofReal a.1))
    (fun w => Subtype.ext (ofReal_rePart_add_I_imPart_H3Octonion w.1))
    (fun w => Subtype.ext (rePartH3Octonion_I_smul w.1))
    (fun w => Subtype.ext (imPartH3Octonion_I_smul w.1))

private def tensorEquivH3ZornTraceZeroℂ :
    ℂ ⊗[ℝ] h3TraceZero ≃ₗ[ℂ] h3TraceZeroℂ :=
  mkComplexTensorEquiv ofRealH3Zorn0 rePartH3Zorn0 imPartH3Zorn0
    (fun a => Subtype.ext (rePartH3Zorn_ofReal a.1))
    (fun a => Subtype.ext (imPartH3Zorn_ofReal a.1))
    (fun w => Subtype.ext (ofReal_rePart_add_I_imPart_H3Zorn w.1))
    (fun w => Subtype.ext (rePartH3Zorn_I_smul w.1))
    (fun w => Subtype.ext (imPartH3Zorn_I_smul w.1))

private def h3OctonionTraceZeroComplexEquiv : h3OctonionTraceZeroℂ ≃ₗ[ℂ] h3TraceZeroℂ where
  toFun a := ⟨h3OctonionComplexEquiv a.1, by
    change H3Zorn.linearTrace (h3OctonionComplexEquiv a.1) = 0
    rw [h3OctonionComplexEquiv_linearTrace]
    exact a.2⟩
  invFun a := ⟨h3OctonionComplexEquiv.symm a.1, by
    change H3Octonion.linearTrace (h3OctonionComplexEquiv.symm a.1) = 0
    rw [← h3OctonionComplexEquiv_linearTrace (h3OctonionComplexEquiv.symm a.1),
      h3OctonionComplexEquiv.apply_symm_apply]
    exact a.2⟩
  left_inv _ := Subtype.ext (h3OctonionComplexEquiv.symm_apply_apply _)
  right_inv _ := Subtype.ext (h3OctonionComplexEquiv.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (h3OctonionComplexEquiv.map_add _ _)
  map_smul' _ _ := Subtype.ext (h3OctonionComplexEquiv.map_smul _ _)

private def h3OctonionTraceZeroBaseChangeEquiv :
    ℂ ⊗[ℝ] h3OctonionTraceZero ≃ₗ[ℂ] ℂ ⊗[ℝ] h3TraceZero :=
  tensorEquivH3OctonionTraceZeroℂ.trans
    (h3OctonionTraceZeroComplexEquiv.trans tensorEquivH3ZornTraceZeroℂ.symm)

@[simp] private theorem tensorEquivH3OctonionTraceZeroℂ_tmul
    (z : ℂ) (x : h3OctonionTraceZero) :
    (tensorEquivH3OctonionTraceZeroℂ (z ⊗ₜ[ℝ] x)).1 = z • ofRealH3Octonion x.1 := rfl

@[simp] private theorem tensorEquivH3ZornTraceZeroℂ_tmul
    (z : ℂ) (x : h3TraceZero) :
    (tensorEquivH3ZornTraceZeroℂ (z ⊗ₜ[ℝ] x)).1 = z • ofRealH3Zorn x.1 := rfl

end H3TraceZeroComplexEquiv

section CompactToQuaternionic

private theorem h3Oct_traceBilinℂ_eq (v₁ v₂ : ℂ ⊗[ℝ] h3OctonionTraceZero) :
    magicBilinℂ h3OctonionJordanDatum.traceBilin₀ v₁ v₂ =
      H3Octonion.traceBilin
        (tensorEquivH3OctonionTraceZeroℂ v₁).1
        (tensorEquivH3OctonionTraceZeroℂ v₂).1 := by
  induction v₁ using TensorProduct.inductionOn with
  | tmul z₁ x₁ =>
    induction v₂ using TensorProduct.inductionOn with
    | tmul z₂ x₂ =>
      simp only [magicBilinℂ_tmul, tensorEquivH3OctonionTraceZeroℂ_tmul,
        H3Octonion.traceBilin_smul_left, H3Octonion.traceBilin_smul_right,
        ofRealH3Octonion_traceBilin]
      rw [mul_comm z₁ z₂, mul_assoc]; rfl
    | add a b ha hb =>
      simp only [map_add, Submodule.coe_add, H3Octonion.traceBilin_add_right] at ha hb ⊢
      rw [ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add,
      H3Octonion.traceBilin_add_left] at ha hb ⊢
    rw [ha, hb]

private theorem h3Zorn_traceBilinℂ_eq (v₁ v₂ : ℂ ⊗[ℝ] h3TraceZero) :
    magicBilinℂ h3ZornJordanDatum.traceBilin₀ v₁ v₂ =
      H3Zorn.traceBilin
        (tensorEquivH3ZornTraceZeroℂ v₁).1
        (tensorEquivH3ZornTraceZeroℂ v₂).1 := by
  induction v₁ using TensorProduct.inductionOn with
  | tmul z₁ x₁ =>
    induction v₂ using TensorProduct.inductionOn with
    | tmul z₂ x₂ =>
      simp only [magicBilinℂ_tmul, tensorEquivH3ZornTraceZeroℂ_tmul,
        H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right,
        ofRealH3Zorn_traceBilin]
      rw [mul_comm z₁ z₂, mul_assoc]; rfl
    | add a b ha hb =>
      simp only [map_add, Submodule.coe_add, H3Zorn.traceBilin_add_right] at ha hb ⊢
      rw [ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add,
      H3Zorn.traceBilin_add_left] at ha hb ⊢
    rw [ha, hb]

private theorem h3Oct_mulℂ_eq (v₁ v₂ : ℂ ⊗[ℝ] h3OctonionTraceZero) :
    (tensorEquivH3OctonionTraceZeroℂ (magicMap2ℂ h3OctonionJordanDatum.mul₀ v₁ v₂)).1 =
      candidateJordanMulOctℂ
        (tensorEquivH3OctonionTraceZeroℂ v₁).1
        (tensorEquivH3OctonionTraceZeroℂ v₂).1 -
      ((1 / 3 : ℂ) * H3Octonion.traceBilin
        (tensorEquivH3OctonionTraceZeroℂ v₁).1
        (tensorEquivH3OctonionTraceZeroℂ v₂).1) • (1 : H3Octonion ℂ) := by
  induction v₁ using TensorProduct.inductionOn with
  | tmul z₁ x₁ =>
    induction v₂ using TensorProduct.inductionOn with
    | tmul z₂ x₂ =>
      simp only [magicMap2ℂ_tmul, tensorEquivH3OctonionTraceZeroℂ_tmul,
        candidateJordanMulOctℂ_smul_left, candidateJordanMulOctℂ_smul_right,
        H3Octonion.traceBilin_smul_left, H3Octonion.traceBilin_smul_right,
        ofRealH3Octonion_traceBilin]
      change (z₁ * z₂) • ofRealH3Octonion (h3OctMul0 x₁ x₂).1 = _
      rw [h3OctMul0_coe, ofRealH3Octonion.map_sub, ofRealH3Octonion_jordanMul,
        ofRealH3Octonion.map_smul, ofRealH3Octonion_one]
      simp only [← Complex.coe_smul, smul_sub, smul_smul]
      congr 1
      · rw [mul_comm z₂ z₁]
      · congr 1; push_cast; ring
    | add a b ha hb =>
      simp only [map_add, Submodule.coe_add, candidateJordanMulOctℂ_add_right,
        H3Octonion.traceBilin_add_right, mul_add, add_smul] at ha hb ⊢
      rw [ha, hb]; abel
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add,
      candidateJordanMulOctℂ_add_left, H3Octonion.traceBilin_add_left,
      mul_add, add_smul] at ha hb ⊢
    rw [ha, hb]; abel

private theorem h3Zorn_mulℂ_eq (v₁ v₂ : ℂ ⊗[ℝ] h3TraceZero) :
    (tensorEquivH3ZornTraceZeroℂ (magicMap2ℂ h3ZornJordanDatum.mul₀ v₁ v₂)).1 =
      candidateJordanMulZornℂ
        (tensorEquivH3ZornTraceZeroℂ v₁).1
        (tensorEquivH3ZornTraceZeroℂ v₂).1 -
      ((1 / 3 : ℂ) * H3Zorn.traceBilin
        (tensorEquivH3ZornTraceZeroℂ v₁).1
        (tensorEquivH3ZornTraceZeroℂ v₂).1) • (1 : H3Zorn ℂ) := by
  induction v₁ using TensorProduct.inductionOn with
  | tmul z₁ x₁ =>
    induction v₂ using TensorProduct.inductionOn with
    | tmul z₂ x₂ =>
      simp only [magicMap2ℂ_tmul, tensorEquivH3ZornTraceZeroℂ_tmul,
        H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right,
        ofRealH3Zorn_traceBilin]
      rw [candidateJordanMulZornℂ, H3Zorn.T_smul_left, H3Zorn.T_smul_right]
      change (z₁ * z₂) • ofRealH3Zorn (MagicSquareTitsBracket.h3Mul0 x₁ x₂).1 = _
      have hm : (MagicSquareTitsBracket.h3Mul0 x₁ x₂).1 =
          x₁.1 * x₂.1 - ((1 / 3 : ℝ) * H3Zorn.traceBilin x₁.1 x₂.1) • (1 : H3Zorn ℝ) := rfl
      rw [hm, ofRealH3Zorn.map_sub, ofRealH3Zorn_jordanMul, ofRealH3Zorn.map_smul,
        ofRealH3Zorn_one]
      simp only [← Complex.coe_smul, smul_sub, smul_smul]
      change (z₁ * z₂) • candidateJordanMulZornℂ (ofRealH3Zorn x₁.1) (ofRealH3Zorn x₂.1) - _ = _
      simp only [candidateJordanMulZornℂ, smul_smul]
      congr 2 <;> [push_cast; push_cast] <;> ring
    | add a b ha hb =>
      simp only [map_add, Submodule.coe_add, candidateJordanMulZornℂ_add_right,
        H3Zorn.traceBilin_add_right, mul_add, add_smul] at ha hb ⊢
      rw [ha, hb]; abel
  | add a b ha hb =>
    have haddL : ∀ u₁ u₂ v : H3Zorn ℂ,
        candidateJordanMulZornℂ (u₁ + u₂) v =
          candidateJordanMulZornℂ u₁ v + candidateJordanMulZornℂ u₂ v := fun u₁ u₂ v => by
      simp [candidateJordanMulZornℂ, H3Zorn.T_add_left, smul_add]
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, haddL,
      H3Zorn.traceBilin_add_left, mul_add, add_smul] at ha hb ⊢
    rw [ha, hb]; abel

private theorem h3Oct_actℂ_eq (F : ℂ ⊗[ℝ] H3OctonionF4Derivations)
    (v : ℂ ⊗[ℝ] h3OctonionTraceZero) :
    (tensorEquivH3OctonionTraceZeroℂ (magicActℂ h3OctonionJordanDatum.act F v)).1 =
      (h3OctonionF4DerivationsExtendEquiv F).1 (tensorEquivH3OctonionTraceZeroℂ v).1 := by
  induction F using TensorProduct.inductionOn with
  | tmul z₁ f =>
    induction v using TensorProduct.inductionOn with
    | tmul z₂ x =>
      simp only [magicActℂ_tmul, tensorEquivH3OctonionTraceZeroℂ_tmul, map_smul]
      have hf : (h3OctonionF4DerivationsExtendEquiv ((1 : ℂ) ⊗ₜ[ℝ] f)).1 =
          liftEnd tensorEquivH3Octonion f.1 := by
        dsimp [h3OctonionF4DerivationsExtendEquiv, mkBaseChangeLieEquiv]
        erw [TensorProduct.AlgebraTensorModule.lift_tmul]
        simp
      rw [show (z₁ ⊗ₜ[ℝ] f) = z₁ • ((1 : ℂ) ⊗ₜ[ℝ] f) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
      simp only [SetLike.val_smul, LinearMap.smul_apply, hf]
      rw [liftEnd_apply_ofReal tensorEquivH3Octonion ofRealH3Octonion
        tensorEquivH3Octonion_tmul, ← mul_smul, mul_comm z₂ z₁]
      rfl
    | add a b ha hb =>
      simp only [map_add, Submodule.coe_add] at ha hb ⊢; rw [ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, AddMemClass.coe_add] at ha hb ⊢
    rw [ha, hb]

private theorem h3Zorn_actℂ_eq (F : ℂ ⊗[ℝ] F4DerivationCarrier) (v : ℂ ⊗[ℝ] h3TraceZero) :
    (tensorEquivH3ZornTraceZeroℂ (magicActℂ h3ZornJordanDatum.act F v)).1 =
      (h3zornF4DerivationsExtendEquiv F).1 (tensorEquivH3ZornTraceZeroℂ v).1 := by
  induction F using TensorProduct.inductionOn with
  | tmul z₁ f =>
    induction v using TensorProduct.inductionOn with
    | tmul z₂ x =>
      simp only [magicActℂ_tmul, tensorEquivH3ZornTraceZeroℂ_tmul, map_smul]
      have hf : (h3zornF4DerivationsExtendEquiv ((1 : ℂ) ⊗ₜ[ℝ] f)).1 =
          liftEnd tensorEquivH3Zorn f.1 := by
        dsimp [h3zornF4DerivationsExtendEquiv, mkBaseChangeLieEquiv]
        erw [TensorProduct.AlgebraTensorModule.lift_tmul]
        simp
      rw [show (z₁ ⊗ₜ[ℝ] f) = z₁ • ((1 : ℂ) ⊗ₜ[ℝ] f) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
      simp only [SetLike.val_smul, LinearMap.smul_apply, hf]
      rw [liftEnd_apply_ofReal tensorEquivH3Zorn ofRealH3Zorn tensorEquivH3Zorn_tmul,
        ← mul_smul, mul_comm z₂ z₁]
      rfl
    | add a b ha hb =>
      simp only [map_add, Submodule.coe_add] at ha hb ⊢; rw [ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, AddMemClass.coe_add] at ha hb ⊢
    rw [ha, hb]

private theorem h3Oct_innerℂ_eq (v₁ v₂ : ℂ ⊗[ℝ] h3OctonionTraceZero) (w : H3Octonion ℂ) :
    (h3OctonionF4DerivationsExtendEquiv (magicMap2ℂ h3OctonionJordanDatum.inner v₁ v₂)).1 w =
      candidateJordanMulOctℂ (tensorEquivH3OctonionTraceZeroℂ v₁).1
        (candidateJordanMulOctℂ (tensorEquivH3OctonionTraceZeroℂ v₂).1 w) -
      candidateJordanMulOctℂ (tensorEquivH3OctonionTraceZeroℂ v₂).1
        (candidateJordanMulOctℂ (tensorEquivH3OctonionTraceZeroℂ v₁).1 w) := by
  induction v₁ using TensorProduct.inductionOn with
  | tmul z₁ x₁ =>
    induction v₂ using TensorProduct.inductionOn with
    | tmul z₂ x₂ =>
      simp only [magicMap2ℂ_tmul, tensorEquivH3OctonionTraceZeroℂ_tmul,
        candidateJordanMulOctℂ_smul_left]
      have hf : (h3OctonionF4DerivationsExtendEquiv
            ((1 : ℂ) ⊗ₜ[ℝ] h3OctonionJordanDatum.inner x₁ x₂)).1 =
          liftEnd tensorEquivH3Octonion (h3OctF4Inner x₁ x₂).1 := by
        dsimp [h3OctonionF4DerivationsExtendEquiv, mkBaseChangeLieEquiv]
        erw [TensorProduct.AlgebraTensorModule.lift_tmul]
        simp; rfl
      rw [show ((z₁ * z₂) ⊗ₜ[ℝ] h3OctonionJordanDatum.inner x₁ x₂) =
        (z₁ * z₂) • ((1 : ℂ) ⊗ₜ[ℝ] h3OctonionJordanDatum.inner x₁ x₂) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
      simp only [SetLike.val_smul, LinearMap.smul_apply, hf]
      rw [← ofReal_rePart_add_I_imPart_H3Octonion w]
      have hreal : ∀ w₀ : H3Octonion ℝ,
          liftEnd tensorEquivH3Octonion (h3OctF4Inner x₁ x₂).1 (ofRealH3Octonion w₀) =
            candidateJordanMulOctℂ (ofRealH3Octonion x₁.1)
              (candidateJordanMulOctℂ (ofRealH3Octonion x₂.1) (ofRealH3Octonion w₀)) -
            candidateJordanMulOctℂ (ofRealH3Octonion x₂.1)
              (candidateJordanMulOctℂ (ofRealH3Octonion x₁.1) (ofRealH3Octonion w₀)) := by
        intro w₀
        rw [liftEnd_apply_ofReal tensorEquivH3Octonion ofRealH3Octonion tensorEquivH3Octonion_tmul]
        change ofRealH3Octonion (x₁.1 * (x₂.1 * w₀) - x₂.1 * (x₁.1 * w₀)) = _
        rw [ofRealH3Octonion.map_sub, ofRealH3Octonion_jordanMul, ofRealH3Octonion_jordanMul,
          ofRealH3Octonion_jordanMul, ofRealH3Octonion_jordanMul]
      simp only [map_add, map_smul, hreal, candidateJordanMulOctℂ_add_right,
        candidateJordanMulOctℂ_smul_right, smul_sub, smul_add, smul_smul]
      rw [show z₁ * (z₂ * Complex.I) = z₁ * z₂ * Complex.I by ring,
        show z₂ * (z₁ * Complex.I) = z₁ * z₂ * Complex.I by ring,
        mul_comm z₂ z₁]
      abel
    | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply, AddMemClass.coe_add,
        candidateJordanMulOctℂ_add_left, candidateJordanMulOctℂ_add_right] at ha hb ⊢
      rw [ha, hb]; abel
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, AddMemClass.coe_add,
      candidateJordanMulOctℂ_add_left, candidateJordanMulOctℂ_add_right] at ha hb ⊢
    rw [ha, hb]; abel

private theorem h3Zorn_innerℂ_eq (v₁ v₂ : ℂ ⊗[ℝ] h3TraceZero) (W : H3Zorn ℂ) :
    (h3zornF4DerivationsExtendEquiv (magicMap2ℂ h3ZornJordanDatum.inner v₁ v₂)).1 W =
      candidateJordanMulZornℂ (tensorEquivH3ZornTraceZeroℂ v₁).1
        (candidateJordanMulZornℂ (tensorEquivH3ZornTraceZeroℂ v₂).1 W) -
      candidateJordanMulZornℂ (tensorEquivH3ZornTraceZeroℂ v₂).1
        (candidateJordanMulZornℂ (tensorEquivH3ZornTraceZeroℂ v₁).1 W) := by
  have haddL : ∀ u₁ u₂ v : H3Zorn ℂ,
      candidateJordanMulZornℂ (u₁ + u₂) v =
        candidateJordanMulZornℂ u₁ v + candidateJordanMulZornℂ u₂ v := fun u₁ u₂ v => by
    simp [candidateJordanMulZornℂ, H3Zorn.T_add_left, smul_add]
  have hsmulL : ∀ (c : ℂ) (u v : H3Zorn ℂ),
      candidateJordanMulZornℂ (c • u) v = c • candidateJordanMulZornℂ u v := fun c u v => by
    rw [candidateJordanMulZornℂ, candidateJordanMulZornℂ, H3Zorn.T_smul_left,
      smul_comm c (1 / 2 : ℂ)]
  induction v₁ using TensorProduct.inductionOn with
  | tmul z₁ x₁ =>
    induction v₂ using TensorProduct.inductionOn with
    | tmul z₂ x₂ =>
      simp only [magicMap2ℂ_tmul, tensorEquivH3ZornTraceZeroℂ_tmul, hsmulL]
      have hf : (h3zornF4DerivationsExtendEquiv
            ((1 : ℂ) ⊗ₜ[ℝ] h3ZornJordanDatum.inner x₁ x₂)).1 =
          liftEnd tensorEquivH3Zorn (MagicSquareTitsBracket.f4Inner x₁ x₂).1 := by
        dsimp [h3zornF4DerivationsExtendEquiv, mkBaseChangeLieEquiv]
        erw [TensorProduct.AlgebraTensorModule.lift_tmul]
        simp; rfl
      rw [show ((z₁ * z₂) ⊗ₜ[ℝ] h3ZornJordanDatum.inner x₁ x₂) =
        (z₁ * z₂) • ((1 : ℂ) ⊗ₜ[ℝ] h3ZornJordanDatum.inner x₁ x₂) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
      simp only [SetLike.val_smul, LinearMap.smul_apply, hf]
      rw [← ofReal_rePart_add_I_imPart_H3Zorn W]
      have hreal : ∀ W₀ : H3Zorn ℝ,
          liftEnd tensorEquivH3Zorn (MagicSquareTitsBracket.f4Inner x₁ x₂).1 (ofRealH3Zorn W₀) =
            candidateJordanMulZornℂ (ofRealH3Zorn x₁.1)
              (candidateJordanMulZornℂ (ofRealH3Zorn x₂.1) (ofRealH3Zorn W₀)) -
            candidateJordanMulZornℂ (ofRealH3Zorn x₂.1)
              (candidateJordanMulZornℂ (ofRealH3Zorn x₁.1) (ofRealH3Zorn W₀)) := by
        intro W₀
        rw [liftEnd_apply_ofReal tensorEquivH3Zorn ofRealH3Zorn tensorEquivH3Zorn_tmul]
        change ofRealH3Zorn (x₁.1 * (x₂.1 * W₀) - x₂.1 * (x₁.1 * W₀)) = _
        rw [ofRealH3Zorn.map_sub, ofRealH3Zorn_jordanMul, ofRealH3Zorn_jordanMul,
          ofRealH3Zorn_jordanMul, ofRealH3Zorn_jordanMul]
      simp only [map_add, map_smul, hreal, candidateJordanMulZornℂ_add_right,
        candidateJordanMulZornℂ_smul_right, smul_sub, smul_add, smul_smul]
      rw [show z₁ * (z₂ * Complex.I) = z₁ * z₂ * Complex.I by ring,
        show z₂ * (z₁ * Complex.I) = z₁ * z₂ * Complex.I by ring,
        mul_comm z₂ z₁]
      abel
    | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply, AddMemClass.coe_add,
        haddL, candidateJordanMulZornℂ_add_right] at ha hb ⊢
      rw [ha, hb]; abel
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, AddMemClass.coe_add,
      haddL, candidateJordanMulZornℂ_add_right] at ha hb ⊢
    rw [ha, hb]; abel

/-- Complexified `ℂ`-Lie algebra isomorphism between `CompactE8Lie` (`𝔈₈(-248)`) and
`QuaternionicE8Lie` (`𝔈₈(-24)`). -/
def compactToQuaternionicBaseChangeEquiv :
    ℂ ⊗[ℝ] CompactE8Lie ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] QuaternionicE8Lie :=
  mkMagicSquareComplexLieEquiv compactOctonionDatum h3OctonionJordanDatum
    compactOctonionDatum h3ZornJordanDatum
    LieEquiv.refl (LinearEquiv.refl ℂ _)
    h3OctonionTraceZeroBaseChangeEquiv h3OctonionF4DerivationsBaseChangeEquiv
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun v₁ v₂ => by
      rw [h3Zorn_traceBilinℂ_eq, h3Oct_traceBilinℂ_eq]
      dsimp [h3OctonionTraceZeroBaseChangeEquiv]
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact h3OctonionComplexEquiv_traceBilin _ _)
    (fun v₁ v₂ => by
      apply tensorEquivH3ZornTraceZeroℂ.injective
      apply Subtype.ext
      have h1 : (tensorEquivH3ZornTraceZeroℂ (h3OctonionTraceZeroBaseChangeEquiv
            (magicMap2ℂ h3OctonionJordanDatum.mul₀ v₁ v₂))).1 =
          h3OctonionComplexEquiv
            (tensorEquivH3OctonionTraceZeroℂ (magicMap2ℂ h3OctonionJordanDatum.mul₀ v₁ v₂)).1 := by
        dsimp [h3OctonionTraceZeroBaseChangeEquiv]
        rw [LinearEquiv.apply_symm_apply]; rfl
      rw [h1, h3Oct_mulℂ_eq, h3Zorn_mulℂ_eq, map_sub, map_smul, h3OctonionComplexEquiv_jordanMul,
        ← h3OctonionComplexEquiv_traceBilin (tensorEquivH3OctonionTraceZeroℂ v₁).1
          (tensorEquivH3OctonionTraceZeroℂ v₂).1, h3OctonionComplexEquiv_one]
      dsimp [h3OctonionTraceZeroBaseChangeEquiv]
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]; rfl)
    (fun F v => by
      apply tensorEquivH3ZornTraceZeroℂ.injective
      apply Subtype.ext
      have h1 : (tensorEquivH3ZornTraceZeroℂ (h3OctonionTraceZeroBaseChangeEquiv
            (magicActℂ h3OctonionJordanDatum.act F v))).1 =
          h3OctonionComplexEquiv
            (tensorEquivH3OctonionTraceZeroℂ (magicActℂ h3OctonionJordanDatum.act F v)).1 := by
        dsimp [h3OctonionTraceZeroBaseChangeEquiv]
        rw [LinearEquiv.apply_symm_apply]; rfl
      have h2 : (h3zornF4DerivationsExtendEquiv (h3OctonionF4DerivationsBaseChangeEquiv F)).1 =
          h3OctonionComplexEquiv.conj (h3OctonionF4DerivationsExtendEquiv F).1 := by
        dsimp [h3OctonionF4DerivationsBaseChangeEquiv]
        rw [LieEquiv.apply_symm_apply]; rfl
      rw [h1, h3Oct_actℂ_eq, h3Zorn_actℂ_eq, h2, LinearEquiv.conj_apply]
      dsimp [h3OctonionTraceZeroBaseChangeEquiv]
      rw [LinearEquiv.apply_symm_apply]
      change h3OctonionComplexEquiv ((h3OctonionF4DerivationsExtendEquiv F).1
          (tensorEquivH3OctonionTraceZeroℂ v).1) =
        h3OctonionComplexEquiv ((h3OctonionF4DerivationsExtendEquiv F).1
          (h3OctonionComplexEquiv.symm (h3OctonionComplexEquiv
            (tensorEquivH3OctonionTraceZeroℂ v).1)))
      rw [LinearEquiv.symm_apply_apply])
    (fun v₁ v₂ => by
      apply h3zornF4DerivationsExtendEquiv.injective
      apply Subtype.ext; apply LinearMap.ext; intro W
      obtain ⟨w, rfl⟩ := h3OctonionComplexEquiv.surjective W
      have h2 : (h3zornF4DerivationsExtendEquiv
            (h3OctonionF4DerivationsBaseChangeEquiv
              (magicMap2ℂ h3OctonionJordanDatum.inner v₁ v₂))).1 =
          h3OctonionComplexEquiv.conj
            (h3OctonionF4DerivationsExtendEquiv
              (magicMap2ℂ h3OctonionJordanDatum.inner v₁ v₂)).1 := by
        dsimp [h3OctonionF4DerivationsBaseChangeEquiv]
        rw [LieEquiv.apply_symm_apply]; rfl
      simp only [LieEquiv.coe_toLieHom]
      rw [h2, LinearEquiv.conj_apply_apply, h3Oct_innerℂ_eq, h3Zorn_innerℂ_eq,
        map_sub, h3OctonionComplexEquiv_jordanMul, h3OctonionComplexEquiv_jordanMul,
        h3OctonionComplexEquiv_jordanMul, h3OctonionComplexEquiv_jordanMul]
      dsimp [h3OctonionTraceZeroBaseChangeEquiv]
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]; rfl)

end CompactToQuaternionic

section QuaternionicToSplit

private lemma zvmℂ_conj_smul (z : ℂ) (X : ZornVectorMatrix ℂ) :
    (z • X).conj = z • X.conj := ZornVectorMatrix.conj_smul z X

private lemma zvmℂ_smul_mul (z : ℂ) (X Y : ZornVectorMatrix ℂ) :
    (z • X).mul Y = z • X.mul Y := ZornVectorMatrix.smul_mul z X Y

private lemma zvmℂ_mul_smul (z : ℂ) (X Y : ZornVectorMatrix ℂ) :
    X.mul (z • Y) = z • X.mul Y := ZornVectorMatrix.mul_smul z X Y

private lemma zvmℂ_trace_smul (z : ℂ) (X : ZornVectorMatrix ℂ) :
    (z • X).trace = z * X.trace := ZornVectorMatrix.trace_smul z X

private lemma zvmℂ_conj_add (X Y : ZornVectorMatrix ℂ) :
    (X + Y).conj = X.conj + Y.conj := ZornVectorMatrix.conj_add X Y

private lemma zvmℂ_mul_add (X Y Z : ZornVectorMatrix ℂ) :
    X.mul (Y + Z) = X.mul Y + X.mul Z := ZornVectorMatrix.mul_add X Y Z

private lemma zvmℂ_add_mul (X Y Z : ZornVectorMatrix ℂ) :
    (X + Y).mul Z = X.mul Z + Y.mul Z := ZornVectorMatrix.add_mul X Y Z

private lemma zvmℂ_trace_add (X Y : ZornVectorMatrix ℂ) :
    (X + Y).trace = X.trace + Y.trace := ZornVectorMatrix.trace_add X Y

private lemma zvmℂ_sub_mul (X Y Z : ZornVectorMatrix ℂ) :
    (X - Y).mul Z = X.mul Z - Y.mul Z := ZornVectorMatrix.sub_mul X Y Z

private lemma zvmℂ_mul_sub (X Y Z : ZornVectorMatrix ℂ) :
    X.mul (Y - Z) = X.mul Y - X.mul Z := ZornVectorMatrix.mul_sub X Y Z

private theorem compactOct_bilinℂ_eq (u₁ u₂ : ℂ ⊗[ℝ] CompactOctonionTraceZero) :
    magicBilinℂ compactOctonionDatum.bilin₀ u₁ u₂ =
      CompactOctonion.trace
        (CompactOctonion.mul
          (tensorEquivCompactOctonionTraceZeroℂ u₁).1
          (CompactOctonion.conj (tensorEquivCompactOctonionTraceZeroℂ u₂).1)) := by
  induction u₁ using TensorProduct.inductionOn with
  | tmul z₁ a₁ =>
    induction u₂ using TensorProduct.inductionOn with
    | tmul z₂ a₂ =>
      rw [magicBilinℂ_tmul, tensorEquivCompactOctonionTraceZeroℂ_tmul,
        tensorEquivCompactOctonionTraceZeroℂ_tmul]
      change z₁ * z₂ * (CompactOctonion.bilin a₁.1 a₂.1 : ℂ) =
        CompactOctonion.trace (CompactOctonion.mul (z₁ • ofRealCompactOctonion a₁.1)
          (CompactOctonion.conj (z₂ • ofRealCompactOctonion a₂.1)))
      rw [CompactOctonion.conj_smul, CompactOctonion.smul_mul, CompactOctonion.mul_smul,
        CompactOctonion.trace_smul, CompactOctonion.trace_smul,
        ← ofRealCompactOctonion_conj, ← ofRealCompactOctonion_mul, ofRealCompactOctonion_trace]
      simp [CompactOctonion.bilin]; ring
    | add a b ha hb =>
      simp only [map_add, Submodule.coe_add, CompactOctonion.conj_add,
        CompactOctonion.mul_add, CompactOctonion.trace_add] at ha hb ⊢
      rw [ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, CompactOctonion.add_mul,
      CompactOctonion.trace_add] at ha hb ⊢
    rw [ha, hb]

private theorem splitOct_bilinℂ_eq (u₁ u₂ : ℂ ⊗[ℝ] splitOctonionTraceZero) :
    magicBilinℂ splitOctonionDatum.bilin₀ u₁ u₂ =
      ZornVectorMatrix.trace
        (ZornVectorMatrix.mul
          (tensorEquivSplitOctonionTraceZeroℂ u₁).1
          (ZornVectorMatrix.conj (tensorEquivSplitOctonionTraceZeroℂ u₂).1)) := by
  induction u₁ using TensorProduct.inductionOn with
  | tmul z₁ a₁ =>
    induction u₂ using TensorProduct.inductionOn with
    | tmul z₂ a₂ =>
      rw [magicBilinℂ_tmul, tensorEquivSplitOctonionTraceZeroℂ_tmul,
        tensorEquivSplitOctonionTraceZeroℂ_tmul]
      change z₁ * z₂ * (zornBilin a₁.1 a₂.1 : ℂ) =
        ZornVectorMatrix.trace (ZornVectorMatrix.mul (z₁ • ofRealZornVectorMatrix a₁.1)
          (ZornVectorMatrix.conj (z₂ • ofRealZornVectorMatrix a₂.1)))
      rw [zvmℂ_conj_smul, zvmℂ_smul_mul, zvmℂ_mul_smul, zvmℂ_trace_smul, zvmℂ_trace_smul,
        ← ofRealZornVectorMatrix_conj, ← ofRealZornVectorMatrix_mul, ofRealZornVectorMatrix_trace]
      simp [zornBilin]; ring
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb, Submodule.coe_add, zvmℂ_conj_add, zvmℂ_mul_add, zvmℂ_trace_add]
  | add a b ha hb =>
    rw [map_add (magicBilinℂ splitOctonionDatum.bilin₀), LinearMap.add_apply,
      ha, hb,
      map_add tensorEquivSplitOctonionTraceZeroℂ, Submodule.coe_add,
      zvmℂ_add_mul, zvmℂ_trace_add]

private theorem compactOct_commℂ_eq (u₁ u₂ : ℂ ⊗[ℝ] CompactOctonionTraceZero) :
    (tensorEquivCompactOctonionTraceZeroℂ (magicMap2ℂ compactOctonionDatum.comm₀ u₁ u₂)).1 =
      CompactOctonion.mul
          (tensorEquivCompactOctonionTraceZeroℂ u₁).1
          (tensorEquivCompactOctonionTraceZeroℂ u₂).1 -
        CompactOctonion.mul
          (tensorEquivCompactOctonionTraceZeroℂ u₂).1
          (tensorEquivCompactOctonionTraceZeroℂ u₁).1 := by
  induction u₁ using TensorProduct.inductionOn with
  | tmul z₁ a₁ =>
    induction u₂ using TensorProduct.inductionOn with
    | tmul z₂ a₂ =>
      simp only [magicMap2ℂ_tmul, tensorEquivCompactOctonionTraceZeroℂ_tmul,
        CompactOctonion.smul_mul, CompactOctonion.mul_smul]
      change (z₁ * z₂) • ofRealCompactOctonion (compactOctComm0 a₁ a₂).1 = _
      rw [compactOctComm0_coe, ofRealCompactOctonion.map_sub, ofRealCompactOctonion_mul,
        ofRealCompactOctonion_mul, ← mul_smul, ← mul_smul, smul_sub, mul_comm z₂ z₁]
    | add a b ha hb =>
      simp only [map_add, Submodule.coe_add,
        CompactOctonion.mul_add, CompactOctonion.add_mul] at ha hb ⊢
      rw [ha, hb]; abel
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add,
      CompactOctonion.add_mul, CompactOctonion.mul_add] at ha hb ⊢
    rw [ha, hb]; abel

private theorem splitOct_commℂ_eq (u₁ u₂ : ℂ ⊗[ℝ] splitOctonionTraceZero) :
    (tensorEquivSplitOctonionTraceZeroℂ (magicMap2ℂ splitOctonionDatum.comm₀ u₁ u₂)).1 =
      ZornVectorMatrix.mul
          (tensorEquivSplitOctonionTraceZeroℂ u₁).1
          (tensorEquivSplitOctonionTraceZeroℂ u₂).1 -
        ZornVectorMatrix.mul
          (tensorEquivSplitOctonionTraceZeroℂ u₂).1
          (tensorEquivSplitOctonionTraceZeroℂ u₁).1 := by
  induction u₁ using TensorProduct.inductionOn with
  | tmul z₁ a₁ =>
    induction u₂ using TensorProduct.inductionOn with
    | tmul z₂ a₂ =>
      rw [magicMap2ℂ_tmul, tensorEquivSplitOctonionTraceZeroℂ_tmul,
        tensorEquivSplitOctonionTraceZeroℂ_tmul, tensorEquivSplitOctonionTraceZeroℂ_tmul]
      change (z₁ * z₂) • ofRealZornVectorMatrix (zornComm0 a₁ a₂).1 =
        ZornVectorMatrix.mul (z₁ • ofRealZornVectorMatrix a₁.1) (z₂ • ofRealZornVectorMatrix a₂.1) -
          ZornVectorMatrix.mul (z₂ • ofRealZornVectorMatrix a₂.1) (z₁ • ofRealZornVectorMatrix a₁.1)
      rw [zvmℂ_smul_mul, zvmℂ_mul_smul, zvmℂ_smul_mul, zvmℂ_mul_smul,
        zornComm0_coe, ofRealZornVectorMatrix.map_sub]
      erw [ofRealZornVectorMatrix_mul, ofRealZornVectorMatrix_mul]
      rw [← mul_smul, ← mul_smul, smul_sub, mul_comm z₂ z₁]
    | add a b ha hb =>
      rw [map_add (magicMap2ℂ splitOctonionDatum.comm₀ (z₁ ⊗ₜ[ℝ] a₁)),
        map_add tensorEquivSplitOctonionTraceZeroℂ, Submodule.coe_add, ha, hb,
        map_add tensorEquivSplitOctonionTraceZeroℂ, Submodule.coe_add,
        zvmℂ_mul_add, zvmℂ_add_mul]
      abel
  | add a b ha hb =>
    rw [map_add (magicMap2ℂ splitOctonionDatum.comm₀),
      LinearMap.add_apply, map_add tensorEquivSplitOctonionTraceZeroℂ, Submodule.coe_add,
      ha, hb, map_add tensorEquivSplitOctonionTraceZeroℂ, Submodule.coe_add,
      zvmℂ_add_mul, zvmℂ_mul_add]
    abel

private theorem extendScalarsLieEquiv_tmul {L₁ L₂ : Type} [LieRing L₁] [LieAlgebra ℝ L₁]
    [LieRing L₂] [LieAlgebra ℝ L₂] (e : L₁ ≃ₗ⁅ℝ⁆ L₂) (z : ℂ) (x : L₁) :
    extendScalarsLieEquiv e (z ⊗ₜ[ℝ] x) = z ⊗ₜ[ℝ] e x := rfl

private theorem zornDerivationsExtendEquiv_one_tmul (d : zornDerivations) :
    (zornDerivationsExtendEquiv ((1 : ℂ) ⊗ₜ[ℝ] d)).1 =
      liftEnd tensorEquivZornVectorMatrix d.1 := by
  dsimp [zornDerivationsExtendEquiv, mkBaseChangeLieEquiv]
  erw [TensorProduct.AlgebraTensorModule.lift_tmul]
  simp

private theorem compactOct_actℂ_eq (D : ℂ ⊗[ℝ] CompactOctonionDerivations)
    (u : ℂ ⊗[ℝ] CompactOctonionTraceZero) :
    (tensorEquivCompactOctonionTraceZeroℂ (magicActℂ compactOctonionDatum.act D u)).1 =
      (compactOctonionDerivationsExtendEquiv D).1
        (tensorEquivCompactOctonionTraceZeroℂ u).1 := by
  induction D using TensorProduct.inductionOn with
  | tmul z₁ d =>
    induction u using TensorProduct.inductionOn with
    | tmul z₂ a =>
      simp only [magicActℂ_tmul, tensorEquivCompactOctonionTraceZeroℂ_tmul, map_smul]
      have hd : (compactOctonionDerivationsExtendEquiv ((1 : ℂ) ⊗ₜ[ℝ] d)).1 =
          liftEnd tensorEquivCompactOctonion d.1 := by
        dsimp [compactOctonionDerivationsExtendEquiv, mkBaseChangeLieEquiv]
        erw [TensorProduct.AlgebraTensorModule.lift_tmul]
        simp
      rw [show (z₁ ⊗ₜ[ℝ] d) = z₁ • ((1 : ℂ) ⊗ₜ[ℝ] d) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
      simp only [SetLike.val_smul, LinearMap.smul_apply, hd]
      rw [liftEnd_apply_ofReal tensorEquivCompactOctonion ofRealCompactOctonion
        tensorEquivCompactOctonion_tmul, ← mul_smul, mul_comm z₂ z₁]
      rfl
    | add a b ha hb =>
      simp only [map_add, Submodule.coe_add] at ha hb ⊢; rw [ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, AddMemClass.coe_add] at ha hb ⊢
    rw [ha, hb]

private theorem splitOct_actℂ_eq (D : ℂ ⊗[ℝ] G2DerivationCarrier)
    (u : ℂ ⊗[ℝ] splitOctonionTraceZero) :
    (tensorEquivSplitOctonionTraceZeroℂ (magicActℂ splitOctonionDatum.act D u)).1 =
      (zornDerivationsExtendEquiv (extendScalarsLieEquiv vDerEquivZornDerivations D)).1
        (tensorEquivSplitOctonionTraceZeroℂ u).1 := by
  induction D using TensorProduct.inductionOn with
  | tmul z₁ d =>
    induction u using TensorProduct.inductionOn with
    | tmul z₂ a =>
      rw [magicActℂ_tmul, tensorEquivSplitOctonionTraceZeroℂ_tmul,
        tensorEquivSplitOctonionTraceZeroℂ_tmul, extendScalarsLieEquiv_tmul]
      rw [show (z₁ ⊗ₜ[ℝ] vDerEquivZornDerivations d) =
          z₁ • ((1 : ℂ) ⊗ₜ[ℝ] vDerEquivZornDerivations d) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
      simp only [SetLike.val_smul, LinearMap.smul_apply, zornDerivationsExtendEquiv_one_tmul,
        map_smul, liftEnd_apply_ofReal tensorEquivZornVectorMatrix ofRealZornVectorMatrix
          tensorEquivZornVectorMatrix_tmul, smul_smul, mul_comm z₂ z₁]
      rfl
    | add a b ha hb =>
      rw [map_add (magicActℂ splitOctonionDatum.act (z₁ ⊗ₜ[ℝ] d)),
        map_add tensorEquivSplitOctonionTraceZeroℂ, Submodule.coe_add, ha, hb,
        map_add tensorEquivSplitOctonionTraceZeroℂ, Submodule.coe_add, map_add]
  | add a b ha hb =>
    rw [map_add (magicActℂ splitOctonionDatum.act), LinearMap.add_apply,
      map_add tensorEquivSplitOctonionTraceZeroℂ, Submodule.coe_add, ha, hb,
      map_add (extendScalarsLieEquiv vDerEquivZornDerivations),
      map_add zornDerivationsExtendEquiv, AddMemClass.coe_add, LinearMap.add_apply]

private theorem compactOct_innerℂ_eq (u₁ u₂ : ℂ ⊗[ℝ] CompactOctonionTraceZero)
    (w : CompactOctonion ℂ) :
    (compactOctonionDerivationsExtendEquiv (magicMap2ℂ compactOctonionDatum.inner u₁ u₂)).1 w =
      let x := (tensorEquivCompactOctonionTraceZeroℂ u₁).1
      let y := (tensorEquivCompactOctonionTraceZeroℂ u₂).1
      (CompactOctonion.mul (CompactOctonion.mul x y - CompactOctonion.mul y x) w -
        CompactOctonion.mul w (CompactOctonion.mul x y - CompactOctonion.mul y x)) -
      (3 : ℂ) • (CompactOctonion.mul (CompactOctonion.mul x y) w -
        CompactOctonion.mul x (CompactOctonion.mul y w)) := by
  induction u₁ using TensorProduct.inductionOn with
  | tmul z₁ a₁ =>
    induction u₂ using TensorProduct.inductionOn with
    | tmul z₂ a₂ =>
      simp only [magicMap2ℂ_tmul, tensorEquivCompactOctonionTraceZeroℂ_tmul]
      have hd : (compactOctonionDerivationsExtendEquiv
            ((1 : ℂ) ⊗ₜ[ℝ] compactOctonionDatum.inner a₁ a₂)).1 =
          liftEnd tensorEquivCompactOctonion (compactG2Inner a₁ a₂).1 := by
        dsimp [compactOctonionDerivationsExtendEquiv, mkBaseChangeLieEquiv]
        erw [TensorProduct.AlgebraTensorModule.lift_tmul]
        simp; rfl
      rw [show ((z₁ * z₂) ⊗ₜ[ℝ] compactOctonionDatum.inner a₁ a₂) =
        (z₁ * z₂) • ((1 : ℂ) ⊗ₜ[ℝ] compactOctonionDatum.inner a₁ a₂) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
      simp only [SetLike.val_smul, LinearMap.smul_apply, hd]
      rw [← ofReal_rePart_add_I_imPart_CompactOctonion w]
      have hreal : ∀ w₀ : CompactOctonion ℝ,
          liftEnd tensorEquivCompactOctonion (compactG2Inner a₁ a₂).1
              (ofRealCompactOctonion w₀) =
            (CompactOctonion.mul
                (CompactOctonion.mul (ofRealCompactOctonion a₁.1) (ofRealCompactOctonion a₂.1) -
                  CompactOctonion.mul (ofRealCompactOctonion a₂.1) (ofRealCompactOctonion a₁.1))
                (ofRealCompactOctonion w₀) -
              CompactOctonion.mul (ofRealCompactOctonion w₀)
                (CompactOctonion.mul (ofRealCompactOctonion a₁.1) (ofRealCompactOctonion a₂.1) -
                  CompactOctonion.mul (ofRealCompactOctonion a₂.1)
                    (ofRealCompactOctonion a₁.1))) -
            (3 : ℂ) • (CompactOctonion.mul
                (CompactOctonion.mul (ofRealCompactOctonion a₁.1) (ofRealCompactOctonion a₂.1))
                (ofRealCompactOctonion w₀) -
              CompactOctonion.mul (ofRealCompactOctonion a₁.1)
                (CompactOctonion.mul (ofRealCompactOctonion a₂.1) (ofRealCompactOctonion w₀))) := by
        intro w₀
        rw [liftEnd_apply_ofReal tensorEquivCompactOctonion ofRealCompactOctonion
          tensorEquivCompactOctonion_tmul]
        change ofRealCompactOctonion ((compactOctStanDer a₁.1 a₂.1).1 w₀) = _
        rw [compactOctStanDer_normal_form]
        simp only [ofRealCompactOctonion.map_sub, map_nsmul,
          ofRealCompactOctonion_mul, compactOctAssociator, ← Nat.cast_smul_eq_nsmul ℂ 3,
          Nat.cast_ofNat]
      simp only [map_add, map_smul, hreal, CompactOctonion.smul_mul, CompactOctonion.mul_smul,
        CompactOctonion.add_mul, CompactOctonion.mul_add, CompactOctonion.sub_mul,
        CompactOctonion.mul_sub, smul_add, smul_sub, smul_smul]
      rw [show z₂ * z₁ = z₁ * z₂ by ring,
        show Complex.I * (z₁ * z₂) = z₁ * z₂ * Complex.I by ring,
        show z₁ * z₂ * 3 = 3 * (z₁ * z₂) by ring,
        show z₁ * z₂ * (Complex.I * 3) = 3 * (z₁ * z₂ * Complex.I) by ring,
        show Complex.I * z₂ * z₁ = z₁ * z₂ * Complex.I by ring]
      abel
    | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply, AddMemClass.coe_add,
        CompactOctonion.add_mul, CompactOctonion.mul_add, CompactOctonion.sub_mul,
        CompactOctonion.mul_sub, smul_sub, smul_add] at ha hb ⊢
      rw [ha, hb]; abel
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, AddMemClass.coe_add,
      CompactOctonion.add_mul, CompactOctonion.mul_add, CompactOctonion.sub_mul,
      CompactOctonion.mul_sub, smul_sub, smul_add] at ha hb ⊢
    rw [ha, hb]; abel

private theorem splitOct_innerℂ_eq (u₁ u₂ : ℂ ⊗[ℝ] splitOctonionTraceZero)
    (W : ZornVectorMatrix ℂ) :
    (zornDerivationsExtendEquiv (extendScalarsLieEquiv vDerEquivZornDerivations
        (magicMap2ℂ splitOctonionDatum.inner u₁ u₂))).1 W =
      let X := (tensorEquivSplitOctonionTraceZeroℂ u₁).1
      let Y := (tensorEquivSplitOctonionTraceZeroℂ u₂).1
      (ZornVectorMatrix.mul (ZornVectorMatrix.mul X Y - ZornVectorMatrix.mul Y X) W -
        ZornVectorMatrix.mul W (ZornVectorMatrix.mul X Y - ZornVectorMatrix.mul Y X)) -
      (3 : ℂ) • (ZornVectorMatrix.mul (ZornVectorMatrix.mul X Y) W -
        ZornVectorMatrix.mul X (ZornVectorMatrix.mul Y W)) := by
  induction u₁ using TensorProduct.inductionOn with
  | tmul z₁ a₁ =>
    induction u₂ using TensorProduct.inductionOn with
    | tmul z₂ a₂ =>
      rw [magicMap2ℂ_tmul, tensorEquivSplitOctonionTraceZeroℂ_tmul,
        tensorEquivSplitOctonionTraceZeroℂ_tmul, extendScalarsLieEquiv_tmul]
      rw [show ((z₁ * z₂) ⊗ₜ[ℝ] vDerEquivZornDerivations (splitOctonionDatum.inner a₁ a₂)) =
          (z₁ * z₂) • ((1 : ℂ) ⊗ₜ[ℝ] vDerEquivZornDerivations (splitOctonionDatum.inner a₁ a₂)) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
      simp only [SetLike.val_smul, LinearMap.smul_apply, zornDerivationsExtendEquiv_one_tmul]
      rw [← ofReal_rePart_add_I_imPart_ZornVectorMatrix W]
      have hreal : ∀ W₀ : ZornVectorMatrix ℝ,
          liftEnd tensorEquivZornVectorMatrix
              (vDerEquivZornDerivations (splitOctonionDatum.inner a₁ a₂)).1
              (ofRealZornVectorMatrix W₀) =
            (ZornVectorMatrix.mul
                (ZornVectorMatrix.mul (ofRealZornVectorMatrix a₁.1)
                  (ofRealZornVectorMatrix a₂.1) -
                  ZornVectorMatrix.mul (ofRealZornVectorMatrix a₂.1)
                    (ofRealZornVectorMatrix a₁.1))
                (ofRealZornVectorMatrix W₀) -
              ZornVectorMatrix.mul (ofRealZornVectorMatrix W₀)
                (ZornVectorMatrix.mul (ofRealZornVectorMatrix a₁.1)
                  (ofRealZornVectorMatrix a₂.1) -
                  ZornVectorMatrix.mul (ofRealZornVectorMatrix a₂.1)
                    (ofRealZornVectorMatrix a₁.1))) -
            (3 : ℂ) • (ZornVectorMatrix.mul
                (ZornVectorMatrix.mul (ofRealZornVectorMatrix a₁.1)
                  (ofRealZornVectorMatrix a₂.1))
                (ofRealZornVectorMatrix W₀) -
              ZornVectorMatrix.mul (ofRealZornVectorMatrix a₁.1)
                (ZornVectorMatrix.mul (ofRealZornVectorMatrix a₂.1)
                  (ofRealZornVectorMatrix W₀))) := by
        intro W₀
        rw [liftEnd_apply_ofReal tensorEquivZornVectorMatrix ofRealZornVectorMatrix
          tensorEquivZornVectorMatrix_tmul]
        change ofRealZornVectorMatrix
          ((Zorn.NativeStanDerivationBilinear.innerDerivation a₁.1 a₂.1).1 W₀) = _
        have hnf := Zorn.NativeStanDerivationBilinear.innerDerivation_operatorial_normal_form
          a₁.1 a₂.1 W₀
        rw [show (Zorn.NativeStanDerivationBilinear.innerDerivation a₁.1 a₂.1).1 W₀ =
          Zorn.NativeStanDerivationBilinear.innerDerivation a₁.1 a₂.1 W₀ from rfl, hnf]
        rw [ofRealZornVectorMatrix.map_sub, ofRealZornVectorMatrix.map_sub, map_nsmul,
          ← Nat.cast_smul_eq_nsmul ℂ 3, Nat.cast_ofNat]
        simp only [show ∀ x y : ZornVectorMatrix ℝ, x * y = ZornVectorMatrix.mul x y from
            fun _ _ => rfl,
          ofRealZornVectorMatrix.map_sub, ofRealZornVectorMatrix_mul]
      simp only [map_add, map_smul, hreal, zvmℂ_smul_mul, zvmℂ_mul_smul, zvmℂ_add_mul,
        zvmℂ_mul_add, zvmℂ_sub_mul, zvmℂ_mul_sub, smul_add, smul_sub, smul_smul]
      rw [show z₂ * z₁ = z₁ * z₂ by ring,
        show Complex.I * (z₁ * z₂) = z₁ * z₂ * Complex.I by ring,
        show z₁ * z₂ * 3 = 3 * (z₁ * z₂) by ring,
        show z₁ * z₂ * (Complex.I * 3) = 3 * (z₁ * z₂ * Complex.I) by ring,
        show Complex.I * z₂ * z₁ = z₁ * z₂ * Complex.I by ring]
      abel
    | add a b ha hb =>
      dsimp only at ha hb ⊢
      rw [map_add (magicMap2ℂ splitOctonionDatum.inner (z₁ ⊗ₜ[ℝ] a₁)),
        map_add (extendScalarsLieEquiv vDerEquivZornDerivations),
        map_add zornDerivationsExtendEquiv, AddMemClass.coe_add, LinearMap.add_apply, ha, hb,
        map_add tensorEquivSplitOctonionTraceZeroℂ, Submodule.coe_add]
      simp only [zvmℂ_add_mul, zvmℂ_mul_add, zvmℂ_sub_mul, zvmℂ_mul_sub,
        smul_sub, smul_add]
      abel
  | add a b ha hb =>
    dsimp only at ha hb ⊢
    rw [map_add (magicMap2ℂ splitOctonionDatum.inner), LinearMap.add_apply,
      map_add (extendScalarsLieEquiv vDerEquivZornDerivations),
      map_add zornDerivationsExtendEquiv, AddMemClass.coe_add, LinearMap.add_apply, ha, hb,
      map_add tensorEquivSplitOctonionTraceZeroℂ, Submodule.coe_add]
    simp only [zvmℂ_add_mul, zvmℂ_mul_add, zvmℂ_sub_mul, zvmℂ_mul_sub,
      smul_sub, smul_add]
    abel

/-- Complexified `ℂ`-Lie algebra isomorphism between `QuaternionicE8Lie` (`𝔈₈(-24)`) and
`SplitE8Lie` (`𝔈₈(+8)`). -/
def quaternionicE8BaseChangeEquiv :
    ℂ ⊗[ℝ] QuaternionicE8Lie ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] SplitE8Lie :=
  let toMS : ℂ ⊗[ℝ] QuaternionicE8Lie ≃ₗ⁅ℂ⁆
      ℂ ⊗[ℝ] MagicSquareLie splitOctonionDatum h3ZornJordanDatum :=
    mkMagicSquareComplexLieEquiv compactOctonionDatum h3ZornJordanDatum
      splitOctonionDatum h3ZornJordanDatum
      compactG2BaseChangeVDerEquiv tensorEquivCompactOctonionTraceZero
      (LinearEquiv.refl ℂ _) LieEquiv.refl
      (fun u₁ u₂ => by
        rw [splitOct_bilinℂ_eq, compactOct_bilinℂ_eq]
        dsimp [tensorEquivCompactOctonionTraceZero]
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        change ZornVectorMatrix.trace (ZornVectorMatrix.mul
            (octonionComplexEquiv (tensorEquivCompactOctonionTraceZeroℂ u₁).1)
            (ZornVectorMatrix.conj
              (octonionComplexEquiv (tensorEquivCompactOctonionTraceZeroℂ u₂).1))) =
          CompactOctonion.trace (CompactOctonion.mul
            (tensorEquivCompactOctonionTraceZeroℂ u₁).1
            (CompactOctonion.conj (tensorEquivCompactOctonionTraceZeroℂ u₂).1))
        rw [← octonionComplexEquiv_trace (CompactOctonion.mul
            (tensorEquivCompactOctonionTraceZeroℂ u₁).1
            (CompactOctonion.conj (tensorEquivCompactOctonionTraceZeroℂ u₂).1)),
          octonionComplexEquiv_mul, octonionComplexEquiv_conj])
      (fun u₁ u₂ => by
        apply tensorEquivSplitOctonionTraceZeroℂ.injective
        apply Subtype.ext
        have h1 : (tensorEquivSplitOctonionTraceZeroℂ (tensorEquivCompactOctonionTraceZero
              (magicMap2ℂ compactOctonionDatum.comm₀ u₁ u₂))).1 =
            octonionComplexEquiv
              (tensorEquivCompactOctonionTraceZeroℂ
                (magicMap2ℂ compactOctonionDatum.comm₀ u₁ u₂)).1 := by
          dsimp [tensorEquivCompactOctonionTraceZero]
          rw [LinearEquiv.apply_symm_apply]; rfl
        rw [h1, compactOct_commℂ_eq, splitOct_commℂ_eq, map_sub,
          octonionComplexEquiv_mul, octonionComplexEquiv_mul]
        dsimp [tensorEquivCompactOctonionTraceZero]
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]; rfl)
      (fun D u => by
        apply tensorEquivSplitOctonionTraceZeroℂ.injective
        apply Subtype.ext
        have h1 : (tensorEquivSplitOctonionTraceZeroℂ (tensorEquivCompactOctonionTraceZero
              (magicActℂ compactOctonionDatum.act D u))).1 =
            octonionComplexEquiv
              (tensorEquivCompactOctonionTraceZeroℂ
                (magicActℂ compactOctonionDatum.act D u)).1 := by
          dsimp [tensorEquivCompactOctonionTraceZero]
          rw [LinearEquiv.apply_symm_apply]; rfl
        have h2 : (zornDerivationsExtendEquiv (extendScalarsLieEquiv vDerEquivZornDerivations
              (compactG2BaseChangeVDerEquiv D))).1 =
            octonionComplexEquiv.conj (compactOctonionDerivationsExtendEquiv D).1 := by
          dsimp [compactG2BaseChangeVDerEquiv, compactG2BaseChangeEquiv]
          rw [LieEquiv.apply_symm_apply, LieEquiv.apply_symm_apply]; rfl
        rw [h1, compactOct_actℂ_eq, splitOct_actℂ_eq, h2, LinearEquiv.conj_apply]
        dsimp [tensorEquivCompactOctonionTraceZero]
        rw [LinearEquiv.apply_symm_apply]
        change octonionComplexEquiv ((compactOctonionDerivationsExtendEquiv D).1
            (tensorEquivCompactOctonionTraceZeroℂ u).1) =
          octonionComplexEquiv ((compactOctonionDerivationsExtendEquiv D).1
            (octonionComplexEquiv.symm (octonionComplexEquiv
              (tensorEquivCompactOctonionTraceZeroℂ u).1)))
        rw [LinearEquiv.symm_apply_apply])
      (fun u₁ u₂ => by
        apply (extendScalarsLieEquiv vDerEquivZornDerivations).injective
        apply zornDerivationsExtendEquiv.injective
        apply Subtype.ext; apply LinearMap.ext; intro W
        obtain ⟨w, rfl⟩ := octonionComplexEquiv.surjective W
        have h2 : (zornDerivationsExtendEquiv (extendScalarsLieEquiv vDerEquivZornDerivations
              (compactG2BaseChangeVDerEquiv
                (magicMap2ℂ compactOctonionDatum.inner u₁ u₂)))).1 =
            octonionComplexEquiv.conj
              (compactOctonionDerivationsExtendEquiv
                (magicMap2ℂ compactOctonionDatum.inner u₁ u₂)).1 := by
          dsimp [compactG2BaseChangeVDerEquiv, compactG2BaseChangeEquiv]
          rw [LieEquiv.apply_symm_apply, LieEquiv.apply_symm_apply]; rfl
        simp only [LieEquiv.coe_toLieHom]
        rw [h2, LinearEquiv.conj_apply_apply, compactOct_innerℂ_eq, splitOct_innerℂ_eq]
        dsimp [tensorEquivCompactOctonionTraceZero]
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
          LinearEquiv.symm_apply_apply]
        simp only [map_sub, map_smul, octonionComplexEquiv_mul]; rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  toMS.trans (extendScalarsLieEquiv splitE8EquivMagicSquare.symm)

/-- Complexified `ℂ`-Lie algebra isomorphism between `CompactE8Lie` (`𝔈₈(-248)`) and
`SplitE8Lie` (`𝔈₈(+8)`). -/
def compactE8BaseChangeEquiv :
    ℂ ⊗[ℝ] CompactE8Lie ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] SplitE8Lie :=
  compactToQuaternionicBaseChangeEquiv.trans quaternionicE8BaseChangeEquiv

/-- `CompactE8Lie` (`𝔈₈(-248)`) is a simple real Lie algebra. -/
instance compactE8Lie_isSimple : LieAlgebra.IsSimple ℝ CompactE8Lie := by
  have : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] SplitE8Lie) := complexSplitE8Lie_isSimple
  have : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] CompactE8Lie) :=
    LieEquiv.isSimple compactE8BaseChangeEquiv.symm
  exact isSimple_of_isSimple_extendScalars this

/-- `QuaternionicE8Lie` (`𝔈₈(-24)`) is a simple real Lie algebra. -/
instance quaternionicE8Lie_isSimple : LieAlgebra.IsSimple ℝ QuaternionicE8Lie := by
  have : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] SplitE8Lie) := complexSplitE8Lie_isSimple
  have : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] QuaternionicE8Lie) :=
    LieEquiv.isSimple quaternionicE8BaseChangeEquiv.symm
  exact isSimple_of_isSimple_extendScalars this

end QuaternionicToSplit

end BaseChangeMagicSquare

end ComplexificationSimplicity

/-! ## 4. Cartan Involutions, `IsKilling ℝ`, & Signature Separation (`-248` vs `-24` vs `+8`) -/

section CartanSignatures

section GenericCartanEngine

private theorem involution_isCompl {V : Type} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] V) (hT : ∀ x : V, T (T x) = x) :
    IsCompl (LinearMap.ker (T - LinearMap.id)) (LinearMap.ker (T + LinearMap.id)) := by
  rw [isCompl_iff]
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    ext x
    simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.id_apply, sub_eq_zero, add_eq_zero_iff_eq_neg, Submodule.mem_bot]
    constructor
    · rintro ⟨h1, h2⟩
      have h2x : (2 : ℝ) • x = 0 := by
        rw [two_smul]
        nth_rw 1 [← h1]
        rw [h2, neg_add_cancel]
      exact (smul_eq_zero.mp h2x).resolve_left (by norm_num)
    · rintro rfl; simp
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hk : (1 / 2 : ℝ) • (x + T x) ∈ LinearMap.ker (T - LinearMap.id) := by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_add, hT]
      module
    have hp : (1 / 2 : ℝ) • (x - T x) ∈ LinearMap.ker (T + LinearMap.id) := by
      simp only [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, map_smul, map_sub, hT]
      module
    have hsum : x = (1 / 2 : ℝ) • (x + T x) + (1 / 2 : ℝ) • (x - T x) := by module
    rw [hsum]
    exact Submodule.add_mem_sup hk hp

private theorem involution_finrank_add {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V) (hT : ∀ x : V, T (T x) = x) :
    Module.finrank ℝ (LinearMap.ker (T - LinearMap.id)) +
        Module.finrank ℝ (LinearMap.ker (T + LinearMap.id)) =
      Module.finrank ℝ V :=
  Submodule.finrank_add_eq_of_isCompl (involution_isCompl T hT)

private theorem involution_trace_eq {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V) (hT : ∀ x : V, T (T x) = x) :
    LinearMap.trace ℝ V T =
      2 * (Module.finrank ℝ (LinearMap.ker (T - LinearMap.id)) : ℝ) -
        (Module.finrank ℝ V : ℝ) := by
  let k := LinearMap.ker (T - LinearMap.id)
  let P : V →ₗ[ℝ] V := (1 / 2 : ℝ) • (LinearMap.id + T)
  have hproj : LinearMap.IsProj k P :=
    { map_mem := fun x => by
        simp only [k, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, P,
          LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add, hT]
        module
      map_id := fun x hx => by
        simp only [k, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx
        dsimp [P]
        rw [hx, ← two_smul ℝ x, smul_smul]
        norm_num }
  have hTP : T = (2 : ℝ) • P - LinearMap.id := by
    ext x
    simp [P]
  conv_lhs => rw [hTP]
  rw [map_sub, map_smul, smul_eq_mul, hproj.trace, LinearMap.trace_id]

private theorem trace_sq_nonpos_of_skew_ortho_gen {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB_symm : ∀ x y, B x y = B y x)
    (hB_nonneg : ∀ x, 0 ≤ B x x)
    (hB_eq_zero : ∀ x, B x x = 0 ↔ x = 0)
    (A : Module.End ℝ V)
    (hskew : ∀ x y, B (A x) y + B x (A y) = 0) :
    LinearMap.trace ℝ V (A * A) ≤ 0 ∧
      (LinearMap.trace ℝ V (A * A) = 0 → A = 0) := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B) ⟨hB_symm⟩
  have hpos : ∀ i, 0 < B (v i) (v i) := fun i =>
    lt_of_le_of_ne (hB_nonneg (v i)) (fun h => (v.ne_zero i) ((hB_eq_zero (v i)).mp h.symm))
  have hrepr : ∀ i (W : V), v.repr W i = B (v i) W / B (v i) (v i) := by
    intro i W
    have hsum : B (v i) W = ∑ j, v.repr W j * B (v i) (v j) := by
      conv_lhs => rw [← v.sum_repr W]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    rw [hsum, Finset.sum_eq_single i]
    · exact (eq_div_iff (ne_of_gt (hpos i))).mpr rfl
    · intro j _ hji
      rw [hv hji.symm, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have htr : LinearMap.trace ℝ V (A * A) =
      ∑ i, -(B (A (v i)) (A (v i)) / B (v i) (v i)) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ v]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Module.End.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrepr i (A (A (v i)))]
    have hsk := hskew (v i) (A (v i))
    have hneg : B (v i) (A (A (v i))) = -B (A (v i)) (A (v i)) := by linarith
    rw [hneg, neg_div]
  rw [htr, Finset.sum_neg_distrib]
  refine ⟨neg_nonpos.mpr (Finset.sum_nonneg fun i _ =>
    div_nonneg (hB_nonneg _) (hpos i).le), ?_⟩
  intro hz
  rw [neg_eq_zero] at hz
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    div_nonneg (hB_nonneg _) (hpos i).le).mp hz
  apply v.ext
  intro i
  have hi := hall i (Finset.mem_univ i)
  rw [div_eq_zero_iff] at hi
  exact (hB_eq_zero _).mp (hi.resolve_right (ne_of_gt (hpos i)))

private theorem trace_sq_nonneg_of_self_ortho_gen {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB_symm : ∀ x y, B x y = B y x)
    (hB_nonneg : ∀ x, 0 ≤ B x x)
    (hB_eq_zero : ∀ x, B x x = 0 ↔ x = 0)
    (A : Module.End ℝ V)
    (hself : ∀ x y, B (A x) y = B x (A y)) :
    0 ≤ LinearMap.trace ℝ V (A * A) ∧
      (LinearMap.trace ℝ V (A * A) = 0 → A = 0) := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B) ⟨hB_symm⟩
  have hpos : ∀ i, 0 < B (v i) (v i) := fun i =>
    lt_of_le_of_ne (hB_nonneg (v i)) (fun h => (v.ne_zero i) ((hB_eq_zero (v i)).mp h.symm))
  have hrepr : ∀ i (W : V), v.repr W i = B (v i) W / B (v i) (v i) := by
    intro i W
    have hsum : B (v i) W = ∑ j, v.repr W j * B (v i) (v j) := by
      conv_lhs => rw [← v.sum_repr W]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    rw [hsum, Finset.sum_eq_single i]
    · exact (eq_div_iff (ne_of_gt (hpos i))).mpr rfl
    · intro j _ hji
      rw [hv hji.symm, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have htr : LinearMap.trace ℝ V (A * A) =
      ∑ i, B (A (v i)) (A (v i)) / B (v i) (v i) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ v]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Module.End.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrepr i (A (A (v i))), ← hself (v i) (A (v i))]
  rw [htr]
  refine ⟨Finset.sum_nonneg fun i _ => div_nonneg (hB_nonneg _) (hpos i).le, ?_⟩
  intro hz
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    div_nonneg (hB_nonneg _) (hpos i).le).mp hz
  apply v.ext
  intro i
  have hi := hall i (Finset.mem_univ i)
  rw [div_eq_zero_iff] at hi
  exact (hB_eq_zero _).mp (hi.resolve_right (ne_of_gt (hpos i)))

private theorem trace_mul_adjoint_nonneg_gen {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB_symm : ∀ x y, B x y = B y x)
    (hB_nonneg : ∀ x, 0 ≤ B x x)
    (hB_eq_zero : ∀ x, B x x = 0 ↔ x = 0)
    (A A' : Module.End ℝ V)
    (hadj : ∀ x y, B (A x) y = B x (A' y)) :
    0 ≤ LinearMap.trace ℝ V (A * A') ∧
      (LinearMap.trace ℝ V (A * A') = 0 → A' = 0) := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B) ⟨hB_symm⟩
  have hpos : ∀ i, 0 < B (v i) (v i) := fun i =>
    lt_of_le_of_ne (hB_nonneg (v i)) (fun h => (v.ne_zero i) ((hB_eq_zero (v i)).mp h.symm))
  have hrepr : ∀ i (W : V), v.repr W i = B (v i) W / B (v i) (v i) := by
    intro i W
    have hsum : B (v i) W = ∑ j, v.repr W j * B (v i) (v j) := by
      conv_lhs => rw [← v.sum_repr W]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    rw [hsum, Finset.sum_eq_single i]
    · exact (eq_div_iff (ne_of_gt (hpos i))).mpr rfl
    · intro j _ hji
      rw [hv hji.symm, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have htr : LinearMap.trace ℝ V (A * A') =
      ∑ i, B (A' (v i)) (A' (v i)) / B (v i) (v i) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ v]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Module.End.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrepr i (A (A' (v i))), ← hadj (A' (v i)) (v i), hB_symm]
  rw [htr]
  refine ⟨Finset.sum_nonneg fun i _ => div_nonneg (hB_nonneg _) (hpos i).le, ?_⟩
  intro hz
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    div_nonneg (hB_nonneg _) (hpos i).le).mp hz
  apply v.ext
  intro i
  have hi := hall i (Finset.mem_univ i)
  rw [div_eq_zero_iff] at hi
  exact (hB_eq_zero _).mp (hi.resolve_right (ne_of_gt (hpos i)))

private theorem ne_iff_ne_or_ne_of_prod_ne {α β : Type} {p q : α × β} (hpq : p ≠ q) :
    p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
  by_contra h
  push Not at h
  exact hpq (Prod.ext h.1 h.2)

private theorem tensorProduct_bilin_posDef {V₁ V₂ : Type}
    [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
    (B₁ : V₁ →ₗ[ℝ] V₁ →ₗ[ℝ] ℝ)
    (hB₁_symm : ∀ x y, B₁ x y = B₁ y x)
    (hB₁_nonneg : ∀ x, 0 ≤ B₁ x x)
    (hB₁_eq_zero : ∀ x, B₁ x x = 0 ↔ x = 0)
    (B₂ : V₂ →ₗ[ℝ] V₂ →ₗ[ℝ] ℝ)
    (hB₂_symm : ∀ x y, B₂ x y = B₂ y x)
    (hB₂_nonneg : ∀ x, 0 ≤ B₂ x x)
    (hB₂_eq_zero : ∀ x, B₂ x x = 0 ↔ x = 0)
    (B₁₂ : (V₁ ⊗[ℝ] V₂) →ₗ[ℝ] (V₁ ⊗[ℝ] V₂) →ₗ[ℝ] ℝ)
    (hB₁₂_tmul : ∀ a₁ a₂ x₁ x₂, B₁₂ (a₁ ⊗ₜ[ℝ] x₁) (a₂ ⊗ₜ[ℝ] x₂) = B₁ a₁ a₂ * B₂ x₁ x₂) :
    (∀ m, 0 ≤ B₁₂ m m) ∧ (∀ m, B₁₂ m m = 0 ↔ m = 0) := by
  obtain ⟨u, hu⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B₁) ⟨hB₁_symm⟩
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B₂) ⟨hB₂_symm⟩
  have hpos₁ : ∀ i, 0 < B₁ (u i) (u i) := fun i =>
    lt_of_le_of_ne (hB₁_nonneg (u i)) (fun h => (u.ne_zero i) ((hB₁_eq_zero (u i)).mp h.symm))
  have hpos₂ : ∀ j, 0 < B₂ (v j) (v j) := fun j =>
    lt_of_le_of_ne (hB₂_nonneg (v j)) (fun h => (v.ne_zero j) ((hB₂_eq_zero (v j)).mp h.symm))
  let b := u.tensorProduct v
  have hb_ortho : ∀ p q,
      B₁₂ (b p) (b q) =
        if p = q then B₁ (u p.1) (u p.1) * B₂ (v p.2) (v p.2) else 0 := by
    intro p q
    dsimp [b]
    rw [Module.Basis.tensorProduct_apply, Module.Basis.tensorProduct_apply, hB₁₂_tmul]
    by_cases hpq : p = q
    · subst hpq; simp
    · simp only [hpq, ↓reduceIte]
      rcases ne_iff_ne_or_ne_of_prod_ne hpq with h1 | h2
      · rw [hu h1, zero_mul]
      · rw [hv h2, mul_zero]
  have hformula : ∀ m : V₁ ⊗[ℝ] V₂,
      B₁₂ m m = ∑ p, (b.repr m p) ^ 2 * (B₁ (u p.1) (u p.1) * B₂ (v p.2) (v p.2)) := by
    intro m
    conv_lhs => rw [← b.sum_repr m]
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, smul_eq_mul, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hb_ortho]
    rw [Finset.sum_eq_single p]
    · simp; ring
    · intro q _ hqp
      simp [hqp]
    · intro hp; exact absurd (Finset.mem_univ p) hp
  refine ⟨fun m => ?_, fun m => ?_⟩
  · rw [hformula m]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (sq_nonneg _) (mul_nonneg (hpos₁ p.1).le (hpos₂ p.2).le)
  · constructor
    · intro hm
      rw [hformula m] at hm
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun p _ =>
        mul_nonneg (sq_nonneg _) (mul_nonneg (hpos₁ p.1).le (hpos₂ p.2).le)).mp hm
      rw [← b.sum_repr m]
      refine Finset.sum_eq_zero fun p _ => ?_
      have hp := hall p (Finset.mem_univ p)
      rw [mul_eq_zero] at hp
      have hsq : (b.repr m p) ^ 2 = 0 :=
        hp.resolve_right (ne_of_gt (mul_pos (hpos₁ p.1) (hpos₂ p.2)))
      rw [sq_eq_zero_iff.mp hsq, zero_smul]
    · rintro rfl; simp

private theorem center_eq_bot_of_isSimple (L : Type) [LieRing L] [LieAlgebra ℝ L]
    [LieAlgebra.IsSimple ℝ L] : LieAlgebra.center ℝ L = ⊥ := by
  rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (LieAlgebra.center ℝ L) with h | h
  · exact h
  · exfalso
    apply LieAlgebra.IsSimple.non_abelian ℝ (L := L)
    refine ⟨fun x y => ?_⟩
    have hx : x ∈ LieAlgebra.center ℝ L := h ▸ Submodule.mem_top
    rw [LieModule.mem_maxTrivSubmodule] at hx
    rw [← lie_skew x y, hx y, neg_zero]

private theorem ad_eq_zero_iff_of_isSimple (L : Type) [LieRing L] [LieAlgebra ℝ L]
    [LieAlgebra.IsSimple ℝ L] (X : L) :
    LieAlgebra.ad ℝ L X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hmem : X ∈ LieAlgebra.center ℝ L := by
      rw [LieModule.mem_maxTrivSubmodule]
      intro Y
      rw [← lie_skew Y X, show ⁅X, Y⁆ = (LieAlgebra.ad ℝ L X) Y from rfl, h,
        LinearMap.zero_apply, neg_zero]
    rw [center_eq_bot_of_isSimple L, LieSubmodule.mem_bot] at hmem
    exact hmem
  · rintro rfl; simp

end GenericCartanEngine

section SplitOctonionAndAlbertInvolutions

/-- Canonical Cartan involution `σ_O` on split octonions `ZornVectorMatrix ℝ`:
`⟨a, v, w, b⟩ ↦ ⟨b, -w, -v, a⟩`. -/
def sigmaO : ZornVectorMatrix ℝ →ₗ[ℝ] ZornVectorMatrix ℝ where
  toFun X := ⟨X.b, fun i => -X.w i, fun i => -X.v i, X.a⟩
  map_add' _ _ := by
    apply ZornVectorMatrix.ext <;> [rfl; (funext i; simp [ZornVectorMatrix.add]; ring);
      (funext i; simp [ZornVectorMatrix.add]; ring); rfl]
  map_smul' r X := by
    apply ZornVectorMatrix.ext <;> [rfl; (funext i; simp [ZornVectorMatrix.smul, mul_neg]);
      (funext i; simp [ZornVectorMatrix.smul, mul_neg]); rfl]

@[simp] theorem sigmaO_a (X : ZornVectorMatrix ℝ) : (sigmaO X).a = X.b := rfl
@[simp] theorem sigmaO_v (X : ZornVectorMatrix ℝ) (i : Fin 3) : (sigmaO X).v i = -X.w i := rfl
@[simp] theorem sigmaO_w (X : ZornVectorMatrix ℝ) (i : Fin 3) : (sigmaO X).w i = -X.v i := rfl
@[simp] theorem sigmaO_b (X : ZornVectorMatrix ℝ) : (sigmaO X).b = X.a := rfl

@[simp] theorem sigmaO_involutive (X : ZornVectorMatrix ℝ) : sigmaO (sigmaO X) = X := by
  apply ZornVectorMatrix.ext <;> [rfl; (funext i; simp); (funext i; simp); rfl]

@[simp] theorem sigmaO_trace (X : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.trace (sigmaO X) = ZornVectorMatrix.trace X := by
  simp [ZornVectorMatrix.trace, add_comm]

theorem sigmaO_conj (X : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.conj (sigmaO X) = sigmaO (ZornVectorMatrix.conj X) := by
  apply ZornVectorMatrix.ext <;>
    [rfl; (funext i; simp [ZornVectorMatrix.conj]);
      (funext i; simp [ZornVectorMatrix.conj]); rfl]

theorem sigmaO_mul (X Y : ZornVectorMatrix ℝ) :
    sigmaO (ZornVectorMatrix.mul X Y) = ZornVectorMatrix.mul (sigmaO X) (sigmaO Y) := by
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.mul, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · funext i
    fin_cases i <;>
      simp [ZornVectorMatrix.mul, ZornVec3.cross] <;>
      ring
  · funext i
    fin_cases i <;>
      simp [ZornVectorMatrix.mul, ZornVec3.cross] <;>
      ring
  · simp [ZornVectorMatrix.mul, ZornVec3.dot, Fin.sum_univ_three]
    ring

theorem zornBilin_sigmaO_preserves (X Y : ZornVectorMatrix ℝ) :
    zornBilin (sigmaO X) (sigmaO Y) = zornBilin X Y := by
  change ZornVectorMatrix.trace
      (ZornVectorMatrix.mul (sigmaO X) (ZornVectorMatrix.conj (sigmaO Y))) =
    ZornVectorMatrix.trace (ZornVectorMatrix.mul X (ZornVectorMatrix.conj Y))
  rw [sigmaO_conj, ← sigmaO_mul, sigmaO_trace]

theorem zornBilin_sigmaO_symm (X Y : ZornVectorMatrix ℝ) :
    zornBilin X (sigmaO Y) = zornBilin Y (sigmaO X) := by
  rw [← zornBilin_sigmaO_preserves X (sigmaO Y), sigmaO_involutive, zornBilin_symm]

theorem zornBilin_sigmaO_formula (X : ZornVectorMatrix ℝ) :
    zornBilin X (sigmaO X) =
      X.a ^ 2 + X.b ^ 2 +
        (X.v 0 ^ 2 + X.v 1 ^ 2 + X.v 2 ^ 2) +
        (X.w 0 ^ 2 + X.w 1 ^ 2 + X.w 2 ^ 2) := by
  simp only [zornBilin, ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
    sigmaO_a, sigmaO_b, sigmaO_v, sigmaO_w, ZornVec3.dot, Fin.sum_univ_three]
  ring

theorem zornBilin_sigmaO_nonneg (X : ZornVectorMatrix ℝ) : 0 ≤ zornBilin X (sigmaO X) := by
  rw [zornBilin_sigmaO_formula]
  positivity

theorem zornBilin_sigmaO_eq_zero_iff (X : ZornVectorMatrix ℝ) :
    zornBilin X (sigmaO X) = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [zornBilin_sigmaO_formula] at h
    have ha_b := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp h
    have ha_bv := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp ha_b.1
    have ha_b0 := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp ha_bv.1
    have hv01 := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp ha_bv.2
    have hv0_1 := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp hv01.1
    have hw01 := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp ha_b.2
    have hw0_1 := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp hw01.1
    apply ZornVectorMatrix.ext (sq_eq_zero_iff.mp ha_b0.1) _ _ (sq_eq_zero_iff.mp ha_b0.2)
    · funext i
      fin_cases i
      · exact sq_eq_zero_iff.mp hv0_1.1
      · exact sq_eq_zero_iff.mp hv0_1.2
      · exact sq_eq_zero_iff.mp hv01.2
    · funext i
      fin_cases i
      · exact sq_eq_zero_iff.mp hw0_1.1
      · exact sq_eq_zero_iff.mp hw0_1.2
      · exact sq_eq_zero_iff.mp hw01.2
  · rintro rfl; simp [zornBilin_sigmaO_formula]

/-- Restriction of `sigmaO` to the 7D trace-zero subspace `splitOctonionTraceZero`. -/
def sigmaO0 : splitOctonionTraceZero →ₗ[ℝ] splitOctonionTraceZero where
  toFun a := ⟨sigmaO a.1, by change ZornVectorMatrix.trace (sigmaO a.1) = 0; rw [sigmaO_trace]; exact a.2⟩
  map_add' _ _ := by apply Subtype.ext; exact map_add sigmaO _ _
  map_smul' r a := by apply Subtype.ext; exact map_smul sigmaO r a.1

@[simp] theorem sigmaO0_coe (a : splitOctonionTraceZero) : (sigmaO0 a).1 = sigmaO a.1 := rfl

@[simp] theorem sigmaO0_involutive (a : splitOctonionTraceZero) :
    sigmaO0 (sigmaO0 a) = a := by
  apply Subtype.ext; exact sigmaO_involutive a.1

private def splitOct0CoordEquiv : splitOctonionTraceZero ≃ₗ[ℝ] (Fin 7 → ℝ) where
  toFun a := ![a.1.a, a.1.v 0, a.1.v 1, a.1.v 2, a.1.w 0, a.1.w 1, a.1.w 2]
  invFun f :=
    ⟨⟨f 0, ![f 1, f 2, f 3], ![f 4, f 5, f 6], -f 0⟩, by
      change ZornVectorMatrix.trace ⟨f 0, _, _, -f 0⟩ = 0
      simp [ZornVectorMatrix.trace]⟩
  map_add' _ _ := by
    ext i; fin_cases i <;> rfl
  map_smul' _ _ := by
    ext i; fin_cases i <;> rfl
  left_inv a := by
    apply Subtype.ext
    apply ZornVectorMatrix.ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · have ha : a.1.a + a.1.b = 0 := a.2
      dsimp; linarith
  right_inv f := by
    ext i; fin_cases i <;> rfl

theorem sigmaO0_trace : LinearMap.trace ℝ splitOctonionTraceZero sigmaO0 = -1 := by
  rw [← LinearMap.trace_conj' sigmaO0 splitOct0CoordEquiv]
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 7))]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    LinearEquiv.coe_coe, Pi.basisFun_apply,
    LinearEquiv.conj_apply, LinearMap.comp_apply, splitOct0CoordEquiv]
  rw [Fin.sum_univ_seven]
  simp [sigmaO0, sigmaO]

/-- Induced involution on `G2DerivationCarrier` (`𝔤₂(2)`): `D ↦ σ_O ∘ D ∘ σ_O`. -/
def sigmaOG2Fun (D : G2DerivationCarrier) : G2DerivationCarrier where
  toFun X := sigmaO (D (sigmaO X))
  map_add' X Y := by
    change sigmaO (D (sigmaO (X + Y))) = sigmaO (D (sigmaO X)) + sigmaO (D (sigmaO Y))
    rw [sigmaO.map_add]
    exact (congrArg sigmaO (D.map_add (sigmaO X) (sigmaO Y))).trans (sigmaO.map_add _ _)
  map_smul' r X := by
    change sigmaO (D (sigmaO (r • X))) = r • sigmaO (D (sigmaO X))
    rw [sigmaO.map_smul]
    exact (congrArg sigmaO (D.map_smul r (sigmaO X))).trans (sigmaO.map_smul r _)
  map_mul' X Y := by
    have hD := D.map_mul (sigmaO X) (sigmaO Y)
    rw [sigmaO_mul, hD]
    change sigmaO (ZornVectorMatrix.add (ZornVectorMatrix.mul (D (sigmaO X)) (sigmaO Y))
      (ZornVectorMatrix.mul (sigmaO X) (D (sigmaO Y)))) = _
    rw [show ∀ A B : ZornVectorMatrix ℝ, ZornVectorMatrix.add A B = A + B from fun _ _ => rfl,
      map_add, sigmaO_mul, sigmaO_mul]
    simp

def sigmaOG2 : G2DerivationCarrier ≃ₗ⁅ℝ⁆ G2DerivationCarrier where
  toFun := sigmaOG2Fun
  invFun := sigmaOG2Fun
  left_inv D := by
    apply ZornVectorMatrix.Derivation.ext; intro X
    simp [sigmaOG2Fun]
  right_inv D := by
    apply ZornVectorMatrix.Derivation.ext; intro X
    simp [sigmaOG2Fun]
  map_add' D₁ D₂ := by
    apply ZornVectorMatrix.Derivation.ext; intro X
    change sigmaO (D₁ (sigmaO X) + D₂ (sigmaO X)) =
      sigmaO (D₁ (sigmaO X)) + sigmaO (D₂ (sigmaO X))
    exact map_add sigmaO _ _
  map_smul' r D := by
    apply ZornVectorMatrix.Derivation.ext; intro X
    change sigmaO (r • D (sigmaO X)) = r • sigmaO (D (sigmaO X))
    exact map_smul sigmaO r _
  map_lie' {D₁ D₂} := by
    apply ZornVectorMatrix.Derivation.ext; intro X
    have hbr : ∀ (A B : G2DerivationCarrier) (Y : ZornVectorMatrix ℝ),
        ⁅A, B⁆ Y = A (B Y) - B (A Y) := fun _ _ _ => rfl
    change sigmaO (⁅D₁, D₂⁆ (sigmaO X)) = ⁅sigmaOG2Fun D₁, sigmaOG2Fun D₂⁆ X
    rw [hbr D₁ D₂ (sigmaO X), hbr (sigmaOG2Fun D₁) (sigmaOG2Fun D₂) X, map_sub]
    dsimp [sigmaOG2Fun]
    simp

@[simp] theorem sigmaOG2_involutive (D : G2DerivationCarrier) :
    sigmaOG2 (sigmaOG2 D) = D :=
  sigmaOG2.left_inv D

theorem sigmaO0_act (D : G2DerivationCarrier) (a : splitOctonionTraceZero) :
    sigmaO0 (splitOctonionDatum.act D a) =
      splitOctonionDatum.act (sigmaOG2 D) (sigmaO0 a) := by
  apply Subtype.ext
  change sigmaO (D a.1) = sigmaO (D (sigmaO (sigmaO a.1)))
  rw [sigmaO_involutive]

theorem sigmaOG2_inner (a b : splitOctonionTraceZero) :
    sigmaOG2 (splitOctonionDatum.inner a b) =
      splitOctonionDatum.inner (sigmaO0 a) (sigmaO0 b) := by
  apply ZornVectorMatrix.Derivation.ext
  intro W
  have hL := Zorn.NativeStanDerivationBilinear.innerDerivation_operatorial_normal_form
    a.1 b.1 (sigmaO W)
  have hR := Zorn.NativeStanDerivationBilinear.innerDerivation_operatorial_normal_form
    (sigmaO a.1) (sigmaO b.1) W
  change sigmaO (Zorn.NativeStanDerivationBilinear.innerDerivation a.1 b.1 (sigmaO W)) =
    Zorn.NativeStanDerivationBilinear.innerDerivation (sigmaO a.1) (sigmaO b.1) W
  rw [hL, hR]
  simp only [show ∀ x y : ZornVectorMatrix ℝ, x * y = ZornVectorMatrix.mul x y from fun _ _ => rfl,
    map_sub, map_nsmul, sigmaO_mul, sigmaO_involutive]

theorem sigmaOG2_trace :
    LinearMap.trace ℝ G2DerivationCarrier sigmaOG2.toLinearMap = -2 := by
  let e := InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv
  rw [← LinearMap.trace_conj' sigmaOG2.toLinearMap e.symm]
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 14))]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    LinearEquiv.coe_coe, Pi.basisFun_apply,
    LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.symm_symm,
    Pi.basisFun_repr]
  change ∑ i : Fin 14, InfoGeometry.Lie.CanonicalZornDerivationDimension.derivationParameters
      (sigmaOG2Fun (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation
        (Pi.single i 1))) i = -2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp [InfoGeometry.Lie.CanonicalZornDerivationDimension.derivationParameters,
    sigmaOG2Fun, sigmaO, InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation,
    InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterAction,
    ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVec3.basis]

/-- Canonical Cartan involution `σ_J` on split Albert algebra `H3Zorn ℝ`:
`⟨α₁, α₂, α₃, a, b, c⟩ ↦ ⟨α₁, α₂, α₃, σ_O a, σ_O b, σ_O c⟩`. -/
def sigmaJ : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ where
  toFun X := ⟨X.α₁, X.α₂, X.α₃, sigmaO X.a, sigmaO X.b, sigmaO X.c⟩
  map_add' X Y := by
    apply H3Zorn.ext_h3 <;> try rfl
    all_goals exact map_add sigmaO _ _
  map_smul' r X := by
    apply H3Zorn.ext_h3 <;> try rfl
    all_goals exact map_smul sigmaO r _

@[simp] theorem sigmaJ_α₁ (X : H3Zorn ℝ) : (sigmaJ X).α₁ = X.α₁ := rfl
@[simp] theorem sigmaJ_α₂ (X : H3Zorn ℝ) : (sigmaJ X).α₂ = X.α₂ := rfl
@[simp] theorem sigmaJ_α₃ (X : H3Zorn ℝ) : (sigmaJ X).α₃ = X.α₃ := rfl
@[simp] theorem sigmaJ_a (X : H3Zorn ℝ) : (sigmaJ X).a = sigmaO X.a := rfl
@[simp] theorem sigmaJ_b (X : H3Zorn ℝ) : (sigmaJ X).b = sigmaO X.b := rfl
@[simp] theorem sigmaJ_c (X : H3Zorn ℝ) : (sigmaJ X).c = sigmaO X.c := rfl

@[simp] theorem sigmaJ_involutive (X : H3Zorn ℝ) : sigmaJ (sigmaJ X) = X := by
  apply H3Zorn.ext_h3 <;> simp

@[simp] theorem sigmaJ_linearTrace (X : H3Zorn ℝ) :
    H3Zorn.linearTrace (sigmaJ X) = H3Zorn.linearTrace X := rfl

@[simp] theorem sigmaJ_one : sigmaJ (1 : H3Zorn ℝ) = 1 := by
  have hz : sigmaO ZornVectorMatrix.zero = ZornVectorMatrix.zero := by
    apply ZornVectorMatrix.ext <;> [rfl; (funext i; simp [ZornVectorMatrix.zero]);
      (funext i; simp [ZornVectorMatrix.zero]); rfl]
  apply H3Zorn.ext_h3 <;> [rfl; rfl; rfl; exact hz; exact hz; exact hz]

private theorem sigmaO_norm (X : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.norm (sigmaO X) = ZornVectorMatrix.norm X := by
  simp only [ZornVectorMatrix.norm, sigmaO_a, sigmaO_b, sigmaO_v, sigmaO_w,
    ZornVec3.dot, Fin.sum_univ_three]
  ring

private theorem sigmaJ_adjointQuad (X : H3Zorn ℝ) :
    H3Zorn.adjointQuad (sigmaJ X) = sigmaJ (H3Zorn.adjointQuad X) := by
  apply H3Zorn.ext_h3
  · simp [H3Zorn.adjointQuad, sigmaO_norm]
  · simp [H3Zorn.adjointQuad, sigmaO_norm]
  · simp [H3Zorn.adjointQuad, sigmaO_norm]
  · simp only [sigmaJ_a, H3Zorn.adjointQuad]
    change (sigmaO X.c).conj.mul (sigmaO X.b).conj - X.α₃ • sigmaO X.a =
      sigmaO (X.c.conj.mul X.b.conj - X.α₃ • X.a)
    rw [map_sub, map_smul, sigmaO_mul, sigmaO_conj, sigmaO_conj]
  · simp only [sigmaJ_b, H3Zorn.adjointQuad]
    change (sigmaO X.a).conj.mul (sigmaO X.c).conj - X.α₁ • sigmaO X.b =
      sigmaO (X.a.conj.mul X.c.conj - X.α₁ • X.b)
    rw [map_sub, map_smul, sigmaO_mul, sigmaO_conj, sigmaO_conj]
  · simp only [sigmaJ_c, H3Zorn.adjointQuad]
    change (sigmaO X.b).conj.mul (sigmaO X.a).conj - X.α₂ • sigmaO X.c =
      sigmaO (X.b.conj.mul X.a.conj - X.α₂ • X.c)
    rw [map_sub, map_smul, sigmaO_mul, sigmaO_conj, sigmaO_conj]

private theorem sigmaJ_crossProduct (X Y : H3Zorn ℝ) :
    H3Zorn.crossProduct (sigmaJ X) (sigmaJ Y) = sigmaJ (H3Zorn.crossProduct X Y) := by
  simp only [H3Zorn.crossProduct, ← map_add, sigmaJ_adjointQuad, map_sub]

theorem sigmaJ_traceBilin_preserves (X Y : H3Zorn ℝ) :
    H3Zorn.traceBilin (sigmaJ X) (sigmaJ Y) = H3Zorn.traceBilin X Y := by
  simp only [H3Zorn.traceBilin, sigmaJ_α₁, sigmaJ_α₂, sigmaJ_α₃, sigmaJ_a, sigmaJ_b, sigmaJ_c]
  rw [show ZornVectorMatrix.trace (ZornVectorMatrix.mul (sigmaO X.a) (ZornVectorMatrix.conj (sigmaO Y.a))) =
      ZornVectorMatrix.trace (ZornVectorMatrix.mul X.a (ZornVectorMatrix.conj Y.a)) from
    zornBilin_sigmaO_preserves X.a Y.a]
  rw [show ZornVectorMatrix.trace (ZornVectorMatrix.mul (sigmaO X.b) (ZornVectorMatrix.conj (sigmaO Y.b))) =
      ZornVectorMatrix.trace (ZornVectorMatrix.mul X.b (ZornVectorMatrix.conj Y.b)) from
    zornBilin_sigmaO_preserves X.b Y.b]
  rw [show ZornVectorMatrix.trace (ZornVectorMatrix.mul (sigmaO X.c) (ZornVectorMatrix.conj (sigmaO Y.c))) =
      ZornVectorMatrix.trace (ZornVectorMatrix.mul X.c (ZornVectorMatrix.conj Y.c)) from
    zornBilin_sigmaO_preserves X.c Y.c]

private theorem sigmaJ_U (X Y : H3Zorn ℝ) :
    H3Zorn.U (sigmaJ X) (sigmaJ Y) = sigmaJ (H3Zorn.U X Y) := by
  simp only [H3Zorn.U, sigmaJ_traceBilin_preserves, sigmaJ_adjointQuad, sigmaJ_crossProduct,
    map_sub, map_smul]

theorem sigmaJ_mul (X Y : H3Zorn ℝ) : sigmaJ (X * Y) = sigmaJ X * sigmaJ Y := by
  change sigmaJ ((1 / 2 : ℝ) • H3Zorn.T X 1 Y) =
    (1 / 2 : ℝ) • H3Zorn.T (sigmaJ X) 1 (sigmaJ Y)
  have h1 : (1 : H3Zorn ℝ) = sigmaJ 1 := sigmaJ_one.symm
  conv_rhs => rw [h1]
  simp only [H3Zorn.T, ← map_add, ← map_sub, ← map_smul, sigmaJ_U]

theorem sigmaJ_traceBilin_symm (X Y : H3Zorn ℝ) :
    H3Zorn.traceBilin X (sigmaJ Y) = H3Zorn.traceBilin Y (sigmaJ X) := by
  rw [← sigmaJ_traceBilin_preserves X (sigmaJ Y), sigmaJ_involutive, H3Zorn.traceBilin_symm]

theorem sigmaJ_traceBilin_nonneg (X : H3Zorn ℝ) : 0 ≤ H3Zorn.traceBilin X (sigmaJ X) := by
  simp only [H3Zorn.traceBilin, sigmaJ_α₁, sigmaJ_α₂, sigmaJ_α₃, sigmaJ_a, sigmaJ_b, sigmaJ_c]
  change 0 ≤ X.α₁ * X.α₁ + X.α₂ * X.α₂ + X.α₃ * X.α₃ +
    zornBilin X.a (sigmaO X.a) + zornBilin X.b (sigmaO X.b) + zornBilin X.c (sigmaO X.c)
  have ha := zornBilin_sigmaO_nonneg X.a
  have hb := zornBilin_sigmaO_nonneg X.b
  have hc := zornBilin_sigmaO_nonneg X.c
  nlinarith [sq_nonneg X.α₁, sq_nonneg X.α₂, sq_nonneg X.α₃]

theorem sigmaJ_traceBilin_eq_zero_iff (X : H3Zorn ℝ) :
    H3Zorn.traceBilin X (sigmaJ X) = 0 ↔ X = 0 := by
  constructor
  · intro h
    simp only [H3Zorn.traceBilin, sigmaJ_α₁, sigmaJ_α₂, sigmaJ_α₃, sigmaJ_a, sigmaJ_b, sigmaJ_c] at h
    change X.α₁ * X.α₁ + X.α₂ * X.α₂ + X.α₃ * X.α₃ +
      zornBilin X.a (sigmaO X.a) + zornBilin X.b (sigmaO X.b) + zornBilin X.c (sigmaO X.c) = 0 at h
    have ha := zornBilin_sigmaO_nonneg X.a
    have hb := zornBilin_sigmaO_nonneg X.b
    have hc := zornBilin_sigmaO_nonneg X.c
    have h1 : X.α₁ = 0 := by nlinarith [sq_nonneg X.α₁, sq_nonneg X.α₂, sq_nonneg X.α₃]
    have h2 : X.α₂ = 0 := by nlinarith [sq_nonneg X.α₁, sq_nonneg X.α₂, sq_nonneg X.α₃]
    have h3 : X.α₃ = 0 := by nlinarith [sq_nonneg X.α₁, sq_nonneg X.α₂, sq_nonneg X.α₃]
    have hza : zornBilin X.a (sigmaO X.a) = 0 := by linarith [sq_nonneg X.α₁, sq_nonneg X.α₂, sq_nonneg X.α₃]
    have hzb : zornBilin X.b (sigmaO X.b) = 0 := by linarith [sq_nonneg X.α₁, sq_nonneg X.α₂, sq_nonneg X.α₃]
    have hzc : zornBilin X.c (sigmaO X.c) = 0 := by linarith [sq_nonneg X.α₁, sq_nonneg X.α₂, sq_nonneg X.α₃]
    exact H3Zorn.ext_h3 (X := X) (Y := 0) h1 h2 h3
      ((zornBilin_sigmaO_eq_zero_iff X.a).mp hza)
      ((zornBilin_sigmaO_eq_zero_iff X.b).mp hzb)
      ((zornBilin_sigmaO_eq_zero_iff X.c).mp hzc)
  · rintro rfl
    simp [H3Zorn.traceBilin, ZornVectorMatrix.zero, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot]

/-- Restriction of `sigmaJ` to the 26D trace-zero subspace `h3TraceZero`. -/
def sigmaJ0 : h3TraceZero →ₗ[ℝ] h3TraceZero where
  toFun x := ⟨sigmaJ x.1, by change H3Zorn.linearTrace (sigmaJ x.1) = 0; exact x.2⟩
  map_add' _ _ := by apply Subtype.ext; exact map_add sigmaJ _ _
  map_smul' r x := by apply Subtype.ext; exact map_smul sigmaJ r x.1

@[simp] theorem sigmaJ0_coe (x : h3TraceZero) : (sigmaJ0 x).1 = sigmaJ x.1 := rfl

@[simp] theorem sigmaJ0_involutive (x : h3TraceZero) : sigmaJ0 (sigmaJ0 x) = x := by
  apply Subtype.ext; exact sigmaJ_involutive x.1

theorem sigmaJ0_mul0 (x y : h3TraceZero) :
    sigmaJ0 (h3ZornJordanDatum.mul₀ x y) = h3ZornJordanDatum.mul₀ (sigmaJ0 x) (sigmaJ0 y) := by
  apply Subtype.ext
  change sigmaJ (MagicSquareTitsBracket.h3Mul0 x y).1 =
    (MagicSquareTitsBracket.h3Mul0 (sigmaJ0 x) (sigmaJ0 y)).1
  simp only [MagicSquareTitsBracket.h3Mul0_coe, map_sub, map_smul, sigmaJ_mul, sigmaJ_one,
    sigmaJ0_coe, sigmaJ_traceBilin_preserves]

private def h3ZornSplitEquiv : H3Zorn ℝ ≃ₗ[ℝ] h3TraceZero × ℝ where
  toFun X :=
    (⟨X - (H3Zorn.linearTrace X / 3) • (1 : H3Zorn ℝ), by
        change H3Zorn.linearTrace (X - (H3Zorn.linearTrace X / 3) • (1 : H3Zorn ℝ)) = 0
        rw [H3Zorn.linearTrace]
        simp only [H3Zorn.sub_readback, H3Zorn.smul_readback, H3Zorn.one_readback,
          H3Zorn.linearTrace]
        ring⟩,
     H3Zorn.linearTrace X)
  invFun p := p.1.1 + (p.2 / 3) • (1 : H3Zorn ℝ)
  map_add' X Y := by
    apply Prod.ext
    · apply Subtype.ext
      change (X + Y) - (H3Zorn.linearTrace (X + Y) / 3) • (1 : H3Zorn ℝ) =
        (X - (H3Zorn.linearTrace X / 3) • (1 : H3Zorn ℝ)) +
          (Y - (H3Zorn.linearTrace Y / 3) • (1 : H3Zorn ℝ))
      rw [H3Zorn.linearTrace_add, add_div, add_smul]
      abel
    · exact H3Zorn.linearTrace_add X Y
  map_smul' r X := by
    apply Prod.ext
    · apply Subtype.ext
      change (r • X) - (H3Zorn.linearTrace (r • X) / 3) • (1 : H3Zorn ℝ) =
        r • (X - (H3Zorn.linearTrace X / 3) • (1 : H3Zorn ℝ))
      rw [H3Zorn.linearTrace_smul, mul_div_assoc, ← smul_smul, smul_sub]
    · exact H3Zorn.linearTrace_smul r X
  left_inv X := by simp
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change (p.1.1 + (p.2 / 3) • (1 : H3Zorn ℝ)) -
          (H3Zorn.linearTrace (p.1.1 + (p.2 / 3) • (1 : H3Zorn ℝ)) / 3) • (1 : H3Zorn ℝ) =
        p.1.1
      have hp : H3Zorn.linearTrace p.1.1 = 0 := p.1.2
      have h1 : H3Zorn.linearTrace (1 : H3Zorn ℝ) = 3 := by
        simp [H3Zorn.linearTrace, H3Zorn.one_readback]; norm_num
      rw [H3Zorn.linearTrace_add, H3Zorn.linearTrace_smul, hp, h1, zero_add]
      have hdiv : p.2 / 3 * 3 = p.2 := by ring
      rw [hdiv, add_sub_cancel_right]
    · change H3Zorn.linearTrace (p.1.1 + (p.2 / 3) • (1 : H3Zorn ℝ)) = p.2
      have hp : H3Zorn.linearTrace p.1.1 = 0 := p.1.2
      have h1 : H3Zorn.linearTrace (1 : H3Zorn ℝ) = 3 := by
        simp [H3Zorn.linearTrace, H3Zorn.one_readback]; norm_num
      rw [H3Zorn.linearTrace_add, H3Zorn.linearTrace_smul, hp, h1, zero_add]
      ring

theorem sigmaJ0_trace : LinearMap.trace ℝ h3TraceZero sigmaJ0 = 2 := by
  have hconj : h3ZornSplitEquiv.conj sigmaJ = sigmaJ0.prodMap LinearMap.id := by
    apply LinearMap.ext; rintro ⟨x, t⟩
    apply Prod.ext
    · apply Subtype.ext
      simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply]
      change (sigmaJ (x.1 + (t / 3) • (1 : H3Zorn ℝ))) -
          (H3Zorn.linearTrace (sigmaJ (x.1 + (t / 3) • (1 : H3Zorn ℝ))) / 3) • (1 : H3Zorn ℝ) =
        sigmaJ x.1
      rw [map_add, map_smul, sigmaJ_one, H3Zorn.linearTrace_add, H3Zorn.linearTrace_smul]
      have hx' : H3Zorn.linearTrace (sigmaJ x.1) = 0 := (sigmaJ0 x).2
      have h1 : H3Zorn.linearTrace (1 : H3Zorn ℝ) = 3 := by
        simp [H3Zorn.linearTrace, H3Zorn.one_readback]; norm_num
      rw [hx', h1, zero_add, show t / 3 * 3 = t by ring, add_sub_cancel_right]
    · simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply]
      change H3Zorn.linearTrace (sigmaJ (x.1 + (t / 3) • (1 : H3Zorn ℝ))) = t
      rw [map_add, map_smul, sigmaJ_one, H3Zorn.linearTrace_add, H3Zorn.linearTrace_smul]
      have hx' : H3Zorn.linearTrace (sigmaJ x.1) = 0 := (sigmaJ0 x).2
      have h1 : H3Zorn.linearTrace (1 : H3Zorn ℝ) = 3 := by
        simp [H3Zorn.linearTrace, H3Zorn.one_readback]; norm_num
      rw [hx', h1, zero_add]; ring
  have htrJ : LinearMap.trace ℝ (H3Zorn ℝ) sigmaJ = 3 := by
    rw [← LinearMap.trace_conj' sigmaJ h3ZornCoordEquiv]
    rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 27))]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
      LinearEquiv.coe_coe, Pi.basisFun_apply,
      LinearEquiv.conj_apply, LinearMap.comp_apply]
    change ∑ i : Fin 27, h3ZornCoordinate (sigmaJ (reconstructH3Zorn (Pi.single i 1))) i = 3
    have hsum : ∀ i : Fin 27,
        h3ZornCoordinate (sigmaJ (reconstructH3Zorn (Pi.single i 1))) i =
          if i.val < 3 then 1 else 0 := by
      intro i
      fin_cases i <;> simp [h3ZornCoordinate, reconstructH3Zorn, sigmaJ, sigmaO]
    simp_rw [hsum]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num
  have htot := LinearMap.trace_conj' sigmaJ h3ZornSplitEquiv
  rw [hconj, LinearMap.trace_prodMap', LinearMap.trace_id, htrJ, Module.finrank_self] at htot
  simp at htot
  linarith

/-- Induced involution on `F4DerivationCarrier` (`H3ZornF4Derivations`, `𝔣₄(4)`):
`F ↦ σ_J ∘ F ∘ σ_J`. -/
def sigmaJF4Fun (F : F4DerivationCarrier) : F4DerivationCarrier :=
  ⟨sigmaJ ∘ₗ F.1 ∘ₗ sigmaJ, fun X Y => by
    simp only [LinearMap.comp_apply]
    have hF := F.2 (sigmaJ X) (sigmaJ Y)
    have hmul : (sigmaJ X) * (sigmaJ Y) = sigmaJ (X * Y) := (sigmaJ_mul X Y).symm
    rw [hmul] at hF
    rw [hF, map_add, sigmaJ_mul, sigmaJ_mul, sigmaJ_involutive, sigmaJ_involutive]⟩

def sigmaJF4 : F4DerivationCarrier ≃ₗ⁅ℝ⁆ F4DerivationCarrier where
  toFun := sigmaJF4Fun
  invFun := sigmaJF4Fun
  left_inv F := by
    apply Subtype.ext; apply LinearMap.ext; intro X
    simp [sigmaJF4Fun]
  right_inv F := by
    apply Subtype.ext; apply LinearMap.ext; intro X
    simp [sigmaJF4Fun]
  map_add' F₁ F₂ := by
    apply Subtype.ext; apply LinearMap.ext; intro X
    simp [sigmaJF4Fun]
  map_smul' r F := by
    apply Subtype.ext; apply LinearMap.ext; intro X
    simp [sigmaJF4Fun]
  map_lie' {F₁ F₂} := by
    apply Subtype.ext; apply LinearMap.ext; intro X
    simp [sigmaJF4Fun, LieSubalgebra.coe_bracket, Ring.lie_def]

@[simp] theorem sigmaJF4_involutive (F : F4DerivationCarrier) :
    sigmaJF4 (sigmaJF4 F) = F :=
  sigmaJF4.left_inv F

theorem sigmaJ0_act (F : F4DerivationCarrier) (x : h3TraceZero) :
    sigmaJ0 (h3ZornJordanDatum.act F x) =
      h3ZornJordanDatum.act (sigmaJF4 F) (sigmaJ0 x) := by
  apply Subtype.ext
  change sigmaJ (F.1 x.1) = sigmaJ (F.1 (sigmaJ (sigmaJ x.1)))
  rw [sigmaJ_involutive]

theorem sigmaJF4_inner (x y : h3TraceZero) :
    sigmaJF4 (h3ZornJordanDatum.inner x y) =
      h3ZornJordanDatum.inner (sigmaJ0 x) (sigmaJ0 y) := by
  apply Subtype.ext; apply LinearMap.ext; intro W
  change sigmaJ ((MagicSquareTitsBracket.f4Inner x y).1 (sigmaJ W)) =
    (MagicSquareTitsBracket.f4Inner (sigmaJ0 x) (sigmaJ0 y)).1 W
  simp only [MagicSquareTitsBracket.f4Inner, h3ZornJordanInnerDerivation_apply]
  rw [map_sub, sigmaJ_mul, sigmaJ_mul, sigmaJ_mul, sigmaJ_mul, sigmaJ_involutive]
  rfl

private def sigmaJSparse : SparseMat27 :=
  [(0, 0, 1), (1, 1, 1), (2, 2, 1),
   (3, 10, 1), (4, 7, -1), (5, 8, -1), (6, 9, -1),
   (7, 4, -1), (8, 5, -1), (9, 6, -1), (10, 3, 1),
   (11, 18, 1), (12, 15, -1), (13, 16, -1), (14, 17, -1),
   (15, 12, -1), (16, 13, -1), (17, 14, -1), (18, 11, 1),
   (19, 26, 1), (20, 23, -1), (21, 24, -1), (22, 25, -1),
   (23, 20, -1), (24, 21, -1), (25, 22, -1), (26, 19, 1)]

private def sigmaJIdx (r : Fin 27) : Fin 27 :=
  match r.val with
  | 0 => 0 | 1 => 1 | 2 => 2
  | 3 => 10 | 4 => 7 | 5 => 8 | 6 => 9 | 7 => 4 | 8 => 5 | 9 => 6 | 10 => 3
  | 11 => 18 | 12 => 15 | 13 => 16 | 14 => 17 | 15 => 12 | 16 => 13 | 17 => 14 | 18 => 11
  | 19 => 26 | 20 => 23 | 21 => 24 | 22 => 25 | 23 => 20 | 24 => 21 | 25 => 22 | _ => 19

private def sigmaJSgn (r : Fin 27) : ℤ :=
  match r.val with
  | 4 | 5 | 6 | 7 | 8 | 9 | 12 | 13 | 14 | 15 | 16 | 17 | 20 | 21 | 22 | 23 | 24 | 25 => -1
  | _ => 1

private theorem h3ZornCoordinate_sigmaJ (X : H3Zorn ℝ) (r : Fin 27) :
    h3ZornCoordinate (sigmaJ X) r = (sigmaJSgn r : ℝ) * h3ZornCoordinate X (sigmaJIdx r) := by
  fin_cases r <;>
    simp [h3ZornCoordinate, sigmaJ, sigmaO, sigmaJSgn, sigmaJIdx]

private theorem h3zornToMatrix_sigmaJ :
    h3zornToMatrix sigmaJ = (sparseToMat sigmaJSparse).map Int.cast := by
  have hsp : (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal sigmaJSparse r c ==
        if c == sigmaJIdx r then sigmaJSgn r else 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hsp
  ext r c
  rw [Matrix.map_apply, h3zornToMatrix_apply, h3ZornCoordinate_sigmaJ,
    h3ZornCoordinate_basis_self]
  change _ = ((sparseVal sigmaJSparse r c : ℤ) : ℝ)
  rw [hsp r c]
  split_ifs <;> simp

private theorem sigmaJF4_f4SimpleH (i : Fin 4) :
    sigmaJF4 (f4SimpleH i) = -f4SimpleH i := by
  have hchk : (List.finRange 4).all (fun i =>
      sparseEq (sparseMul sigmaJSparse (sparseMul (f4CartanDiagSparse i) sigmaJSparse))
        (sparseNeg (f4CartanDiagSparse i))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  apply Subtype.ext
  apply h3zornToMatrix.injective
  have hcoe : (sigmaJF4 (f4SimpleH i) : Module.End ℝ (H3Zorn ℝ)) =
      sigmaJ * (f4SimpleH i : Module.End ℝ (H3Zorn ℝ)) * sigmaJ := by
    apply LinearMap.ext; intro x; rfl
  rw [hcoe, map_mul, map_mul, h3zornToMatrix_sigmaJ, h3zornToMatrix_f4SimpleH,
    show ((-f4SimpleH i : F4DerivationCarrier) : Module.End ℝ (H3Zorn ℝ)) =
      -(f4SimpleH i : Module.End ℝ (H3Zorn ℝ)) from rfl,
    map_neg, h3zornToMatrix_f4SimpleH]
  have hmat := congrArg (fun M : Matrix (Fin 27) (Fin 27) ℤ => M.map (Int.cast : ℤ → ℝ))
    (sparseToMat_eq_of_sparseEq (hchk i))
  simp only [sparseToMat_mul, sparseToMat_neg] at hmat
  rw [Matrix.mul_assoc]
  ext r c
  have hrc := congrArg (fun M : Matrix (Fin 27) (Fin 27) ℝ => M r c) hmat
  simpa [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum] using hrc

private theorem matrix27Int_noncommutative :
    ∃ A B : Matrix (Fin 27) (Fin 27) ℤ, A * B ≠ B * A := by
  refine ⟨sparseToMat sigmaJSparse, sparseToMat (f4CartanDiagSparse 0), ?_⟩
  intro h
  have h47 := congrArg (fun M : Matrix (Fin 27) (Fin 27) ℤ => M ⟨4, by omega⟩ ⟨7, by omega⟩) h
  rw [← sparseToMat_mul, ← sparseToMat_mul] at h47
  have hl : sparseToMat (sparseMul sigmaJSparse (f4CartanDiagSparse 0))
      ⟨4, by omega⟩ ⟨7, by omega⟩ = -1 := by decide
  have hr : sparseToMat (sparseMul (f4CartanDiagSparse 0) sigmaJSparse)
      ⟨4, by omega⟩ ⟨7, by omega⟩ = 1 := by decide
  rw [hl, hr] at h47
  omega

private theorem matrix27Real_noncommutative :
    ∃ A B : Matrix (Fin 27) (Fin 27) ℝ, A * B ≠ B * A := by
  refine ⟨h3zornToMatrix sigmaJ, h3zornToMatrix (f4SimpleH 0).1, ?_⟩
  rw [h3zornToMatrix_sigmaJ, h3zornToMatrix_f4SimpleH]
  intro h
  have h47 := congrArg (fun M : Matrix (Fin 27) (Fin 27) ℝ => M ⟨4, by omega⟩ ⟨7, by omega⟩) h
  have hmapL : (sparseToMat sigmaJSparse).map (Int.cast : ℤ → ℝ) *
      (sparseToMat (f4CartanDiagSparse 0)).map (Int.cast : ℤ → ℝ) =
      (sparseToMat (sparseMul sigmaJSparse (f4CartanDiagSparse 0))).map Int.cast := by
    rw [sparseToMat_mul]
    ext r c; simp [Matrix.mul_apply]
  have hmapR : (sparseToMat (f4CartanDiagSparse 0)).map (Int.cast : ℤ → ℝ) *
      (sparseToMat sigmaJSparse).map (Int.cast : ℤ → ℝ) =
      (sparseToMat (sparseMul (f4CartanDiagSparse 0) sigmaJSparse)).map Int.cast := by
    rw [sparseToMat_mul]
    ext r c; simp [Matrix.mul_apply]
  rw [hmapL, hmapR, Matrix.map_apply, Matrix.map_apply] at h47
  have hl : sparseToMat (sparseMul sigmaJSparse (f4CartanDiagSparse 0))
      ⟨4, by omega⟩ ⟨7, by omega⟩ = -1 := by decide
  have hr : sparseToMat (sparseMul (f4CartanDiagSparse 0) sigmaJSparse)
      ⟨4, by omega⟩ ⟨7, by omega⟩ = 1 := by decide
  rw [hl, hr] at h47
  norm_num at h47

theorem sigmaJF4_trace :
    LinearMap.trace ℝ F4DerivationCarrier sigmaJF4.toLinearMap = -4 := by
  rw [LinearMap.trace_eq_matrix_trace ℝ f4ChevalleyBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    Fintype.sum_sum_type, f4ChevalleyBasis_inl, f4ChevalleyBasis_inr]
  have h1 : ∀ i : Fin 4,
      (f4ChevalleyBasis.repr (sigmaJF4 (f4SimpleH i))) (Sum.inl i) = -1 := by
    intro i
    rw [sigmaJF4_f4SimpleH i, map_neg, Finsupp.neg_apply, ← f4ChevalleyBasis_inl i,
      Module.Basis.repr_self, Finsupp.single_eq_same]
  have h2 : ∀ r : Fin 48,
      (f4ChevalleyBasis.repr (sigmaJF4 (f4RootVec r))) (Sum.inr r) = 0 := by
    intro r
    obtain ⟨i, hi⟩ := f4RootEigenvalue_ne_zero r
    let X := sigmaJF4 (f4RootVec r)
    have hbrL : ⁅f4SimpleH i, X⁆ = -(f4RootEigenvalue i r : ℝ) • X := by
      have hid : f4SimpleH i = -sigmaJF4 (f4SimpleH i) := by
        rw [sigmaJF4_f4SimpleH i, neg_neg]
      conv_lhs => rw [hid, neg_lie]
      dsimp [X]
      rw [← LieEquiv.map_lie, f4RootVec_bracket_H, map_smul, ← neg_smul]
    have hrep := f4ChevalleyBasis.sum_repr X
    rw [Fintype.sum_sum_type] at hrep
    simp only [f4ChevalleyBasis_inl, f4ChevalleyBasis_inr] at hrep
    have hKillH : ⁅f4SimpleH i, ∑ j : Fin 4,
        (f4ChevalleyBasis.repr X) (Sum.inl j) • f4SimpleH j⁆ = 0 := by
      rw [lie_sum]
      exact Finset.sum_eq_zero fun j _ => by rw [lie_smul, f4SimpleH_comm, smul_zero]
    have hbrR : ⁅f4SimpleH i, X⁆ =
        ∑ q : Fin 48, ((f4ChevalleyBasis.repr X) (Sum.inr q) * (f4RootEigenvalue i q : ℝ)) •
          f4RootVec q := by
      conv_lhs => rw [← hrep]
      rw [lie_add, hKillH, zero_add, lie_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [lie_smul, f4RootVec_bracket_H, smul_smul]
    have hcoeff := congrArg (fun Y => (f4ChevalleyBasis.repr Y) (Sum.inr r))
      (hbrL.symm.trans hbrR)
    simp only [map_smul, smul_eq_mul, map_sum, ← f4ChevalleyBasis_inr,
      Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, Finsupp.single_apply] at hcoeff
    rw [Finset.sum_eq_single r] at hcoeff
    · simp only [↓reduceIte, mul_one] at hcoeff
      have hnz : (f4RootEigenvalue i r : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hi
      have h2eq : 2 * (f4RootEigenvalue i r : ℝ) * (f4ChevalleyBasis.repr X) (Sum.inr r) = 0 := by
        linarith
      rcases mul_eq_zero.mp h2eq with h0 | hdone
      · exfalso; exact hnz (by linarith)
      · exact hdone
    · intro q _ hqr
      simp [Sum.inr.injEq, hqr]
    · intro hr; exact absurd (Finset.mem_univ r) hr
  have hs1 : (∑ i : Fin 4, (f4ChevalleyBasis.repr (sigmaJF4 (f4SimpleH i))) (Sum.inl i)) = -4 := by
    simp_rw [h1]
    norm_num
  have hs2 : (∑ r : Fin 48, (f4ChevalleyBasis.repr (sigmaJF4 (f4RootVec r))) (Sum.inr r)) = 0 := by
    simp_rw [h2]
    norm_num
  change (∑ i : Fin 4, (f4ChevalleyBasis.repr (sigmaJF4 (f4SimpleH i))) (Sum.inl i)) +
      (∑ r : Fin 48, (f4ChevalleyBasis.repr (sigmaJF4 (f4RootVec r))) (Sum.inr r)) = -4
  rw [hs1, hs2]
  norm_num

end SplitOctonionAndAlbertInvolutions

section E8CartanInvolutionsAndSignatures

section GenericMSInvolution

private def msLinearEquiv {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) :
    MagicSquareLie O J ≃ₗ[ℝ] G₂ × ((O₀ ⊗[ℝ] J₀) × F₄) where
  toFun X := (X.g2, (X.mixed, X.f4))
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv X := by cases X; rfl
  right_inv p := by rcases p with ⟨g, m, f⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def msCartanInvolution {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (θG2 : G₂ ≃ₗ⁅ℝ⁆ G₂) (θO : O₀ →ₗ[ℝ] O₀) (θJ : J₀ →ₗ[ℝ] J₀) (θF4 : F₄ ≃ₗ⁅ℝ⁆ F₄)
    (hθG2_inv : ∀ D, θG2 (θG2 D) = D)
    (hθO_inv : ∀ a, θO (θO a) = a)
    (hθJ_inv : ∀ x, θJ (θJ x) = x)
    (hθF4_inv : ∀ F, θF4 (θF4 F) = F)
    (hθO_bilin : ∀ a b, O.bilin₀ (θO a) (θO b) = O.bilin₀ a b)
    (hθO_comm : ∀ a b, θO (O.comm₀ a b) = O.comm₀ (θO a) (θO b))
    (hθO_act : ∀ D a, θO (O.act D a) = O.act (θG2 D) (θO a))
    (hθO_inner : ∀ a b, θG2 (O.inner a b) = O.inner (θO a) (θO b))
    (hθJ_bilin : ∀ x y, J.traceBilin₀ (θJ x) (θJ y) = J.traceBilin₀ x y)
    (hθJ_mul : ∀ x y, θJ (J.mul₀ x y) = J.mul₀ (θJ x) (θJ y))
    (hθJ_act : ∀ F x, θJ (J.act F x) = J.act (θF4 F) (θJ x))
    (hθJ_inner : ∀ x y, θF4 (J.inner x y) = J.inner (θJ x) (θJ y)) :
    MagicSquareLie O J ≃ₗ⁅ℝ⁆ MagicSquareLie O J :=
  let θM : (O₀ ⊗[ℝ] J₀) →ₗ[ℝ] (O₀ ⊗[ℝ] J₀) := TensorProduct.map θO θJ
  let toFun : MagicSquareLie O J → MagicSquareLie O J := fun X =>
    ⟨θG2 X.g2, θM X.mixed, θF4 X.f4⟩
  have hθM_inv : ∀ m : O₀ ⊗[ℝ] J₀, θM (θM m) = m := fun m => by
    induction m using TensorProduct.inductionOn with
    | tmul a x => simp [θM, TensorProduct.map_tmul, hθO_inv, hθJ_inv]
    | add _ _ h1 h2 => simp [map_add, h1, h2]
  have hbilinM : ∀ m₁ m₂ : O₀ ⊗[ℝ] J₀,
      magicMixedBilin O J (θM m₁) (θM m₂) = magicMixedBilin O J m₁ m₂ := fun m₁ m₂ => by
    induction m₁ using TensorProduct.inductionOn with
    | tmul a x =>
      induction m₂ using TensorProduct.inductionOn with
      | tmul b y =>
        simp [θM, TensorProduct.map_tmul, magicMixedBilin_tmul, hθO_bilin, hθJ_bilin]
      | add _ _ h1 h2 => simp [map_add, h1, h2]
    | add _ _ h1 h2 => simp [map_add, LinearMap.add_apply, h1, h2]
  have hmixed_g2 : ∀ (D : G₂) (m : O₀ ⊗[ℝ] J₀),
      θM (magicG2MixedActLM O D m) = magicG2MixedActLM O (θG2 D) (θM m) := fun D m => by
    induction m using TensorProduct.inductionOn with
    | tmul a x => simp [θM, TensorProduct.map_tmul, magicG2MixedActLM_tmul, hθO_act]
    | add _ _ h1 h2 => simp [map_add, h1, h2]
  have hmixed_f4 : ∀ (F : F₄) (m : O₀ ⊗[ℝ] J₀),
      θM (magicF4MixedActLM J F m) = magicF4MixedActLM J (θF4 F) (θM m) := fun F m => by
    induction m using TensorProduct.inductionOn with
    | tmul a x => simp [θM, TensorProduct.map_tmul, magicF4MixedActLM_tmul, hθJ_act]
    | add _ _ h1 h2 => simp [map_add, h1, h2]
  have hmix_mix_g2 : ∀ m₁ m₂ : O₀ ⊗[ℝ] J₀,
      θG2 (magicMixedToG2LM O J m₁ m₂) = magicMixedToG2LM O J (θM m₁) (θM m₂) := fun m₁ m₂ => by
    induction m₁ using TensorProduct.inductionOn with
    | tmul a x =>
      induction m₂ using TensorProduct.inductionOn with
      | tmul b y =>
        simp [θM, TensorProduct.map_tmul, magicMixedToG2LM_tmul, map_smul, hθJ_bilin, hθO_inner]
      | add _ _ h1 h2 => simp [map_add, h1, h2]
    | add _ _ h1 h2 => simp [map_add, LinearMap.add_apply, h1, h2]
  have hmix_mix_mix : ∀ m₁ m₂ : O₀ ⊗[ℝ] J₀,
      θM (magicMixedToMixedLM O J m₁ m₂) =
        magicMixedToMixedLM O J (θM m₁) (θM m₂) := fun m₁ m₂ => by
    induction m₁ using TensorProduct.inductionOn with
    | tmul a x =>
      induction m₂ using TensorProduct.inductionOn with
      | tmul b y =>
        simp [θM, TensorProduct.map_tmul, magicMixedToMixedLM_tmul, hθO_comm, hθJ_mul]
      | add _ _ h1 h2 => simp [map_add, h1, h2]
    | add _ _ h1 h2 => simp [map_add, LinearMap.add_apply, h1, h2]
  have hmix_mix_f4 : ∀ m₁ m₂ : O₀ ⊗[ℝ] J₀,
      θF4 (magicMixedToF4LM O J m₁ m₂) = magicMixedToF4LM O J (θM m₁) (θM m₂) := fun m₁ m₂ => by
    induction m₁ using TensorProduct.inductionOn with
    | tmul a x =>
      induction m₂ using TensorProduct.inductionOn with
      | tmul b y =>
        simp [θM, TensorProduct.map_tmul, magicMixedToF4LM_tmul, map_smul, hθO_bilin, hθJ_inner]
      | add _ _ h1 h2 => simp [map_add, h1, h2]
    | add _ _ h1 h2 => simp [map_add, LinearMap.add_apply, h1, h2]
  { toFun := toFun
    invFun := toFun
    left_inv := fun X => by
      apply MagicSquareLie.ext
      · exact hθG2_inv X.g2
      · exact hθM_inv X.mixed
      · exact hθF4_inv X.f4
    right_inv := fun X => by
      apply MagicSquareLie.ext
      · exact hθG2_inv X.g2
      · exact hθM_inv X.mixed
      · exact hθF4_inv X.f4
    map_add' := fun X Y => by
      apply MagicSquareLie.ext
      · exact map_add θG2 _ _
      · exact map_add θM _ _
      · exact map_add θF4 _ _
    map_smul' := fun r X => by
      apply MagicSquareLie.ext
      · exact map_smul θG2 r _
      · exact map_smul θM r _
      · exact map_smul θF4 r _
    map_lie' := fun {X Y} => by
      apply MagicSquareLie.ext
      · change θG2 (⁅X.g2, Y.g2⁆ + magicMixedToG2LM O J X.mixed Y.mixed) =
          ⁅θG2 X.g2, θG2 Y.g2⁆ + magicMixedToG2LM O J (θM X.mixed) (θM Y.mixed)
        rw [map_add, LieEquiv.map_lie, hmix_mix_g2]
      · change θM (magicG2MixedActLM O X.g2 Y.mixed - magicG2MixedActLM O Y.g2 X.mixed +
            magicF4MixedActLM J X.f4 Y.mixed - magicF4MixedActLM J Y.f4 X.mixed +
            magicMixedToMixedLM O J X.mixed Y.mixed) =
          magicG2MixedActLM O (θG2 X.g2) (θM Y.mixed) -
            magicG2MixedActLM O (θG2 Y.g2) (θM X.mixed) +
            magicF4MixedActLM J (θF4 X.f4) (θM Y.mixed) -
            magicF4MixedActLM J (θF4 Y.f4) (θM X.mixed) +
            magicMixedToMixedLM O J (θM X.mixed) (θM Y.mixed)
        rw [map_add, map_sub, map_add, map_sub, hmixed_g2, hmixed_g2, hmixed_f4, hmixed_f4,
          hmix_mix_mix]
      · change θF4 (⁅X.f4, Y.f4⁆ + magicMixedToF4LM O J X.mixed Y.mixed) =
          ⁅θF4 X.f4, θF4 Y.f4⁆ + magicMixedToF4LM O J (θM X.mixed) (θM Y.mixed)
        rw [map_add, LieEquiv.map_lie, hmix_mix_f4] }

private theorem msCartanInvolution_trace {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [FiniteDimensional ℝ O₀]
    [LieRing G₂] [LieAlgebra ℝ G₂] [FiniteDimensional ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [FiniteDimensional ℝ J₀]
    [LieRing F₄] [LieAlgebra ℝ F₄] [FiniteDimensional ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (θG2 : G₂ ≃ₗ⁅ℝ⁆ G₂) (θO : O₀ →ₗ[ℝ] O₀) (θJ : J₀ →ₗ[ℝ] J₀) (θF4 : F₄ ≃ₗ⁅ℝ⁆ F₄)
    (hθG2_inv hθO_inv hθJ_inv hθF4_inv hθO_bilin hθO_comm hθO_act hθO_inner
      hθJ_bilin hθJ_mul hθJ_act hθJ_inner) :
    LinearMap.trace ℝ (MagicSquareLie O J)
        (msCartanInvolution O J θG2 θO θJ θF4 hθG2_inv hθO_inv hθJ_inv hθF4_inv
          hθO_bilin hθO_comm hθO_act hθO_inner hθJ_bilin hθJ_mul hθJ_act hθJ_inner).toLinearMap =
      LinearMap.trace ℝ G₂ θG2.toLinearMap +
        LinearMap.trace ℝ O₀ θO * LinearMap.trace ℝ J₀ θJ +
        LinearMap.trace ℝ F₄ θF4.toLinearMap := by
  let e := msLinearEquiv O J
  have hconj : e.conj (msCartanInvolution O J θG2 θO θJ θF4 hθG2_inv hθO_inv hθJ_inv hθF4_inv
      hθO_bilin hθO_comm hθO_act hθO_inner hθJ_bilin hθJ_mul hθJ_act hθJ_inner).toLinearMap =
      θG2.toLinearMap.prodMap ((TensorProduct.map θO θJ).prodMap θF4.toLinearMap) := by
    apply LinearMap.ext; rintro ⟨g, m, f⟩
    rfl
  rw [← LinearMap.trace_conj' _ e, hconj, LinearMap.trace_prodMap', LinearMap.trace_prodMap',
    LinearMap.trace_tensorProduct', add_assoc]

end GenericMSInvolution

section BlockPositivity

private theorem compactOct0_bilin_nonneg (a : CompactOctonionTraceZero) :
    0 ≤ compactOctonionDatum.bilin₀ a a := by
  change 0 ≤ CompactOctonion.bilin a.1 a.1
  rw [CompactOctonion.bilin_self]
  exact mul_nonneg (by norm_num) (CompactOctonion.norm_nonneg a.1)

private theorem compactOct0_bilin_eq_zero_iff (a : CompactOctonionTraceZero) :
    compactOctonionDatum.bilin₀ a a = 0 ↔ a = 0 := by
  change CompactOctonion.bilin a.1 a.1 = 0 ↔ a = 0
  rw [CompactOctonion.bilin_self]
  constructor
  · intro h
    have hn : CompactOctonion.norm a.1 = 0 := by linarith
    exact Subtype.ext ((CompactOctonion.norm_eq_zero_iff a.1).mp hn)
  · rintro rfl; simp

private theorem compactG2_neg_bilin_nonneg (D : CompactOctonionDerivations) :
    0 ≤ -compactOctonionDatum.g2Bilin D D := by
  change 0 ≤ -LinearMap.trace ℝ (CompactOctonion ℝ) (D.1 * D.1)
  exact neg_nonneg.mpr (compactG2_trace_sq_nonpos D)

private theorem compactG2_neg_bilin_eq_zero_iff (D : CompactOctonionDerivations) :
    -compactOctonionDatum.g2Bilin D D = 0 ↔ D = 0 := by
  change -LinearMap.trace ℝ (CompactOctonion ℝ) (D.1 * D.1) = 0 ↔ D = 0
  rw [neg_eq_zero]
  exact compactG2_trace_sq_eq_zero_iff D

private theorem h3Oct0_traceBilin_nonneg (x : h3OctonionTraceZero) :
    0 ≤ h3OctonionJordanDatum.traceBilin₀ x x :=
  H3Octonion.traceBilin_self_nonneg x.1

private theorem h3Oct0_traceBilin_eq_zero_iff (x : h3OctonionTraceZero) :
    h3OctonionJordanDatum.traceBilin₀ x x = 0 ↔ x = 0 := by
  change H3Octonion.traceBilin x.1 x.1 = 0 ↔ x = 0
  rw [H3Octonion.traceBilin_self_eq_zero_iff, Subtype.ext_iff]
  rfl

private def h3OctTraceBilinFullLM : H3Octonion ℝ →ₗ[ℝ] H3Octonion ℝ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ H3Octonion.traceBilin
    H3Octonion.traceBilin_add_left
    H3Octonion.traceBilin_smul_left
    H3Octonion.traceBilin_add_right
    H3Octonion.traceBilin_smul_right

private theorem h3OctF4_neg_bilin_nonneg (F : H3OctonionF4Derivations) :
    0 ≤ -h3OctonionJordanDatum.f4Bilin F F := by
  change 0 ≤ -LinearMap.trace ℝ (H3Octonion ℝ) (F.1 * F.1)
  have htr := trace_sq_nonpos_of_skew_ortho_gen h3OctTraceBilinFullLM
    H3Octonion.traceBilin_symm
    H3Octonion.traceBilin_self_nonneg
    H3Octonion.traceBilin_self_eq_zero_iff
    F.1
    (fun x y => h3Octonion_derivation_traceBilin_skew F x y)
  exact neg_nonneg.mpr htr.1

private theorem h3OctF4_neg_bilin_eq_zero_iff (F : H3OctonionF4Derivations) :
    -h3OctonionJordanDatum.f4Bilin F F = 0 ↔ F = 0 := by
  change -LinearMap.trace ℝ (H3Octonion ℝ) (F.1 * F.1) = 0 ↔ F = 0
  have htr := trace_sq_nonpos_of_skew_ortho_gen h3OctTraceBilinFullLM
    H3Octonion.traceBilin_symm
    H3Octonion.traceBilin_self_nonneg
    H3Octonion.traceBilin_self_eq_zero_iff
    F.1
    (fun x y => h3Octonion_derivation_traceBilin_skew F x y)
  constructor
  · intro h
    rw [neg_eq_zero] at h
    exact Subtype.ext (htr.2 h)
  · rintro rfl; simp

private theorem zorn_derivation_kills_one (D : G2DerivationCarrier) :
    D ZornVectorMatrix.one = 0 := by
  have h := D.map_mul ZornVectorMatrix.one ZornVectorMatrix.one
  change D (ZornVectorMatrix.mul ZornVectorMatrix.one ZornVectorMatrix.one) =
    ZornVectorMatrix.add (ZornVectorMatrix.mul (D ZornVectorMatrix.one) ZornVectorMatrix.one)
      (ZornVectorMatrix.mul ZornVectorMatrix.one (D ZornVectorMatrix.one)) at h
  rw [show ZornVectorMatrix.mul ZornVectorMatrix.one ZornVectorMatrix.one =
        ZornVectorMatrix.one from by
      apply ZornVectorMatrix.ext <;>
        simp [ZornVectorMatrix.one, ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross],
    show ZornVectorMatrix.mul (D ZornVectorMatrix.one) ZornVectorMatrix.one =
        D ZornVectorMatrix.one from by
      apply ZornVectorMatrix.ext <;>
        [simp [ZornVectorMatrix.one, ZornVectorMatrix.mul, ZornVec3.dot];
          (funext i; simp [ZornVectorMatrix.one, ZornVectorMatrix.mul, ZornVec3.cross]);
          (funext i; simp [ZornVectorMatrix.one, ZornVectorMatrix.mul, ZornVec3.cross]);
          simp [ZornVectorMatrix.one, ZornVectorMatrix.mul, ZornVec3.dot]],
    show ZornVectorMatrix.mul ZornVectorMatrix.one (D ZornVectorMatrix.one) =
        D ZornVectorMatrix.one from by
      apply ZornVectorMatrix.ext <;>
        [simp [ZornVectorMatrix.one, ZornVectorMatrix.mul, ZornVec3.dot];
          (funext i; simp [ZornVectorMatrix.one, ZornVectorMatrix.mul, ZornVec3.cross]);
          (funext i; simp [ZornVectorMatrix.one, ZornVectorMatrix.mul, ZornVec3.cross]);
          simp [ZornVectorMatrix.one, ZornVectorMatrix.mul, ZornVec3.dot]],
    show ZornVectorMatrix.add (D ZornVectorMatrix.one) (D ZornVectorMatrix.one) =
      D ZornVectorMatrix.one + D ZornVectorMatrix.one from rfl] at h
  have h0 : D ZornVectorMatrix.one + D ZornVectorMatrix.one = D ZornVectorMatrix.one := h.symm
  calc
    D ZornVectorMatrix.one
      = (D ZornVectorMatrix.one + D ZornVectorMatrix.one) - D ZornVectorMatrix.one :=
          (add_sub_cancel_right _ _).symm
    _ = D ZornVectorMatrix.one - D ZornVectorMatrix.one := by rw [h0]
    _ = 0 := sub_self _

private theorem zornBilin_deriv_skew_full (D : G2DerivationCarrier)
    (x y : ZornVectorMatrix ℝ) :
    zornBilin (D x) y + zornBilin x (D y) = 0 := by
  let rx : ℝ := ZornVectorMatrix.trace x / 2
  let ry : ℝ := ZornVectorMatrix.trace y / 2
  have hx0 : ZornVectorMatrix.trace (x - rx • ZornVectorMatrix.one) = 0 := by
    change (x + -(ZornVectorMatrix.smul rx ZornVectorMatrix.one)).a +
      (x + -(ZornVectorMatrix.smul rx ZornVectorMatrix.one)).b = 0
    change (x.a + -(rx * 1)) + (x.b + -(rx * 1)) = 0
    dsimp [rx, ZornVectorMatrix.trace]; ring
  have hy0 : ZornVectorMatrix.trace (y - ry • ZornVectorMatrix.one) = 0 := by
    change (y + -(ZornVectorMatrix.smul ry ZornVectorMatrix.one)).a +
      (y + -(ZornVectorMatrix.smul ry ZornVectorMatrix.one)).b = 0
    change (y.a + -(ry * 1)) + (y.b + -(ry * 1)) = 0
    dsimp [ry, ZornVectorMatrix.trace]; ring
  let x0 : splitOctonionTraceZero := ⟨x - rx • ZornVectorMatrix.one, hx0⟩
  let y0 : splitOctonionTraceZero := ⟨y - ry • ZornVectorMatrix.one, hy0⟩
  have hx : x = x0.1 + rx • ZornVectorMatrix.one :=
    (sub_add_cancel x (rx • ZornVectorMatrix.one)).symm
  have hy : y = y0.1 + ry • ZornVectorMatrix.one :=
    (sub_add_cancel y (ry • ZornVectorMatrix.one)).symm
  let DL : ZornVectorMatrix ℝ →ₗ[ℝ] ZornVectorMatrix ℝ :=
    { toFun := fun w => D w
      map_add' := fun a b => D.map_add a b
      map_smul' := fun r a => D.map_smul r a }
  have hDL : ∀ w, D w = DL w := fun _ => rfl
  have h1D : ∀ z : ZornVectorMatrix ℝ, zornBilin ZornVectorMatrix.one (DL z) = 0 := by
    intro z
    have hz : ZornVectorMatrix.trace (DL z) = 0 :=
      InfoGeometry.Lie.SplitDerivationCoordinates.every_derivation_trace_zero D z
    simp only [zornBilin, ZornVectorMatrix.one, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVec3.dot, zero_mul, Finset.sum_const_zero, one_mul,
      add_zero, zero_add] at hz ⊢
    have hz' : (DL z).a + (DL z).b = 0 := hz
    linarith
  have hD1 : ∀ z : ZornVectorMatrix ℝ, zornBilin (DL ZornVectorMatrix.one) z = 0 := by
    intro z; change zornBilin (D ZornVectorMatrix.one) z = 0
    rw [zorn_derivation_kills_one D]; simp [zornBilin]
  have hsk0 : zornBilin (DL x0.1) y0.1 + zornBilin x0.1 (DL y0.1) = 0 :=
    MagicSquareTitsBracket.zornBilin_deriv_skew D x0 y0
  simp only [hDL]
  rw [hx, hy]
  simp only [map_add, map_smul, zornBilin_add_left, zornBilin_add_right,
    zornBilin_smul_left, zornBilin_smul_right, hD1, h1D, mul_zero, add_zero]
  have hsym1 : zornBilin (DL x0.1) ZornVectorMatrix.one = 0 := by
    rw [zornBilin_symm, h1D x0.1]
  have hsym2 : zornBilin x0.1 (DL ZornVectorMatrix.one) = 0 := by
    rw [zornBilin_symm]; exact hD1 x0.1
  simp only [hsym1, hsym2, mul_zero, add_zero]
  exact hsk0

private def zornSigmaInnerLM : ZornVectorMatrix ℝ →ₗ[ℝ] ZornVectorMatrix ℝ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => zornBilin x (sigmaO y))
    (fun x₁ x₂ y => zornBilin_add_left x₁ x₂ (sigmaO y))
    (fun r x y => zornBilin_smul_left r x (sigmaO y))
    (fun x y₁ y₂ => by simp only [map_add, zornBilin_add_right])
    (fun r x y => by simp only [map_smul, zornBilin_smul_right, smul_eq_mul])

private theorem zornG2_sigma_neg_bilin_nonneg (D : G2DerivationCarrier) :
    0 ≤ -splitOctonionDatum.g2Bilin D (sigmaOG2 D) := by
  let DL : Module.End ℝ (ZornVectorMatrix ℝ) := (vDerEquivZornDerivations D).1
  let DSL : Module.End ℝ (ZornVectorMatrix ℝ) := (vDerEquivZornDerivations (sigmaOG2 D)).1
  change 0 ≤ -LinearMap.trace ℝ (ZornVectorMatrix ℝ) (DL * DSL)
  rw [← map_neg, ← mul_neg]
  have hadj : ∀ x y : ZornVectorMatrix ℝ,
      zornSigmaInnerLM (DL x) y = zornSigmaInnerLM x ((-DSL) y) := by
    intro x y
    change zornBilin (D x) (sigmaO y) = zornBilin x (sigmaO (-(sigmaO (D (sigmaO y)))))
    rw [map_neg, sigmaO_involutive]
    have hsk := zornBilin_deriv_skew_full D x (sigmaO y)
    rw [zornBilin_neg_right]
    linarith
  exact (trace_mul_adjoint_nonneg_gen zornSigmaInnerLM
    zornBilin_sigmaO_symm zornBilin_sigmaO_nonneg zornBilin_sigmaO_eq_zero_iff
    DL (-DSL) hadj).1

private theorem zornG2_sigma_neg_bilin_eq_zero_iff (D : G2DerivationCarrier) :
    -splitOctonionDatum.g2Bilin D (sigmaOG2 D) = 0 ↔ D = 0 := by
  let DL : Module.End ℝ (ZornVectorMatrix ℝ) := (vDerEquivZornDerivations D).1
  let DSL : Module.End ℝ (ZornVectorMatrix ℝ) := (vDerEquivZornDerivations (sigmaOG2 D)).1
  change -LinearMap.trace ℝ (ZornVectorMatrix ℝ) (DL * DSL) = 0 ↔ D = 0
  rw [← map_neg, ← mul_neg]
  have hadj : ∀ x y : ZornVectorMatrix ℝ,
      zornSigmaInnerLM (DL x) y = zornSigmaInnerLM x ((-DSL) y) := by
    intro x y
    change zornBilin (D x) (sigmaO y) = zornBilin x (sigmaO (-(sigmaO (D (sigmaO y)))))
    rw [map_neg, sigmaO_involutive]
    have hsk := zornBilin_deriv_skew_full D x (sigmaO y)
    rw [zornBilin_neg_right]
    linarith
  have htr := trace_mul_adjoint_nonneg_gen zornSigmaInnerLM
    zornBilin_sigmaO_symm zornBilin_sigmaO_nonneg zornBilin_sigmaO_eq_zero_iff
    DL (-DSL) hadj
  constructor
  · intro hz
    have hneg0 : -DSL = 0 := htr.2 hz
    have hsig0 : DSL = 0 := neg_eq_zero.mp hneg0
    have hD_sig : sigmaOG2 D = 0 := by
      apply ZornVectorMatrix.Derivation.ext; intro x
      exact LinearMap.ext_iff.mp hsig0 x
    have := congrArg sigmaOG2 hD_sig
    simpa [sigmaOG2_involutive] using this
  · rintro rfl; dsimp [DL, DSL]; simp

private def h3ZornSigmaInnerLM : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => H3Zorn.traceBilin x (sigmaJ y))
    (fun x₁ x₂ y => H3Zorn.traceBilin_add_left x₁ x₂ (sigmaJ y))
    (fun r x y => H3Zorn.traceBilin_smul_left r x (sigmaJ y))
    (fun x y₁ y₂ => by simp only [map_add, H3Zorn.traceBilin_add_right])
    (fun r x y => by simp only [map_smul, H3Zorn.traceBilin_smul_right, smul_eq_mul])

private theorem zornF4_sigma_neg_bilin_nonneg (F : F4DerivationCarrier) :
    0 ≤ -h3ZornJordanDatum.f4Bilin F (sigmaJF4 F) := by
  change 0 ≤ -LinearMap.trace ℝ (H3Zorn ℝ) (F.1 * (sigmaJF4 F).1)
  rw [← map_neg, ← mul_neg]
  have hadj : ∀ x y : H3Zorn ℝ,
      h3ZornSigmaInnerLM (F.1 x) y = h3ZornSigmaInnerLM x ((-(sigmaJF4 F).1) y) := by
    intro x y
    change H3Zorn.traceBilin (F.1 x) (sigmaJ y) =
      H3Zorn.traceBilin x (sigmaJ (-(sigmaJ (F.1 (sigmaJ y)))))
    rw [map_neg, sigmaJ_involutive, ← neg_one_smul ℝ, H3Zorn.traceBilin_smul_right]
    have hsk := h3ZornF4_derivation_traceBilin_skew F x (sigmaJ y)
    linarith
  exact (trace_mul_adjoint_nonneg_gen h3ZornSigmaInnerLM
    sigmaJ_traceBilin_symm sigmaJ_traceBilin_nonneg sigmaJ_traceBilin_eq_zero_iff
    F.1 (-(sigmaJF4 F).1) hadj).1

private theorem zornF4_sigma_neg_bilin_eq_zero_iff (F : F4DerivationCarrier) :
    -h3ZornJordanDatum.f4Bilin F (sigmaJF4 F) = 0 ↔ F = 0 := by
  change -LinearMap.trace ℝ (H3Zorn ℝ) (F.1 * (sigmaJF4 F).1) = 0 ↔ F = 0
  rw [← map_neg, ← mul_neg]
  have hadj : ∀ x y : H3Zorn ℝ,
      h3ZornSigmaInnerLM (F.1 x) y = h3ZornSigmaInnerLM x ((-(sigmaJF4 F).1) y) := by
    intro x y
    change H3Zorn.traceBilin (F.1 x) (sigmaJ y) =
      H3Zorn.traceBilin x (sigmaJ (-(sigmaJ (F.1 (sigmaJ y)))))
    rw [map_neg, sigmaJ_involutive, ← neg_one_smul ℝ, H3Zorn.traceBilin_smul_right]
    have hsk := h3ZornF4_derivation_traceBilin_skew F x (sigmaJ y)
    linarith
  have htr := trace_mul_adjoint_nonneg_gen h3ZornSigmaInnerLM
    sigmaJ_traceBilin_symm sigmaJ_traceBilin_nonneg sigmaJ_traceBilin_eq_zero_iff
    F.1 (-(sigmaJF4 F).1) hadj
  constructor
  · intro hz
    have hneg0 : -(sigmaJF4 F).1 = 0 := htr.2 hz
    have hsig0 : (sigmaJF4 F).1 = 0 := neg_eq_zero.mp hneg0
    have hF_sig : sigmaJF4 F = 0 := Subtype.ext hsig0
    have := congrArg sigmaJF4 hF_sig
    simpa [sigmaJF4_involutive] using this
  · rintro rfl; simp

end BlockPositivity

section CompactE8Cartan

/-- Cartan involution on `CompactE8Lie` (`𝔈₈(-248)`), namely the identity `LieEquiv.refl`. -/
def compactE8CartanInvolution : CompactE8Lie ≃ₗ⁅ℝ⁆ CompactE8Lie :=
  LieEquiv.refl

def compactE8CartanCompact : Submodule ℝ CompactE8Lie :=
  LinearMap.ker (compactE8CartanInvolution.toLinearMap - LinearMap.id)

def compactE8CartanNoncompact : Submodule ℝ CompactE8Lie :=
  LinearMap.ker (compactE8CartanInvolution.toLinearMap + LinearMap.id)

theorem compactE8CartanCompact_eq_top : compactE8CartanCompact = ⊤ := by
  rw [compactE8CartanCompact]
  ext X
  simp [compactE8CartanInvolution]

theorem compactE8CartanNoncompact_eq_bot : compactE8CartanNoncompact = ⊥ := by
  rw [compactE8CartanNoncompact]
  ext X
  simp only [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, Submodule.mem_bot]
  change compactE8CartanInvolution X + X = 0 ↔ X = 0
  change X + X = 0 ↔ X = 0
  constructor
  · intro h
    have h2 : (2 : ℝ) • X = 0 := by rw [two_smul]; exact h
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  · rintro rfl; simp

theorem finrank_compactE8CartanCompact :
    Module.finrank ℝ compactE8CartanCompact = 248 := by
  rw [compactE8CartanCompact_eq_top, finrank_top, finrank_compactE8Lie]

theorem finrank_compactE8CartanNoncompact :
    Module.finrank ℝ compactE8CartanNoncompact = 0 := by
  rw [compactE8CartanNoncompact_eq_bot, finrank_bot]

/-- Cartan signature of `CompactE8Lie` (`𝔈₈(-248)`): `dim p - dim k = 0 - 248 = -248`. -/
theorem compactE8_signature_eq_neg_248 :
    (Module.finrank ℝ compactE8CartanNoncompact : ℤ) -
      Module.finrank ℝ compactE8CartanCompact = -248 := by
  rw [finrank_compactE8CartanNoncompact, finrank_compactE8CartanCompact]
  norm_num

private def compactE8CartanInner : CompactE8Lie →ₗ[ℝ] CompactE8Lie →ₗ[ℝ] ℝ :=
  -(magicInvBilin compactOctonionDatum h3OctonionJordanDatum)

private theorem compactE8CartanInner_symm (X Y : CompactE8Lie) :
    compactE8CartanInner X Y = compactE8CartanInner Y X := by
  simp only [compactE8CartanInner, LinearMap.neg_apply, neg_inj]
  exact magicInvBilin_symm X Y

private theorem compactE8CartanInner_posDef :
    (∀ X, 0 ≤ compactE8CartanInner X X) ∧
      (∀ X, compactE8CartanInner X X = 0 ↔ X = 0) := by
  let Bmix : (CompactOctonionTraceZero ⊗[ℝ] h3OctonionTraceZero) →ₗ[ℝ]
      (CompactOctonionTraceZero ⊗[ℝ] h3OctonionTraceZero) →ₗ[ℝ] ℝ :=
    magicMixedBilin compactOctonionDatum h3OctonionJordanDatum
  have hmix_pd := tensorProduct_bilin_posDef
    compactOctonionDatum.bilin₀
    compactOctonionDatum.bilin_symm
    compactOct0_bilin_nonneg
    compactOct0_bilin_eq_zero_iff
    h3OctonionJordanDatum.traceBilin₀
    h3OctonionJordanDatum.traceBilin_symm
    h3Oct0_traceBilin_nonneg
    h3Oct0_traceBilin_eq_zero_iff
    Bmix
    (fun _ _ _ _ => rfl)
  have hval : ∀ X : CompactE8Lie, compactE8CartanInner X X =
      3 * (-compactOctonionDatum.g2Bilin X.g2 X.g2) +
        6 * Bmix X.mixed X.mixed +
        (-h3OctonionJordanDatum.f4Bilin X.f4 X.f4) := by
    intro X
    change -(3 * compactOctonionDatum.g2Bilin X.g2 X.g2 -
      6 * Bmix X.mixed X.mixed + h3OctonionJordanDatum.f4Bilin X.f4 X.f4) = _
    ring
  refine ⟨fun X => ?_, fun X => ?_⟩
  · rw [hval]
    have hg := compactG2_neg_bilin_nonneg X.g2
    have hm := hmix_pd.1 X.mixed
    have hf := h3OctF4_neg_bilin_nonneg X.f4
    linarith
  · constructor
    · intro h
      rw [hval] at h
      have hg := compactG2_neg_bilin_nonneg X.g2
      have hm := hmix_pd.1 X.mixed
      have hf := h3OctF4_neg_bilin_nonneg X.f4
      have hg0 : -compactOctonionDatum.g2Bilin X.g2 X.g2 = 0 := by linarith
      have hm0 : Bmix X.mixed X.mixed = 0 := by linarith
      have hf0 : -h3OctonionJordanDatum.f4Bilin X.f4 X.f4 = 0 := by linarith
      apply MagicSquareLie.ext
      · exact (compactG2_neg_bilin_eq_zero_iff X.g2).mp hg0
      · exact (hmix_pd.2 X.mixed).mp hm0
      · exact (h3OctF4_neg_bilin_eq_zero_iff X.f4).mp hf0
    · rintro rfl; simp

/-- Negative semi-definiteness of the Killing form on `CompactE8Lie` (`𝔈₈(-248)`). -/
theorem compactE8_killingForm_nonpos (X : CompactE8Lie) :
    killingForm ℝ CompactE8Lie X X ≤ 0 := by
  rw [killingForm_apply_apply]
  refine (trace_sq_nonpos_of_skew_ortho_gen compactE8CartanInner
    compactE8CartanInner_symm compactE8CartanInner_posDef.1 compactE8CartanInner_posDef.2
    (LieAlgebra.ad ℝ CompactE8Lie X) (fun Y Z => ?_)).1
  simp only [compactE8CartanInner, LinearMap.neg_apply, LieAlgebra.ad_apply]
  have hinv := magicInvBilin_lieInvariant X Y Z
  linarith

/-- Strict negative definiteness of the Killing form on `CompactE8Lie` (`𝔈₈(-248)`). -/
theorem compactE8_killingForm_eq_zero_iff (X : CompactE8Lie) :
    killingForm ℝ CompactE8Lie X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [killingForm_apply_apply] at h
    have had0 := (trace_sq_nonpos_of_skew_ortho_gen compactE8CartanInner
      compactE8CartanInner_symm compactE8CartanInner_posDef.1 compactE8CartanInner_posDef.2
      (LieAlgebra.ad ℝ CompactE8Lie X) (fun Y Z => by
        simp only [compactE8CartanInner, LinearMap.neg_apply, LieAlgebra.ad_apply]
        have hinv := magicInvBilin_lieInvariant X Y Z
        linarith)).2 h
    exact (ad_eq_zero_iff_of_isSimple CompactE8Lie X).mp had0
  · rintro rfl; simp

/-- `CompactE8Lie` (`𝔈₈(-248)`) has non-degenerate Killing form (`IsKilling ℝ`). -/
instance compactE8Lie_isKilling : LieAlgebra.IsKilling ℝ CompactE8Lie := by
  constructor
  rw [eq_bot_iff]
  intro Z hZ
  rw [LieSubmodule.mem_bot]
  have hZker : ∀ W : CompactE8Lie, killingForm ℝ CompactE8Lie W Z = 0 := fun W =>
    (LieIdeal.mem_killingCompl ℝ CompactE8Lie ⊤).mp hZ W (LieSubmodule.mem_top W)
  exact (compactE8_killingForm_eq_zero_iff Z).mp (hZker Z)

end CompactE8Cartan

section QuaternionicE8Cartan

/-- Cartan involution `(id_{G₂}, id ⊗ σ_J0, σ_{F₄})` on `QuaternionicE8Lie` (`𝔈₈(-24)`). -/
def quaternionicE8CartanInvolution : QuaternionicE8Lie ≃ₗ⁅ℝ⁆ QuaternionicE8Lie :=
  msCartanInvolution compactOctonionDatum h3ZornJordanDatum
    LieEquiv.refl LinearMap.id sigmaJ0 sigmaJF4
    (fun _ => rfl) (fun _ => rfl) sigmaJ0_involutive sigmaJF4_involutive
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun x y => sigmaJ_traceBilin_preserves x.1 y.1)
    sigmaJ0_mul0
    sigmaJ0_act
    sigmaJF4_inner

@[simp] theorem quaternionicE8CartanInvolution_involutive (X : QuaternionicE8Lie) :
    quaternionicE8CartanInvolution (quaternionicE8CartanInvolution X) = X :=
  quaternionicE8CartanInvolution.left_inv X

def quaternionicE8CartanCompact : Submodule ℝ QuaternionicE8Lie :=
  LinearMap.ker (quaternionicE8CartanInvolution.toLinearMap - LinearMap.id)

def quaternionicE8CartanNoncompact : Submodule ℝ QuaternionicE8Lie :=
  LinearMap.ker (quaternionicE8CartanInvolution.toLinearMap + LinearMap.id)

theorem quaternionicE8CartanInvolution_trace :
    LinearMap.trace ℝ QuaternionicE8Lie quaternionicE8CartanInvolution.toLinearMap = 24 := by
  have htr := msCartanInvolution_trace compactOctonionDatum h3ZornJordanDatum
    LieEquiv.refl LinearMap.id sigmaJ0 sigmaJF4
    (fun _ => rfl) (fun _ => rfl) sigmaJ0_involutive sigmaJF4_involutive
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun x y => sigmaJ_traceBilin_preserves x.1 y.1)
    sigmaJ0_mul0 sigmaJ0_act sigmaJF4_inner
  change LinearMap.trace ℝ QuaternionicE8Lie
      (msCartanInvolution compactOctonionDatum h3ZornJordanDatum
        LieEquiv.refl LinearMap.id sigmaJ0 sigmaJF4
        (fun _ => rfl) (fun _ => rfl) sigmaJ0_involutive sigmaJF4_involutive
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun x y => sigmaJ_traceBilin_preserves x.1 y.1)
        sigmaJ0_mul0 sigmaJ0_act sigmaJF4_inner).toLinearMap = 24
  rw [htr]
  change LinearMap.trace ℝ CompactOctonionDerivations (LieEquiv.refl : CompactOctonionDerivations ≃ₗ⁅ℝ⁆ CompactOctonionDerivations).toLinearMap +
      LinearMap.trace ℝ CompactOctonionTraceZero LinearMap.id *
        LinearMap.trace ℝ h3TraceZero sigmaJ0 +
      LinearMap.trace ℝ F4DerivationCarrier sigmaJF4.toLinearMap = 24
  have hid : (LieEquiv.refl :
      CompactOctonionDerivations ≃ₗ⁅ℝ⁆ CompactOctonionDerivations).toLinearMap =
      LinearMap.id := rfl
  rw [hid, LinearMap.trace_id, LinearMap.trace_id, finrank_compactOctonionDerivations,
    finrank_compactOctonionTraceZero, sigmaJ0_trace, sigmaJF4_trace]
  norm_num

theorem finrank_quaternionicE8CartanCompact :
    Module.finrank ℝ quaternionicE8CartanCompact = 136 := by
  have htr := involution_trace_eq quaternionicE8CartanInvolution.toLinearMap
    quaternionicE8CartanInvolution_involutive
  rw [quaternionicE8CartanInvolution_trace, finrank_quaternionicE8Lie] at htr
  norm_num at htr
  change (24 : ℝ) = 2 * (Module.finrank ℝ quaternionicE8CartanCompact : ℝ) - 248 at htr
  have hk : (Module.finrank ℝ quaternionicE8CartanCompact : ℝ) = 136 := by linarith
  exact_mod_cast hk

theorem finrank_quaternionicE8CartanNoncompact :
    Module.finrank ℝ quaternionicE8CartanNoncompact = 112 := by
  have hsum := involution_finrank_add quaternionicE8CartanInvolution.toLinearMap
    quaternionicE8CartanInvolution_involutive
  have hk := finrank_quaternionicE8CartanCompact
  change Module.finrank ℝ quaternionicE8CartanCompact +
      Module.finrank ℝ quaternionicE8CartanNoncompact = Module.finrank ℝ QuaternionicE8Lie at hsum
  rw [hk, finrank_quaternionicE8Lie] at hsum
  omega

/-- Cartan signature of `QuaternionicE8Lie` (`𝔈₈(-24)`): `dim p - dim k = 112 - 136 = -24`. -/
theorem quaternionicE8_signature_eq_neg_24 :
    (Module.finrank ℝ quaternionicE8CartanNoncompact : ℤ) -
      Module.finrank ℝ quaternionicE8CartanCompact = -24 := by
  rw [finrank_quaternionicE8CartanNoncompact, finrank_quaternionicE8CartanCompact]
  norm_num

private def quaternionicE8CartanInner : QuaternionicE8Lie →ₗ[ℝ] QuaternionicE8Lie →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun X Y => -magicInvBilin compactOctonionDatum h3ZornJordanDatum
      X (quaternionicE8CartanInvolution Y))
    (fun X₁ X₂ Y => by
      simp only [map_add, LinearMap.add_apply, neg_add])
    (fun r X Y => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_neg])
    (fun X Y₁ Y₂ => by
      simp only [map_add, neg_add])
    (fun r X Y => by
      simp only [map_smul, smul_eq_mul, mul_neg])

private theorem quaternionicE8CartanInvolution_preserves_invBilin
    (X Y : QuaternionicE8Lie) :
    magicInvBilin compactOctonionDatum h3ZornJordanDatum
        (quaternionicE8CartanInvolution X) (quaternionicE8CartanInvolution Y) =
      magicInvBilin compactOctonionDatum h3ZornJordanDatum X Y := by
  have hmix : ∀ m₁ m₂ : CompactOctonionTraceZero ⊗[ℝ] h3TraceZero,
      magicMixedBilin compactOctonionDatum h3ZornJordanDatum
          (TensorProduct.map LinearMap.id sigmaJ0 m₁)
          (TensorProduct.map LinearMap.id sigmaJ0 m₂) =
        magicMixedBilin compactOctonionDatum h3ZornJordanDatum m₁ m₂ := by
    intro m₁ m₂
    induction m₁ using TensorProduct.inductionOn with
    | tmul a x =>
      induction m₂ using TensorProduct.inductionOn with
      | tmul b y =>
        simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, magicMixedBilin_tmul]
        change CompactOctonion.bilin a.1 b.1 * H3Zorn.traceBilin (sigmaJ x.1) (sigmaJ y.1) =
          CompactOctonion.bilin a.1 b.1 * H3Zorn.traceBilin x.1 y.1
        rw [sigmaJ_traceBilin_preserves]
      | add _ _ h1 h2 =>
        simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq] at h1 h2
        simp [map_add, h1, h2]
    | add _ _ h1 h2 => simp [map_add, LinearMap.add_apply, h1, h2]
  have hf4 : ∀ F₁ F₂ : F4DerivationCarrier,
      h3ZornJordanDatum.f4Bilin (sigmaJF4 F₁) (sigmaJF4 F₂) =
        h3ZornJordanDatum.f4Bilin F₁ F₂ := by
    intro F₁ F₂
    change LinearMap.trace ℝ (H3Zorn ℝ) ((sigmaJF4 F₁).1 * (sigmaJF4 F₂).1) =
      LinearMap.trace ℝ (H3Zorn ℝ) (F₁.1 * F₂.1)
    have hconj : ∀ F : F4DerivationCarrier,
        (sigmaJF4 F).1 = sigmaJ * F.1 * sigmaJ := fun _ => rfl
    rw [hconj F₁, hconj F₂]
    have hs2 : sigmaJ * sigmaJ = (1 : Module.End ℝ (H3Zorn ℝ)) := by
      apply LinearMap.ext; intro x; simp
    calc
      LinearMap.trace ℝ (H3Zorn ℝ) ((sigmaJ * F₁.1 * sigmaJ) * (sigmaJ * F₂.1 * sigmaJ))
        = LinearMap.trace ℝ (H3Zorn ℝ) (sigmaJ * F₁.1 * (sigmaJ * sigmaJ) * F₂.1 * sigmaJ) := by
            simp only [mul_assoc]
      _ = LinearMap.trace ℝ (H3Zorn ℝ) (sigmaJ * (F₁.1 * F₂.1) * sigmaJ) := by
            rw [hs2, mul_one]; simp only [mul_assoc]
      _ = LinearMap.trace ℝ (H3Zorn ℝ) ((F₁.1 * F₂.1) * (sigmaJ * sigmaJ)) := by
            rw [mul_assoc sigmaJ (F₁.1 * F₂.1) sigmaJ, LinearMap.trace_mul_comm]
            simp only [mul_assoc]
      _ = LinearMap.trace ℝ (H3Zorn ℝ) (F₁.1 * F₂.1) := by rw [hs2, mul_one]
  change 3 * compactOctonionDatum.g2Bilin X.g2 Y.g2 -
      6 * magicMixedBilin compactOctonionDatum h3ZornJordanDatum
        (TensorProduct.map LinearMap.id sigmaJ0 X.mixed)
        (TensorProduct.map LinearMap.id sigmaJ0 Y.mixed) +
      h3ZornJordanDatum.f4Bilin (sigmaJF4 X.f4) (sigmaJF4 Y.f4) =
    3 * compactOctonionDatum.g2Bilin X.g2 Y.g2 -
      6 * magicMixedBilin compactOctonionDatum h3ZornJordanDatum X.mixed Y.mixed +
      h3ZornJordanDatum.f4Bilin X.f4 Y.f4
  rw [hmix, hf4]

private theorem quaternionicE8CartanInner_symm (X Y : QuaternionicE8Lie) :
    quaternionicE8CartanInner X Y = quaternionicE8CartanInner Y X := by
  change -magicInvBilin compactOctonionDatum h3ZornJordanDatum X (quaternionicE8CartanInvolution Y) =
    -magicInvBilin compactOctonionDatum h3ZornJordanDatum Y (quaternionicE8CartanInvolution X)
  rw [← quaternionicE8CartanInvolution_preserves_invBilin X (quaternionicE8CartanInvolution Y),
    quaternionicE8CartanInvolution_involutive, magicInvBilin_symm]

private theorem quaternionicE8CartanInner_posDef :
    (∀ X, 0 ≤ quaternionicE8CartanInner X X) ∧
      (∀ X, quaternionicE8CartanInner X X = 0 ↔ X = 0) := by
  let Bmix : (CompactOctonionTraceZero ⊗[ℝ] h3TraceZero) →ₗ[ℝ]
      (CompactOctonionTraceZero ⊗[ℝ] h3TraceZero) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun m₁ m₂ => magicMixedBilin compactOctonionDatum h3ZornJordanDatum m₁
        (TensorProduct.map LinearMap.id sigmaJ0 m₂))
      (fun _ _ _ => by simp only [map_add, LinearMap.add_apply])
      (fun _ _ _ => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
      (fun _ _ _ => by simp only [map_add])
      (fun _ _ _ => by simp only [map_smul, smul_eq_mul])
  let BJ0 : h3TraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => h3ZornJordanDatum.traceBilin₀ x (sigmaJ0 y))
      (fun _ _ _ => by simp only [map_add, LinearMap.add_apply])
      (fun _ _ _ => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
      (fun _ _ _ => by simp only [map_add])
      (fun _ _ _ => by simp only [map_smul, smul_eq_mul])
  have hmix_pd := tensorProduct_bilin_posDef
    compactOctonionDatum.bilin₀
    compactOctonionDatum.bilin_symm
    compactOct0_bilin_nonneg
    compactOct0_bilin_eq_zero_iff
    BJ0
    (fun x y => sigmaJ_traceBilin_symm x.1 y.1)
    (fun x => sigmaJ_traceBilin_nonneg x.1)
    (fun x => by
      change H3Zorn.traceBilin x.1 (sigmaJ x.1) = 0 ↔ x = 0
      rw [sigmaJ_traceBilin_eq_zero_iff, Subtype.ext_iff]; rfl)
    Bmix
    (fun a₁ a₂ x₁ x₂ => by
      change magicMixedBilin compactOctonionDatum h3ZornJordanDatum
          (a₁ ⊗ₜ[ℝ] x₁) (LinearMap.id a₂ ⊗ₜ[ℝ] sigmaJ0 x₂) =
        compactOctonionDatum.bilin₀ a₁ a₂ * BJ0 x₁ x₂
      rw [magicMixedBilin_tmul]; rfl)
  have hval : ∀ X : QuaternionicE8Lie, quaternionicE8CartanInner X X =
      3 * (-compactOctonionDatum.g2Bilin X.g2 X.g2) +
        6 * Bmix X.mixed X.mixed +
        (-h3ZornJordanDatum.f4Bilin X.f4 (sigmaJF4 X.f4)) := by
    intro X
    change -magicInvBilin compactOctonionDatum h3ZornJordanDatum X
        (quaternionicE8CartanInvolution X) = _
    have hg : (quaternionicE8CartanInvolution X).g2 = X.g2 := rfl
    have hm : (quaternionicE8CartanInvolution X).mixed =
        TensorProduct.map LinearMap.id sigmaJ0 X.mixed := rfl
    have hf : (quaternionicE8CartanInvolution X).f4 = sigmaJF4 X.f4 := rfl
    change -(3 * compactOctonionDatum.g2Bilin X.g2 (quaternionicE8CartanInvolution X).g2 -
      6 * magicMixedBilin compactOctonionDatum h3ZornJordanDatum X.mixed
        (quaternionicE8CartanInvolution X).mixed +
      h3ZornJordanDatum.f4Bilin X.f4 (quaternionicE8CartanInvolution X).f4) = _
    rw [hg, hm, hf]
    change -(3 * compactOctonionDatum.g2Bilin X.g2 X.g2 -
      6 * Bmix X.mixed X.mixed + h3ZornJordanDatum.f4Bilin X.f4 (sigmaJF4 X.f4)) = _
    ring
  refine ⟨fun X => ?_, fun X => ?_⟩
  · rw [hval]
    have hg := compactG2_neg_bilin_nonneg X.g2
    have hm := hmix_pd.1 X.mixed
    have hf := zornF4_sigma_neg_bilin_nonneg X.f4
    linarith
  · constructor
    · intro h
      rw [hval] at h
      have hg := compactG2_neg_bilin_nonneg X.g2
      have hm := hmix_pd.1 X.mixed
      have hf := zornF4_sigma_neg_bilin_nonneg X.f4
      have hg0 : -compactOctonionDatum.g2Bilin X.g2 X.g2 = 0 := by linarith
      have hm0 : Bmix X.mixed X.mixed = 0 := by linarith
      have hf0 : -h3ZornJordanDatum.f4Bilin X.f4 (sigmaJF4 X.f4) = 0 := by linarith
      apply MagicSquareLie.ext
      · exact (compactG2_neg_bilin_eq_zero_iff X.g2).mp hg0
      · exact (hmix_pd.2 X.mixed).mp hm0
      · exact (zornF4_sigma_neg_bilin_eq_zero_iff X.f4).mp hf0
    · rintro rfl; simp

private theorem quaternionicE8CartanInner_ad_skew {X : QuaternionicE8Lie}
    (hX : X ∈ quaternionicE8CartanCompact) (Y Z : QuaternionicE8Lie) :
    quaternionicE8CartanInner (LieAlgebra.ad ℝ QuaternionicE8Lie X Y) Z +
      quaternionicE8CartanInner Y (LieAlgebra.ad ℝ QuaternionicE8Lie X Z) = 0 := by
  have hθ : quaternionicE8CartanInvolution X = X := by
    simpa [quaternionicE8CartanCompact, sub_eq_zero] using hX
  change -magicInvBilin compactOctonionDatum h3ZornJordanDatum ⁅X, Y⁆
      (quaternionicE8CartanInvolution Z) +
    (-magicInvBilin compactOctonionDatum h3ZornJordanDatum Y
      (quaternionicE8CartanInvolution ⁅X, Z⁆)) = 0
  rw [LieEquiv.map_lie, hθ]
  have hinv := magicInvBilin_lieInvariant X Y (quaternionicE8CartanInvolution Z)
  linarith

private theorem quaternionicE8CartanInner_ad_self {X : QuaternionicE8Lie}
    (hX : X ∈ quaternionicE8CartanNoncompact) (Y Z : QuaternionicE8Lie) :
    quaternionicE8CartanInner (LieAlgebra.ad ℝ QuaternionicE8Lie X Y) Z =
      quaternionicE8CartanInner Y (LieAlgebra.ad ℝ QuaternionicE8Lie X Z) := by
  have hθ : quaternionicE8CartanInvolution X = -X := by
    simpa [quaternionicE8CartanNoncompact, add_eq_zero_iff_eq_neg] using hX
  change -magicInvBilin compactOctonionDatum h3ZornJordanDatum ⁅X, Y⁆
      (quaternionicE8CartanInvolution Z) =
    -magicInvBilin compactOctonionDatum h3ZornJordanDatum Y
      (quaternionicE8CartanInvolution ⁅X, Z⁆)
  rw [LieEquiv.map_lie, hθ, neg_lie, map_neg]
  have hinv := magicInvBilin_lieInvariant X Y (quaternionicE8CartanInvolution Z)
  linarith

theorem quaternionicE8_killingForm_k_nonpos {X : QuaternionicE8Lie}
    (hX : X ∈ quaternionicE8CartanCompact) :
    killingForm ℝ QuaternionicE8Lie X X ≤ 0 := by
  rw [killingForm_apply_apply]
  exact (trace_sq_nonpos_of_skew_ortho_gen quaternionicE8CartanInner
    quaternionicE8CartanInner_symm quaternionicE8CartanInner_posDef.1
    quaternionicE8CartanInner_posDef.2 (LieAlgebra.ad ℝ QuaternionicE8Lie X)
    (quaternionicE8CartanInner_ad_skew hX)).1

theorem quaternionicE8_killingForm_k_eq_zero_iff {X : QuaternionicE8Lie}
    (hX : X ∈ quaternionicE8CartanCompact) :
    killingForm ℝ QuaternionicE8Lie X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [killingForm_apply_apply] at h
    have had0 := (trace_sq_nonpos_of_skew_ortho_gen quaternionicE8CartanInner
      quaternionicE8CartanInner_symm quaternionicE8CartanInner_posDef.1
      quaternionicE8CartanInner_posDef.2 (LieAlgebra.ad ℝ QuaternionicE8Lie X)
      (quaternionicE8CartanInner_ad_skew hX)).2 h
    exact (ad_eq_zero_iff_of_isSimple QuaternionicE8Lie X).mp had0
  · rintro rfl; simp

theorem quaternionicE8_killingForm_p_nonneg {X : QuaternionicE8Lie}
    (hX : X ∈ quaternionicE8CartanNoncompact) :
    0 ≤ killingForm ℝ QuaternionicE8Lie X X := by
  rw [killingForm_apply_apply]
  exact (trace_sq_nonneg_of_self_ortho_gen quaternionicE8CartanInner
    quaternionicE8CartanInner_symm quaternionicE8CartanInner_posDef.1
    quaternionicE8CartanInner_posDef.2 (LieAlgebra.ad ℝ QuaternionicE8Lie X)
    (quaternionicE8CartanInner_ad_self hX)).1

theorem quaternionicE8_killingForm_p_eq_zero_iff {X : QuaternionicE8Lie}
    (hX : X ∈ quaternionicE8CartanNoncompact) :
    killingForm ℝ QuaternionicE8Lie X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [killingForm_apply_apply] at h
    have had0 := (trace_sq_nonneg_of_self_ortho_gen quaternionicE8CartanInner
      quaternionicE8CartanInner_symm quaternionicE8CartanInner_posDef.1
      quaternionicE8CartanInner_posDef.2 (LieAlgebra.ad ℝ QuaternionicE8Lie X)
      (quaternionicE8CartanInner_ad_self hX)).2 h
    exact (ad_eq_zero_iff_of_isSimple QuaternionicE8Lie X).mp had0
  · rintro rfl; simp

theorem quaternionicE8_killingForm_k_p_ortho {X Y : QuaternionicE8Lie}
    (hX : X ∈ quaternionicE8CartanCompact)
    (hY : Y ∈ quaternionicE8CartanNoncompact) :
    killingForm ℝ QuaternionicE8Lie X Y = 0 := by
  have heq := LieAlgebra.killingForm_of_equiv_apply quaternionicE8CartanInvolution X Y
  have hθX : quaternionicE8CartanInvolution X = X := by
    simpa [quaternionicE8CartanCompact, sub_eq_zero] using hX
  have hθY : quaternionicE8CartanInvolution Y = -Y := by
    simpa [quaternionicE8CartanNoncompact, add_eq_zero_iff_eq_neg] using hY
  rw [hθX, hθY, map_neg] at heq
  linarith

/-- `QuaternionicE8Lie` (`𝔈₈(-24)`) has non-degenerate Killing form (`IsKilling ℝ`). -/
instance quaternionicE8Lie_isKilling : LieAlgebra.IsKilling ℝ QuaternionicE8Lie := by
  constructor
  rw [eq_bot_iff]
  intro Z hZ
  rw [LieSubmodule.mem_bot]
  have hZker : ∀ W : QuaternionicE8Lie, killingForm ℝ QuaternionicE8Lie W Z = 0 := fun W =>
    (LieIdeal.mem_killingCompl ℝ QuaternionicE8Lie ⊤).mp hZ W (LieSubmodule.mem_top W)
  let Zk : QuaternionicE8Lie := (1 / 2 : ℝ) • (Z + quaternionicE8CartanInvolution Z)
  let Zp : QuaternionicE8Lie := (1 / 2 : ℝ) • (Z - quaternionicE8CartanInvolution Z)
  have hZk : Zk ∈ quaternionicE8CartanCompact := by
    change quaternionicE8CartanInvolution Zk - Zk = 0
    dsimp [Zk]
    rw [map_smul, map_add, quaternionicE8CartanInvolution_involutive]
    module
  have hZp : Zp ∈ quaternionicE8CartanNoncompact := by
    change quaternionicE8CartanInvolution Zp + Zp = 0
    dsimp [Zp]
    rw [map_smul, map_sub, quaternionicE8CartanInvolution_involutive]
    module
  have hsum : Z = Zk + Zp := by dsimp [Zk, Zp]; module
  have hZk0 : Zk = 0 := by
    apply (quaternionicE8_killingForm_k_eq_zero_iff hZk).mp
    have h1 := hZker Zk
    rw [hsum, map_add, quaternionicE8_killingForm_k_p_ortho hZk hZp, add_zero] at h1
    exact h1
  have hZp0 : Zp = 0 := by
    apply (quaternionicE8_killingForm_p_eq_zero_iff hZp).mp
    have h1 := hZker Zp
    rw [hsum, map_add, LieModule.traceForm_comm,
      quaternionicE8_killingForm_k_p_ortho hZk hZp, zero_add] at h1
    exact h1
  rw [hsum, hZk0, hZp0, add_zero]

end QuaternionicE8Cartan

section SplitE8Cartan

open MagicSquareTitsBracket

private def splitMagicCartanInvolution :
    MagicSquareLie splitOctonionDatum h3ZornJordanDatum ≃ₗ⁅ℝ⁆
      MagicSquareLie splitOctonionDatum h3ZornJordanDatum :=
  msCartanInvolution splitOctonionDatum h3ZornJordanDatum
    sigmaOG2 sigmaO0 sigmaJ0 sigmaJF4
    sigmaOG2_involutive sigmaO0_involutive sigmaJ0_involutive sigmaJF4_involutive
    (fun a b => zornBilin_sigmaO_preserves a.1 b.1)
    (fun a b => by
      apply Subtype.ext
      change sigmaO (ZornVectorMatrix.mul a.1 b.1 - ZornVectorMatrix.mul b.1 a.1) =
        ZornVectorMatrix.mul (sigmaO a.1) (sigmaO b.1) -
          ZornVectorMatrix.mul (sigmaO b.1) (sigmaO a.1)
      rw [map_sub, sigmaO_mul, sigmaO_mul])
    sigmaO0_act
    sigmaOG2_inner
    (fun x y => sigmaJ_traceBilin_preserves x.1 y.1)
    sigmaJ0_mul0
    sigmaJ0_act
    sigmaJF4_inner

/-- Cartan involution `(σ_{G₂}, σ_O ⊗ σ_J, σ_{F₄})` on `SplitE8Lie` (`𝔈₈(+8)`). -/
def splitE8CartanInvolution : SplitE8Lie ≃ₗ⁅ℝ⁆ SplitE8Lie :=
  (splitE8EquivMagicSquare.trans splitMagicCartanInvolution).trans splitE8EquivMagicSquare.symm

@[simp] theorem splitE8CartanInvolution_involutive (X : SplitE8Lie) :
    splitE8CartanInvolution (splitE8CartanInvolution X) = X := by
  change splitE8EquivMagicSquare.symm (splitMagicCartanInvolution (splitE8EquivMagicSquare
    (splitE8EquivMagicSquare.symm (splitMagicCartanInvolution (splitE8EquivMagicSquare X))))) = X
  rw [LieEquiv.apply_symm_apply]
  have hinv : splitMagicCartanInvolution (splitMagicCartanInvolution
      (splitE8EquivMagicSquare X)) = splitE8EquivMagicSquare X :=
    splitMagicCartanInvolution.left_inv (splitE8EquivMagicSquare X)
  rw [hinv, LieEquiv.symm_apply_apply]

def splitE8CartanCompact : Submodule ℝ SplitE8Lie :=
  LinearMap.ker (splitE8CartanInvolution.toLinearMap - LinearMap.id)

def splitE8CartanNoncompact : Submodule ℝ SplitE8Lie :=
  LinearMap.ker (splitE8CartanInvolution.toLinearMap + LinearMap.id)

private theorem finrank_splitOctonionTraceZero :
    Module.finrank ℝ splitOctonionTraceZero = 7 := by
  rw [LinearEquiv.finrank_eq splitOct0CoordEquiv, Module.finrank_fin_fun]

private theorem finrank_splitE8Lie : Module.finrank ℝ SplitE8Lie = 248 := by
  let _free1 : Module.Free ℝ splitOctonionTraceZero :=
    Module.Free.of_divisionRing ℝ splitOctonionTraceZero
  let _free2 : Module.Free ℝ h3TraceZero := Module.Free.of_divisionRing ℝ h3TraceZero
  let _fin1 : Module.Finite ℝ splitOctonionTraceZero :=
    Module.finite_of_finrank_pos (by rw [finrank_splitOctonionTraceZero]; norm_num)
  let _fin2 : Module.Finite ℝ h3TraceZero :=
    Module.finite_of_finrank_pos (by rw [finrank_h3TraceZero]; norm_num)
  let _finG2 : Module.Finite ℝ G2DerivationCarrier :=
    Module.finite_of_finrank_pos (by rw [finrank_g2DerivationCarrier]; norm_num)
  let _finMix : Module.Finite ℝ (splitOctonionTraceZero ⊗[ℝ] h3TraceZero) := inferInstance
  let _finF4 : Module.Finite ℝ F4DerivationCarrier :=
    Module.finite_of_finrank_pos (by rw [finrank_f4DerivationCarrier]; norm_num)
  rw [LinearEquiv.finrank_eq splitE8EquivMagicSquare.toLinearEquiv,
    LinearEquiv.finrank_eq (msLinearEquiv splitOctonionDatum h3ZornJordanDatum),
    Module.finrank_prod, Module.finrank_prod, Module.finrank_tensorProduct,
    finrank_g2DerivationCarrier, finrank_splitOctonionTraceZero,
    finrank_h3TraceZero, finrank_f4DerivationCarrier]

theorem splitE8CartanInvolution_trace :
    LinearMap.trace ℝ SplitE8Lie splitE8CartanInvolution.toLinearMap = -8 := by
  let _free1 : Module.Free ℝ splitOctonionTraceZero :=
    Module.Free.of_divisionRing ℝ splitOctonionTraceZero
  let _free2 : Module.Free ℝ h3TraceZero := Module.Free.of_divisionRing ℝ h3TraceZero
  let _fin1 : Module.Finite ℝ splitOctonionTraceZero :=
    Module.finite_of_finrank_pos (by rw [finrank_splitOctonionTraceZero]; norm_num)
  let _fin2 : Module.Finite ℝ h3TraceZero :=
    Module.finite_of_finrank_pos (by rw [finrank_h3TraceZero]; norm_num)
  let _finG2 : Module.Finite ℝ G2DerivationCarrier :=
    Module.finite_of_finrank_pos (by rw [finrank_g2DerivationCarrier]; norm_num)
  let _finF4 : Module.Finite ℝ F4DerivationCarrier :=
    Module.finite_of_finrank_pos (by rw [finrank_f4DerivationCarrier]; norm_num)
  have hconj : splitE8EquivMagicSquare.toLinearEquiv.conj
      splitE8CartanInvolution.toLinearMap = splitMagicCartanInvolution.toLinearMap := by
    apply LinearMap.ext; intro X
    change splitE8EquivMagicSquare (splitE8EquivMagicSquare.symm
      (splitMagicCartanInvolution (splitE8EquivMagicSquare
        (splitE8EquivMagicSquare.symm X)))) = splitMagicCartanInvolution X
    rw [LieEquiv.apply_symm_apply, LieEquiv.apply_symm_apply]
  have htr := msCartanInvolution_trace splitOctonionDatum h3ZornJordanDatum
    sigmaOG2 sigmaO0 sigmaJ0 sigmaJF4
    sigmaOG2_involutive sigmaO0_involutive sigmaJ0_involutive sigmaJF4_involutive
    (fun a b => zornBilin_sigmaO_preserves a.1 b.1)
    (fun a b => by
      apply Subtype.ext
      change sigmaO (ZornVectorMatrix.mul a.1 b.1 - ZornVectorMatrix.mul b.1 a.1) =
        ZornVectorMatrix.mul (sigmaO a.1) (sigmaO b.1) -
          ZornVectorMatrix.mul (sigmaO b.1) (sigmaO a.1)
      rw [map_sub, sigmaO_mul, sigmaO_mul])
    sigmaO0_act sigmaOG2_inner
    (fun x y => sigmaJ_traceBilin_preserves x.1 y.1)
    sigmaJ0_mul0 sigmaJ0_act sigmaJF4_inner
  rw [← LinearMap.trace_conj' splitE8CartanInvolution.toLinearMap
      splitE8EquivMagicSquare.toLinearEquiv, hconj]
  change LinearMap.trace ℝ (MagicSquareLie splitOctonionDatum h3ZornJordanDatum)
      (msCartanInvolution splitOctonionDatum h3ZornJordanDatum
        sigmaOG2 sigmaO0 sigmaJ0 sigmaJF4
        sigmaOG2_involutive sigmaO0_involutive sigmaJ0_involutive sigmaJF4_involutive
        (fun a b => zornBilin_sigmaO_preserves a.1 b.1)
        (fun a b => by
          apply Subtype.ext
          change sigmaO (ZornVectorMatrix.mul a.1 b.1 - ZornVectorMatrix.mul b.1 a.1) =
            ZornVectorMatrix.mul (sigmaO a.1) (sigmaO b.1) -
              ZornVectorMatrix.mul (sigmaO b.1) (sigmaO a.1)
          rw [map_sub, sigmaO_mul, sigmaO_mul])
        sigmaO0_act sigmaOG2_inner
        (fun x y => sigmaJ_traceBilin_preserves x.1 y.1)
        sigmaJ0_mul0 sigmaJ0_act sigmaJF4_inner).toLinearMap = -8
  rw [htr]
  change LinearMap.trace ℝ G2DerivationCarrier sigmaOG2.toLinearMap +
      LinearMap.trace ℝ splitOctonionTraceZero sigmaO0 *
        LinearMap.trace ℝ h3TraceZero sigmaJ0 +
      LinearMap.trace ℝ F4DerivationCarrier sigmaJF4.toLinearMap = -8
  rw [sigmaOG2_trace, sigmaO0_trace, sigmaJ0_trace, sigmaJF4_trace]
  norm_num

theorem finrank_splitE8CartanCompact :
    Module.finrank ℝ splitE8CartanCompact = 120 := by
  have htr := involution_trace_eq splitE8CartanInvolution.toLinearMap
    splitE8CartanInvolution_involutive
  rw [splitE8CartanInvolution_trace, finrank_splitE8Lie] at htr
  norm_num at htr
  change (-8 : ℝ) = 2 * (Module.finrank ℝ splitE8CartanCompact : ℝ) - 248 at htr
  have hk : (Module.finrank ℝ splitE8CartanCompact : ℝ) = 120 := by linarith
  exact_mod_cast hk

theorem finrank_splitE8CartanNoncompact :
    Module.finrank ℝ splitE8CartanNoncompact = 128 := by
  have hsum := involution_finrank_add splitE8CartanInvolution.toLinearMap
    splitE8CartanInvolution_involutive
  have hk := finrank_splitE8CartanCompact
  change Module.finrank ℝ splitE8CartanCompact +
      Module.finrank ℝ splitE8CartanNoncompact = Module.finrank ℝ SplitE8Lie at hsum
  rw [hk, finrank_splitE8Lie] at hsum
  omega

/-- Cartan signature of `SplitE8Lie` (`𝔈₈(+8)`): `dim p - dim k = 128 - 120 = +8`. -/
theorem splitE8_signature_eq_pos_8 :
    (Module.finrank ℝ splitE8CartanNoncompact : ℤ) -
      Module.finrank ℝ splitE8CartanCompact = 8 := by
  rw [finrank_splitE8CartanNoncompact, finrank_splitE8CartanCompact]
  norm_num

private def splitE8CartanInner : SplitE8Lie →ₗ[ℝ] SplitE8Lie →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun X Y => -splitE8InvBilin X (splitE8CartanInvolution Y))
    (fun X₁ X₂ Y => by simp only [map_add, LinearMap.add_apply, neg_add])
    (fun r X Y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_neg])
    (fun X Y₁ Y₂ => by simp only [map_add, neg_add])
    (fun r X Y => by simp only [map_smul, smul_eq_mul, mul_neg])

private theorem splitE8CartanInvolution_preserves_invBilin (X Y : SplitE8Lie) :
    splitE8InvBilin (splitE8CartanInvolution X) (splitE8CartanInvolution Y) =
      splitE8InvBilin X Y := by
  let X' := splitE8EquivMagicSquare X
  let Y' := splitE8EquivMagicSquare Y
  have hX' : splitE8EquivMagicSquare (splitE8CartanInvolution X) =
      splitMagicCartanInvolution X' := by
    simp [splitE8CartanInvolution, X']
  have hY' : splitE8EquivMagicSquare (splitE8CartanInvolution Y) =
      splitMagicCartanInvolution Y' := by
    simp [splitE8CartanInvolution, Y']
  rw [splitE8InvBilin_apply, splitE8InvBilin_apply, hX', hY']
  have hg2 : ∀ D₁ D₂ : G2DerivationCarrier,
      splitOctonionDatum.g2Bilin (sigmaOG2 D₁) (sigmaOG2 D₂) =
        splitOctonionDatum.g2Bilin D₁ D₂ := by
    intro D₁ D₂
    change LinearMap.trace ℝ (ZornVectorMatrix ℝ)
        ((vDerEquivZornDerivations (sigmaOG2 D₁)).1 *
          (vDerEquivZornDerivations (sigmaOG2 D₂)).1) =
      LinearMap.trace ℝ (ZornVectorMatrix ℝ)
        ((vDerEquivZornDerivations D₁).1 * (vDerEquivZornDerivations D₂).1)
    have hc : ∀ D : G2DerivationCarrier,
        (vDerEquivZornDerivations (sigmaOG2 D)).1 =
          sigmaO * (vDerEquivZornDerivations D).1 * sigmaO := fun _ => by
      apply LinearMap.ext; intro x; rfl
    rw [hc D₁, hc D₂]
    have hs2 : sigmaO * sigmaO = (1 : Module.End ℝ (ZornVectorMatrix ℝ)) := by
      apply LinearMap.ext; intro x; simp
    calc
      LinearMap.trace ℝ (ZornVectorMatrix ℝ)
          ((sigmaO * (vDerEquivZornDerivations D₁).1 * sigmaO) *
            (sigmaO * (vDerEquivZornDerivations D₂).1 * sigmaO))
        = LinearMap.trace ℝ (ZornVectorMatrix ℝ)
            (sigmaO * (vDerEquivZornDerivations D₁).1 * (sigmaO * sigmaO) *
              (vDerEquivZornDerivations D₂).1 * sigmaO) := by
            simp only [mul_assoc]
      _ = LinearMap.trace ℝ (ZornVectorMatrix ℝ)
            (sigmaO * ((vDerEquivZornDerivations D₁).1 *
              (vDerEquivZornDerivations D₂).1) * sigmaO) := by
            rw [hs2, mul_one]; simp only [mul_assoc]
      _ = LinearMap.trace ℝ (ZornVectorMatrix ℝ)
            (((vDerEquivZornDerivations D₁).1 * (vDerEquivZornDerivations D₂).1) *
              (sigmaO * sigmaO)) := by
            rw [mul_assoc sigmaO _ sigmaO, LinearMap.trace_mul_comm]
            simp only [mul_assoc]
      _ = LinearMap.trace ℝ (ZornVectorMatrix ℝ)
            ((vDerEquivZornDerivations D₁).1 * (vDerEquivZornDerivations D₂).1) := by
            rw [hs2, mul_one]
  have hmix : ∀ m₁ m₂ : splitOctonionTraceZero ⊗[ℝ] h3TraceZero,
      magicMixedBilin splitOctonionDatum h3ZornJordanDatum
          (TensorProduct.map sigmaO0 sigmaJ0 m₁)
          (TensorProduct.map sigmaO0 sigmaJ0 m₂) =
        magicMixedBilin splitOctonionDatum h3ZornJordanDatum m₁ m₂ := by
    intro m₁ m₂
    induction m₁ using TensorProduct.inductionOn with
    | tmul a x =>
      induction m₂ using TensorProduct.inductionOn with
      | tmul b y =>
        simp only [TensorProduct.map_tmul, magicMixedBilin_tmul]
        change zornBilin (sigmaO a.1) (sigmaO b.1) * H3Zorn.traceBilin (sigmaJ x.1) (sigmaJ y.1) =
          zornBilin a.1 b.1 * H3Zorn.traceBilin x.1 y.1
        rw [zornBilin_sigmaO_preserves, sigmaJ_traceBilin_preserves]
      | add _ _ h1 h2 =>
        simp only [TensorProduct.map_tmul] at h1 h2
        simp [map_add, h1, h2]
    | add _ _ h1 h2 => simp [map_add, LinearMap.add_apply, h1, h2]
  have hf4 : ∀ F₁ F₂ : F4DerivationCarrier,
      h3ZornJordanDatum.f4Bilin (sigmaJF4 F₁) (sigmaJF4 F₂) =
        h3ZornJordanDatum.f4Bilin F₁ F₂ := by
    intro F₁ F₂
    change LinearMap.trace ℝ (H3Zorn ℝ) ((sigmaJF4 F₁).1 * (sigmaJF4 F₂).1) =
      LinearMap.trace ℝ (H3Zorn ℝ) (F₁.1 * F₂.1)
    have hc : ∀ F : F4DerivationCarrier, (sigmaJF4 F).1 = sigmaJ * F.1 * sigmaJ := fun _ => rfl
    rw [hc F₁, hc F₂]
    have hs2 : sigmaJ * sigmaJ = (1 : Module.End ℝ (H3Zorn ℝ)) := by
      apply LinearMap.ext; intro x; simp
    calc
      LinearMap.trace ℝ (H3Zorn ℝ) ((sigmaJ * F₁.1 * sigmaJ) * (sigmaJ * F₂.1 * sigmaJ))
        = LinearMap.trace ℝ (H3Zorn ℝ) (sigmaJ * F₁.1 * (sigmaJ * sigmaJ) * F₂.1 * sigmaJ) := by
            simp only [mul_assoc]
      _ = LinearMap.trace ℝ (H3Zorn ℝ) (sigmaJ * (F₁.1 * F₂.1) * sigmaJ) := by
            rw [hs2, mul_one]; simp only [mul_assoc]
      _ = LinearMap.trace ℝ (H3Zorn ℝ) ((F₁.1 * F₂.1) * (sigmaJ * sigmaJ)) := by
            rw [mul_assoc sigmaJ (F₁.1 * F₂.1) sigmaJ, LinearMap.trace_mul_comm]
            simp only [mul_assoc]
      _ = LinearMap.trace ℝ (H3Zorn ℝ) (F₁.1 * F₂.1) := by rw [hs2, mul_one]
  change 3 * splitOctonionDatum.g2Bilin (sigmaOG2 X'.g2) (sigmaOG2 Y'.g2) -
      6 * magicMixedBilin splitOctonionDatum h3ZornJordanDatum
        (TensorProduct.map sigmaO0 sigmaJ0 X'.mixed)
        (TensorProduct.map sigmaO0 sigmaJ0 Y'.mixed) +
      h3ZornJordanDatum.f4Bilin (sigmaJF4 X'.f4) (sigmaJF4 Y'.f4) =
    3 * splitOctonionDatum.g2Bilin X'.g2 Y'.g2 -
      6 * magicMixedBilin splitOctonionDatum h3ZornJordanDatum X'.mixed Y'.mixed +
      h3ZornJordanDatum.f4Bilin X'.f4 Y'.f4
  rw [hg2, hmix, hf4]

private theorem splitE8CartanInner_symm (X Y : SplitE8Lie) :
    splitE8CartanInner X Y = splitE8CartanInner Y X := by
  change -splitE8InvBilin X (splitE8CartanInvolution Y) =
    -splitE8InvBilin Y (splitE8CartanInvolution X)
  rw [← splitE8CartanInvolution_preserves_invBilin X (splitE8CartanInvolution Y),
    splitE8CartanInvolution_involutive, splitE8InvBilin_symm]

private theorem splitE8CartanInner_posDef :
    (∀ X, 0 ≤ splitE8CartanInner X X) ∧
      (∀ X, splitE8CartanInner X X = 0 ↔ X = 0) := by
  let BO0 : splitOctonionTraceZero →ₗ[ℝ] splitOctonionTraceZero →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun a b => splitOctonionDatum.bilin₀ a (sigmaO0 b))
      (fun _ _ _ => by simp only [map_add, LinearMap.add_apply])
      (fun _ _ _ => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
      (fun _ _ _ => by simp only [map_add])
      (fun _ _ _ => by simp only [map_smul, smul_eq_mul])
  let BJ0 : h3TraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => h3ZornJordanDatum.traceBilin₀ x (sigmaJ0 y))
      (fun _ _ _ => by simp only [map_add, LinearMap.add_apply])
      (fun _ _ _ => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
      (fun _ _ _ => by simp only [map_add])
      (fun _ _ _ => by simp only [map_smul, smul_eq_mul])
  let Bmix : (splitOctonionTraceZero ⊗[ℝ] h3TraceZero) →ₗ[ℝ]
      (splitOctonionTraceZero ⊗[ℝ] h3TraceZero) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun m₁ m₂ => magicMixedBilin splitOctonionDatum h3ZornJordanDatum m₁
        (TensorProduct.map sigmaO0 sigmaJ0 m₂))
      (fun _ _ _ => by simp only [map_add, LinearMap.add_apply])
      (fun _ _ _ => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
      (fun _ _ _ => by simp only [map_add])
      (fun _ _ _ => by simp only [map_smul, smul_eq_mul])
  have hmix_pd := tensorProduct_bilin_posDef
    BO0
    (fun a b => zornBilin_sigmaO_symm a.1 b.1)
    (fun a => zornBilin_sigmaO_nonneg a.1)
    (fun a => by
      change zornBilin a.1 (sigmaO a.1) = 0 ↔ a = 0
      rw [zornBilin_sigmaO_eq_zero_iff, Subtype.ext_iff]; rfl)
    BJ0
    (fun x y => sigmaJ_traceBilin_symm x.1 y.1)
    (fun x => sigmaJ_traceBilin_nonneg x.1)
    (fun x => by
      change H3Zorn.traceBilin x.1 (sigmaJ x.1) = 0 ↔ x = 0
      rw [sigmaJ_traceBilin_eq_zero_iff, Subtype.ext_iff]; rfl)
    Bmix
    (fun a₁ a₂ x₁ x₂ => by
      change magicMixedBilin splitOctonionDatum h3ZornJordanDatum
          (a₁ ⊗ₜ[ℝ] x₁) (sigmaO0 a₂ ⊗ₜ[ℝ] sigmaJ0 x₂) = BO0 a₁ a₂ * BJ0 x₁ x₂
      rw [magicMixedBilin_tmul]; rfl)
  have hval : ∀ X : SplitE8Lie, splitE8CartanInner X X =
      3 * (-splitOctonionDatum.g2Bilin X.g2 (sigmaOG2 X.g2)) +
        6 * Bmix X.mixed X.mixed +
        (-h3ZornJordanDatum.f4Bilin X.f4 (sigmaJF4 X.f4)) := by
    intro X
    change -splitE8InvBilin X (splitE8CartanInvolution X) = _
    rw [splitE8InvBilin_apply]
    have hX : splitE8EquivMagicSquare (splitE8CartanInvolution X) =
        splitMagicCartanInvolution (splitE8EquivMagicSquare X) := by
      simp [splitE8CartanInvolution]
    rw [hX]
    change -(3 * splitOctonionDatum.g2Bilin X.g2 (sigmaOG2 X.g2) -
      6 * Bmix X.mixed X.mixed + h3ZornJordanDatum.f4Bilin X.f4 (sigmaJF4 X.f4)) = _
    ring
  refine ⟨fun X => ?_, fun X => ?_⟩
  · rw [hval]
    have hg := zornG2_sigma_neg_bilin_nonneg X.g2
    have hm := hmix_pd.1 X.mixed
    have hf := zornF4_sigma_neg_bilin_nonneg X.f4
    linarith
  · constructor
    · intro h
      rw [hval] at h
      have hg := zornG2_sigma_neg_bilin_nonneg X.g2
      have hm := hmix_pd.1 X.mixed
      have hf := zornF4_sigma_neg_bilin_nonneg X.f4
      have hg0 : -splitOctonionDatum.g2Bilin X.g2 (sigmaOG2 X.g2) = 0 := by linarith
      have hm0 : Bmix X.mixed X.mixed = 0 := by linarith
      have hf0 : -h3ZornJordanDatum.f4Bilin X.f4 (sigmaJF4 X.f4) = 0 := by linarith
      apply splitE8EquivMagicSquare.injective
      apply MagicSquareLie.ext
      · exact (zornG2_sigma_neg_bilin_eq_zero_iff X.g2).mp hg0
      · exact (hmix_pd.2 X.mixed).mp hm0
      · exact (zornF4_sigma_neg_bilin_eq_zero_iff X.f4).mp hf0
    · rintro rfl; simp

private theorem splitE8CartanInner_ad_skew {X : SplitE8Lie}
    (hX : X ∈ splitE8CartanCompact) (Y Z : SplitE8Lie) :
    splitE8CartanInner (LieAlgebra.ad ℝ SplitE8Lie X Y) Z +
      splitE8CartanInner Y (LieAlgebra.ad ℝ SplitE8Lie X Z) = 0 := by
  have hθ : splitE8CartanInvolution X = X := by
    simpa [splitE8CartanCompact, sub_eq_zero] using hX
  change -splitE8InvBilin ⁅X, Y⁆ (splitE8CartanInvolution Z) +
    (-splitE8InvBilin Y (splitE8CartanInvolution ⁅X, Z⁆)) = 0
  rw [LieEquiv.map_lie, hθ]
  have hinv := splitE8InvBilin_lieInvariant X Y (splitE8CartanInvolution Z)
  linarith

private theorem splitE8CartanInner_ad_self {X : SplitE8Lie}
    (hX : X ∈ splitE8CartanNoncompact) (Y Z : SplitE8Lie) :
    splitE8CartanInner (LieAlgebra.ad ℝ SplitE8Lie X Y) Z =
      splitE8CartanInner Y (LieAlgebra.ad ℝ SplitE8Lie X Z) := by
  have hθ : splitE8CartanInvolution X = -X := by
    simpa [splitE8CartanNoncompact, add_eq_zero_iff_eq_neg] using hX
  change -splitE8InvBilin ⁅X, Y⁆ (splitE8CartanInvolution Z) =
    -splitE8InvBilin Y (splitE8CartanInvolution ⁅X, Z⁆)
  rw [LieEquiv.map_lie, hθ, neg_lie, map_neg]
  have hinv := splitE8InvBilin_lieInvariant X Y (splitE8CartanInvolution Z)
  linarith

theorem splitE8_killingForm_k_nonpos {X : SplitE8Lie}
    (hX : X ∈ splitE8CartanCompact) :
    killingForm ℝ SplitE8Lie X X ≤ 0 := by
  rw [killingForm_apply_apply]
  exact (trace_sq_nonpos_of_skew_ortho_gen splitE8CartanInner
    splitE8CartanInner_symm splitE8CartanInner_posDef.1 splitE8CartanInner_posDef.2
    (LieAlgebra.ad ℝ SplitE8Lie X) (splitE8CartanInner_ad_skew hX)).1

theorem splitE8_killingForm_k_eq_zero_iff {X : SplitE8Lie}
    (hX : X ∈ splitE8CartanCompact) :
    killingForm ℝ SplitE8Lie X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [killingForm_apply_apply] at h
    have had0 := (trace_sq_nonpos_of_skew_ortho_gen splitE8CartanInner
      splitE8CartanInner_symm splitE8CartanInner_posDef.1 splitE8CartanInner_posDef.2
      (LieAlgebra.ad ℝ SplitE8Lie X) (splitE8CartanInner_ad_skew hX)).2 h
    exact (ad_eq_zero_iff_of_isSimple SplitE8Lie X).mp had0
  · rintro rfl; simp

theorem splitE8_killingForm_p_nonneg {X : SplitE8Lie}
    (hX : X ∈ splitE8CartanNoncompact) :
    0 ≤ killingForm ℝ SplitE8Lie X X := by
  rw [killingForm_apply_apply]
  exact (trace_sq_nonneg_of_self_ortho_gen splitE8CartanInner
    splitE8CartanInner_symm splitE8CartanInner_posDef.1 splitE8CartanInner_posDef.2
    (LieAlgebra.ad ℝ SplitE8Lie X) (splitE8CartanInner_ad_self hX)).1

theorem splitE8_killingForm_p_eq_zero_iff {X : SplitE8Lie}
    (hX : X ∈ splitE8CartanNoncompact) :
    killingForm ℝ SplitE8Lie X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [killingForm_apply_apply] at h
    have had0 := (trace_sq_nonneg_of_self_ortho_gen splitE8CartanInner
      splitE8CartanInner_symm splitE8CartanInner_posDef.1 splitE8CartanInner_posDef.2
      (LieAlgebra.ad ℝ SplitE8Lie X) (splitE8CartanInner_ad_self hX)).2 h
    exact (ad_eq_zero_iff_of_isSimple SplitE8Lie X).mp had0
  · rintro rfl; simp

theorem splitE8_killingForm_k_p_ortho {X Y : SplitE8Lie}
    (hX : X ∈ splitE8CartanCompact)
    (hY : Y ∈ splitE8CartanNoncompact) :
    killingForm ℝ SplitE8Lie X Y = 0 := by
  have heq := LieAlgebra.killingForm_of_equiv_apply splitE8CartanInvolution X Y
  have hθX : splitE8CartanInvolution X = X := by
    simpa [splitE8CartanCompact, sub_eq_zero] using hX
  have hθY : splitE8CartanInvolution Y = -Y := by
    simpa [splitE8CartanNoncompact, add_eq_zero_iff_eq_neg] using hY
  rw [hθX, hθY, map_neg] at heq
  linarith

end SplitE8Cartan

section E8RealFormSeparation

open MagicSquareTitsBracket

theorem e8_real_form_signatures_pairwise_distinct :
    (-248 : ℤ) ≠ -24 ∧ (-24 : ℤ) ≠ 8 ∧ (-248 : ℤ) ≠ 8 := by
  norm_num

/-- `CompactE8Lie` (`𝔈₈(-248)`) is not isomorphic as a real Lie algebra to
`QuaternionicE8Lie` (`𝔈₈(-24)`). -/
theorem compactE8_not_lieEquiv_quaternionicE8 :
    IsEmpty (CompactE8Lie ≃ₗ⁅ℝ⁆ QuaternionicE8Lie) := by
  refine ⟨fun e => ?_⟩
  have hpos : 0 < Module.finrank ℝ quaternionicE8CartanNoncompact := by
    rw [finrank_quaternionicE8CartanNoncompact]; norm_num
  have hne : quaternionicE8CartanNoncompact ≠ ⊥ := fun hb => by
    rw [hb, finrank_bot] at hpos; norm_num at hpos
  obtain ⟨Y, hYp, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hKpos : 0 < killingForm ℝ QuaternionicE8Lie Y Y :=
    lt_of_le_of_ne (quaternionicE8_killingForm_p_nonneg hYp)
      (fun h => hY0 ((quaternionicE8_killingForm_p_eq_zero_iff hYp).mp h.symm))
  have hKneg : killingForm ℝ CompactE8Lie (e.symm Y) (e.symm Y) ≤ 0 :=
    compactE8_killingForm_nonpos (e.symm Y)
  have heq := LieAlgebra.killingForm_of_equiv_apply e (e.symm Y) (e.symm Y)
  rw [e.apply_symm_apply] at heq
  linarith

/-- `CompactE8Lie` (`𝔈₈(-248)`) is not isomorphic as a real Lie algebra to
`SplitE8Lie` (`𝔈₈(+8)`). -/
theorem compactE8_not_lieEquiv_splitE8 :
    IsEmpty (CompactE8Lie ≃ₗ⁅ℝ⁆ SplitE8Lie) := by
  refine ⟨fun e => ?_⟩
  have hpos : 0 < Module.finrank ℝ splitE8CartanNoncompact := by
    rw [finrank_splitE8CartanNoncompact]; norm_num
  have hne : splitE8CartanNoncompact ≠ ⊥ := fun hb => by
    rw [hb, finrank_bot] at hpos; norm_num at hpos
  obtain ⟨Y, hYp, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hKpos : 0 < killingForm ℝ SplitE8Lie Y Y :=
    lt_of_le_of_ne (splitE8_killingForm_p_nonneg hYp)
      (fun h => hY0 ((splitE8_killingForm_p_eq_zero_iff hYp).mp h.symm))
  have hKneg : killingForm ℝ CompactE8Lie (e.symm Y) (e.symm Y) ≤ 0 :=
    compactE8_killingForm_nonpos (e.symm Y)
  have heq := LieAlgebra.killingForm_of_equiv_apply e (e.symm Y) (e.symm Y)
  rw [e.apply_symm_apply] at heq
  linarith

/-- `QuaternionicE8Lie` (`𝔈₈(-24)`) is not isomorphic as a real Lie algebra to
`SplitE8Lie` (`𝔈₈(+8)`), proved via `128 + 136 = 264 > 248`. -/
theorem quaternionicE8_not_lieEquiv_splitE8 :
    IsEmpty (QuaternionicE8Lie ≃ₗ⁅ℝ⁆ SplitE8Lie) := by
  refine ⟨fun e => ?_⟩
  let K' : Submodule ℝ SplitE8Lie :=
    Submodule.map e.toLinearEquiv.toLinearMap quaternionicE8CartanCompact
  have hK'_fin : Module.finrank ℝ K' = 136 := by
    have heq := (e.toLinearEquiv.submoduleMap quaternionicE8CartanCompact).finrank_eq
    rw [← heq, finrank_quaternionicE8CartanCompact]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq K' splitE8CartanNoncompact
  have hle : Module.finrank ℝ (K' ⊔ splitE8CartanNoncompact : Submodule ℝ SplitE8Lie) ≤ 248 := by
    rw [← finrank_splitE8Lie]
    exact Submodule.finrank_le _
  have hinf : 0 < Module.finrank ℝ (K' ⊓ splitE8CartanNoncompact : Submodule ℝ SplitE8Lie) := by
    rw [hK'_fin, finrank_splitE8CartanNoncompact] at hsum
    omega
  have hne : (K' ⊓ splitE8CartanNoncompact : Submodule ℝ SplitE8Lie) ≠ ⊥ := fun hb => by
    rw [hb, finrank_bot] at hinf; norm_num at hinf
  obtain ⟨Y, hYmem, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rcases hYmem with ⟨hYK', hYp⟩
  have hKpos : 0 < killingForm ℝ SplitE8Lie Y Y :=
    lt_of_le_of_ne (splitE8_killingForm_p_nonneg hYp)
      (fun h => hY0 ((splitE8_killingForm_p_eq_zero_iff hYp).mp h.symm))
  rcases (Submodule.mem_map.mp hYK') with ⟨X, hXk, hXe⟩
  have hKneg : killingForm ℝ QuaternionicE8Lie X X ≤ 0 :=
    quaternionicE8_killingForm_k_nonpos hXk
  have heq := LieAlgebra.killingForm_of_equiv_apply e X X
  change killingForm ℝ SplitE8Lie (e.toLinearEquiv.toLinearMap X)
      (e.toLinearEquiv.toLinearMap X) = killingForm ℝ QuaternionicE8Lie X X at heq
  rw [hXe] at heq
  linarith

end E8RealFormSeparation

end E8CartanInvolutionsAndSignatures

end CartanSignatures

end InfoGeometry.Algebra
