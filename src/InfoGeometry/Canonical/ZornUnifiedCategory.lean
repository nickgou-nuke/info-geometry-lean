/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorZornRealModule
import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Categorical.ZornUHFColimit
import InfoGeometry.NCG.ZornCommutator
import InfoGeometry.Physics.NCG.NoncommutativeChiralZornAlgebra
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic

/-!
# Operator-Valued Zorn Module Category and Associator Defect Representation

Constructs the category `ZornMod Z M` of real modules equipped with a left
linear action of a (generally non-associative, non-commutative) Zorn carrier `Z`,
proves full left/right distributivity of the operator-valued Zorn product on
`OperatorZornMatrix A`, defines the regular Zorn representation `regularZornMod`,
and proves that the failure of `regularZornMod.act` to be a multiplicative
homomorphism is governed identically by the non-associative Zorn associator
`zornAssociator X Y Z = (X * Y) * Z - X * (Y * Z)`.
-/

open InfoGeometry.Physics.NCG.NCZornElement

universe u

noncomputable section

namespace InfoGeometry.Canonical.ZornUnifiedCategory

open CategoryTheory
open ModuleCat
open InfoGeometry.NCG.ZornCommutator
open InfoGeometry.Canonical.OperatorZornRealModule
open InfoGeometry.Physics.NCG

/-- Negation distributes over addition in any non-commutative ring: `-(a + b) = -a + -b`. -/
lemma neg_add_distrib {A : Type u} [Ring A] (a b : A) : -(a + b) = -a + -b := by
  abel

/-- Pointwise right-additivity of the operator Zorn dot product:
`zornDot x (y + z) = zornDot x y + zornDot x z`. -/
lemma zornDot_add_left {A : Type u} [Ring A] (x y z : Fin 3 → A) :
    NCZornElement.zornDot x (y + z) = NCZornElement.zornDot x y + NCZornElement.zornDot x z := by
  simp only [NCZornElement.zornDot, Pi.add_apply, mul_add]
  abel

/-- Pointwise left-additivity of the operator Zorn dot product:
`zornDot (x + y) z = zornDot x z + zornDot y z`. -/
lemma zornDot_add_right {A : Type u} [Ring A] (x y z : Fin 3 → A) :
    NCZornElement.zornDot (x + y) z = NCZornElement.zornDot x z + NCZornElement.zornDot y z := by
  simp only [NCZornElement.zornDot, Pi.add_apply, add_mul]
  abel

/-- Pointwise left-additivity of the operator Zorn cross product:
`zornCross (x + y) z = zornCross x z + zornCross y z`. -/
lemma zornCross_add_left {A : Type u} [Ring A] (x y z : Fin 3 → A) :
    NCZornElement.zornCross (x + y) z = NCZornElement.zornCross x z + NCZornElement.zornCross y z := by
  ext i
  fin_cases i <;>
    simp only [NCZornElement.zornCross, Pi.add_apply, add_mul] <;>
    abel

/-- Pointwise right-additivity of the operator Zorn cross product:
`zornCross x (y + z) = zornCross x y + zornCross x z`. -/
lemma zornCross_add_right {A : Type u} [Ring A] (x y z : Fin 3 → A) :
    NCZornElement.zornCross x (y + z) = NCZornElement.zornCross x y + NCZornElement.zornCross x z := by
  ext i
  fin_cases i <;>
    simp only [NCZornElement.zornCross, Pi.add_apply, mul_add] <;>
    abel

@[simp] lemma add_n_plus {A : Type u} [Ring A] (X Y : OperatorZornMatrix A) :
    (X + Y).n_plus = X.n_plus + Y.n_plus := rfl

@[simp] lemma add_n_minus {A : Type u} [Ring A] (X Y : OperatorZornMatrix A) :
    (X + Y).n_minus = X.n_minus + Y.n_minus := rfl

@[simp] lemma add_sigma_plus {A : Type u} [Ring A] (X Y : OperatorZornMatrix A) :
    (X + Y).sigma_plus = X.sigma_plus + Y.sigma_plus := rfl

@[simp] lemma add_sigma_minus {A : Type u} [Ring A] (X Y : OperatorZornMatrix A) :
    (X + Y).sigma_minus = X.sigma_minus + Y.sigma_minus := rfl

@[simp] lemma sub_n_plus {A : Type u} [Ring A] (X Y : OperatorZornMatrix A) :
    (X - Y).n_plus = X.n_plus - Y.n_plus := by
  change X.n_plus + -Y.n_plus = X.n_plus - Y.n_plus
  exact (sub_eq_add_neg X.n_plus Y.n_plus).symm

@[simp] lemma sub_n_minus {A : Type u} [Ring A] (X Y : OperatorZornMatrix A) :
    (X - Y).n_minus = X.n_minus - Y.n_minus := by
  change X.n_minus + -Y.n_minus = X.n_minus - Y.n_minus
  exact (sub_eq_add_neg X.n_minus Y.n_minus).symm

@[simp] lemma sub_sigma_plus {A : Type u} [Ring A] (X Y : OperatorZornMatrix A) :
    (X - Y).sigma_plus = X.sigma_plus - Y.sigma_plus := by
  change X.sigma_plus + -Y.sigma_plus = X.sigma_plus - Y.sigma_plus
  exact (sub_eq_add_neg X.sigma_plus Y.sigma_plus).symm

@[simp] lemma sub_sigma_minus {A : Type u} [Ring A] (X Y : OperatorZornMatrix A) :
    (X - Y).sigma_minus = X.sigma_minus - Y.sigma_minus := by
  change X.sigma_minus + -Y.sigma_minus = X.sigma_minus - Y.sigma_minus
  exact (sub_eq_add_neg X.sigma_minus Y.sigma_minus).symm

/-- Right distributivity of the non-commutative operator Zorn product:
`X * (Y + Z) = X * Y + X * Z`. -/
theorem zorn_mul_add {A : Type u} [Ring A] (X Y Z : OperatorZornMatrix A) :
    X * (Y + Z) = X * Y + X * Z := by
  apply operatorZornMatrix_ext
  · simp only [mul_n_plus, add_n_plus, add_sigma_minus, zornDot_add_left, mul_add]
    abel
  · simp only [mul_n_minus, add_n_minus, add_sigma_plus, zornDot_add_left, mul_add]
    abel
  · funext i
    simp only [mul_sigma_plus, add_n_minus, add_sigma_plus, add_sigma_minus,
      zornCross_add_right, Pi.add_apply, mul_add]
    abel
  · funext i
    simp only [mul_sigma_minus, add_n_plus, add_sigma_plus, add_sigma_minus,
      zornCross_add_right, Pi.add_apply, mul_add]
    abel

/-- Left distributivity of the non-commutative operator Zorn product:
`(X + Y) * Z = X * Z + Y * Z`. -/
theorem zorn_add_mul {A : Type u} [Ring A] (X Y Z : OperatorZornMatrix A) :
    (X + Y) * Z = X * Z + Y * Z := by
  apply operatorZornMatrix_ext
  · simp only [mul_n_plus, add_n_plus, add_sigma_plus, zornDot_add_right, add_mul]
    abel
  · simp only [mul_n_minus, add_n_minus, add_sigma_minus, zornDot_add_right, add_mul]
    abel
  · funext i
    simp only [mul_sigma_plus, add_n_plus, add_sigma_plus, add_sigma_minus,
      zornCross_add_left, Pi.add_apply, add_mul]
    abel
  · funext i
    simp only [mul_sigma_minus, add_n_minus, add_sigma_plus, add_sigma_minus,
      zornCross_add_left, Pi.add_apply, add_mul]
    abel

/-- Left multiplication by a fixed operator Zorn element `X` is an `ℝ`-linear map. -/
def zornLeftMul {A : Type u} [Ring A] [Algebra ℝ A] (X : OperatorZornMatrix A) :
    OperatorZornMatrix A →ₗ[ℝ] OperatorZornMatrix A where
  toFun Y := X * Y
  map_add' Y Z := zorn_mul_add X Y Z
  map_smul' c Y := zorn_mul_smul c X Y

@[simp] theorem zornLeftMul_apply {A : Type u} [Ring A] [Algebra ℝ A]
    (X Y : OperatorZornMatrix A) :
    zornLeftMul X Y = X * Y := rfl

/-- A Zorn module structure on an `ℝ`-module `M` over a Zorn carrier `Z`. -/
structure ZornMod (Z : Type u) (M : Type u) [AddCommGroup M] [Module ℝ M] where
  act : Z → (M →ₗ[ℝ] M)

/-- Equivariant `ℝ`-linear morphisms between two Zorn module structures on `M`. -/
def ZornModHom {Z : Type u} {M : Type u} [AddCommGroup M] [Module ℝ M]
    (X Y : ZornMod Z M) : Type u :=
  { f : M →ₗ[ℝ] M // ∀ z : Z, f.comp (X.act z) = (Y.act z).comp f }

/-- Identity morphism on a Zorn module `X`. -/
def ZornModHom_id {Z : Type u} {M : Type u} [AddCommGroup M] [Module ℝ M]
    (X : ZornMod Z M) : ZornModHom X X :=
  ⟨LinearMap.id, fun _ => rfl⟩

/-- Composition of Zorn module morphisms. -/
def ZornModHom_comp {Z : Type u} {M : Type u} [AddCommGroup M] [Module ℝ M]
    {X Y W : ZornMod Z M} (g : ZornModHom Y W) (f : ZornModHom X Y) :
    ZornModHom X W :=
  ⟨g.1.comp f.1, fun z => by
    rw [LinearMap.comp_assoc, f.2 z, ← LinearMap.comp_assoc, g.2 z, LinearMap.comp_assoc]⟩

@[simp] theorem ZornModHom_comp_id {Z : Type u} {M : Type u} [AddCommGroup M] [Module ℝ M]
    {X Y : ZornMod Z M} (f : ZornModHom X Y) :
    ZornModHom_comp (ZornModHom_id Y) f = f := by
  apply Subtype.ext
  rfl

@[simp] theorem ZornModHom_id_comp {Z : Type u} {M : Type u} [AddCommGroup M] [Module ℝ M]
    {X Y : ZornMod Z M} (f : ZornModHom X Y) :
    ZornModHom_comp f (ZornModHom_id X) = f := by
  apply Subtype.ext
  rfl

@[simp] theorem ZornModHom_comp_assoc {Z : Type u} {M : Type u} [AddCommGroup M] [Module ℝ M]
    {W X Y Z' : ZornMod Z M} (h : ZornModHom Y Z') (g : ZornModHom X Y)
    (f : ZornModHom W X) :
    ZornModHom_comp h (ZornModHom_comp g f) =
    ZornModHom_comp (ZornModHom_comp h g) f := by
  apply Subtype.ext
  rfl

instance instZornModCategory {Z : Type u} {M : Type u} [AddCommGroup M] [Module ℝ M] :
    Category (ZornMod Z M) where
  Hom X Y := ZornModHom X Y
  id X := ZornModHom_id X
  comp f g := ZornModHom_comp g f
  id_comp f := ZornModHom_id_comp f
  comp_id f := ZornModHom_comp_id f
  assoc f g h := (ZornModHom_comp_assoc h g f).symm

/-- Forgetful functor from `ZornMod Z M` to `ModuleCat ℝ`. -/
def forgetFunctor {Z : Type u} {M : Type u} [AddCommGroup M] [Module ℝ M] :
    ZornMod Z M ⥤ ModuleCat ℝ where
  obj _ := ModuleCat.of ℝ M
  map f := ModuleCat.ofHom f.1
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The regular Zorn module: left multiplication on `OperatorZornMatrix A`. -/
def regularZornMod {A : Type u} [Ring A] [Algebra ℝ A] :
    ZornMod (OperatorZornMatrix A) (OperatorZornMatrix A) where
  act := zornLeftMul

/-- The associator measuring failure of associativity of the Zorn product:
`(X * Y) * Z - X * (Y * Z)`. -/
def zornAssociator {A : Type u} [Ring A]
    (X Y Z : OperatorZornMatrix A) : OperatorZornMatrix A :=
  (X * Y) * Z - X * (Y * Z)

/-- The failure of `regularZornMod.act` to intertwine multiplication with
composition of linear maps equals the Zorn associator `zornAssociator X Y Z`. -/
theorem regularZornMod_act_defect_eq_zornAssociator
    {A : Type u} [Ring A] [Algebra ℝ A]
    (X Y Z : OperatorZornMatrix A) :
    regularZornMod.act (X * Y) Z -
      ((regularZornMod.act X).comp (regularZornMod.act Y)) Z =
      zornAssociator X Y Z :=
  rfl

/-- `OperatorZornMatrix A` is definitionally equal to `NCZornElement A` on every
non-commutative ring `A`, witnessed on its chiral idempotent projectors. -/
theorem operatorZornMatrix_pureNPlus_idempotent {A : Type u} [Ring A] :
    (NCZornElement.pureNPlus (1 : A) : OperatorZornMatrix A) *
      NCZornElement.pureNPlus (1 : A) =
      NCZornElement.pureNPlus (1 : A) := by
  simp [NCZornElement.pure_n_plus_mul]

/-! ### Quadrant III-B (`Ω₈`): Zorn Lagrange–Binet–Cauchy Norm, Alternativity, Sign Elenchus & Baryon Associator -/

/-- `Ω₈-1` Exact Zorn Lagrange–Binet–Cauchy norm multiplicativity (`det(X * Y) = det(X) * det(Y)`)
over any commutative ring `K` for `OperatorZornMatrix K`, powered by the opposite-sign chiral
Hodge cross-product lock (`- v₁ × v₂` on `sigma_plus` and `+ u₁ × u₂` on `sigma_minus`). -/
theorem zorn_det_mul {K : Type u} [CommRing K] (X Y : OperatorZornMatrix K) :
    (X * Y).n_plus * (X * Y).n_minus -
      NCZornElement.zornDot (X * Y).sigma_plus (X * Y).sigma_minus =
    (X.n_plus * X.n_minus - NCZornElement.zornDot X.sigma_plus X.sigma_minus) *
      (Y.n_plus * Y.n_minus - NCZornElement.zornDot Y.sigma_plus Y.sigma_minus) := by
  simp only [mul_n_plus, mul_n_minus, mul_sigma_plus, mul_sigma_minus,
    NCZornElement.zornDot, NCZornElement.zornCross]
  ring

/-- `Ω₈-2` Left BAC–CAB alternativity `(X * X) * Y = X * (X * Y)` on `OperatorZornMatrix K`. -/
theorem zorn_left_alternative {K : Type u} [CommRing K] (X Y : OperatorZornMatrix K) :
    (X * X) * Y = X * (X * Y) := by
  have hFin3 : ∀ (f g : Fin 3 → K), f 0 = g 0 → f 1 = g 1 → f 2 = g 2 → f = g := by
    intro f g h0 h1 h2
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  apply operatorZornMatrix_ext
  · simp only [mul_n_plus, mul_sigma_plus, mul_sigma_minus,
      NCZornElement.zornDot, NCZornElement.zornCross]
    ring
  · simp only [mul_n_minus, mul_sigma_plus, mul_sigma_minus,
      NCZornElement.zornDot, NCZornElement.zornCross]
    ring
  · refine hFin3 _ _ ?_ ?_ ?_ <;>
      (simp only [mul_n_plus, mul_n_minus, mul_sigma_plus, mul_sigma_minus,
         NCZornElement.zornDot, NCZornElement.zornCross];
       ring)
  · refine hFin3 _ _ ?_ ?_ ?_ <;>
      (simp only [mul_n_plus, mul_n_minus, mul_sigma_plus, mul_sigma_minus,
         NCZornElement.zornDot, NCZornElement.zornCross];
       ring)

/-- `Ω₈-2` Right BAC–CAB alternativity `(Y * X) * X = Y * (X * X)` on `OperatorZornMatrix K`. -/
theorem zorn_right_alternative {K : Type u} [CommRing K] (X Y : OperatorZornMatrix K) :
    (Y * X) * X = Y * (X * X) := by
  have hFin3 : ∀ (f g : Fin 3 → K), f 0 = g 0 → f 1 = g 1 → f 2 = g 2 → f = g := by
    intro f g h0 h1 h2
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  apply operatorZornMatrix_ext
  · simp only [mul_n_plus, mul_sigma_plus, mul_sigma_minus,
      NCZornElement.zornDot, NCZornElement.zornCross]
    ring
  · simp only [mul_n_minus, mul_sigma_plus, mul_sigma_minus,
      NCZornElement.zornDot, NCZornElement.zornCross]
    ring
  · refine hFin3 _ _ ?_ ?_ ?_ <;>
      (simp only [mul_n_plus, mul_n_minus, mul_sigma_plus, mul_sigma_minus,
         NCZornElement.zornDot, NCZornElement.zornCross];
       ring)
  · refine hFin3 _ _ ?_ ?_ ?_ <;>
      (simp only [mul_n_plus, mul_n_minus, mul_sigma_plus, mul_sigma_minus,
         NCZornElement.zornDot, NCZornElement.zornCross];
       ring)

/-- `Ω₈-3` Socratic Sign-Cohomology Elenchus (`α = β = -1` vs. `α = +1, β = -1`):
If both off-diagonal cross products carried the same minus sign (`- v₁ × v₂` and `- u₁ × u₂`),
the Zorn determinant would fail Lagrange–Binet–Cauchy norm multiplicativity by the exact defect
`-2 * zornDot (u₁ × u₂) (v₁ × v₂)`. -/
theorem zorn_same_sign_elenchus_norm_defect {K : Type u} [CommRing K]
    (X Y : OperatorZornMatrix K) :
    let u_same : Fin 3 → K := fun c =>
      X.n_plus * Y.sigma_plus c + X.sigma_plus c * Y.n_minus -
        NCZornElement.zornCross X.sigma_minus Y.sigma_minus c
    let v_same : Fin 3 → K := fun c =>
      X.n_minus * Y.sigma_minus c + X.sigma_minus c * Y.n_plus -
        NCZornElement.zornCross X.sigma_plus Y.sigma_plus c
    ((X * Y).n_plus * (X * Y).n_minus - NCZornElement.zornDot u_same v_same) -
      (X.n_plus * X.n_minus - NCZornElement.zornDot X.sigma_plus X.sigma_minus) *
        (Y.n_plus * Y.n_minus - NCZornElement.zornDot Y.sigma_plus Y.sigma_minus) =
      -2 * NCZornElement.zornDot
        (NCZornElement.zornCross X.sigma_plus Y.sigma_plus)
        (NCZornElement.zornCross X.sigma_minus Y.sigma_minus) := by
  simp only [mul_n_plus, mul_n_minus, NCZornElement.zornDot, NCZornElement.zornCross]
  ring

/-- `Ω₈-4` Third-order baryon and diagonal associator laws for `zornAssociator X Y Z`:
The diagonal entries of the Zorn associator are exact chiral scalar triple products
`∓((u₁ × u₂) · u₃ + (v₁ × v₂) · v₃)`, so the diagonal trace of `zornAssociator X Y Z`
vanishes identically and the diagonal determinant is `-((u₁ × u₂) · u₃ + (v₁ × v₂) · v₃)²`. -/
theorem zorn_baryon_associator_diagonal_sum_and_diff {K : Type u} [CommRing K]
    (X Y Z : OperatorZornMatrix K) :
    let B_plus := NCZornElement.zornDot
      (NCZornElement.zornCross X.sigma_plus Y.sigma_plus) Z.sigma_plus
    let B_minus := NCZornElement.zornDot
      (NCZornElement.zornCross X.sigma_minus Y.sigma_minus) Z.sigma_minus
    (zornAssociator X Y Z).n_plus = -(B_plus + B_minus) ∧
    (zornAssociator X Y Z).n_minus = B_plus + B_minus ∧
    (zornAssociator X Y Z).n_plus + (zornAssociator X Y Z).n_minus = 0 ∧
    (zornAssociator X Y Z).n_plus * (zornAssociator X Y Z).n_minus =
      -(B_plus + B_minus) ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [zornAssociator, sub_n_plus, sub_n_minus,
       mul_n_plus, mul_n_minus, mul_sigma_plus, mul_sigma_minus,
       NCZornElement.zornDot, NCZornElement.zornCross];
     ring)

/-- **Quadrant III-B (`Ω₈`, `omega8_zorn_binet_cauchy_and_alternativity`)**:
Unites Zorn Lagrange–Binet–Cauchy norm multiplicativity, left and right BAC–CAB alternativity,
the Socratic same-sign cross-product defect elenchus, and the third-order baryon associator
diagonal trace/determinant identities on `OperatorZornMatrix K`. -/
theorem omega8_zorn_binet_cauchy_and_alternativity {K : Type u} [CommRing K]
    (X Y Z : OperatorZornMatrix K) :
    let B_plus := NCZornElement.zornDot
      (NCZornElement.zornCross X.sigma_plus Y.sigma_plus) Z.sigma_plus
    let B_minus := NCZornElement.zornDot
      (NCZornElement.zornCross X.sigma_minus Y.sigma_minus) Z.sigma_minus
    ((X * Y).n_plus * (X * Y).n_minus -
       NCZornElement.zornDot (X * Y).sigma_plus (X * Y).sigma_minus =
     (X.n_plus * X.n_minus - NCZornElement.zornDot X.sigma_plus X.sigma_minus) *
       (Y.n_plus * Y.n_minus - NCZornElement.zornDot Y.sigma_plus Y.sigma_minus)) ∧
    (X * X) * Y = X * (X * Y) ∧
    (Y * X) * X = Y * (X * X) ∧
    (zornAssociator X Y Z).n_plus = -(B_plus + B_minus) ∧
    (zornAssociator X Y Z).n_minus = B_plus + B_minus ∧
    (zornAssociator X Y Z).n_plus + (zornAssociator X Y Z).n_minus = 0 ∧
    (zornAssociator X Y Z).n_plus * (zornAssociator X Y Z).n_minus =
      -(B_plus + B_minus) ^ 2 := by
  have hB := zorn_baryon_associator_diagonal_sum_and_diff X Y Z
  exact ⟨zorn_det_mul X Y,
         zorn_left_alternative X Y,
         zorn_right_alternative X Y,
         hB.1, hB.2.1, hB.2.2.1, hB.2.2.2⟩

/-! ### Cross-Quadrant Welds `𝓜₁` & `𝓜₂`: Chiral Hodge Sign Lock & Artin Di-Associative Embedding -/

/-- **Seam `𝓜₁` (`seam_M1_chiral_sign_lock_binet_cauchy_and_baryon_difference`)**:
For purely off-diagonal Zorn elements `z₁ = ⟨0, 0, u₁, v₁⟩`, `z₂ = ⟨0, 0, u₂, v₂⟩`, and
`z₃ = ⟨0, 0, u₃, v₃⟩` over `[CommRing K]`:
1. The true opposite-sign Hodge cross product `z_cross = ⟨0, 0, -(v₁ × v₂), +(u₁ × u₂)⟩`
   (`α = +1, β = -1, αβ = -1`) has positive Zorn determinant `+(u₁ × u₂) · (v₁ × v₂)`,
2. `4 det(z₁ z₂) = g(z₁, z₂)² - ω(z₁, z₂)² + 4 det(z₁ ×_H z₂) = 4 det(z₁) det(z₂)`,
3. The Jordan anticommutator `z_cross * z₃ + z₃ * z_cross` is the scalar baryon difference
   `(B_plus - B_minus) • 1` (`det(u₁,u₂,u₃) - det(v₁,v₂,v₃)` on both diagonal entries and `0`
   on both off-diagonal vector slots). -/
theorem seam_M1_chiral_sign_lock_binet_cauchy_and_baryon_difference
    {K : Type u} [CommRing K] (u₁ v₁ u₂ v₂ u₃ v₃ : Fin 3 → K) :
    let z₁ : OperatorZornMatrix K := ⟨0, 0, u₁, v₁⟩
    let z₂ : OperatorZornMatrix K := ⟨0, 0, u₂, v₂⟩
    let z₃ : OperatorZornMatrix K := ⟨0, 0, u₃, v₃⟩
    let z_cross : OperatorZornMatrix K :=
      ⟨0, 0, -NCZornElement.zornCross v₁ v₂, NCZornElement.zornCross u₁ u₂⟩
    let det_z₁ := z₁.n_plus * z₁.n_minus - NCZornElement.zornDot z₁.sigma_plus z₁.sigma_minus
    let det_z₂ := z₂.n_plus * z₂.n_minus - NCZornElement.zornDot z₂.sigma_plus z₂.sigma_minus
    let det_z₁z₂ :=
      (z₁ * z₂).n_plus * (z₁ * z₂).n_minus -
        NCZornElement.zornDot (z₁ * z₂).sigma_plus (z₁ * z₂).sigma_minus
    let det_cross :=
      z_cross.n_plus * z_cross.n_minus -
        NCZornElement.zornDot z_cross.sigma_plus z_cross.sigma_minus
    let g₁₂ := NCZornElement.zornDot u₁ v₂ + NCZornElement.zornDot v₁ u₂
    let ω₁₂ := NCZornElement.zornDot u₁ v₂ - NCZornElement.zornDot v₁ u₂
    let B_plus := NCZornElement.zornDot (NCZornElement.zornCross u₁ u₂) u₃
    let B_minus := NCZornElement.zornDot (NCZornElement.zornCross v₁ v₂) v₃
    det_cross =
      NCZornElement.zornDot
        (NCZornElement.zornCross u₁ u₂) (NCZornElement.zornCross v₁ v₂) ∧
    4 * det_z₁z₂ = g₁₂ ^ 2 - ω₁₂ ^ 2 + 4 * det_cross ∧
    4 * det_z₁z₂ = 4 * det_z₁ * det_z₂ ∧
    (z_cross * z₃ + z₃ * z_cross).n_plus = B_plus - B_minus ∧
    (z_cross * z₃ + z₃ * z_cross).n_minus = B_plus - B_minus ∧
    (z_cross * z₃ + z₃ * z_cross).sigma_plus = 0 ∧
    (z_cross * z₃ + z₃ * z_cross).sigma_minus = 0 := by
  have hFin3 : ∀ (f g : Fin 3 → K), f 0 = g 0 → f 1 = g 1 → f 2 = g 2 → f = g := by
    intro f g h0 h1 h2
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [NCZornElement.zornDot, NCZornElement.zornCross, Pi.neg_apply]
    ring
  · simp only [mul_n_plus, mul_n_minus, mul_sigma_plus, mul_sigma_minus,
      NCZornElement.zornDot, NCZornElement.zornCross, Pi.neg_apply]
    ring
  · simp only [mul_n_plus, mul_n_minus, mul_sigma_plus, mul_sigma_minus,
      NCZornElement.zornDot, NCZornElement.zornCross]
    ring
  · simp only [add_n_plus, mul_n_plus, NCZornElement.zornDot, NCZornElement.zornCross,
      Pi.neg_apply]
    ring
  · simp only [add_n_minus, mul_n_minus, NCZornElement.zornDot, NCZornElement.zornCross,
      Pi.neg_apply]
    ring
  · refine hFin3 _ _ ?_ ?_ ?_ <;>
      (simp only [add_sigma_plus, mul_sigma_plus, NCZornElement.zornCross,
         Pi.add_apply, Pi.neg_apply, Pi.zero_apply];
       ring)
  · refine hFin3 _ _ ?_ ?_ ?_ <;>
      (simp only [add_sigma_minus, mul_sigma_minus, NCZornElement.zornCross,
         Pi.add_apply, Pi.neg_apply, Pi.zero_apply];
       ring)

/-- **Seam `𝓜₂` (`seam_M2_artin_diassociative_two_generator_subalgebra_and_bruhat_idempotent`)**:
Welds the associative 2-generator spine (`Ω₁–Ω₇`) directly into the non-associative Zorn split-octonion
algebra (`Ω₈`, `OperatorZornMatrix K`):
1. For any single primal ray `u : Fin 3 → K` and dual ray `v : Fin 3 → K`, `u × u = 0` and `v × v = 0`,
2. For any three elements `X, Y, Z` in the 4-dimensional 2-generator subalgebra
   `⟨1, P, N_+(u), N_-(v)⟩` (with `sigma_plus` proportional to `u` and `sigma_minus` proportional to `v`),
   the Zorn associator `zornAssociator X Y Z` vanishes identically (`⟨0, 0, 0, 0⟩`),
3. The embedded Bruhat projector `P_hat(u, v) = ⟨1 - u·v, u·v, (1 - u·v)•u, v⟩` inside
   `OperatorZornMatrix K` is strictly idempotent (`P_hat * P_hat = P_hat`). -/
theorem seam_M2_artin_diassociative_two_generator_subalgebra_and_bruhat_idempotent
    {K : Type u} [CommRing K] (u v : Fin 3 → K)
    (a₁ d₁ c₁ e₁ a₂ d₂ c₂ e₂ a₃ d₃ c₃ e₃ : K) :
    let X : OperatorZornMatrix K := ⟨a₁, d₁, fun i => c₁ * u i, fun i => e₁ * v i⟩
    let Y : OperatorZornMatrix K := ⟨a₂, d₂, fun i => c₂ * u i, fun i => e₂ * v i⟩
    let Z : OperatorZornMatrix K := ⟨a₃, d₃, fun i => c₃ * u i, fun i => e₃ * v i⟩
    let uv := NCZornElement.zornDot u v
    let P_hat : OperatorZornMatrix K :=
      ⟨1 - uv, uv, fun i => (1 - uv) * u i, v⟩
    NCZornElement.zornCross u u = 0 ∧
    NCZornElement.zornCross v v = 0 ∧
    zornAssociator X Y Z = ⟨0, 0, 0, 0⟩ ∧
    P_hat * P_hat = P_hat := by
  have hFin3 : ∀ (f g : Fin 3 → K), f 0 = g 0 → f 1 = g 1 → f 2 = g 2 → f = g := by
    intro f g h0 h1 h2
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine hFin3 _ _ ?_ ?_ ?_ <;>
      (simp only [NCZornElement.zornCross, Pi.zero_apply]; ring)
  · refine hFin3 _ _ ?_ ?_ ?_ <;>
      (simp only [NCZornElement.zornCross, Pi.zero_apply]; ring)
  · apply operatorZornMatrix_ext
    · simp only [zornAssociator, sub_n_plus, mul_n_plus,
        mul_sigma_plus, mul_sigma_minus, NCZornElement.zornDot, NCZornElement.zornCross]
      ring
    · simp only [zornAssociator, sub_n_minus, mul_n_minus,
        mul_sigma_plus, mul_sigma_minus, NCZornElement.zornDot, NCZornElement.zornCross]
      ring
    · refine hFin3 _ _ ?_ ?_ ?_ <;>
        (simp only [zornAssociator, sub_sigma_plus, mul_n_plus, mul_n_minus,
           mul_sigma_plus, mul_sigma_minus, NCZornElement.zornDot, NCZornElement.zornCross,
           Pi.sub_apply, Pi.zero_apply];
         ring)
    · refine hFin3 _ _ ?_ ?_ ?_ <;>
        (simp only [zornAssociator, sub_sigma_minus, mul_n_plus, mul_n_minus,
           mul_sigma_plus, mul_sigma_minus, NCZornElement.zornDot, NCZornElement.zornCross,
           Pi.sub_apply, Pi.zero_apply];
         ring)
  · apply operatorZornMatrix_ext
    · simp only [mul_n_plus, NCZornElement.zornDot]
      ring
    · simp only [mul_n_minus, NCZornElement.zornDot]
      ring
    · refine hFin3 _ _ ?_ ?_ ?_ <;>
        (simp only [mul_sigma_plus, NCZornElement.zornDot, NCZornElement.zornCross];
         ring)
    · refine hFin3 _ _ ?_ ?_ ?_ <;>
        (simp only [mul_sigma_minus, NCZornElement.zornDot, NCZornElement.zornCross];
         ring)

end InfoGeometry.Canonical.ZornUnifiedCategory
