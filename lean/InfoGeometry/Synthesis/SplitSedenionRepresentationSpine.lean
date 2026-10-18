/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Synthesis.Cl44PrimitiveIdempotentIdeal
import InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis

/-!
# Abstract Derivation Transport and Separate $\mathrm{Cl}(4,4)$ Nambu and Matrix-Ideal Results

The module collects independent finite algebraic results. Section 1 is a generic transport
interface; it is not instantiated here with the split-sedenion $G_2$ derivation family. Section 2
uses the native Clifford carrier `InfoGeometry.Clifford.Cl44`. Section 3 instead uses the matrix
carrier `InfoGeometry.Cl44IdempotentIdeal.Cl44 = Matrix (Fin 16) (Fin 16) ℝ`. No map identifying
these two carriers, or intertwining their products or actions, is established here. In particular,
the matrix right-ideal calculations are separate from the native Clifford Nambu-ideal results.
No classification of all sedenion derivations, 17-dimensional decomposition, or physical
equivalence is claimed.

1. **Section 1 — Abstract Derivation Representation & Intertwiner Spine**:
   - Defines `IsProductDerivation`, `transportedProduct`, `transportOperator`, and `Intertwines`
     for general $\mathbb{R}$-modules equipped with an explicit (possibly non-associative) binary
     operation. The transported operation is constructed from the carrier equivalence; no pre-existing
     product on the target carrier is identified with it.
   - Proves `derivation_transport`, `transport_intertwines`, `intertwines_comp`, commutator
     closure `productDerivation_commutator`, and commutator equivariance
     `transportOperator_commutator`.

2. **Section 2 — Nambu Real Majorana Generators & Left/Right Ideals in the Native Clifford Carrier**:
   - Defines the two-component Nambu doublet `nambuField44` and the real Majorana generators
     `nambuMajoranaPlus` and `nambuMajoranaMinus` in native `Cl44`, proving their recovery of the
     orthonormal generators `e k` and `f k`, their $\pm 1$ square laws, and mutual anticommutation.
   - Proves right annihilation of the four-mode vacuum idempotent by all creation operators
     (`cl44VacuumIdempotent_right_annihilated : cl44VacuumIdempotent * adag k = 0`), defines the
     single-excitation left- and right-ideal Nambu generators `nambuLeftIdealGen` and
     `nambuRightIdealGen`, and proves the left-right contraction identity
     `nambuRightIdealGen_mul_nambuLeftIdealGen`.

3. **Section 3 — Separate Matrix-Model Right Ideal & Left/Right Matrix-Unit Contractions**:
   - In the $16 \times 16$ matrix model `InfoGeometry.Cl44IdempotentIdeal`, defines the principal
     right ideal `RightIdeal`, constructs the 16-dimensional linear isomorphism `rightIdealEquiv`,
     and proves the left-right basis contraction identities `rightIdealBasisMat_mul_leftIdealBasisMat`
     and `leftRightDyad_mul_leftIdealBasisMat`.
-/

set_option autoImplicit false
noncomputable section

namespace InfoGeometry.Synthesis.SplitSedenionRepresentationSpine

universe u v

/-!
## Section 1: Abstract Derivation Representation & Intertwiner Spine
-/

/-- A linear map satisfying the Leibniz law for a possibly nonassociative binary operation.
Additivity or bilinearity of the operation is not part of this predicate. -/
def IsProductDerivation
    {A : Type u} [AddCommGroup A] [Module ℝ A]
    (mulA : A → A → A) (D : A →ₗ[ℝ] A) : Prop :=
  ∀ x y, D (mulA x y) = mulA (D x) y + mulA x (D y)

/-- Conjugate a derivation by a linear equivalence of carriers.
The target multiplication is *transported*, not presumed to coincide
with a pre-existing associative product. -/
def transportedProduct
    {A : Type u} {B : Type v}
    [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B]
    (e : A ≃ₗ[ℝ] B) (mulA : A → A → A)
    (x y : B) : B :=
  e (mulA (e.symm x) (e.symm y))

/-- The conjugated operator on a second carrier. -/
def transportOperator
    {A : Type u} {B : Type v}
    [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B]
    (e : A ≃ₗ[ℝ] B) (D : A →ₗ[ℝ] A) : B →ₗ[ℝ] B :=
  e.toLinearMap.comp (D.comp e.symm.toLinearMap)

/-- Leibniz maps survive an exact change of linear carrier when the operation is transported. -/
theorem derivation_transport
    {A : Type u} {B : Type v}
    [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B]
    (e : A ≃ₗ[ℝ] B) (mulA : A → A → A)
    (D : A →ₗ[ℝ] A)
    (hD : IsProductDerivation mulA D) :
    IsProductDerivation (transportedProduct e mulA)
      (transportOperator e D) := by
  intro x y
  dsimp [transportedProduct, transportOperator]
  rw [e.symm_apply_apply, hD (e.symm x) (e.symm y), map_add,
    e.symm_apply_apply, e.symm_apply_apply]

/-- An intertwiner equation is the exact condition for two descriptions
to realize the same given derivation action. -/
def Intertwines
    {A : Type u} {B : Type v}
    [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B]
    (T : A →ₗ[ℝ] B)
    (DA : A →ₗ[ℝ] A) (DB : B →ₗ[ℝ] B) : Prop :=
  ∀ x, T (DA x) = DB (T x)

/-- Carrier transport provides a canonical intertwiner. -/
theorem transport_intertwines
    {A : Type u} {B : Type v}
    [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B]
    (e : A ≃ₗ[ℝ] B) (D : A →ₗ[ℝ] A) :
    Intertwines e.toLinearMap D (transportOperator e D) := by
  intro x
  simp [transportOperator]

/-- Operator intertwining is closed under composition of linear maps. -/
theorem intertwines_comp
    {A : Type u} {B : Type v} {C : Type*}
    [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B]
    [AddCommGroup C] [Module ℝ C]
    (T : A →ₗ[ℝ] B) (U : B →ₗ[ℝ] C)
    (DA : A →ₗ[ℝ] A) (DB : B →ₗ[ℝ] B)
    (DC : C →ₗ[ℝ] C)
    (hT : Intertwines T DA DB)
    (hU : Intertwines U DB DC) :
    Intertwines (U.comp T) DA DC := by
  intro x
  change U (T (DA x)) = DC (U (T x))
  rw [hT x, hU (T x)]

/-- Commutator closure of linear product derivations for any additive product `mulA`. -/
theorem productDerivation_commutator
    {A : Type u} [AddCommGroup A] [Module ℝ A]
    (mulA : A → A → A)
    (h_add_left : ∀ x y z, mulA (x + y) z = mulA x z + mulA y z)
    (h_add_right : ∀ x y z, mulA x (y + z) = mulA x y + mulA x z)
    (D₁ D₂ : A →ₗ[ℝ] A)
    (hD₁ : IsProductDerivation mulA D₁)
    (hD₂ : IsProductDerivation mulA D₂) :
    IsProductDerivation mulA (D₁.comp D₂ - D₂.comp D₁) := by
  have h_sub_left : ∀ u v w, mulA (u - v) w = mulA u w - mulA v w := by
    intro u v w
    apply eq_sub_of_add_eq
    rw [← h_add_left (u - v) v w, sub_add_cancel]
  have h_sub_right : ∀ u v w, mulA u (v - w) = mulA u v - mulA u w := by
    intro u v w
    apply eq_sub_of_add_eq
    rw [← h_add_right u (v - w) w, sub_add_cancel]
  intro x y
  dsimp [LinearMap.sub_apply, LinearMap.comp_apply]
  rw [hD₂ x y, hD₁ x y, map_add, map_add,
    hD₁ (D₂ x) y, hD₁ x (D₂ y), hD₂ (D₁ x) y, hD₂ x (D₁ y),
    h_sub_left, h_sub_right]
  abel

/-- Carrier transport preserves the commutator of two linear operators. -/
theorem transportOperator_commutator
    {A : Type u} {B : Type v}
    [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B]
    (e : A ≃ₗ[ℝ] B) (D₁ D₂ : A →ₗ[ℝ] A) :
    transportOperator e (D₁.comp D₂ - D₂.comp D₁) =
      (transportOperator e D₁).comp (transportOperator e D₂) -
        (transportOperator e D₂).comp (transportOperator e D₁) := by
  ext x
  simp [transportOperator]

/-!
## Section 2: Nambu Real Majorana Generators & Left/Right Ideal Generators in $\mathrm{Cl}(4,4)$
-/

open InfoGeometry
open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Cl44IdempotentIdeal
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis

/-- Vector-level recovery of the positive basis vector `eVec k` from `aVec k + adagVec k`. -/
theorem aVec_add_adagVec (k : Fin 4) : aVec k + adagVec k = eVec k := by
  ext i
  simp only [aVec, adagVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Vector-level recovery of the negative basis vector `fVec k` from `aVec k - adagVec k`. -/
theorem aVec_sub_adagVec (k : Fin 4) : aVec k - adagVec k = fVec k := by
  ext i
  simp only [aVec, adagVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Sum of the $k$-th Witt annihilation and creation operators in $\mathrm{Cl}(4,4)$ recovers `e k`. -/
theorem a_add_adag (k : Fin 4) : a k + adag k = e k := by
  change CliffordAlgebra.ι splitQ44 (aVec k) + CliffordAlgebra.ι splitQ44 (adagVec k) =
    CliffordAlgebra.ι splitQ44 (eVec k)
  rw [← map_add (CliffordAlgebra.ι splitQ44) (aVec k) (adagVec k), aVec_add_adagVec k]

/-- Difference of the $k$-th Witt annihilation and creation operators in $\mathrm{Cl}(4,4)$ recovers `f k`. -/
theorem a_sub_adag (k : Fin 4) : a k - adag k = f k := by
  change CliffordAlgebra.ι splitQ44 (aVec k) - CliffordAlgebra.ι splitQ44 (adagVec k) =
    CliffordAlgebra.ι splitQ44 (fVec k)
  rw [← map_sub (CliffordAlgebra.ι splitQ44) (aVec k) (adagVec k), aVec_sub_adagVec k]

/-- Two-component Nambu doublet $\Psi_k = (a_k, a_k^\dagger)$ in $\mathrm{Cl}(4,4)$ for mode $k \in \mathrm{Fin}\, 4$. -/
def nambuField44 (k : Fin 4) : Fin 2 → InfoGeometry.Clifford.Cl44
  | 0 => a k
  | 1 => adag k

/-- Positive-square real Majorana generator $\gamma_k^+ = \Psi_{k,0} + \Psi_{k,1} = a_k + a_k^\dagger$
recovered from the Nambu doublet in $\mathrm{Cl}(4,4)$. -/
def nambuMajoranaPlus (k : Fin 4) : InfoGeometry.Clifford.Cl44 :=
  nambuField44 k 0 + nambuField44 k 1

/-- Negative-square real Majorana generator $\gamma_k^- = \Psi_{k,0} - \Psi_{k,1} = a_k - a_k^\dagger$
recovered from the Nambu doublet in $\mathrm{Cl}(4,4)$. -/
def nambuMajoranaMinus (k : Fin 4) : InfoGeometry.Clifford.Cl44 :=
  nambuField44 k 0 - nambuField44 k 1

/-- The positive Nambu Majorana operator $\gamma_k^+$ coincides with the orthonormal generator $e_k$. -/
theorem nambuMajoranaPlus_eq_e (k : Fin 4) : nambuMajoranaPlus k = e k := by
  exact a_add_adag k

/-- The negative Nambu Majorana operator $\gamma_k^-$ coincides with the orthonormal generator $f_k$. -/
theorem nambuMajoranaMinus_eq_f (k : Fin 4) : nambuMajoranaMinus k = f k := by
  exact a_sub_adag k

/-- Every positive Nambu Majorana operator squares to $+1$ in $\mathrm{Cl}(4,4)$. -/
theorem nambuMajoranaPlus_sq (k : Fin 4) :
    nambuMajoranaPlus k * nambuMajoranaPlus k = 1 := by
  rw [nambuMajoranaPlus_eq_e k]
  exact e_sq k

/-- Every negative Nambu Majorana operator squares to $-1$ in $\mathrm{Cl}(4,4)$. -/
theorem nambuMajoranaMinus_sq (k : Fin 4) :
    nambuMajoranaMinus k * nambuMajoranaMinus k = -(1 : InfoGeometry.Clifford.Cl44) := by
  rw [nambuMajoranaMinus_eq_f k]
  exact f_sq k

/-- Positive and negative Nambu Majorana operators anticommute across all modes $j, k \in \mathrm{Fin}\, 4$. -/
theorem nambuMajorana_anticomm (j k : Fin 4) :
    nambuMajoranaPlus j * nambuMajoranaMinus k +
      nambuMajoranaMinus k * nambuMajoranaPlus j = 0 := by
  rw [nambuMajoranaPlus_eq_e j, nambuMajoranaMinus_eq_f k]
  exact e_mul_f_add_swap j k

/-- Right multiplication by $a_k^\dagger$ annihilates the $k$-th mode projector $P_k = a_k a_k^\dagger$. -/
theorem wittModeProj_mul_adag_self (k : Fin 4) :
    wittModeProj k * adag k = 0 := by
  change (a k * adag k) * adag k = 0
  rw [mul_assoc, adag_sq_zero k, mul_zero]

/-- A creation generator $a_j^\dagger$ commutes with a Witt mode projector $P_i = a_i a_i^\dagger$
belonging to a distinct mode $i \neq j$. -/
theorem creation_commute_wittModeProj {i j : Fin 4} (hij : i ≠ j) :
    wittModeProj i * adag j = adag j * wittModeProj i := by
  have hdd : adag i * adag j = -(adag j * adag i) :=
    eq_neg_of_add_eq_zero_left (witt_creation_anticomm i j)
  have had : a i * adag j = -(adag j * a i) :=
    eq_neg_of_add_eq_zero_left (witt_CAR_ne i j hij)
  dsimp [wittModeProj]
  change (a i * adag i) * adag j = adag j * (a i * adag i)
  calc
    (a i * adag i) * adag j = a i * (adag i * adag j) := by rw [mul_assoc]
    _ = a i * -(adag j * adag i) := by rw [hdd]
    _ = -(a i * adag j) * adag i := by noncomm_ring
    _ = -(-(adag j * a i)) * adag i := by rw [had]
    _ = adag j * (a i * adag i) := by noncomm_ring

/-- Every creation generator $a_k^\dagger$ right-annihilates the four-mode vacuum idempotent
$f = P_0 P_1 P_2 P_3$. -/
theorem cl44VacuumIdempotent_right_annihilated (k : Fin 4) :
    cl44VacuumIdempotent * adag k = 0 := by
  fin_cases k
  · have hd := wittModeProj_mul_adag_self 0
    have h1 := creation_commute_wittModeProj (i := 1) (j := 0) (by decide)
    have h2 := creation_commute_wittModeProj (i := 2) (j := 0) (by decide)
    have h3 := creation_commute_wittModeProj (i := 3) (j := 0) (by decide)
    calc
      cl44VacuumIdempotent * adag 0 =
          wittModeProj 0 * wittModeProj 1 * wittModeProj 2 * (wittModeProj 3 * adag 0) := by
        unfold cl44VacuumIdempotent; noncomm_ring
      _ = wittModeProj 0 * wittModeProj 1 * (wittModeProj 2 * adag 0) * wittModeProj 3 := by
        rw [h3]; noncomm_ring
      _ = wittModeProj 0 * (wittModeProj 1 * adag 0) * wittModeProj 2 * wittModeProj 3 := by
        rw [h2]; noncomm_ring
      _ = (wittModeProj 0 * adag 0) * wittModeProj 1 * wittModeProj 2 * wittModeProj 3 := by
        rw [h1]; noncomm_ring
      _ = 0 := by
        rw [hd]; noncomm_ring
  · have hd := wittModeProj_mul_adag_self 1
    have h2 := creation_commute_wittModeProj (i := 2) (j := 1) (by decide)
    have h3 := creation_commute_wittModeProj (i := 3) (j := 1) (by decide)
    calc
      cl44VacuumIdempotent * adag 1 =
          wittModeProj 0 * wittModeProj 1 * wittModeProj 2 * (wittModeProj 3 * adag 1) := by
        unfold cl44VacuumIdempotent; noncomm_ring
      _ = wittModeProj 0 * wittModeProj 1 * (wittModeProj 2 * adag 1) * wittModeProj 3 := by
        rw [h3]; noncomm_ring
      _ = wittModeProj 0 * (wittModeProj 1 * adag 1) * wittModeProj 2 * wittModeProj 3 := by
        rw [h2]; noncomm_ring
      _ = 0 := by
        rw [hd]; noncomm_ring
  · have hd := wittModeProj_mul_adag_self 2
    have h3 := creation_commute_wittModeProj (i := 3) (j := 2) (by decide)
    calc
      cl44VacuumIdempotent * adag 2 =
          wittModeProj 0 * wittModeProj 1 * wittModeProj 2 * (wittModeProj 3 * adag 2) := by
        unfold cl44VacuumIdempotent; noncomm_ring
      _ = wittModeProj 0 * wittModeProj 1 * (wittModeProj 2 * adag 2) * wittModeProj 3 := by
        rw [h3]; noncomm_ring
      _ = 0 := by
        rw [hd]; noncomm_ring
  · have hd := wittModeProj_mul_adag_self 3
    calc
      cl44VacuumIdempotent * adag 3 =
          wittModeProj 0 * wittModeProj 1 * wittModeProj 2 * (wittModeProj 3 * adag 3) := by
        unfold cl44VacuumIdempotent; noncomm_ring
      _ = 0 := by
        rw [hd]; noncomm_ring

/-- Single-excitation Nambu generator $a_k^\dagger f$ in the left principal ideal $\mathrm{Cl}(4,4) f$. -/
def nambuLeftIdealGen (k : Fin 4) : InfoGeometry.Clifford.Cl44 :=
  adag k * cl44VacuumIdempotent

/-- Single-excitation Nambu generator $f a_k$ in the right principal ideal $f \mathrm{Cl}(4,4)$. -/
def nambuRightIdealGen (k : Fin 4) : InfoGeometry.Clifford.Cl44 :=
  cl44VacuumIdempotent * a k

/-- Every single-excitation Nambu left generator `nambuLeftIdealGen k` belongs to `cl44LeftPrincipalIdeal`. -/
theorem nambuLeftIdealGen_mem_leftIdeal (k : Fin 4) :
    nambuLeftIdealGen k ∈ cl44LeftPrincipalIdeal :=
  ⟨adag k, rfl⟩

/-- Every single-excitation Nambu right generator `nambuRightIdealGen k` belongs to `cl44RightPrincipalIdeal`. -/
theorem nambuRightIdealGen_mem_rightIdeal (k : Fin 4) :
    nambuRightIdealGen k ∈ cl44RightPrincipalIdeal :=
  ⟨a k, rfl⟩

/-- **Left-Right Nambu Ideal Contraction Theorem**:
Contracting the $j$-th right-ideal Nambu generator $f a_j$ with the $k$-th left-ideal Nambu
generator $a_k^\dagger f$ yields $\delta_{j,k} f$ in the vacuum corner $f \mathrm{Cl}(4,4) f$. -/
theorem nambuRightIdealGen_mul_nambuLeftIdealGen (j k : Fin 4) :
    nambuRightIdealGen j * nambuLeftIdealGen k =
      if j = k then cl44VacuumIdempotent else 0 := by
  unfold nambuRightIdealGen nambuLeftIdealGen
  have hcar : a j * adag k = (if j = k then 1 else 0) - adag k * a j :=
    eq_sub_of_add_eq (witt_CAR j k)
  have h_right_ann : cl44VacuumIdempotent * adag k = 0 :=
    cl44VacuumIdempotent_right_annihilated k
  have h_left_ann : a j * cl44VacuumIdempotent = 0 :=
    cl44VacuumIdempotent_annihilated j
  have h_reorder :
      (cl44VacuumIdempotent * a j) * (adag k * cl44VacuumIdempotent) =
        cl44VacuumIdempotent * (if j = k then 1 else 0) * cl44VacuumIdempotent := by
    calc
      (cl44VacuumIdempotent * a j) * (adag k * cl44VacuumIdempotent) =
          cl44VacuumIdempotent * (a j * adag k) * cl44VacuumIdempotent := by noncomm_ring
      _ = cl44VacuumIdempotent * ((if j = k then 1 else 0) - adag k * a j) *
            cl44VacuumIdempotent := by rw [hcar]
      _ = cl44VacuumIdempotent * (if j = k then 1 else 0) * cl44VacuumIdempotent -
            (cl44VacuumIdempotent * adag k) * (a j * cl44VacuumIdempotent) := by noncomm_ring
      _ = cl44VacuumIdempotent * (if j = k then 1 else 0) * cl44VacuumIdempotent -
            0 * 0 := by rw [h_right_ann, h_left_ann]
      _ = cl44VacuumIdempotent * (if j = k then 1 else 0) * cl44VacuumIdempotent := by
        noncomm_ring
  rw [h_reorder]
  by_cases hjk : j = k
  · simp [hjk, cl44VacuumIdempotent_idempotent]
  · simp [hjk]

/-!
### Separate Matrix-Model Right Ideal & Left-Right Basis Contractions in $M_{16}(\mathbb{R})$
-/

/-- The first Witt annihilation matrix in `Matrix (Fin 16) (Fin 16) ℝ`. -/
def uWitt0Mat : Matrix (Fin 16) (Fin 16) ℝ :=
  InfoGeometry.Cl44IdempotentIdeal.uWitt0

/-- The first Witt creation matrix in `Matrix (Fin 16) (Fin 16) ℝ`. -/
def vWitt0Mat : Matrix (Fin 16) (Fin 16) ℝ :=
  InfoGeometry.Cl44IdempotentIdeal.vWitt0

/-- Non-commutativity of the first Witt annihilation and creation matrices in
`Matrix (Fin 16) (Fin 16) ℝ`. -/
theorem uWitt0_mul_vWitt0_ne_comm :
    uWitt0Mat * vWitt0Mat ≠ vWitt0Mat * uWitt0Mat :=
  InfoGeometry.Cl44IdempotentIdeal.uWitt0_mul_vWitt0_ne_comm

/-- Left multiplication by `f` as an $\mathbb{R}$-linear map on `Cl44IdempotentIdeal.Cl44`. -/
def mulLeftMap (f : Cl44IdempotentIdeal.Cl44) :
    Cl44IdempotentIdeal.Cl44 →ₗ[ℝ] Cl44IdempotentIdeal.Cl44 where
  toFun M := f * M
  map_add' M N := Matrix.mul_add f M N
  map_smul' c M := Matrix.mul_smul f c M

/-- The principal right ideal $f \cdot M_{16}(\mathbb{R}) = \operatorname{range}(L_f)$ in the matrix model. -/
def RightIdeal (f : Cl44IdempotentIdeal.Cl44) : Submodule ℝ Cl44IdempotentIdeal.Cl44 :=
  LinearMap.range (mulLeftMap f)

/-- Every matrix `X` in `RightIdeal primIdem` vanishes outside row `0`. -/
lemma rightIdeal_row_zero (X : Cl44IdempotentIdeal.Cl44) (hX : X ∈ RightIdeal primIdem)
    (i j : Fin 16) (hi : i ≠ 0) : X i j = 0 := by
  rcases hX with ⟨M, rfl⟩
  dsimp [mulLeftMap]
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _
  unfold primIdem
  have hnot : ¬(i = 0 ∧ m = 0) := fun h => hi h.1
  simp [hnot]

/-- Every matrix `X` in `RightIdeal primIdem` is supported on row `0`. -/
lemma rightIdeal_val_eq (X : Cl44IdempotentIdeal.Cl44) (hX : X ∈ RightIdeal primIdem)
    (i j : Fin 16) : X i j = if i = 0 then X 0 j else 0 := by
  by_cases hi : i = 0
  · subst hi; simp
  · rw [rightIdeal_row_zero X hX i j hi]; simp [hi]

/-- Projection from `RightIdeal f` to the 16-component co-spinor covector (row `0`). -/
def toCoSpinor (f : Cl44IdempotentIdeal.Cl44) :
    RightIdeal f →ₗ[ℝ] (Fin 16 → ℝ) where
  toFun X j := X.1 0 j
  map_add' _ _ := by ext j; rfl
  map_smul' _ _ := by ext j; rfl

/-- Embedding a 16-component co-spinor covector `v : Fin 16 → ℝ` into row `0` of a $16 \times 16$ matrix. -/
def fromCoSpinorMat (v : Fin 16 → ℝ) : Cl44IdempotentIdeal.Cl44 :=
  fun i j => if i = 0 then v j else 0

/-- Every row-0 co-spinor matrix `fromCoSpinorMat v` belongs to `RightIdeal primIdem`. -/
theorem fromCoSpinorMat_mem_rightIdeal (v : Fin 16 → ℝ) :
    fromCoSpinorMat v ∈ RightIdeal primIdem := by
  use fromCoSpinorMat v
  dsimp [mulLeftMap]
  ext i j
  rw [Matrix.mul_apply]
  have h_zero : ∀ m : Fin 16, m ≠ 0 → primIdem i m * fromCoSpinorMat v m j = 0 := by
    intro m hm
    unfold primIdem
    have hnot : ¬(i = 0 ∧ m = 0) := fun h => hm h.2
    simp [hnot]
  rw [Finset.sum_eq_single 0]
  · by_cases hi : i = 0 <;> simp [primIdem, fromCoSpinorMat, hi]
  · intro m _ hm
    exact h_zero m hm
  · intro h0
    exact False.elim (h0 (Finset.mem_univ 0))

/-- Linear reconstruction map from `Fin 16 → ℝ` into `RightIdeal primIdem`. -/
def fromCoSpinor : (Fin 16 → ℝ) →ₗ[ℝ] RightIdeal primIdem where
  toFun v := ⟨fromCoSpinorMat v, fromCoSpinorMat_mem_rightIdeal v⟩
  map_add' _ _ := by
    ext i j
    dsimp [fromCoSpinorMat]
    split_ifs <;> ring
  map_smul' _ _ := by
    ext i j
    dsimp [fromCoSpinorMat]
    split_ifs <;> ring

/-- Constructive 16-dimensional $\mathbb{R}$-linear equivalence between `RightIdeal primIdem`
and `Fin 16 → ℝ`. -/
def rightIdealEquiv : RightIdeal primIdem ≃ₗ[ℝ] (Fin 16 → ℝ) where
  toFun := toCoSpinor primIdem
  invFun := fromCoSpinor
  left_inv := by
    intro ⟨X, hX⟩
    ext i j
    dsimp [toCoSpinor, fromCoSpinor, fromCoSpinorMat]
    exact (rightIdeal_val_eq X hX i j).symm
  right_inv := by
    intro v
    ext j
    dsimp [toCoSpinor, fromCoSpinor, fromCoSpinorMat]
  map_add' := (toCoSpinor primIdem).map_add
  map_smul' := (toCoSpinor primIdem).map_smul

/-- Elementary column-0 basis matrix $E_{i,0} \in \mathcal{S}_L$ for $i \in \mathrm{Fin}\, 16$. -/
def leftIdealBasisMat (i : Fin 16) : Cl44IdempotentIdeal.Cl44 :=
  fun r c => if r = i ∧ c = 0 then 1 else 0

/-- Elementary row-0 basis matrix $E_{0,j} \in \mathcal{S}_R$ for $j \in \mathrm{Fin}\, 16$. -/
def rightIdealBasisMat (j : Fin 16) : Cl44IdempotentIdeal.Cl44 :=
  fun r c => if r = 0 ∧ c = j then 1 else 0

/-- Right multiplication by `primIdem` fixes every left-ideal basis generator `leftIdealBasisMat i`. -/
theorem leftIdealBasisMat_mul_primIdem (i : Fin 16) :
    leftIdealBasisMat i * primIdem = leftIdealBasisMat i := by
  ext r c
  rw [Matrix.mul_apply, Finset.sum_eq_single 0]
  · by_cases hr : r = i <;> by_cases hc : c = 0 <;>
      simp [leftIdealBasisMat, primIdem, hr, hc]
  · intro m _ hm
    simp [primIdem, hm]
  · intro h0
    exact False.elim (h0 (Finset.mem_univ 0))

/-- Contraction of a right-ideal basis generator $E_{0,j}$ with a left-ideal basis generator $E_{i,0}$
lands in the scalar corner $\mathbb{R} \cdot E_{0,0}$: $E_{0,j} E_{i,0} = \delta_{i,j} f$. -/
theorem rightIdealBasisMat_mul_leftIdealBasisMat (j i : Fin 16) :
    rightIdealBasisMat j * leftIdealBasisMat i = if i = j then primIdem else 0 := by
  ext r c
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · by_cases hij : i = j
    · by_cases hr : r = 0 <;> by_cases hc : c = 0 <;>
        simp [rightIdealBasisMat, leftIdealBasisMat, primIdem, hij, hr, hc]
    · simp [rightIdealBasisMat, leftIdealBasisMat, hij]
  · intro m _ hmi
    simp [leftIdealBasisMat, hmi]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- The rank-1 left-right dyad $E_{i,0} E_{0,j} = E_{i,j}$ acts on the left-ideal basis
$E_{m,0}$ as the elementary matrix unit transition $E_{m,0} \mapsto \delta_{j,m} E_{i,0}$. -/
theorem leftRightDyad_mul_leftIdealBasisMat (i j m : Fin 16) :
    (leftIdealBasisMat i * rightIdealBasisMat j) * leftIdealBasisMat m =
      if j = m then leftIdealBasisMat i else 0 := by
  rw [Matrix.mul_assoc, rightIdealBasisMat_mul_leftIdealBasisMat j m]
  by_cases hjm : j = m
  · subst hjm
    simp [leftIdealBasisMat_mul_primIdem i]
  · have hmj : m ≠ j := fun h => hjm h.symm
    simp [hjm, hmj]

end InfoGeometry.Synthesis.SplitSedenionRepresentationSpine
