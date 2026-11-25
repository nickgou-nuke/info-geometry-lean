/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Algebra.H3ZornCarrierBasis
import InfoGeometry.Algebra.SplitAlbertF4BasisTrace
import InfoGeometry.Canonical.H3ZornF4BasisExactSpan

/-!
# Split-Albert `F₄` derivation dimension and Peirce–triality closure

This module closes debt `D18_h3zorn_split_f4` constructively for the verified
real split Albert Jordan algebra `H3Zorn ℝ`:

1. Coordinates, split `(4,4)` bilinear pairing `zornBilin`, and the 28-dimensional
   skew-adjoint Lie subalgebra `zornSkewAdjoint` (`so(4,4)`) on `ZornVectorMatrix ℝ`.
2. Exact Peirce multiplication identities for `h3_diag₁`, `h3_diag₂`, `h3_diag₃`
   and off-diagonal slots `mkOff12`, `mkOff23`, `mkOff31` under the installed Jordan
   product `*` (`candidateJordanMul`).
3. Surjective Peirce evaluation map `peirceEval : H3ZornF4Derivations →ₗ[ℝ] (Zorn × (Zorn × Zorn))`
   with explicit inner-derivation section `peirceSection` spanning the 24D shift sector.
4. Constructive Lie/linear equivalence `stabilizerEquivSO44 : LinearMap.ker peirceEval ≃ₗ[ℝ] zornSkewAdjoint`
   showing the idempotent stabilizer is exact 28-dimensional `so(4,4)` via the split-octonion
   trace-zero right nucleus theorem (`zorn_right_nucleus_trace_zero_eq_zero`) and inner rank-2
   lifting (`liftSO44ToKer`).
5. Main theorems:
   * `finrank_H3ZornF4Derivations : Module.finrank ℝ H3ZornF4Derivations = 52`
   * `f4BasisSpan_eq_H3ZornF4Derivations : f4BasisSpan = H3ZornF4Derivations.toSubmodule`
   * `f4Basis_linearIndependent : LinearIndependent ℝ (fun i : Fin 52 => (f4Basis i).1)`
   * `shiftSubmodule_sup_trialitySubmodule` and `disjoint_shiftSubmodule_trialitySubmodule`
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.SplitAlbertF4DimensionClosure

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

abbrev Zorn := ZornVectorMatrix ℝ
abbrev H3 := H3Zorn ℝ
abbrev EndH3 := Module.End ℝ H3

/-! ## 1. 8D `ZornVectorMatrix ℝ` coordinates, split `(4,4)` pairing, and `so(4,4)` -/

/-- Coordinate map from `ZornVectorMatrix ℝ` to `Fin 8 → ℝ`. -/
def zornCoord : Zorn →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun x := ![x.a, x.v 0, x.v 1, x.v 2, x.w 0, x.w 1, x.w 2, x.b]
  map_add' x y := by
    ext i
    fin_cases i <;> rfl
  map_smul' r x := by
    ext i
    fin_cases i <;> rfl

/-- Reconstruction map from `Fin 8 → ℝ` to `ZornVectorMatrix ℝ`. -/
def zornReconstruct : (Fin 8 → ℝ) →ₗ[ℝ] Zorn where
  toFun v :=
    ⟨v 0,
     fun i => if i = 0 then v 1 else if i = 1 then v 2 else v 3,
     fun i => if i = 0 then v 4 else if i = 1 then v 5 else v 6,
     v 7⟩
  map_add' u v := by
    apply ZornVectorMatrix.ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  map_smul' r v := by
    apply ZornVectorMatrix.ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · rfl

@[simp] theorem zornCoord_zornReconstruct (v : Fin 8 → ℝ) :
    zornCoord (zornReconstruct v) = v := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem zornReconstruct_zornCoord (x : Zorn) :
    zornReconstruct (zornCoord x) = x := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · rfl

/-- Linear equivalence `ZornVectorMatrix ℝ ≃ₗ[ℝ] (Fin 8 → ℝ)`. -/
def zornCoordEquiv : Zorn ≃ₗ[ℝ] (Fin 8 → ℝ) :=
  LinearEquiv.ofLinearMap zornCoord zornReconstruct
    (LinearMap.ext zornCoord_zornReconstruct)
    (LinearMap.ext zornReconstruct_zornCoord)

instance : Module.Finite ℝ Zorn :=
  Module.Finite.equiv zornCoordEquiv.symm

theorem finrank_zorn : Module.finrank ℝ Zorn = 8 := by
  rw [zornCoordEquiv.finrank_eq, Module.finrank_fin_fun]

theorem zorn_eq_sum_basis (x : Zorn) :
    x = ∑ i : Fin 8, zornCoord x i • zorn_basis i := by
  rw [Fin.sum_univ_eight]
  apply ZornVectorMatrix.ext
  · simp [zornCoord, zorn_basis]
  · funext j; fin_cases j <;> simp [zornCoord, zorn_basis]
  · funext j; fin_cases j <;> simp [zornCoord, zorn_basis]
  · simp [zornCoord, zorn_basis]

/-- Composition-algebra split `(4,4)` bilinear pairing `B(x, y) = tr(x * conj y)`. -/
def zornBilin (x y : Zorn) : ℝ :=
  ZornVectorMatrix.trace (ZornVectorMatrix.mul x (ZornVectorMatrix.conj y))

theorem zornBilin_eq_coords (x y : Zorn) :
    zornBilin x y =
      x.a * y.b + x.b * y.a -
        (x.v 0 * y.w 0 + x.v 1 * y.w 1 + x.v 2 * y.w 2 +
         x.w 0 * y.v 0 + x.w 1 * y.v 1 + x.w 2 * y.v 2) := by
  simp [zornBilin, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVec3.dot, Fin.sum_univ_three]
  ring

theorem zornBilin_symm (x y : Zorn) : zornBilin x y = zornBilin y x := by
  rw [zornBilin_eq_coords, zornBilin_eq_coords]
  ring

@[simp] theorem zornBilin_zero_left (y : Zorn) : zornBilin 0 y = 0 := by
  simp [zornBilin_eq_coords]

@[simp] theorem zornBilin_zero_left' (y : Zorn) : zornBilin ZornVectorMatrix.zero y = 0 :=
  zornBilin_zero_left y

@[simp] theorem zornBilin_zero_right (x : Zorn) : zornBilin x 0 = 0 := by
  simp [zornBilin_eq_coords]

@[simp] theorem zornBilin_zero_right' (x : Zorn) : zornBilin x ZornVectorMatrix.zero = 0 :=
  zornBilin_zero_right x

theorem zornBilin_add_left (x₁ x₂ y : Zorn) :
    zornBilin (x₁ + x₂) y = zornBilin x₁ y + zornBilin x₂ y := by
  simp only [zornBilin_eq_coords, ZornVectorMatrix.add_a', ZornVectorMatrix.add_v',
    ZornVectorMatrix.add_w', ZornVectorMatrix.add_b']
  ring

theorem zornBilin_add_right (x y₁ y₂ : Zorn) :
    zornBilin x (y₁ + y₂) = zornBilin x y₁ + zornBilin x y₂ := by
  rw [zornBilin_symm x (y₁ + y₂), zornBilin_add_left, zornBilin_symm y₁ x, zornBilin_symm y₂ x]

theorem zornBilin_smul_left (r : ℝ) (x y : Zorn) :
    zornBilin (r • x) y = r * zornBilin x y := by
  simp only [zornBilin_eq_coords, ZornVectorMatrix.smul_a', ZornVectorMatrix.smul_v',
    ZornVectorMatrix.smul_w', ZornVectorMatrix.smul_b']
  ring

theorem zornBilin_smul_right (r : ℝ) (x y : Zorn) :
    zornBilin x (r • y) = r * zornBilin x y := by
  rw [zornBilin_symm x (r • y), zornBilin_smul_left, zornBilin_symm y x]

theorem zornBilin_sub_left (x₁ x₂ y : Zorn) :
    zornBilin (x₁ - x₂) y = zornBilin x₁ y - zornBilin x₂ y := by
  rw [sub_eq_add_neg, zornBilin_add_left, ← neg_one_smul ℝ x₂, zornBilin_smul_left]
  ring

theorem zornBilin_sub_right (x y₁ y₂ : Zorn) :
    zornBilin x (y₁ - y₂) = zornBilin x y₁ - zornBilin x y₂ := by
  rw [zornBilin_symm x (y₁ - y₂), zornBilin_sub_left, zornBilin_symm y₁ x, zornBilin_symm y₂ x]

theorem zornBilin_sum_left {ι : Type*} (s : Finset ι) (f : ι → Zorn) (y : Zorn) :
    zornBilin (∑ i ∈ s, f i) y = ∑ i ∈ s, zornBilin (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, zornBilin_add_left, ih, Finset.sum_insert ha]

theorem zornBilin_sum_right {ι : Type*} (x : Zorn) (s : Finset ι) (f : ι → Zorn) :
    zornBilin x (∑ i ∈ s, f i) = ∑ i ∈ s, zornBilin x (f i) := by
  rw [zornBilin_symm, zornBilin_sum_left]
  refine Finset.sum_congr rfl fun i _ => zornBilin_symm (f i) x

theorem zornBilin_self (x : Zorn) :
    zornBilin x x = 2 * ZornVectorMatrix.norm x := by
  simp [zornBilin_eq_coords, ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_three]
  ring

theorem zornBilin_one_right (x : Zorn) :
    zornBilin x ZornVectorMatrix.one = ZornVectorMatrix.trace x := by
  simp [zornBilin_eq_coords, ZornVectorMatrix.one, ZornVectorMatrix.trace]

/-- Index involution swapping split dual pairs `(0↔7, 1↔4, 2↔5, 3↔6)`. -/
def zornDualIdx : Fin 8 → Fin 8
  | 0 => 7
  | 1 => 4
  | 2 => 5
  | 3 => 6
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | 7 => 0

/-- Sign matching the `(+, +, +, +, -, -, -, -)` split pairing on `zorn_basis`. -/
def zornDualSign : Fin 8 → ℝ
  | 0 => 1
  | 7 => 1
  | _ => -1

/-- Exact `zornBilin`-dual basis of `zorn_basis`. -/
def zornDualBasis (i : Fin 8) : Zorn :=
  zornDualSign i • zorn_basis (zornDualIdx i)

@[simp] theorem zornBilin_basis_dualBasis (i j : Fin 8) :
    zornBilin (zorn_basis i) (zornDualBasis j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [zornBilin_eq_coords, zornDualBasis, zornDualIdx, zornDualSign, zorn_basis,
      ZornVectorMatrix.neg]

@[simp] theorem zornBilin_dualBasis_basis (i j : Fin 8) :
    zornBilin (zornDualBasis i) (zorn_basis j) = if i = j then 1 else 0 := by
  rw [zornBilin_symm, zornBilin_basis_dualBasis]
  simp [eq_comm]

theorem zornCoord_eq_zornBilin_dualBasis (x : Zorn) (i : Fin 8) :
    zornCoord x i = zornBilin (zornDualBasis i) x := by
  fin_cases i <;>
    simp [zornCoord, zornBilin_eq_coords, zornDualBasis, zornDualIdx, zornDualSign, zorn_basis,
      ZornVectorMatrix.neg] <;>
    ring

theorem zorn_eq_zero_of_forall_zornBilin_basis (x : Zorn)
    (h : ∀ i : Fin 8, zornBilin (zorn_basis i) x = 0) : x = 0 := by
  have hdual : ∀ i : Fin 8, zornCoord x i = 0 := by
    intro i
    rw [zornCoord_eq_zornBilin_dualBasis, zornDualBasis, zornBilin_smul_left, h (zornDualIdx i),
      mul_zero]
  rw [zorn_eq_sum_basis x]
  simp only [hdual, zero_smul, Finset.sum_const_zero]

theorem zorn_eq_zero_of_forall_zornBilin_dualBasis (x : Zorn)
    (h : ∀ i : Fin 8, zornBilin (zornDualBasis i) x = 0) : x = 0 := by
  rw [zorn_eq_sum_basis x]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [zornCoord_eq_zornBilin_dualBasis, h i, zero_smul]

/-- Explicit orthogonal signature `(4,4)` witness for `zornBilin` and `ZornVectorMatrix.norm`. -/
theorem zorn_split_signature_44 :
    let p0 := zorn_basis 0 + zorn_basis 7
    let p1 := zorn_basis 1 - zorn_basis 4
    let p2 := zorn_basis 2 - zorn_basis 5
    let p3 := zorn_basis 3 - zorn_basis 6
    let m0 := zorn_basis 0 - zorn_basis 7
    let m1 := zorn_basis 1 + zorn_basis 4
    let m2 := zorn_basis 2 + zorn_basis 5
    let m3 := zorn_basis 3 + zorn_basis 6
    ZornVectorMatrix.norm p0 = 1 ∧ ZornVectorMatrix.norm p1 = 1 ∧
      ZornVectorMatrix.norm p2 = 1 ∧ ZornVectorMatrix.norm p3 = 1 ∧
      ZornVectorMatrix.norm m0 = -1 ∧ ZornVectorMatrix.norm m1 = -1 ∧
      ZornVectorMatrix.norm m2 = -1 ∧ ZornVectorMatrix.norm m3 = -1 ∧
      zornBilin p0 m0 = 0 ∧ zornBilin p1 m1 = 0 ∧
      zornBilin p2 m2 = 0 ∧ zornBilin p3 m3 = 0 := by
  simp [zorn_basis, zornBilin_eq_coords, ZornVectorMatrix.norm, ZornVec3.dot,
    sub_eq_add_neg, ZornVectorMatrix.add, ZornVectorMatrix.neg]

/-- The 28-dimensional split Lie algebra `so(4,4)` of endomorphisms of `Zorn` skew-adjoint
with respect to the split `(4,4)` pairing `zornBilin`. -/
def zornSkewAdjoint : LieSubalgebra ℝ (Module.End ℝ Zorn) where
  carrier := {T | ∀ x y : Zorn, zornBilin (T x) y + zornBilin x (T y) = 0}
  zero_mem' x y := by
    simp only [LinearMap.zero_apply, zornBilin_zero_left, zornBilin_zero_right, add_zero]
  add_mem' {D E} hD hE x y := by
    simp only [LinearMap.add_apply, zornBilin_add_left, zornBilin_add_right]
    rw [add_add_add_comm, hD x y, hE x y, add_zero]
  smul_mem' r {D} hD x y := by
    simp only [LinearMap.smul_apply, zornBilin_smul_left, zornBilin_smul_right]
    rw [← mul_add, hD x y, mul_zero]
  lie_mem' {D E} hD hE x y := by
    simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply,
      zornBilin_sub_left, zornBilin_sub_right]
    have h1 := hD (E x) y
    have h2 := hE x (D y)
    have h3 := hE (D x) y
    have h4 := hD x (E y)
    calc
      zornBilin (D (E x)) y - zornBilin (E (D x)) y + (zornBilin x (D (E y)) - zornBilin x (E (D y)))
          = (zornBilin (D (E x)) y + zornBilin (E x) (D y)) -
              (zornBilin (E (D x)) y + zornBilin (D x) (E y)) -
              (zornBilin (E x) (D y) + zornBilin x (E (D y))) +
              (zornBilin (D x) (E y) + zornBilin x (D (E y))) := by abel
      _ = 0 - 0 - 0 + 0 := by rw [h1, h2, h3, h4]
      _ = 0 := by norm_num

/-- The 28 strictly ordered pairs `(i, j)` with `i < j` in `Fin 8`. -/
abbrev StrictPair8 := {p : Fin 8 × Fin 8 // p.1 < p.2}

theorem card_strictPair8 : Fintype.card StrictPair8 = 28 := by
  decide

/-- Expand a 28-tuple on `StrictPair8` into a skew-symmetric `8 × 8` matrix. -/
def skewEntry (f : StrictPair8 → ℝ) (i j : Fin 8) : ℝ :=
  if h : i < j then f ⟨(i, j), h⟩
  else if h' : j < i then -f ⟨(j, i), h'⟩
  else 0

theorem skewEntry_antisymm (f : StrictPair8 → ℝ) (i j : Fin 8) :
    skewEntry f j i = -skewEntry f i j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [skewEntry, hij, not_lt.mpr (le_of_lt hij)]
  · simp [skewEntry]
  · simp [skewEntry, hji, not_lt.mpr (le_of_lt hji)]

/-- Endomorphism of `Zorn` determined by skew matrix `skewEntry f`. -/
def skewEndOfStrict (f : StrictPair8 → ℝ) : Module.End ℝ Zorn where
  toFun x := ∑ i : Fin 8, (∑ j : Fin 8, skewEntry f i j * zornCoord x j) • zornDualBasis i
  map_add' x y := by
    simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_smul]
  map_smul' r x := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hscalar : (∑ j : Fin 8, skewEntry f i j * (r * zornCoord x j)) =
        r * ∑ j : Fin 8, skewEntry f i j * zornCoord x j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_left_comm (skewEntry f i j) r (zornCoord x j)
    rw [smul_smul, hscalar]

theorem zornBilin_basis_skewEndOfStrict (f : StrictPair8 → ℝ) (p q : Fin 8) :
    zornBilin (zorn_basis p) (skewEndOfStrict f (zorn_basis q)) = skewEntry f p q := by
  simp only [skewEndOfStrict, LinearMap.coe_mk, AddHom.coe_mk]
  rw [zornBilin_sum_right]
  have hcol : ∀ j : Fin 8, zornCoord (zorn_basis q) j = if j = q then 1 else 0 := by
    intro j
    fin_cases q <;> fin_cases j <;> simp [zornCoord, zorn_basis]
  simp only [zornBilin_smul_right, zornBilin_basis_dualBasis, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, hcol, Finset.sum_ite_eq']

theorem skewEndOfStrict_mem_zornSkewAdjoint (f : StrictPair8 → ℝ) :
    skewEndOfStrict f ∈ zornSkewAdjoint := by
  intro x y
  have h1 : zornBilin (skewEndOfStrict f x) y =
      ∑ i : Fin 8, ∑ j : Fin 8, zornCoord x i * zornCoord y j * skewEntry f j i := by
    conv_lhs => rw [zorn_eq_sum_basis x, zorn_eq_sum_basis y]
    simp only [map_sum, LinearMap.map_smul, zornBilin_sum_left, zornBilin_smul_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zornBilin_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zornBilin_smul_right, zornBilin_symm (skewEndOfStrict f (zorn_basis i)) (zorn_basis j),
      zornBilin_basis_skewEndOfStrict]
    ring
  have h2 : zornBilin x (skewEndOfStrict f y) =
      ∑ i : Fin 8, ∑ j : Fin 8, zornCoord x i * zornCoord y j * skewEntry f i j := by
    conv_lhs => rw [zorn_eq_sum_basis x, zorn_eq_sum_basis y]
    simp only [map_sum, LinearMap.map_smul, zornBilin_sum_left, zornBilin_smul_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zornBilin_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zornBilin_smul_right, zornBilin_basis_skewEndOfStrict]
    ring
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [skewEntry_antisymm f i j]
  ring

/-- Linear isomorphism `zornSkewAdjoint ≃ₗ[ℝ] (StrictPair8 → ℝ)`, proving `so(4,4)` has dimension 28. -/
def zornSkewAdjointEquiv : zornSkewAdjoint ≃ₗ[ℝ] (StrictPair8 → ℝ) where
  toFun T p := zornBilin (zorn_basis p.1.1) (T.1 (zorn_basis p.1.2))
  invFun f := ⟨skewEndOfStrict f, skewEndOfStrict_mem_zornSkewAdjoint f⟩
  map_add' T₁ T₂ := by
    ext p
    change zornBilin (zorn_basis p.1.1) (T₁.1 (zorn_basis p.1.2) + T₂.1 (zorn_basis p.1.2)) = _
    exact zornBilin_add_right _ _ _
  map_smul' r T := by
    ext p
    change zornBilin (zorn_basis p.1.1) (r • T.1 (zorn_basis p.1.2)) = _
    exact zornBilin_smul_right _ _ _
  left_inv T := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rw [zorn_eq_sum_basis x, map_sum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [LinearMap.map_smul]
    refine congrArg (zornCoord x q • ·) ?_
    apply sub_eq_zero.mp
    apply zorn_eq_zero_of_forall_zornBilin_basis
    intro p
    rw [zornBilin_symm (zorn_basis p) _, zornBilin_sub_left,
      zornBilin_symm _ (zorn_basis p), zornBilin_symm _ (zorn_basis p),
      zornBilin_basis_skewEndOfStrict]
    rcases lt_trichotomy p q with hpq | rfl | hqp
    · simp [skewEntry, hpq]
    · have hself := T.2 (zorn_basis p) (zorn_basis p)
      rw [zornBilin_symm (T.1 (zorn_basis p)) (zorn_basis p)] at hself
      simp [skewEntry]
      linarith
    · have hpq_n : ¬ p < q := not_lt.mpr (le_of_lt hqp)
      simp only [skewEntry, hpq_n, ↓reduceDIte, hqp]
      have hskew := T.2 (zorn_basis q) (zorn_basis p)
      rw [zornBilin_symm (T.1 (zorn_basis q)) (zorn_basis p)] at hskew
      linarith
  right_inv f := by
    ext p
    change zornBilin (zorn_basis p.1.1) (skewEndOfStrict f (zorn_basis p.1.2)) = f p
    rw [zornBilin_basis_skewEndOfStrict]
    simp [skewEntry, p.2]

theorem finrank_zornSkewAdjoint : Module.finrank ℝ zornSkewAdjoint = 28 := by
  rw [zornSkewAdjointEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, card_strictPair8]

/-! ## 2. Exact Peirce multiplication laws on `H3Zorn ℝ` -/

/-- Embedding into the `(1,2)` Peirce block. -/
def mkOff12 (x : Zorn) : H3 := ⟨0, 0, 0, x, 0, 0⟩
/-- Embedding into the `(2,3)` Peirce block. -/
def mkOff23 (y : Zorn) : H3 := ⟨0, 0, 0, 0, y, 0⟩
/-- Embedding into the `(3,1)` Peirce block. -/
def mkOff31 (z : Zorn) : H3 := ⟨0, 0, 0, 0, 0, z⟩

@[simp] theorem mkOff12_zero : mkOff12 0 = 0 := rfl
@[simp] theorem mkOff23_zero : mkOff23 0 = 0 := rfl
@[simp] theorem mkOff31_zero : mkOff31 0 = 0 := rfl

theorem mkOff12_add (x y : Zorn) : mkOff12 (x + y) = mkOff12 x + mkOff12 y := by
  apply ext_h3 <;> simp [mkOff12, add_readback, zvm_add_def]
theorem mkOff23_add (x y : Zorn) : mkOff23 (x + y) = mkOff23 x + mkOff23 y := by
  apply ext_h3 <;> simp [mkOff23, add_readback, zvm_add_def]
theorem mkOff31_add (x y : Zorn) : mkOff31 (x + y) = mkOff31 x + mkOff31 y := by
  apply ext_h3 <;> simp [mkOff31, add_readback, zvm_add_def]

theorem mkOff12_smul (r : ℝ) (x : Zorn) : mkOff12 (r • x) = r • mkOff12 x := by
  apply ext_h3 <;> simp [mkOff12, smul_readback, zvm_smul_def]
theorem mkOff23_smul (r : ℝ) (x : Zorn) : mkOff23 (r • x) = r • mkOff23 x := by
  apply ext_h3 <;> simp [mkOff23, smul_readback, zvm_smul_def]
theorem mkOff31_smul (r : ℝ) (x : Zorn) : mkOff31 (r • x) = r • mkOff31 x := by
  apply ext_h3 <;> simp [mkOff31, smul_readback, zvm_smul_def]

@[simp] theorem mkOff12_basis (i : Fin 8) : mkOff12 (zorn_basis i) = h3_off₁₂ i := rfl
@[simp] theorem mkOff23_basis (i : Fin 8) : mkOff23 (zorn_basis i) = h3_off₂₃ i := rfl
@[simp] theorem mkOff31_basis (i : Fin 8) : mkOff31 (zorn_basis i) = h3_off₃₁ i := rfl

theorem h3_diag₁_add_diag₂_add_diag₃ :
    h3_diag₁ + h3_diag₂ + h3_diag₃ = (1 : H3) := by
  apply ext_h3 <;> simp [h3_diag₁, h3_diag₂, h3_diag₃, add_readback, one_readback]

theorem h3Zorn_decomp (X : H3) :
    X = X.α₁ • h3_diag₁ + X.α₂ • h3_diag₂ + X.α₃ • h3_diag₃ +
      mkOff12 X.a + mkOff23 X.b + mkOff31 X.c := by
  apply ext_h3 <;> simp [h3_diag₁, h3_diag₂, h3_diag₃, mkOff12, mkOff23, mkOff31,
    add_readback, smul_readback]

theorem h3_diag₁_mul (X : H3) :
    h3_diag₁ * X = ⟨X.α₁, 0, 0, (1 / 2 : ℝ) • X.a, 0, (1 / 2 : ℝ) • X.c⟩ := by
  rw [← candidateJordanMul_eq_mul, candidateJordanMul_trace_formula]
  rw [show h3_diag₁ = diagCartan 1 0 0 from rfl, H3Zorn.crossProduct_diagCartan_left]
  apply ext_h3
  · simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback]; ring
  · simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · ext i <;> simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.zero] <;> ring
  · ext i <;> simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.zero] <;> ring
  · ext i <;> simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.zero] <;> ring

theorem h3_diag₂_mul (X : H3) :
    h3_diag₂ * X = ⟨0, X.α₂, 0, (1 / 2 : ℝ) • X.a, (1 / 2 : ℝ) • X.b, 0⟩ := by
  rw [← candidateJordanMul_eq_mul, candidateJordanMul_trace_formula]
  rw [show h3_diag₂ = diagCartan 0 1 0 from rfl, H3Zorn.crossProduct_diagCartan_left]
  apply ext_h3
  · simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback]; ring
  · simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · ext i <;> simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.zero] <;> ring
  · ext i <;> simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.zero] <;> ring
  · ext i <;> simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.zero] <;> ring

theorem h3_diag₃_mul (X : H3) :
    h3_diag₃ * X = ⟨0, 0, X.α₃, 0, (1 / 2 : ℝ) • X.b, (1 / 2 : ℝ) • X.c⟩ := by
  rw [← candidateJordanMul_eq_mul, candidateJordanMul_trace_formula]
  rw [show h3_diag₃ = diagCartan 0 0 1 from rfl, H3Zorn.crossProduct_diagCartan_left]
  apply ext_h3
  · simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback]; ring
  · ext i <;> simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.zero] <;> ring
  · ext i <;> simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.zero] <;> ring
  · ext i <;> simp [diagCartan, H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.zero] <;> ring

theorem mkOff12_mul_mkOff12 (x y : Zorn) :
    mkOff12 x * mkOff12 y = ⟨zornBilin x y / 2, zornBilin x y / 2, 0, 0, 0, 0⟩ := by
  rw [← candidateJordanMul_eq_mul, candidateJordanMul_trace_formula]
  have hnorm :
      ZornVectorMatrix.norm (ZornVectorMatrix.add x y) -
        ZornVectorMatrix.norm x - ZornVectorMatrix.norm y = zornBilin x y := by
    rw [ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj]
    simp only [zornBilin]
    ring
  apply ext_h3
  · simp [mkOff12, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace, add_readback,
      sub_readback, smul_readback, one_readback]; linarith [hnorm]
  · simp [mkOff12, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace, add_readback,
      sub_readback, smul_readback, one_readback]; linarith [hnorm]
  · simp [mkOff12, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace, add_readback,
      sub_readback, smul_readback, one_readback]; ring
  · ext i <;> simp [mkOff12, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace,
      add_readback, sub_readback, smul_readback, one_readback, ZornVectorMatrix.sub,
      ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.conj,
      ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
  · ext i <;> simp [mkOff12, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace,
      add_readback, sub_readback, smul_readback, one_readback, ZornVectorMatrix.sub,
      ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.conj,
      ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
  · ext i <;> simp [mkOff12, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace,
      add_readback, sub_readback, smul_readback, one_readback, ZornVectorMatrix.sub,
      ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.conj,
      ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]

theorem mkOff23_mul_mkOff23 (x y : Zorn) :
    mkOff23 x * mkOff23 y = ⟨0, zornBilin x y / 2, zornBilin x y / 2, 0, 0, 0⟩ := by
  rw [← candidateJordanMul_eq_mul, candidateJordanMul_trace_formula]
  have hnorm :
      ZornVectorMatrix.norm (ZornVectorMatrix.add x y) -
        ZornVectorMatrix.norm x - ZornVectorMatrix.norm y = zornBilin x y := by
    rw [ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj]
    simp only [zornBilin]
    ring
  apply ext_h3
  · simp [mkOff23, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace, add_readback,
      sub_readback, smul_readback, one_readback]; ring
  · simp [mkOff23, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace, add_readback,
      sub_readback, smul_readback, one_readback]; linarith [hnorm]
  · simp [mkOff23, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace, add_readback,
      sub_readback, smul_readback, one_readback]; linarith [hnorm]
  · ext i <;> simp [mkOff23, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace,
      add_readback, sub_readback, smul_readback, one_readback, ZornVectorMatrix.sub,
      ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.conj,
      ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
  · ext i <;> simp [mkOff23, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace,
      add_readback, sub_readback, smul_readback, one_readback, ZornVectorMatrix.sub,
      ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.conj,
      ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
  · ext i <;> simp [mkOff23, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace,
      add_readback, sub_readback, smul_readback, one_readback, ZornVectorMatrix.sub,
      ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.conj,
      ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]

theorem mkOff12_mul_mkOff23 (x y : Zorn) :
    mkOff12 x * mkOff23 y = mkOff31 ((1 / 2 : ℝ) • ZornVectorMatrix.conj (ZornVectorMatrix.mul x y)) := by
  rw [← candidateJordanMul_eq_mul, candidateJordanMul_trace_formula]
  apply ext_h3
  · simp [mkOff12, mkOff23, mkOff31, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace,
      add_readback, sub_readback, smul_readback, one_readback, ZornVectorMatrix.norm, ZornVec3.dot]
  · simp [mkOff12, mkOff23, mkOff31, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace,
      add_readback, sub_readback, smul_readback, one_readback, ZornVectorMatrix.norm, ZornVec3.dot]
  · simp [mkOff12, mkOff23, mkOff31, H3Zorn.crossProduct, H3Zorn.adjointQuad, H3Zorn.linearTrace,
      add_readback, sub_readback, smul_readback, one_readback, ZornVectorMatrix.norm, ZornVec3.dot]
  · ext i <;> simp [mkOff12, mkOff23, mkOff31, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot,
      ZornVec3.cross]
  · ext i <;> simp [mkOff12, mkOff23, mkOff31, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot,
      ZornVec3.cross]
  · simp only [mkOff12, mkOff23, mkOff31, H3Zorn.crossProduct, H3Zorn.adjointQuad,
      H3Zorn.linearTrace, add_readback, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
      ZornVectorMatrix.zero, zvm_smul_def]
    rw [ZornVectorMatrix.conj_mul x y]
    ext i <;> simp [ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]

/-! ## 3. Peirce evaluation map and explicit 24D shift section -/

/-- Peirce shift readout extracting the `(1,2)`, `(2,3)`, `(3,1)` infinitesimal shifts of
the diagonal idempotents `h3_diag₁`, `h3_diag₂`. -/
def peirceEval : H3ZornF4Derivations →ₗ[ℝ] (Zorn × (Zorn × Zorn)) where
  toFun D := ((D.1 h3_diag₁).a, ((D.1 h3_diag₂).b, (D.1 h3_diag₁).c))
  map_add' _ _ := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> rfl
  map_smul' _ _ := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> rfl

theorem diag_deriv_vanish (D : H3ZornF4Derivations) :
    (D.1 h3_diag₁).α₁ = 0 ∧ (D.1 h3_diag₁).α₂ = 0 ∧ (D.1 h3_diag₁).α₃ = 0 ∧ (D.1 h3_diag₁).b = 0 ∧
    (D.1 h3_diag₂).α₁ = 0 ∧ (D.1 h3_diag₂).α₂ = 0 ∧ (D.1 h3_diag₂).α₃ = 0 ∧ (D.1 h3_diag₂).c = 0 ∧
    (D.1 h3_diag₃).α₁ = 0 ∧ (D.1 h3_diag₃).α₂ = 0 ∧ (D.1 h3_diag₃).α₃ = 0 ∧ (D.1 h3_diag₃).a = 0 := by
  have he1 : h3_diag₁ * h3_diag₁ = h3_diag₁ := by
    rw [h3_diag₁_mul]; apply ext_h3 <;> simp [h3_diag₁]
  have he2 : h3_diag₂ * h3_diag₂ = h3_diag₂ := by
    rw [h3_diag₂_mul]; apply ext_h3 <;> simp [h3_diag₂]
  have he3 : h3_diag₃ * h3_diag₃ = h3_diag₃ := by
    rw [h3_diag₃_mul]; apply ext_h3 <;> simp [h3_diag₃]
  have hd1 := D.2 h3_diag₁ h3_diag₁
  rw [he1, mul_comm (D.1 h3_diag₁) h3_diag₁, h3_diag₁_mul] at hd1
  have hd2 := D.2 h3_diag₂ h3_diag₂
  rw [he2, mul_comm (D.1 h3_diag₂) h3_diag₂, h3_diag₂_mul] at hd2
  have hd3 := D.2 h3_diag₃ h3_diag₃
  rw [he3, mul_comm (D.1 h3_diag₃) h3_diag₃, h3_diag₃_mul] at hd3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg H3Zorn.α₁ hd1; simp [add_readback] at h; linarith
  · have h := congrArg H3Zorn.α₂ hd1; simp [add_readback] at h; exact h
  · have h := congrArg H3Zorn.α₃ hd1; simp [add_readback] at h; exact h
  · have h := congrArg H3Zorn.b hd1; simpa [add_readback, zvm_add_def] using h
  · have h := congrArg H3Zorn.α₁ hd2; simp [add_readback] at h; exact h
  · have h := congrArg H3Zorn.α₂ hd2; simp [add_readback] at h; linarith
  · have h := congrArg H3Zorn.α₃ hd2; simp [add_readback] at h; exact h
  · have h := congrArg H3Zorn.c hd2; simpa [add_readback, zvm_add_def] using h
  · have h := congrArg H3Zorn.α₁ hd3; simp [add_readback] at h; exact h
  · have h := congrArg H3Zorn.α₂ hd3; simp [add_readback] at h; exact h
  · have h := congrArg H3Zorn.α₃ hd3; simp [add_readback] at h; linarith
  · have h := congrArg H3Zorn.a hd3; simpa [add_readback, zvm_add_def] using h

theorem mem_ker_peirceEval_iff (D : H3ZornF4Derivations) :
    D ∈ LinearMap.ker peirceEval ↔
      D.1 h3_diag₁ = 0 ∧ D.1 h3_diag₂ = 0 ∧ D.1 h3_diag₃ = 0 := by
  constructor
  · intro hker
    have hpe : peirceEval D = 0 := LinearMap.mem_ker.mp hker
    have ha1 : (D.1 h3_diag₁).a = 0 := congrArg Prod.fst hpe
    have hb2 : (D.1 h3_diag₂).b = 0 := congrArg (fun p => p.2.1) hpe
    have hc1 : (D.1 h3_diag₁).c = 0 := congrArg (fun p => p.2.2) hpe
    obtain ⟨h11, h12, h13, h1b, h21, h22, h23, h2c, h31, h32, h33, h3a⟩ := diag_deriv_vanish D
    have hD1 : D.1 (1 : H3) = 0 :=
      h3Zorn_derivation_apply_one_eq_zero ⟨D.1, D.2⟩
    have hsum : D.1 h3_diag₁ + D.1 h3_diag₂ + D.1 h3_diag₃ = 0 := by
      rw [← map_add, ← map_add, h3_diag₁_add_diag₂_add_diag₃, hD1]
    have ha2 : (D.1 h3_diag₂).a = 0 := by
      have ha := congrArg H3Zorn.a hsum
      rw [add_readback, add_readback] at ha
      dsimp only at ha
      rw [ha1, h3a, ← zvm_add_def, ← zvm_add_def, zero_add, add_zero] at ha
      exact ha
    have hb3 : (D.1 h3_diag₃).b = 0 := by
      have hb := congrArg H3Zorn.b hsum
      rw [add_readback, add_readback] at hb
      dsimp only at hb
      rw [h1b, hb2, ← zvm_add_def, ← zvm_add_def, zero_add, zero_add] at hb
      exact hb
    have hc3 : (D.1 h3_diag₃).c = 0 := by
      have hc := congrArg H3Zorn.c hsum
      rw [add_readback, add_readback] at hc
      dsimp only at hc
      rw [hc1, h2c, ← zvm_add_def, ← zvm_add_def, zero_add, zero_add] at hc
      exact hc
    refine ⟨?_, ?_, ?_⟩
    · apply ext_h3 <;> assumption
    · apply ext_h3 <;> assumption
    · apply ext_h3 <;> assumption
  · rintro ⟨h1, h2, _⟩
    rw [LinearMap.mem_ker]
    dsimp [peirceEval]
    rw [h1, h2]
    rfl

theorem h3ZornJordanInnerDerivation_add_left (a₁ a₂ b : H3) :
    (h3ZornJordanInnerDerivation (a₁ + a₂) b : EndH3) =
      (h3ZornJordanInnerDerivation a₁ b : EndH3) +
        (h3ZornJordanInnerDerivation a₂ b : EndH3) := by
  apply LinearMap.ext; intro x
  simp only [h3ZornJordanInnerDerivation_apply, LinearMap.add_apply, add_mul, mul_add]
  abel

theorem h3ZornJordanInnerDerivation_add_right (a b₁ b₂ : H3) :
    (h3ZornJordanInnerDerivation a (b₁ + b₂) : EndH3) =
      (h3ZornJordanInnerDerivation a b₁ : EndH3) +
        (h3ZornJordanInnerDerivation a b₂ : EndH3) := by
  apply LinearMap.ext; intro x
  simp only [h3ZornJordanInnerDerivation_apply, LinearMap.add_apply, add_mul, mul_add]
  abel

theorem h3ZornJordanInnerDerivation_smul_left (r : ℝ) (a b : H3) :
    (h3ZornJordanInnerDerivation (r • a) b : EndH3) =
      r • (h3ZornJordanInnerDerivation a b : EndH3) := by
  apply LinearMap.ext; intro x
  simp only [h3ZornJordanInnerDerivation_apply, LinearMap.smul_apply, smul_mul_assoc,
    mul_smul_comm, smul_sub]

theorem h3ZornJordanInnerDerivation_smul_right (r : ℝ) (a b : H3) :
    (h3ZornJordanInnerDerivation a (r • b) : EndH3) =
      r • (h3ZornJordanInnerDerivation a b : EndH3) := by
  apply LinearMap.ext; intro x
  simp only [h3ZornJordanInnerDerivation_apply, LinearMap.smul_apply, smul_mul_assoc,
    mul_smul_comm, smul_sub]

theorem h3ZornJordanInnerDerivation_swap (a b : H3) :
    (h3ZornJordanInnerDerivation a b : EndH3) =
      -(h3ZornJordanInnerDerivation b a : EndH3) := by
  apply LinearMap.ext; intro x
  simp only [h3ZornJordanInnerDerivation_apply, LinearMap.neg_apply, neg_sub]

theorem h3ZornJordanInnerDerivation_self (a : H3) :
    (h3ZornJordanInnerDerivation a a : EndH3) = 0 := by
  apply LinearMap.ext; intro x
  simp

/-- Helper bundling any inner derivation directly into `H3ZornF4Derivations`. -/
def innerDerivF4 (a b : H3) : H3ZornF4Derivations :=
  ⟨(h3ZornJordanInnerDerivation a b : EndH3), h3ZornJordanInnerDerivation_mem_F4 a b⟩

private theorem mkOff12_mul_diag₁ (x : Zorn) : mkOff12 x * h3_diag₁ = (1 / 2 : ℝ) • mkOff12 x := by
  rw [mul_comm, h3_diag₁_mul]; apply ext_h3 <;> simp [mkOff12, smul_readback, zero_readback, ZornVectorMatrix.smul_zero]
private theorem mkOff12_mul_diag₂ (x : Zorn) : mkOff12 x * h3_diag₂ = (1 / 2 : ℝ) • mkOff12 x := by
  rw [mul_comm, h3_diag₂_mul]; apply ext_h3 <;> simp [mkOff12, smul_readback, zero_readback, ZornVectorMatrix.smul_zero]
private theorem mkOff12_mul_diag₃ (x : Zorn) : mkOff12 x * h3_diag₃ = 0 := by
  rw [mul_comm, h3_diag₃_mul]; apply ext_h3 <;> simp [mkOff12, smul_readback, zero_readback, ZornVectorMatrix.smul_zero]
private theorem mkOff23_mul_diag₁ (y : Zorn) : mkOff23 y * h3_diag₁ = 0 := by
  rw [mul_comm, h3_diag₁_mul]; apply ext_h3 <;> simp [mkOff23, smul_readback, zero_readback, ZornVectorMatrix.smul_zero]
private theorem mkOff23_mul_diag₂ (y : Zorn) : mkOff23 y * h3_diag₂ = (1 / 2 : ℝ) • mkOff23 y := by
  rw [mul_comm, h3_diag₂_mul]; apply ext_h3 <;> simp [mkOff23, smul_readback, zero_readback, ZornVectorMatrix.smul_zero]
private theorem mkOff23_mul_diag₃ (y : Zorn) : mkOff23 y * h3_diag₃ = (1 / 2 : ℝ) • mkOff23 y := by
  rw [mul_comm, h3_diag₃_mul]; apply ext_h3 <;> simp [mkOff23, smul_readback, zero_readback, ZornVectorMatrix.smul_zero]
private theorem mkOff31_mul_diag₁ (z : Zorn) : mkOff31 z * h3_diag₁ = (1 / 2 : ℝ) • mkOff31 z := by
  rw [mul_comm, h3_diag₁_mul]; apply ext_h3 <;> simp [mkOff31, smul_readback, zero_readback, ZornVectorMatrix.smul_zero]
private theorem mkOff31_mul_diag₂ (z : Zorn) : mkOff31 z * h3_diag₂ = 0 := by
  rw [mul_comm, h3_diag₂_mul]; apply ext_h3 <;> simp [mkOff31, smul_readback, zero_readback, ZornVectorMatrix.smul_zero]
private theorem mkOff31_mul_diag₃ (z : Zorn) : mkOff31 z * h3_diag₃ = (1 / 2 : ℝ) • mkOff31 z := by
  rw [mul_comm, h3_diag₃_mul]; apply ext_h3 <;> simp [mkOff31, smul_readback, zero_readback, ZornVectorMatrix.smul_zero]

private theorem diag1_mul_diag1 : h3_diag₁ * h3_diag₁ = h3_diag₁ := by
  rw [h3_diag₁_mul]; apply ext_h3 <;> simp [h3_diag₁, ZornVectorMatrix.smul_zero]
private theorem diag2_mul_diag2 : h3_diag₂ * h3_diag₂ = h3_diag₂ := by
  rw [h3_diag₂_mul]; apply ext_h3 <;> simp [h3_diag₂, ZornVectorMatrix.smul_zero]
private theorem diag1_mul_diag2 : h3_diag₁ * h3_diag₂ = 0 := by
  rw [h3_diag₁_mul]; apply ext_h3 <;> simp [h3_diag₂, zero_readback, ZornVectorMatrix.smul_zero]
private theorem diag2_mul_diag1 : h3_diag₂ * h3_diag₁ = 0 := by
  rw [h3_diag₂_mul]; apply ext_h3 <;> simp [h3_diag₁, zero_readback, ZornVectorMatrix.smul_zero]

theorem innerD_diag1_off12_eval (x : Zorn) :
    peirceEval (innerDerivF4 h3_diag₁ (mkOff12 x)) = ((-1 / 4 : ℝ) • x, (0, 0)) := by
  have hd1 : (innerDerivF4 h3_diag₁ (mkOff12 x)).1 h3_diag₁ = (-1 / 4 : ℝ) • mkOff12 x := by
    change (h3ZornJordanInnerDerivation h3_diag₁ (mkOff12 x) : EndH3) h3_diag₁ = _
    rw [h3ZornJordanInnerDerivation_apply, mkOff12_mul_diag₁, mul_smul_comm,
      mul_comm h3_diag₁ (mkOff12 x), mkOff12_mul_diag₁, diag1_mul_diag1,
      mkOff12_mul_diag₁, smul_smul]
    module
  have hd2 : (innerDerivF4 h3_diag₁ (mkOff12 x)).1 h3_diag₂ = (1 / 4 : ℝ) • mkOff12 x := by
    change (h3ZornJordanInnerDerivation h3_diag₁ (mkOff12 x) : EndH3) h3_diag₂ = _
    rw [h3ZornJordanInnerDerivation_apply, mkOff12_mul_diag₂, mul_smul_comm,
      mul_comm h3_diag₁ (mkOff12 x), mkOff12_mul_diag₁, diag1_mul_diag2,
      mul_zero, sub_zero, smul_smul]
    norm_num
  apply Prod.ext
  · change ((innerDerivF4 h3_diag₁ (mkOff12 x)).1 h3_diag₁).a = _
    rw [hd1, smul_readback, ← zvm_smul_def]; rfl
  · apply Prod.ext
    · change ((innerDerivF4 h3_diag₁ (mkOff12 x)).1 h3_diag₂).b = 0
      rw [hd2, smul_readback, mkOff12]; simp
    · change ((innerDerivF4 h3_diag₁ (mkOff12 x)).1 h3_diag₁).c = 0
      rw [hd1, smul_readback, mkOff12]; simp

theorem innerD_diag2_off23_eval (y : Zorn) :
    peirceEval (innerDerivF4 h3_diag₂ (mkOff23 y)) = (0, ((-1 / 4 : ℝ) • y, 0)) := by
  have hd1 : (innerDerivF4 h3_diag₂ (mkOff23 y)).1 h3_diag₁ = 0 := by
    change (h3ZornJordanInnerDerivation h3_diag₂ (mkOff23 y) : EndH3) h3_diag₁ = 0
    rw [h3ZornJordanInnerDerivation_apply, mkOff23_mul_diag₁, diag2_mul_diag1,
      mul_zero, mul_zero, sub_zero]
  have hd2 : (innerDerivF4 h3_diag₂ (mkOff23 y)).1 h3_diag₂ = (-1 / 4 : ℝ) • mkOff23 y := by
    change (h3ZornJordanInnerDerivation h3_diag₂ (mkOff23 y) : EndH3) h3_diag₂ = _
    rw [h3ZornJordanInnerDerivation_apply, mkOff23_mul_diag₂, mul_smul_comm,
      mul_comm h3_diag₂ (mkOff23 y), mkOff23_mul_diag₂, diag2_mul_diag2,
      mkOff23_mul_diag₂, smul_smul]
    module
  apply Prod.ext
  · change ((innerDerivF4 h3_diag₂ (mkOff23 y)).1 h3_diag₁).a = 0
    rw [hd1]; rfl
  · apply Prod.ext
    · change ((innerDerivF4 h3_diag₂ (mkOff23 y)).1 h3_diag₂).b = _
      rw [hd2, smul_readback, ← zvm_smul_def]; rfl
    · change ((innerDerivF4 h3_diag₂ (mkOff23 y)).1 h3_diag₁).c = 0
      rw [hd1]; rfl

theorem innerD_diag1_off31_eval (z : Zorn) :
    peirceEval (innerDerivF4 h3_diag₁ (mkOff31 z)) = (0, (0, (-1 / 4 : ℝ) • z)) := by
  have hd1 : (innerDerivF4 h3_diag₁ (mkOff31 z)).1 h3_diag₁ = (-1 / 4 : ℝ) • mkOff31 z := by
    change (h3ZornJordanInnerDerivation h3_diag₁ (mkOff31 z) : EndH3) h3_diag₁ = _
    rw [h3ZornJordanInnerDerivation_apply, mkOff31_mul_diag₁, mul_smul_comm,
      mul_comm h3_diag₁ (mkOff31 z), mkOff31_mul_diag₁, diag1_mul_diag1,
      mkOff31_mul_diag₁, smul_smul]
    module
  have hd2 : (innerDerivF4 h3_diag₁ (mkOff31 z)).1 h3_diag₂ = 0 := by
    change (h3ZornJordanInnerDerivation h3_diag₁ (mkOff31 z) : EndH3) h3_diag₂ = 0
    rw [h3ZornJordanInnerDerivation_apply, mkOff31_mul_diag₂, diag1_mul_diag2,
      mul_zero, mul_zero, sub_zero]
  apply Prod.ext
  · change ((innerDerivF4 h3_diag₁ (mkOff31 z)).1 h3_diag₁).a = 0
    rw [hd1, smul_readback, mkOff31]; simp
  · apply Prod.ext
    · change ((innerDerivF4 h3_diag₁ (mkOff31 z)).1 h3_diag₂).b = 0
      rw [hd2]; rfl
    · change ((innerDerivF4 h3_diag₁ (mkOff31 z)).1 h3_diag₁).c = _
      rw [hd1, smul_readback, ← zvm_smul_def]; rfl

/-- Explicit linear right inverse `peirceSection : (Zorn × (Zorn × Zorn)) →ₗ[ℝ] H3ZornF4Derivations`
for `peirceEval`. -/
def peirceSection : (Zorn × (Zorn × Zorn)) →ₗ[ℝ] H3ZornF4Derivations where
  toFun p := (-4 : ℝ) •
    (innerDerivF4 h3_diag₁ (mkOff12 p.1) +
      innerDerivF4 h3_diag₂ (mkOff23 p.2.1) +
      innerDerivF4 h3_diag₁ (mkOff31 p.2.2))
  map_add' p q := by
    apply Subtype.ext
    change (-4 : ℝ) • ((innerDerivF4 h3_diag₁ (mkOff12 (p.1 + q.1))).1 +
        (innerDerivF4 h3_diag₂ (mkOff23 (p.2.1 + q.2.1))).1 +
        (innerDerivF4 h3_diag₁ (mkOff31 (p.2.2 + q.2.2))).1) =
      ((-4 : ℝ) • ((innerDerivF4 h3_diag₁ (mkOff12 p.1)).1 +
        (innerDerivF4 h3_diag₂ (mkOff23 p.2.1)).1 +
        (innerDerivF4 h3_diag₁ (mkOff31 p.2.2)).1)) +
      ((-4 : ℝ) • ((innerDerivF4 h3_diag₁ (mkOff12 q.1)).1 +
        (innerDerivF4 h3_diag₂ (mkOff23 q.2.1)).1 +
        (innerDerivF4 h3_diag₁ (mkOff31 q.2.2)).1))
    simp only [mkOff12_add, mkOff23_add, mkOff31_add, innerDerivF4,
      h3ZornJordanInnerDerivation_add_right]
    module
  map_smul' r p := by
    apply Subtype.ext
    change (-4 : ℝ) • ((innerDerivF4 h3_diag₁ (mkOff12 (r • p.1))).1 +
        (innerDerivF4 h3_diag₂ (mkOff23 (r • p.2.1))).1 +
        (innerDerivF4 h3_diag₁ (mkOff31 (r • p.2.2))).1) =
      r • ((-4 : ℝ) • ((innerDerivF4 h3_diag₁ (mkOff12 p.1)).1 +
        (innerDerivF4 h3_diag₂ (mkOff23 p.2.1)).1 +
        (innerDerivF4 h3_diag₁ (mkOff31 p.2.2)).1))
    simp only [mkOff12_smul, mkOff23_smul, mkOff31_smul, innerDerivF4,
      h3ZornJordanInnerDerivation_smul_right]
    module

theorem peirceEval_peirceSection (p : Zorn × (Zorn × Zorn)) :
    peirceEval (peirceSection p) = p := by
  dsimp [peirceSection]
  rw [map_smul, map_add, map_add, innerD_diag1_off12_eval, innerD_diag2_off23_eval,
    innerD_diag1_off31_eval]
  apply Prod.ext
  · change (-4 : ℝ) • ((-1 / 4 : ℝ) • p.1 + 0 + 0) = p.1
    rw [add_zero, add_zero, smul_smul]; norm_num
  · apply Prod.ext
    · change (-4 : ℝ) • (0 + (-1 / 4 : ℝ) • p.2.1 + 0) = p.2.1
      rw [zero_add, add_zero, smul_smul]; norm_num
    · change (-4 : ℝ) • (0 + 0 + (-1 / 4 : ℝ) • p.2.2) = p.2.2
      rw [zero_add, zero_add, smul_smul]; norm_num

/-! ## 4. Stabilizer isomorphism `LinearMap.ker peirceEval ≃ₗ[ℝ] zornSkewAdjoint` (`so(4,4)`) -/

theorem ker_preserves_off12 (D : LinearMap.ker peirceEval) (x : Zorn) :
    D.1.1 (mkOff12 x) = mkOff12 ((D.1.1 (mkOff12 x)).a) := by
  obtain ⟨hd1, hd2, hd3⟩ := (mem_ker_peirceEval_iff D.1).mp D.2
  have h1 := D.1.2 h3_diag₁ (mkOff12 x)
  have h2 := D.1.2 h3_diag₂ (mkOff12 x)
  have h3 := D.1.2 h3_diag₃ (mkOff12 x)
  rw [hd1, zero_mul, zero_add, mul_comm h3_diag₁ (mkOff12 x), mkOff12_mul_diag₁, map_smul] at h1
  rw [hd2, zero_mul, zero_add, mul_comm h3_diag₂ (mkOff12 x), mkOff12_mul_diag₂, map_smul] at h2
  rw [hd3, zero_mul, zero_add, mul_comm h3_diag₃ (mkOff12 x), mkOff12_mul_diag₃, map_zero] at h3
  rw [h3_diag₁_mul] at h1
  rw [h3_diag₂_mul] at h2
  rw [h3_diag₃_mul] at h3
  have hα₁ : (D.1.1 (mkOff12 x)).α₁ = 0 := by
    have t := congrArg H3Zorn.α₁ h2; rw [smul_readback] at t; dsimp only at t; linarith
  have hα₂ : (D.1.1 (mkOff12 x)).α₂ = 0 := by
    have t := congrArg H3Zorn.α₂ h1; rw [smul_readback] at t; dsimp only at t; linarith
  have hα₃ : (D.1.1 (mkOff12 x)).α₃ = 0 := by
    have t := congrArg H3Zorn.α₃ h1; rw [smul_readback] at t; dsimp only at t; linarith
  have hb : (D.1.1 (mkOff12 x)).b = 0 := by
    have t := congrArg H3Zorn.b h1
    rw [smul_readback] at t; dsimp only at t; rw [← zvm_smul_def] at t
    exact (smul_eq_zero.mp t).resolve_left (by norm_num)
  have hc : (D.1.1 (mkOff12 x)).c = 0 := by
    have t := congrArg H3Zorn.c h2
    rw [smul_readback] at t; dsimp only at t; rw [← zvm_smul_def] at t
    exact (smul_eq_zero.mp t).resolve_left (by norm_num)
  apply ext_h3
  · exact hα₁
  · exact hα₂
  · exact hα₃
  · rfl
  · exact hb
  · exact hc

theorem ker_preserves_off23 (D : LinearMap.ker peirceEval) (y : Zorn) :
    D.1.1 (mkOff23 y) = mkOff23 ((D.1.1 (mkOff23 y)).b) := by
  obtain ⟨hd1, hd2, hd3⟩ := (mem_ker_peirceEval_iff D.1).mp D.2
  have h1 := D.1.2 h3_diag₁ (mkOff23 y)
  have h2 := D.1.2 h3_diag₂ (mkOff23 y)
  have h3 := D.1.2 h3_diag₃ (mkOff23 y)
  rw [hd1, zero_mul, zero_add, mul_comm h3_diag₁ (mkOff23 y), mkOff23_mul_diag₁, map_zero] at h1
  rw [hd2, zero_mul, zero_add, mul_comm h3_diag₂ (mkOff23 y), mkOff23_mul_diag₂, map_smul] at h2
  rw [hd3, zero_mul, zero_add, mul_comm h3_diag₃ (mkOff23 y), mkOff23_mul_diag₃, map_smul] at h3
  rw [h3_diag₁_mul] at h1
  rw [h3_diag₂_mul] at h2
  rw [h3_diag₃_mul] at h3
  have hα₁ : (D.1.1 (mkOff23 y)).α₁ = 0 := by
    have t := congrArg H3Zorn.α₁ h2; rw [smul_readback] at t; dsimp only at t; linarith
  have hα₂ : (D.1.1 (mkOff23 y)).α₂ = 0 := by
    have t := congrArg H3Zorn.α₂ h3; rw [smul_readback] at t; dsimp only at t; linarith
  have hα₃ : (D.1.1 (mkOff23 y)).α₃ = 0 := by
    have t := congrArg H3Zorn.α₃ h2; rw [smul_readback] at t; dsimp only at t; linarith
  have ha : (D.1.1 (mkOff23 y)).a = 0 := by
    have t := congrArg H3Zorn.a h3
    rw [smul_readback] at t; dsimp only at t; rw [← zvm_smul_def] at t
    exact (smul_eq_zero.mp t).resolve_left (by norm_num)
  have hc : (D.1.1 (mkOff23 y)).c = 0 := by
    have t := congrArg H3Zorn.c h2
    rw [smul_readback] at t; dsimp only at t; rw [← zvm_smul_def] at t
    exact (smul_eq_zero.mp t).resolve_left (by norm_num)
  apply ext_h3
  · exact hα₁
  · exact hα₂
  · exact hα₃
  · exact ha
  · rfl
  · exact hc

theorem ker_preserves_off31 (D : LinearMap.ker peirceEval) (z : Zorn) :
    D.1.1 (mkOff31 z) = mkOff31 ((D.1.1 (mkOff31 z)).c) := by
  obtain ⟨hd1, hd2, hd3⟩ := (mem_ker_peirceEval_iff D.1).mp D.2
  have h1 := D.1.2 h3_diag₁ (mkOff31 z)
  have h2 := D.1.2 h3_diag₂ (mkOff31 z)
  have h3 := D.1.2 h3_diag₃ (mkOff31 z)
  rw [hd1, zero_mul, zero_add, mul_comm h3_diag₁ (mkOff31 z), mkOff31_mul_diag₁, map_smul] at h1
  rw [hd2, zero_mul, zero_add, mul_comm h3_diag₂ (mkOff31 z), mkOff31_mul_diag₂, map_zero] at h2
  rw [hd3, zero_mul, zero_add, mul_comm h3_diag₃ (mkOff31 z), mkOff31_mul_diag₃, map_smul] at h3
  rw [h3_diag₁_mul] at h1
  rw [h3_diag₂_mul] at h2
  rw [h3_diag₃_mul] at h3
  have hα₁ : (D.1.1 (mkOff31 z)).α₁ = 0 := by
    have t := congrArg H3Zorn.α₁ h3; rw [smul_readback] at t; dsimp only at t; linarith
  have hα₂ : (D.1.1 (mkOff31 z)).α₂ = 0 := by
    have t := congrArg H3Zorn.α₂ h1; rw [smul_readback] at t; dsimp only at t; linarith
  have hα₃ : (D.1.1 (mkOff31 z)).α₃ = 0 := by
    have t := congrArg H3Zorn.α₃ h1; rw [smul_readback] at t; dsimp only at t; linarith
  have ha : (D.1.1 (mkOff31 z)).a = 0 := by
    have t := congrArg H3Zorn.a h3
    rw [smul_readback] at t; dsimp only at t; rw [← zvm_smul_def] at t
    exact (smul_eq_zero.mp t).resolve_left (by norm_num)
  have hb : (D.1.1 (mkOff31 z)).b = 0 := by
    have t := congrArg H3Zorn.b h1
    rw [smul_readback] at t; dsimp only at t; rw [← zvm_smul_def] at t
    exact (smul_eq_zero.mp t).resolve_left (by norm_num)
  apply ext_h3
  · exact hα₁
  · exact hα₂
  · exact hα₃
  · exact ha
  · exact hb
  · rfl

/-- Induced endomorphism on the `(1,2)` Peirce block `Zorn`. -/
def stabOp12 (D : LinearMap.ker peirceEval) : Module.End ℝ Zorn where
  toFun x := (D.1.1 (mkOff12 x)).a
  map_add' x y := by
    change (D.1.1 (mkOff12 (x + y))).a = (D.1.1 (mkOff12 x)).a + (D.1.1 (mkOff12 y)).a
    rw [mkOff12_add, map_add]; rfl
  map_smul' r x := by
    change (D.1.1 (mkOff12 (r • x))).a = r • (D.1.1 (mkOff12 x)).a
    rw [mkOff12_smul, map_smul]; rfl

/-- Induced endomorphism on the `(2,3)` Peirce block `Zorn`. -/
def stabOp23 (D : LinearMap.ker peirceEval) : Module.End ℝ Zorn where
  toFun y := (D.1.1 (mkOff23 y)).b
  map_add' x y := by
    change (D.1.1 (mkOff23 (x + y))).b = (D.1.1 (mkOff23 x)).b + (D.1.1 (mkOff23 y)).b
    rw [mkOff23_add, map_add]; rfl
  map_smul' r x := by
    change (D.1.1 (mkOff23 (r • x))).b = r • (D.1.1 (mkOff23 x)).b
    rw [mkOff23_smul, map_smul]; rfl

/-- Induced endomorphism on the `(3,1)` Peirce block `Zorn`. -/
def stabOp31 (D : LinearMap.ker peirceEval) : Module.End ℝ Zorn where
  toFun z := (D.1.1 (mkOff31 z)).c
  map_add' x y := by
    change (D.1.1 (mkOff31 (x + y))).c = (D.1.1 (mkOff31 x)).c + (D.1.1 (mkOff31 y)).c
    rw [mkOff31_add, map_add]; rfl
  map_smul' r x := by
    change (D.1.1 (mkOff31 (r • x))).c = r • (D.1.1 (mkOff31 x)).c
    rw [mkOff31_smul, map_smul]; rfl

private lemma add_eq_zero_of_half_add_eq_zero {a b : ℝ} (h : a / 2 + b / 2 = 0) : a + b = 0 := by
  linarith [h]

theorem stabOp12_mem_zornSkewAdjoint (D : LinearMap.ker peirceEval) :
    stabOp12 D ∈ zornSkewAdjoint := by
  intro x y
  have h := D.1.2 (mkOff12 x) (mkOff12 y)
  rw [ker_preserves_off12 D x, ker_preserves_off12 D y] at h
  rw [mkOff12_mul_mkOff12, mkOff12_mul_mkOff12, mkOff12_mul_mkOff12] at h
  obtain ⟨hd1, hd2, _⟩ := (mem_ker_peirceEval_iff D.1).mp D.2
  have hleft : D.1.1 ⟨zornBilin x y / 2, zornBilin x y / 2, 0, 0, 0, 0⟩ = 0 := by
    have hdiag : (⟨zornBilin x y / 2, zornBilin x y / 2, 0, 0, 0, 0⟩ : H3) =
        (zornBilin x y / 2) • h3_diag₁ + (zornBilin x y / 2) • h3_diag₂ := by
      apply ext_h3 <;> simp [h3_diag₁, h3_diag₂, add_readback, smul_readback]
    rw [hdiag, map_add, map_smul, map_smul, hd1, hd2, smul_zero, add_zero]
  rw [hleft] at h
  have hα₁ := congrArg H3Zorn.α₁ h.symm
  simp only [add_readback, zero_readback] at hα₁
  exact add_eq_zero_of_half_add_eq_zero hα₁

theorem stabOp23_mem_zornSkewAdjoint (D : LinearMap.ker peirceEval) :
    stabOp23 D ∈ zornSkewAdjoint := by
  intro x y
  have h := D.1.2 (mkOff23 x) (mkOff23 y)
  rw [ker_preserves_off23 D x, ker_preserves_off23 D y] at h
  rw [mkOff23_mul_mkOff23, mkOff23_mul_mkOff23, mkOff23_mul_mkOff23] at h
  obtain ⟨_, hd2, hd3⟩ := (mem_ker_peirceEval_iff D.1).mp D.2
  have hleft : D.1.1 ⟨0, zornBilin x y / 2, zornBilin x y / 2, 0, 0, 0⟩ = 0 := by
    have hdiag : (⟨0, zornBilin x y / 2, zornBilin x y / 2, 0, 0, 0⟩ : H3) =
        (zornBilin x y / 2) • h3_diag₂ + (zornBilin x y / 2) • h3_diag₃ := by
      apply ext_h3 <;> simp [h3_diag₂, h3_diag₃, add_readback, smul_readback]
    rw [hdiag, map_add, map_smul, map_smul, hd2, hd3, smul_zero, add_zero]
  rw [hleft] at h
  have hα₂ := congrArg H3Zorn.α₂ h.symm
  simp only [add_readback, zero_readback] at hα₂
  exact add_eq_zero_of_half_add_eq_zero hα₂

/-- Linear restriction map from the Peirce idempotent stabilizer to `so(4,4)`. -/
def stabilizerRes12 : LinearMap.ker peirceEval →ₗ[ℝ] zornSkewAdjoint where
  toFun D := ⟨stabOp12 D, stabOp12_mem_zornSkewAdjoint D⟩
  map_add' D E := by
    apply Subtype.ext; apply LinearMap.ext; intro x
    change (D.1.1 (mkOff12 x)).a + (E.1.1 (mkOff12 x)).a = _
    rfl
  map_smul' r D := by
    apply Subtype.ext; apply LinearMap.ext; intro x
    change r • (D.1.1 (mkOff12 x)).a = _
    rfl

private lemma lie_mem_ker_peirceEval (D E : LinearMap.ker peirceEval) :
    (⟨⁅D.1.1, E.1.1⁆, H3ZornF4Derivations.lie_mem D.1.2 E.1.2⟩ : H3ZornF4Derivations) ∈
      LinearMap.ker peirceEval := by
  rw [mem_ker_peirceEval_iff]
  obtain ⟨hd1, hd2, hd3⟩ := (mem_ker_peirceEval_iff D.1).mp D.2
  obtain ⟨he1, he2, he3⟩ := (mem_ker_peirceEval_iff E.1).mp E.2
  refine ⟨?_, ?_, ?_⟩
  · change D.1.1 (E.1.1 h3_diag₁) - E.1.1 (D.1.1 h3_diag₁) = 0
    rw [he1, hd1, map_zero, map_zero, sub_self]
  · change D.1.1 (E.1.1 h3_diag₂) - E.1.1 (D.1.1 h3_diag₂) = 0
    rw [he2, hd2, map_zero, map_zero, sub_self]
  · change D.1.1 (E.1.1 h3_diag₃) - E.1.1 (D.1.1 h3_diag₃) = 0
    rw [he3, hd3, map_zero, map_zero, sub_self]

theorem stabilizerRes12_lie (D E : LinearMap.ker peirceEval) :
    (stabilizerRes12 ⟨⟨⁅D.1.1, E.1.1⁆, H3ZornF4Derivations.lie_mem D.1.2 E.1.2⟩,
      lie_mem_ker_peirceEval D E⟩).1 = ⁅(stabilizerRes12 D).1, (stabilizerRes12 E).1⁆ := by
  apply LinearMap.ext
  intro x
  simp only [stabilizerRes12, LinearMap.coe_mk, AddHom.coe_mk, stabOp12, Ring.lie_def,
    Module.End.mul_apply, LinearMap.sub_apply]
  have hDE : E.1.1 (mkOff12 x) = mkOff12 ((E.1.1 (mkOff12 x)).a) := ker_preserves_off12 E x
  have hED : D.1.1 (mkOff12 x) = mkOff12 ((D.1.1 (mkOff12 x)).a) := ker_preserves_off12 D x
  rw [hDE, hED]
  rfl

/-- **Split-Octonion Trace-Zero Right Nucleus Theorem**:
Any trace-zero element `u : ZornVectorMatrix ℝ` satisfying `(x * y) * u = x * (y * u)` for all
`x, y` must vanish identically. Tested at the three basis pairs `(b₁, b₂)`, `(b₂, b₃)`, `(b₄, b₅)`. -/
theorem zorn_right_nucleus_trace_zero_eq_zero (u : Zorn)
    (htr : u.a + u.b = 0)
    (hassoc : ∀ x y : Zorn,
      ZornVectorMatrix.mul (ZornVectorMatrix.mul x y) u =
        ZornVectorMatrix.mul x (ZornVectorMatrix.mul y u)) :
    u = 0 := by
  have h12 := hassoc (zorn_basis 1) (zorn_basis 2)
  have h23 := hassoc (zorn_basis 2) (zorn_basis 3)
  have h45 := hassoc (zorn_basis 4) (zorn_basis 5)
  have ha12 := congrArg ZornVectorMatrix.a h12
  have hv0_12 := congrArg (fun z : Zorn => z.v 0) h12
  have hv1_12 := congrArg (fun z : Zorn => z.v 1) h12
  have hw2_12 := congrArg (fun z : Zorn => z.w 2) h12
  have ha23 := congrArg ZornVectorMatrix.a h23
  have hw0_23 := congrArg (fun z : Zorn => z.w 0) h23
  have hv1_45 := congrArg (fun z : Zorn => z.v 1) h45
  have ha45 := congrArg ZornVectorMatrix.a h45
  simp only [zorn_basis, ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross,
    Fin.sum_univ_three] at ha12 hv0_12 hv1_12 hw2_12 ha23 hw0_23 hv1_45 ha45
  norm_num at ha12 hv0_12 hv1_12 hw2_12 ha23 hw0_23 hv1_45 ha45
  -- Note: ha12 gives -u.v 2 = 0, hv0_12 gives u.w 1 = 0, hv1_12 gives -u.w 0 = 0,
  -- hw2_12 gives u.a - u.b = 0; ha23 gives -u.v 0 = 0, hw0_23 gives u.a - u.b = 0;
  -- hv1_45 gives -u.v 0 = 0, ha45 gives -u.w 2 = 0; wait let's check v1 and w1!
  have hv1_23 := congrArg (fun z : Zorn => z.v 1) h23
  have hv0_45 := congrArg (fun z : Zorn => z.v 0) h45
  have hw1_45 := congrArg (fun z : Zorn => z.w 1) h45
  have hw0_45 := congrArg (fun z : Zorn => z.w 0) h45
  simp only [zorn_basis, ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross,
    Fin.sum_univ_three] at hv1_23 hv0_45 hw1_45 hw0_45
  norm_num at hv1_23 hv0_45 hw1_45 hw0_45
  apply ZornVectorMatrix.ext
  · change u.a = 0; linarith [htr]
  · funext i; fin_cases i <;> (change u.v _ = 0; dsimp; linarith [htr])
  · funext i; fin_cases i <;> (change u.w _ = 0; dsimp; linarith [htr])
  · change u.b = 0; linarith [htr]

theorem stabilizerRes12_injective : Function.Injective stabilizerRes12 := by
  rw [injective_iff_map_eq_zero]
  intro D hD
  have h12 : ∀ x : Zorn, stabOp12 D x = 0 := fun x =>
    congrArg (fun T : zornSkewAdjoint => T.1 x) hD
  have htri : ∀ x y : Zorn,
      stabOp31 D (ZornVectorMatrix.conj (ZornVectorMatrix.mul x y)) =
        ZornVectorMatrix.conj (ZornVectorMatrix.mul x (stabOp23 D y)) := by
    intro x y
    have hL := D.1.2 (mkOff12 x) (mkOff23 y)
    rw [ker_preserves_off12 D x, show (D.1.1 (mkOff12 x)).a = 0 from h12 x,
      mkOff12_zero, zero_mul, zero_add] at hL
    rw [ker_preserves_off23 D y, mkOff12_mul_mkOff23, mkOff12_mul_mkOff23,
      mkOff31_smul, map_smul, ker_preserves_off31 D _, mkOff31_smul] at hL
    have hc := congrArg H3Zorn.c hL
    change (1 / 2 : ℝ) • stabOp31 D (ZornVectorMatrix.conj (ZornVectorMatrix.mul x y)) =
      (1 / 2 : ℝ) • ZornVectorMatrix.conj (ZornVectorMatrix.mul x (stabOp23 D y)) at hc
    exact (smul_right_injective Zorn (by norm_num : (1 / 2 : ℝ) ≠ 0)) hc
  set u := stabOp23 D ZornVectorMatrix.one
  have hu_skew := stabOp23_mem_zornSkewAdjoint D ZornVectorMatrix.one ZornVectorMatrix.one
  rw [zornBilin_symm ZornVectorMatrix.one (stabOp23 D ZornVectorMatrix.one),
    zornBilin_one_right] at hu_skew
  have hu_tr : u.a + u.b = 0 := by
    have : 2 * ZornVectorMatrix.trace u = 0 := by linarith
    have : ZornVectorMatrix.trace u = 0 := by linarith
    exact this
  have h23_of_one : ∀ y : Zorn,
      stabOp31 D (ZornVectorMatrix.conj y) = ZornVectorMatrix.conj (stabOp23 D y) := by
    intro y
    have h := htri ZornVectorMatrix.one y
    rwa [ZornVectorMatrix.one_mul, ZornVectorMatrix.one_mul] at h
  have h31_of_x : ∀ x : Zorn,
      stabOp31 D (ZornVectorMatrix.conj x) =
        ZornVectorMatrix.conj (ZornVectorMatrix.mul x u) := by
    intro x
    have h := htri x ZornVectorMatrix.one
    rwa [ZornVectorMatrix.mul_one] at h
  have h23_eq : ∀ y : Zorn, stabOp23 D y = ZornVectorMatrix.mul y u := by
    intro y
    have h := (h23_of_one y).symm.trans (h31_of_x y)
    simpa [ZornVectorMatrix.conj_conj] using congrArg ZornVectorMatrix.conj h
  have hassoc : ∀ x y : Zorn,
      ZornVectorMatrix.mul (ZornVectorMatrix.mul x y) u =
        ZornVectorMatrix.mul x (ZornVectorMatrix.mul y u) := by
    intro x y
    have h1 := h31_of_x (ZornVectorMatrix.mul x y)
    have h2 := htri x y
    rw [h23_eq y] at h2
    have h3 := h1.symm.trans h2
    simpa [ZornVectorMatrix.conj_conj] using congrArg ZornVectorMatrix.conj h3
  have hu0 : u = 0 := zorn_right_nucleus_trace_zero_eq_zero u hu_tr hassoc
  have h23_zero : ∀ y : Zorn, stabOp23 D y = 0 := by
    intro y
    rw [h23_eq y, hu0]
    exact ZornVectorMatrix.mul_zero y
  have h31_zero : ∀ z : Zorn, stabOp31 D z = 0 := by
    intro z
    have h := h23_of_one (ZornVectorMatrix.conj z)
    rw [ZornVectorMatrix.conj_conj, h23_zero] at h
    exact h.trans ZornVectorMatrix.conj_zero
  obtain ⟨hd1, hd2, hd3⟩ := (mem_ker_peirceEval_iff D.1).mp D.2
  apply Subtype.ext; apply Subtype.ext; apply LinearMap.ext; intro X
  conv_lhs => rw [h3Zorn_decomp X]
  simp only [map_add, map_smul, hd1, hd2, hd3, smul_zero, add_zero, zero_add]
  rw [ker_preserves_off12 D X.a, ker_preserves_off23 D X.b, ker_preserves_off31 D X.c]
  change mkOff12 (stabOp12 D X.a) + mkOff23 (stabOp23 D X.b) + mkOff31 (stabOp31 D X.c) = 0
  rw [h12, h23_zero, h31_zero]
  simp only [mkOff12_zero, mkOff23_zero, mkOff31_zero, add_zero]

theorem innerD_off12_off12_mem_ker (x y : Zorn) :
    innerDerivF4 (mkOff12 x) (mkOff12 y) ∈ LinearMap.ker peirceEval := by
  rw [mem_ker_peirceEval_iff]
  refine ⟨?_, ?_, ?_⟩
  · change (h3ZornJordanInnerDerivation (mkOff12 x) (mkOff12 y) : EndH3) h3_diag₁ = 0
    rw [h3ZornJordanInnerDerivation_apply, mkOff12_mul_diag₁, mkOff12_mul_diag₁,
      mul_smul_comm, mul_smul_comm, mkOff12_mul_mkOff12, mkOff12_mul_mkOff12,
      zornBilin_symm x y, sub_self]
  · change (h3ZornJordanInnerDerivation (mkOff12 x) (mkOff12 y) : EndH3) h3_diag₂ = 0
    rw [h3ZornJordanInnerDerivation_apply, mkOff12_mul_diag₂, mkOff12_mul_diag₂,
      mul_smul_comm, mul_smul_comm, mkOff12_mul_mkOff12, mkOff12_mul_mkOff12,
      zornBilin_symm x y, sub_self]
  · change (h3ZornJordanInnerDerivation (mkOff12 x) (mkOff12 y) : EndH3) h3_diag₃ = 0
    rw [h3ZornJordanInnerDerivation_apply, mkOff12_mul_diag₃, mkOff12_mul_diag₃,
      mul_zero, mul_zero, sub_zero]

theorem innerD_off12_off12_apply_off12 (x y z : Zorn) :
    (h3ZornJordanInnerDerivation (mkOff12 x) (mkOff12 y) : EndH3) (mkOff12 z) =
      mkOff12 ((1 / 2 : ℝ) • (zornBilin y z • x - zornBilin x z • y)) := by
  rw [h3ZornJordanInnerDerivation_apply, mkOff12_mul_mkOff12, mkOff12_mul_mkOff12]
  have hterm : ∀ (r : ℝ) (w : Zorn),
      mkOff12 w * (⟨r / 2, r / 2, 0, 0, 0, 0⟩ : H3) = (r / 2 : ℝ) • mkOff12 w := by
    intro r w
    have hd : (⟨r / 2, r / 2, 0, 0, 0, 0⟩ : H3) = (r / 2) • h3_diag₁ + (r / 2) • h3_diag₂ := by
      apply ext_h3 <;> simp [h3_diag₁, h3_diag₂, add_readback, smul_readback]
    rw [hd, mul_add, mul_smul_comm, mul_smul_comm, mkOff12_mul_diag₁, mkOff12_mul_diag₂, smul_smul]
    module
  rw [hterm, hterm]
  have hsub : ∀ u v : Zorn, mkOff12 (u - v) = mkOff12 u - mkOff12 v := by
    intro u v
    apply ext_h3 <;> (simp [mkOff12, sub_readback, ← zvm_zero_def]; try rfl)
  rw [mkOff12_smul, hsub, mkOff12_smul, mkOff12_smul, smul_sub, smul_smul, smul_smul]
  module

/-- Bundled inner derivation in `LinearMap.ker peirceEval` generated by two `(1,2)` elements. -/
def innerKerOff12 (x y : Zorn) : LinearMap.ker peirceEval :=
  ⟨innerDerivF4 (mkOff12 x) (mkOff12 y), innerD_off12_off12_mem_ker x y⟩

theorem stabilizerRes12_innerKerOff12_bilin (x y p q : Zorn) :
    zornBilin p ((stabilizerRes12 (innerKerOff12 x y)).1 q) =
      (1 / 2 : ℝ) * (zornBilin y q * zornBilin p x - zornBilin x q * zornBilin p y) := by
  change zornBilin p ((h3ZornJordanInnerDerivation (mkOff12 x) (mkOff12 y) : EndH3) (mkOff12 q)).a = _
  rw [innerD_off12_off12_apply_off12]
  simp only [mkOff12, zornBilin_smul_right]
  rw [zornBilin_symm p (_ - _), zornBilin_sub_left, zornBilin_smul_left, zornBilin_smul_left,
    zornBilin_symm x p, zornBilin_symm y p]

/-- Explicit lift from `zornSkewAdjoint` (`so(4,4)`) back to `LinearMap.ker peirceEval`. -/
def liftSO44ToKer (T : zornSkewAdjoint) : LinearMap.ker peirceEval :=
  ∑ p : StrictPair8,
    (2 * zornBilin (zorn_basis p.1.1) (T.1 (zorn_basis p.1.2))) •
      innerKerOff12 (zornDualBasis p.1.1) (zornDualBasis p.1.2)

private lemma zornBilin_stabilizerRes12_sum (i : Fin 8) (q : Zorn)
    (s : Finset StrictPair8) (f : StrictPair8 → ℝ) (g : StrictPair8 → LinearMap.ker peirceEval) :
    zornBilin (zorn_basis i) ((stabilizerRes12 (∑ p ∈ s, f p • g p)).1 q) =
      ∑ p ∈ s, f p * zornBilin (zorn_basis i) ((stabilizerRes12 (g p)).1 q) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, map_zero, ZeroMemClass.coe_zero, LinearMap.zero_apply,
        zornBilin_zero_right]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, map_add, map_smul]
      change zornBilin (zorn_basis i)
          ((f a • (stabilizerRes12 (g a)).1 + (stabilizerRes12 (∑ p ∈ s, f p • g p)).1) q) = _
      rw [LinearMap.add_apply, LinearMap.smul_apply, zornBilin_add_right, zornBilin_smul_right, ih,
        Finset.sum_insert ha]

theorem stabilizerRes12_liftSO44ToKer (T : zornSkewAdjoint) :
    stabilizerRes12 (liftSO44ToKer T) = T := by
  apply Subtype.ext; apply LinearMap.ext; intro x
  rw [zorn_eq_sum_basis x, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [LinearMap.map_smul]
  refine congrArg (zornCoord x j • ·) ?_
  apply sub_eq_zero.mp
  apply zorn_eq_zero_of_forall_zornBilin_basis
  intro i
  rw [zornBilin_symm (zorn_basis i) _, zornBilin_sub_left, zornBilin_symm _ (zorn_basis i),
    zornBilin_symm _ (zorn_basis i)]
  dsimp [liftSO44ToKer]
  rw [zornBilin_stabilizerRes12_sum]
  have hpair_eval :
      ∀ p : StrictPair8,
        zornBilin (zorn_basis i)
          ((stabilizerRes12 (innerKerOff12 (zornDualBasis p.1.1) (zornDualBasis p.1.2))).1
            (zorn_basis j)) =
        (1 / 2 : ℝ) *
          ((if p.1.2 = j then 1 else 0) * (if i = p.1.1 then 1 else 0) -
           (if p.1.1 = j then 1 else 0) * (if i = p.1.2 then 1 else 0)) := by
    intro p
    rw [stabilizerRes12_innerKerOff12_bilin, zornBilin_dualBasis_basis, zornBilin_dualBasis_basis,
      zornBilin_basis_dualBasis, zornBilin_basis_dualBasis]
  simp_rw [hpair_eval]
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hne : i ≠ j := ne_of_lt hij
    have huniq : ∀ p : StrictPair8,
        (2 * zornBilin (zorn_basis p.1.1) (T.1 (zorn_basis p.1.2))) *
          ((1 / 2 : ℝ) *
            ((if p.1.2 = j then (1 : ℝ) else 0) * (if i = p.1.1 then 1 else 0) -
             (if p.1.1 = j then 1 else 0) * (if i = p.1.2 then 1 else 0))) =
        if p = ⟨(i, j), hij⟩ then zornBilin (zorn_basis i) (T.1 (zorn_basis j)) else 0 := by
      intro p
      by_cases hp : p = ⟨(i, j), hij⟩
      · subst hp; simp [hne]; ring
      · have hp12 : ¬ (p.1.2 = j ∧ i = p.1.1) := by
          rintro ⟨h2, h1⟩
          apply hp; apply Subtype.ext; apply Prod.ext <;> [exact h1.symm; exact h2]
        have hp21 : ¬ (p.1.1 = j ∧ i = p.1.2) := by
          rintro ⟨h1, h2⟩
          have : i < j := hij
          have : p.1.1 < p.1.2 := p.2
          omega
        simp only [hp, ↓reduceIte]
        by_cases hA : p.1.2 = j
        · have hB : i ≠ p.1.1 := fun h => hp12 ⟨hA, h⟩
          by_cases hC : p.1.1 = j
          · have hD : i ≠ p.1.2 := fun h => hp21 ⟨hC, h⟩
            simp [hA, hB, hC, hD]
          · simp [hA, hB, hC]
        · by_cases hC : p.1.1 = j
          · have hD : i ≠ p.1.2 := fun h => hp21 ⟨hC, h⟩
            simp [hA, hC, hD]
          · simp [hA, hC]
    rw [Finset.sum_congr rfl fun p _ => huniq p, Finset.sum_ite_eq']
    simp [sub_self]
  · have hzero : ∀ p : StrictPair8,
        (2 * zornBilin (zorn_basis p.1.1) (T.1 (zorn_basis p.1.2))) *
          ((1 / 2 : ℝ) *
            ((if p.1.2 = i then (1 : ℝ) else 0) * (if i = p.1.1 then 1 else 0) -
             (if p.1.1 = i then 1 else 0) * (if i = p.1.2 then 1 else 0))) = 0 := by
      intro p
      have hp_lt : p.1.1 < p.1.2 := p.2
      by_cases h1 : p.1.2 = i
      · have h2 : i ≠ p.1.1 := by omega
        have h3 : p.1.1 ≠ i := by omega
        simp [h1, h2, h3]
      · by_cases h3 : p.1.1 = i
        · have h4 : i ≠ p.1.2 := by omega
          simp [h1, h3, h4]
        · simp [h1, h3]
    rw [Finset.sum_congr rfl fun p _ => hzero p, Finset.sum_const_zero]
    have hself := T.2 (zorn_basis i) (zorn_basis i)
    rw [zornBilin_symm (T.1 (zorn_basis i)) (zorn_basis i)] at hself
    linarith
  · have hne : j ≠ i := ne_of_lt hji
    have huniq : ∀ p : StrictPair8,
        (2 * zornBilin (zorn_basis p.1.1) (T.1 (zorn_basis p.1.2))) *
          ((1 / 2 : ℝ) *
            ((if p.1.2 = j then (1 : ℝ) else 0) * (if i = p.1.1 then 1 else 0) -
             (if p.1.1 = j then 1 else 0) * (if i = p.1.2 then 1 else 0))) =
        if p = ⟨(j, i), hji⟩ then -zornBilin (zorn_basis j) (T.1 (zorn_basis i)) else 0 := by
      intro p
      by_cases hp : p = ⟨(j, i), hji⟩
      · subst hp; simp [hne.symm]; ring
      · have hp12 : ¬ (p.1.2 = j ∧ i = p.1.1) := by
          rintro ⟨h2, h1⟩
          have : p.1.1 < p.1.2 := p.2
          omega
        have hp21 : ¬ (p.1.1 = j ∧ i = p.1.2) := by
          rintro ⟨h1, h2⟩
          apply hp; apply Subtype.ext; apply Prod.ext <;> [exact h1; exact h2.symm]
        simp only [hp, ↓reduceIte]
        by_cases hA : p.1.2 = j
        · have hB : i ≠ p.1.1 := fun h => hp12 ⟨hA, h⟩
          by_cases hC : p.1.1 = j
          · have hD : i ≠ p.1.2 := fun h => hp21 ⟨hC, h⟩
            simp [hA, hB, hC, hD]
          · simp [hA, hB, hC]
        · by_cases hC : p.1.1 = j
          · have hD : i ≠ p.1.2 := fun h => hp21 ⟨hC, h⟩
            simp [hA, hC, hD]
          · simp [hA, hC]
    rw [Finset.sum_congr rfl fun p _ => huniq p, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    have hskew := T.2 (zorn_basis i) (zorn_basis j)
    rw [zornBilin_symm (T.1 (zorn_basis i)) (zorn_basis j)] at hskew
    linarith

theorem stabilizerRes12_surjective : Function.Surjective stabilizerRes12 :=
  fun T => ⟨liftSO44ToKer T, stabilizerRes12_liftSO44ToKer T⟩

/-- Complete linear isomorphism `LinearMap.ker peirceEval ≃ₗ[ℝ] zornSkewAdjoint` (`so(4,4)`). -/
def stabilizerEquivSO44 : LinearMap.ker peirceEval ≃ₗ[ℝ] zornSkewAdjoint :=
  LinearEquiv.ofBijective stabilizerRes12 ⟨stabilizerRes12_injective, stabilizerRes12_surjective⟩

/-! ## 5. Main `F₄` dimension, basis generation, linear independence, and `24 ⊕ 28` closure -/

instance : Module.Finite ℝ H3 :=
  Module.Finite.equiv h3ZornCoordEquiv.symm

/-- **Main Dimension Theorem (`D18_h3zorn_split_f4`)**:
$$\dim_{\mathbb{R}}\bigl(\operatorname{Der}(H_3(\mathbb{O}_s))\bigr) = 52.$$ -/
theorem finrank_H3ZornF4Derivations : Module.finrank ℝ H3ZornF4Derivations = 52 :=
  H3ZornF4BasisExactSpan.finrank_f4_real
    finrank_zorn finrank_zornSkewAdjoint
    peirceEval peirceSection peirceEval_peirceSection stabilizerEquivSO44

theorem finrank_ker_peirceEval : Module.finrank ℝ (LinearMap.ker peirceEval) = 28 := by
  rw [stabilizerEquivSO44.finrank_eq, finrank_zornSkewAdjoint]

theorem range_peirceEval_eq_top : LinearMap.range peirceEval = ⊤ :=
  H3ZornF4BasisExactSpan.range_eq_top_of_section peirceEval peirceSection peirceEval_peirceSection

/-- Submodule spanned by the first 24 Peirce shift basis derivations. -/
def shiftSubmodule : Submodule ℝ EndH3 :=
  Submodule.span ℝ (Set.range fun i : Fin 24 => (f4Basis ⟨i.1, by omega⟩).1)

/-- Submodule spanned by the last 28 `so(4,4)` triality basis derivations. -/
def trialitySubmodule : Submodule ℝ EndH3 :=
  Submodule.span ℝ (Set.range fun i : Fin 28 => (f4Basis ⟨24 + i.1, by omega⟩).1)

theorem shiftSubmodule_le_F4 : shiftSubmodule ≤ H3ZornF4Derivations.toSubmodule := by
  refine Submodule.span_le.mpr ?_
  rintro D ⟨i, rfl⟩
  exact (f4Basis ⟨i.1, by omega⟩).property

theorem trialitySubmodule_le_F4 : trialitySubmodule ≤ H3ZornF4Derivations.toSubmodule := by
  refine Submodule.span_le.mpr ?_
  rintro D ⟨i, rfl⟩
  exact (f4Basis ⟨24 + i.1, by omega⟩).property

theorem shiftSubmodule_le_f4BasisSpan : shiftSubmodule ≤ f4BasisSpan := by
  refine Submodule.span_le.mpr ?_
  rintro D ⟨i, rfl⟩
  exact Submodule.subset_span ⟨⟨i.1, by omega⟩, rfl⟩

theorem trialitySubmodule_le_f4BasisSpan : trialitySubmodule ≤ f4BasisSpan := by
  refine Submodule.span_le.mpr ?_
  rintro D ⟨i, rfl⟩
  exact Submodule.subset_span ⟨⟨24 + i.1, by omega⟩, rfl⟩

theorem f4BasisSpan_eq_shift_sup_triality :
    f4BasisSpan = shiftSubmodule ⊔ trialitySubmodule := by
  refine le_antisymm ?_ (sup_le shiftSubmodule_le_f4BasisSpan trialitySubmodule_le_f4BasisSpan)
  refine Submodule.span_le.mpr ?_
  rintro D ⟨i, rfl⟩
  by_cases hi : i.1 < 24
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨⟨i.1, hi⟩, rfl⟩)
  · refine Submodule.mem_sup_right (Submodule.subset_span ⟨⟨i.1 - 24, by omega⟩, ?_⟩)
    dsimp only
    have hid : (⟨24 + (i.1 - 24), by omega⟩ : Fin 52) = i := by
      ext; dsimp; omega
    rw [hid]

private def trialityPair (t : Fin 28) : StrictPair8 :=
  (![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(0, 3), by decide⟩, ⟨(0, 4), by decide⟩,
     ⟨(0, 5), by decide⟩, ⟨(0, 6), by decide⟩, ⟨(0, 7), by decide⟩, ⟨(1, 2), by decide⟩,
     ⟨(1, 3), by decide⟩, ⟨(1, 4), by decide⟩, ⟨(1, 5), by decide⟩, ⟨(1, 6), by decide⟩,
     ⟨(1, 7), by decide⟩, ⟨(2, 3), by decide⟩, ⟨(2, 4), by decide⟩, ⟨(2, 5), by decide⟩,
     ⟨(2, 6), by decide⟩, ⟨(2, 7), by decide⟩, ⟨(3, 4), by decide⟩, ⟨(3, 5), by decide⟩,
     ⟨(3, 6), by decide⟩, ⟨(3, 7), by decide⟩, ⟨(4, 5), by decide⟩, ⟨(4, 6), by decide⟩,
     ⟨(4, 7), by decide⟩, ⟨(5, 6), by decide⟩, ⟨(5, 7), by decide⟩, ⟨(6, 7), by decide⟩] :
      Fin 28 → StrictPair8) t

private theorem trialityPair_injective : Function.Injective trialityPair := by
  intro i j hij
  revert i j hij
  decide

private theorem trialityPair_surjective :
    ∀ (i j : Fin 8), i < j → ∃ t : Fin 28, (trialityPair t).1 = (i, j) := by
  decide

private theorem f4Basis_triality_eq (t : Fin 28) :
    (f4Basis ⟨24 + t.1, by omega⟩).1 =
      (h3ZornJordanInnerDerivation
        (h3_off₁₂ (trialityPair t).1.1) (h3_off₁₂ (trialityPair t).1.2) : EndH3) := by
  fin_cases t <;> rfl

private theorem f4Basis_shift_12 (k : Fin 8) :
    (f4Basis ⟨k.1, by omega⟩).1 =
      (h3ZornJordanInnerDerivation h3_diag₁ (h3_off₁₂ k) : EndH3) := by
  fin_cases k <;> rfl

private theorem f4Basis_shift_31 (k : Fin 8) :
    (f4Basis ⟨8 + k.1, by omega⟩).1 =
      (h3ZornJordanInnerDerivation h3_diag₁ (h3_off₃₁ k) : EndH3) := by
  fin_cases k <;> rfl

private theorem f4Basis_shift_23 (k : Fin 8) :
    (f4Basis ⟨16 + k.1, by omega⟩).1 =
      (h3ZornJordanInnerDerivation h3_diag₂ (h3_off₂₃ k) : EndH3) := by
  fin_cases k <;> rfl

private theorem f4Basis_off12_pair (i j : Fin 8) (hij : i < j) :
    (h3ZornJordanInnerDerivation (h3_off₁₂ i) (h3_off₁₂ j) : EndH3) ∈ trialitySubmodule := by
  rcases trialityPair_surjective i j hij with ⟨t, ht⟩
  have h1 : (trialityPair t).1.1 = i := congrArg Prod.fst ht
  have h2 : (trialityPair t).1.2 = j := congrArg Prod.snd ht
  rw [← h1, ← h2, ← f4Basis_triality_eq t]
  exact Submodule.subset_span ⟨t, rfl⟩

theorem innerD_off12_basis_mem_trialitySubmodule (i j : Fin 8) :
    (h3ZornJordanInnerDerivation (h3_off₁₂ i) (h3_off₁₂ j) : EndH3) ∈ trialitySubmodule := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact f4Basis_off12_pair i j hij
  · rw [h3ZornJordanInnerDerivation_self]
    exact trialitySubmodule.zero_mem
  · rw [h3ZornJordanInnerDerivation_swap]
    exact trialitySubmodule.neg_mem (f4Basis_off12_pair j i hji)

theorem innerD_off12_dualBasis_mem_trialitySubmodule (i j : Fin 8) :
    (h3ZornJordanInnerDerivation (mkOff12 (zornDualBasis i)) (mkOff12 (zornDualBasis j)) : EndH3) ∈
      trialitySubmodule := by
  simp only [zornDualBasis, mkOff12_smul, h3ZornJordanInnerDerivation_smul_left,
    h3ZornJordanInnerDerivation_smul_right, mkOff12_basis]
  exact trialitySubmodule.smul_mem _ (trialitySubmodule.smul_mem _
    (innerD_off12_basis_mem_trialitySubmodule _ _))

theorem peirceSection_mem_shiftSubmodule (p : Zorn × (Zorn × Zorn)) :
    (peirceSection p).1 ∈ shiftSubmodule := by
  rcases p with ⟨x, y, z⟩
  change ((-4 : ℝ) • ((innerDerivF4 h3_diag₁ (mkOff12 x)).1 +
      (innerDerivF4 h3_diag₂ (mkOff23 y)).1 +
      (innerDerivF4 h3_diag₁ (mkOff31 z)).1) : EndH3) ∈ shiftSubmodule
  refine shiftSubmodule.smul_mem (-4 : ℝ) (shiftSubmodule.add_mem (shiftSubmodule.add_mem ?_ ?_) ?_)
  · rw [zorn_eq_sum_basis x]
    have hsum12 : ∀ s : Finset (Fin 8), ∀ c : Fin 8 → ℝ,
        (h3ZornJordanInnerDerivation h3_diag₁ (mkOff12 (∑ i ∈ s, c i • zorn_basis i)) : EndH3) ∈
          shiftSubmodule := by
      intro s c
      induction s using Finset.induction_on with
      | empty =>
          simp only [Finset.sum_empty, mkOff12_zero]
          have : (h3ZornJordanInnerDerivation h3_diag₁ (0 : H3) : EndH3) = 0 := by
            apply LinearMap.ext; intro u
            rw [h3ZornJordanInnerDerivation_apply, zero_mul, mul_zero, zero_mul, sub_self]; rfl
          rw [this]; exact shiftSubmodule.zero_mem
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, mkOff12_add, mkOff12_smul, h3ZornJordanInnerDerivation_add_right,
            h3ZornJordanInnerDerivation_smul_right, mkOff12_basis]
          refine shiftSubmodule.add_mem (shiftSubmodule.smul_mem _ ?_) ih
          rw [← f4Basis_shift_12 a]
          exact Submodule.subset_span ⟨⟨a.1, by omega⟩, rfl⟩
    exact hsum12 Finset.univ (zornCoord x)
  · rw [zorn_eq_sum_basis y]
    have hsum23 : ∀ s : Finset (Fin 8), ∀ c : Fin 8 → ℝ,
        (h3ZornJordanInnerDerivation h3_diag₂ (mkOff23 (∑ i ∈ s, c i • zorn_basis i)) : EndH3) ∈
          shiftSubmodule := by
      intro s c
      induction s using Finset.induction_on with
      | empty =>
          simp only [Finset.sum_empty, mkOff23_zero]
          have : (h3ZornJordanInnerDerivation h3_diag₂ (0 : H3) : EndH3) = 0 := by
            apply LinearMap.ext; intro u
            rw [h3ZornJordanInnerDerivation_apply, zero_mul, mul_zero, zero_mul, sub_self]; rfl
          rw [this]; exact shiftSubmodule.zero_mem
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, mkOff23_add, mkOff23_smul, h3ZornJordanInnerDerivation_add_right,
            h3ZornJordanInnerDerivation_smul_right, mkOff23_basis]
          refine shiftSubmodule.add_mem (shiftSubmodule.smul_mem _ ?_) ih
          rw [← f4Basis_shift_23 a]
          exact Submodule.subset_span ⟨⟨16 + a.1, by omega⟩, rfl⟩
    exact hsum23 Finset.univ (zornCoord y)
  · rw [zorn_eq_sum_basis z]
    have hsum31 : ∀ s : Finset (Fin 8), ∀ c : Fin 8 → ℝ,
        (h3ZornJordanInnerDerivation h3_diag₁ (mkOff31 (∑ i ∈ s, c i • zorn_basis i)) : EndH3) ∈
          shiftSubmodule := by
      intro s c
      induction s using Finset.induction_on with
      | empty =>
          simp only [Finset.sum_empty, mkOff31_zero]
          have : (h3ZornJordanInnerDerivation h3_diag₁ (0 : H3) : EndH3) = 0 := by
            apply LinearMap.ext; intro u
            rw [h3ZornJordanInnerDerivation_apply, zero_mul, mul_zero, zero_mul, sub_self]; rfl
          rw [this]; exact shiftSubmodule.zero_mem
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, mkOff31_add, mkOff31_smul, h3ZornJordanInnerDerivation_add_right,
            h3ZornJordanInnerDerivation_smul_right, mkOff31_basis]
          refine shiftSubmodule.add_mem (shiftSubmodule.smul_mem _ ?_) ih
          rw [← f4Basis_shift_31 a]
          exact Submodule.subset_span ⟨⟨8 + a.1, by omega⟩, rfl⟩
    exact hsum31 Finset.univ (zornCoord z)

theorem shiftSubmodule_mem_eq_peirceSection (D : EndH3) (hD : D ∈ shiftSubmodule) :
    D = (peirceSection (peirceEval ⟨D, shiftSubmodule_le_F4 hD⟩)).1 := by
  refine Submodule.span_induction (p := fun E hE =>
      E = (peirceSection (peirceEval ⟨E, shiftSubmodule_le_F4 hE⟩)).1)
    ?_ ?_ ?_ ?_ hD
  · rintro _ ⟨i, rfl⟩
    have hi : i.1 < 8 ∨ (8 ≤ i.1 ∧ i.1 < 16) ∨ (16 ≤ i.1 ∧ i.1 < 24) := by omega
    rcases hi with h1 | h2 | h3
    · have hid : (⟨i.1, by omega⟩ : Fin 52) = ⟨(⟨i.1, h1⟩ : Fin 8).1, by omega⟩ := rfl
      simp_rw [hid, f4Basis_shift_12 ⟨i.1, h1⟩]
      have hmem : (⟨(h3ZornJordanInnerDerivation h3_diag₁ (h3_off₁₂ ⟨i.1, h1⟩) : EndH3),
          h3ZornJordanInnerDerivation_mem_F4 _ _⟩ : H3ZornF4Derivations) =
          innerDerivF4 h3_diag₁ (mkOff12 (zorn_basis ⟨i.1, h1⟩)) := rfl
      rw [hmem, innerD_diag1_off12_eval]
      have hz2 : (h3ZornJordanInnerDerivation h3_diag₂ (0 : H3) : EndH3) = 0 := by
        apply LinearMap.ext; intro u
        rw [h3ZornJordanInnerDerivation_apply, zero_mul, mul_zero, zero_mul, sub_self]; rfl
      have hz1 : (h3ZornJordanInnerDerivation h3_diag₁ (0 : H3) : EndH3) = 0 := by
        apply LinearMap.ext; intro u
        rw [h3ZornJordanInnerDerivation_apply, zero_mul, mul_zero, zero_mul, sub_self]; rfl
      change (h3ZornJordanInnerDerivation h3_diag₁ (mkOff12 (zorn_basis ⟨i.1, h1⟩)) : EndH3) =
        (-4 : ℝ) • ((h3ZornJordanInnerDerivation h3_diag₁ (mkOff12 ((-1 / 4 : ℝ) • zorn_basis ⟨i.1, h1⟩)) : EndH3) +
          (h3ZornJordanInnerDerivation h3_diag₂ (mkOff23 0) : EndH3) +
          (h3ZornJordanInnerDerivation h3_diag₁ (mkOff31 0) : EndH3))
      rw [mkOff23_zero, mkOff31_zero, hz1, hz2, add_zero, add_zero, mkOff12_smul,
        h3ZornJordanInnerDerivation_smul_right, smul_smul]
      norm_num
    · have hid : (⟨i.1, by omega⟩ : Fin 52) = ⟨8 + (⟨i.1 - 8, by omega⟩ : Fin 8).1, by omega⟩ := by
        ext; dsimp; omega
      simp_rw [hid, f4Basis_shift_31 ⟨i.1 - 8, by omega⟩]
      have hmem : (⟨(h3ZornJordanInnerDerivation h3_diag₁ (h3_off₃₁ ⟨i.1 - 8, by omega⟩) : EndH3),
          h3ZornJordanInnerDerivation_mem_F4 _ _⟩ : H3ZornF4Derivations) =
          innerDerivF4 h3_diag₁ (mkOff31 (zorn_basis ⟨i.1 - 8, by omega⟩)) := rfl
      rw [hmem, innerD_diag1_off31_eval]
      have hz2 : (h3ZornJordanInnerDerivation h3_diag₂ (0 : H3) : EndH3) = 0 := by
        apply LinearMap.ext; intro u
        rw [h3ZornJordanInnerDerivation_apply, zero_mul, mul_zero, zero_mul, sub_self]; rfl
      have hz1 : (h3ZornJordanInnerDerivation h3_diag₁ (0 : H3) : EndH3) = 0 := by
        apply LinearMap.ext; intro u
        rw [h3ZornJordanInnerDerivation_apply, zero_mul, mul_zero, zero_mul, sub_self]; rfl
      change (h3ZornJordanInnerDerivation h3_diag₁ (mkOff31 (zorn_basis ⟨i.1 - 8, by omega⟩)) : EndH3) =
        (-4 : ℝ) • ((h3ZornJordanInnerDerivation h3_diag₁ (mkOff12 0) : EndH3) +
          (h3ZornJordanInnerDerivation h3_diag₂ (mkOff23 0) : EndH3) +
          (h3ZornJordanInnerDerivation h3_diag₁ (mkOff31 ((-1 / 4 : ℝ) • zorn_basis ⟨i.1 - 8, by omega⟩)) : EndH3))
      rw [mkOff12_zero, mkOff23_zero, hz1, hz2, zero_add, zero_add, mkOff31_smul,
        h3ZornJordanInnerDerivation_smul_right, smul_smul]
      norm_num
    · have hid : (⟨i.1, by omega⟩ : Fin 52) = ⟨16 + (⟨i.1 - 16, by omega⟩ : Fin 8).1, by omega⟩ := by
        ext; dsimp; omega
      simp_rw [hid, f4Basis_shift_23 ⟨i.1 - 16, by omega⟩]
      have hmem : (⟨(h3ZornJordanInnerDerivation h3_diag₂ (h3_off₂₃ ⟨i.1 - 16, by omega⟩) : EndH3),
          h3ZornJordanInnerDerivation_mem_F4 _ _⟩ : H3ZornF4Derivations) =
          innerDerivF4 h3_diag₂ (mkOff23 (zorn_basis ⟨i.1 - 16, by omega⟩)) := rfl
      rw [hmem, innerD_diag2_off23_eval]
      have hz1 : (h3ZornJordanInnerDerivation h3_diag₁ (0 : H3) : EndH3) = 0 := by
        apply LinearMap.ext; intro u
        rw [h3ZornJordanInnerDerivation_apply, zero_mul, mul_zero, zero_mul, sub_self]; rfl
      change (h3ZornJordanInnerDerivation h3_diag₂ (mkOff23 (zorn_basis ⟨i.1 - 16, by omega⟩)) : EndH3) =
        (-4 : ℝ) • ((h3ZornJordanInnerDerivation h3_diag₁ (mkOff12 0) : EndH3) +
          (h3ZornJordanInnerDerivation h3_diag₂ (mkOff23 ((-1 / 4 : ℝ) • zorn_basis ⟨i.1 - 16, by omega⟩)) : EndH3) +
          (h3ZornJordanInnerDerivation h3_diag₁ (mkOff31 0) : EndH3))
      rw [mkOff12_zero, mkOff31_zero, hz1, zero_add, add_zero, mkOff23_smul,
        h3ZornJordanInnerDerivation_smul_right, smul_smul]
      norm_num
  · have h0 : (⟨0, shiftSubmodule_le_F4 shiftSubmodule.zero_mem⟩ : H3ZornF4Derivations) = 0 := rfl
    rw [h0, map_zero, map_zero]; rfl
  · intro E₁ E₂ hE₁ hE₂ ih₁ ih₂
    have heq : (⟨E₁ + E₂, shiftSubmodule_le_F4 (shiftSubmodule.add_mem hE₁ hE₂)⟩ :
        H3ZornF4Derivations) =
        ⟨E₁, shiftSubmodule_le_F4 hE₁⟩ + ⟨E₂, shiftSubmodule_le_F4 hE₂⟩ := rfl
    have hcoe : ∀ a b : H3ZornF4Derivations, (a + b).1 = a.1 + b.1 := fun _ _ => rfl
    rw [heq, map_add, map_add, hcoe]
    conv_lhs => rw [ih₁, ih₂]
  · intro r E hE ih
    have heq : (⟨r • E, shiftSubmodule_le_F4 (shiftSubmodule.smul_mem r hE)⟩ :
        H3ZornF4Derivations) = r • ⟨E, shiftSubmodule_le_F4 hE⟩ := rfl
    have hcoe : ∀ (c : ℝ) (a : H3ZornF4Derivations), (c • a).1 = c • a.1 := fun _ _ => rfl
    rw [heq, map_smul, map_smul, hcoe]
    conv_lhs => rw [ih]

theorem trialitySubmodule_eq_ker_peirceEval :
    ∀ D : H3ZornF4Derivations, D ∈ LinearMap.ker peirceEval ↔ D.1 ∈ trialitySubmodule := by
  intro D
  constructor
  · intro hker
    have hlift : liftSO44ToKer (stabilizerRes12 ⟨D, hker⟩) = ⟨D, hker⟩ :=
      stabilizerRes12_injective (stabilizerRes12_liftSO44ToKer (stabilizerRes12 ⟨D, hker⟩))
    have hcoe : D.1 = (liftSO44ToKer (stabilizerRes12 ⟨D, hker⟩)).1.1 :=
      congrArg (fun x : LinearMap.ker peirceEval => x.1.1) hlift.symm
    rw [hcoe]
    dsimp [liftSO44ToKer]
    have hsum_coe : ∀ (s : Finset StrictPair8) (f : StrictPair8 → LinearMap.ker peirceEval),
        (∑ x ∈ s, f x).1.1 = ∑ x ∈ s, (f x).1.1 := by
      intro s f
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]; exact congrArg (_ + ·) ih
    rw [hsum_coe]
    refine trialitySubmodule.sum_mem fun p _ => trialitySubmodule.smul_mem _ ?_
    exact innerD_off12_dualBasis_mem_trialitySubmodule p.1.1 p.1.2
  · intro htri
    rw [LinearMap.mem_ker]
    refine Submodule.span_induction
      (p := fun E hE => peirceEval ⟨E, trialitySubmodule_le_F4 hE⟩ = 0)
      ?_ ?_ ?_ ?_ htri
    · rintro _ ⟨i, rfl⟩
      dsimp only
      have hmem : (⟨(f4Basis ⟨24 + i.1, by omega⟩).1,
          trialitySubmodule_le_F4 (Submodule.subset_span ⟨i, rfl⟩)⟩ : H3ZornF4Derivations) =
          innerDerivF4 (mkOff12 (zorn_basis (trialityPair i).1.1))
            (mkOff12 (zorn_basis (trialityPair i).1.2)) := by
        apply Subtype.ext
        exact f4Basis_triality_eq i
      rw [hmem]
      exact LinearMap.mem_ker.mp (innerD_off12_off12_mem_ker _ _)
    · have h0 : (⟨0, trialitySubmodule_le_F4 trialitySubmodule.zero_mem⟩ : H3ZornF4Derivations) = 0 := rfl
      rw [h0, map_zero]
    · intro E₁ E₂ hE₁ hE₂ ih₁ ih₂
      have heq : (⟨E₁ + E₂, trialitySubmodule_le_F4 (trialitySubmodule.add_mem hE₁ hE₂)⟩ :
          H3ZornF4Derivations) =
          ⟨E₁, trialitySubmodule_le_F4 hE₁⟩ + ⟨E₂, trialitySubmodule_le_F4 hE₂⟩ := rfl
      rw [heq, map_add, ih₁, ih₂, add_zero]
    · intro r E hE ih
      have heq : (⟨r • E, trialitySubmodule_le_F4 (trialitySubmodule.smul_mem r hE)⟩ :
          H3ZornF4Derivations) = r • ⟨E, trialitySubmodule_le_F4 hE⟩ := rfl
      rw [heq, map_smul, ih, smul_zero]

/-- **Intrinsic `24 + 28` Peirce–Triality Span Closure**:
`shiftSubmodule ⊔ trialitySubmodule = H3ZornF4Derivations.toSubmodule`. -/
theorem shiftSubmodule_sup_trialitySubmodule :
    shiftSubmodule ⊔ trialitySubmodule = H3ZornF4Derivations.toSubmodule := by
  refine le_antisymm (sup_le shiftSubmodule_le_F4 trialitySubmodule_le_F4) ?_
  intro D hD
  let D_sub : H3ZornF4Derivations := ⟨D, hD⟩
  let S : H3ZornF4Derivations := peirceSection (peirceEval D_sub)
  let K : H3ZornF4Derivations := D_sub - S
  have hKker : K ∈ LinearMap.ker peirceEval := by
    rw [LinearMap.mem_ker, map_sub, peirceEval_peirceSection, sub_self]
  have hSmem : S.1 ∈ shiftSubmodule := peirceSection_mem_shiftSubmodule (peirceEval D_sub)
  have hKmem : K.1 ∈ trialitySubmodule := (trialitySubmodule_eq_ker_peirceEval K).mp hKker
  have hDeq : D = S.1 + K.1 := by
    change D_sub.1 = S.1 + (D_sub.1 - S.1)
    abel
  rw [hDeq]
  exact Submodule.add_mem_sup hSmem hKmem

/-- **Intrinsic Directness (`shiftSubmodule ⊓ trialitySubmodule = ⊥`)**:
The 24-dimensional Peirce-shift sector and 28-dimensional `so(4,4)` stabilizer sector are disjoint. -/
theorem disjoint_shiftSubmodule_trialitySubmodule :
    Disjoint shiftSubmodule trialitySubmodule := by
  rw [disjoint_iff]
  ext D
  simp only [Submodule.mem_inf, Submodule.mem_bot]
  constructor
  · rintro ⟨hs, ht⟩
    have hker : peirceEval ⟨D, shiftSubmodule_le_F4 hs⟩ = 0 := by
      have ht' := (trialitySubmodule_eq_ker_peirceEval ⟨D, trialitySubmodule_le_F4 ht⟩).mpr ht
      exact LinearMap.mem_ker.mp ht'
    rw [shiftSubmodule_mem_eq_peirceSection D hs, hker, map_zero, ZeroMemClass.coe_zero]
  · rintro rfl
    exact ⟨shiftSubmodule.zero_mem, trialitySubmodule.zero_mem⟩

/-- **Exact Span Identity**:
The 52 explicit inner derivations `f4Basis` span all of `H3ZornF4Derivations`. -/
theorem f4BasisSpan_eq_H3ZornF4Derivations :
    f4BasisSpan = H3ZornF4Derivations.toSubmodule := by
  rw [f4BasisSpan_eq_shift_sup_triality, shiftSubmodule_sup_trialitySubmodule]

/-- **Exact Dimension of `f4BasisSpan` is `52`**. -/
theorem finrank_f4BasisSpan : Module.finrank ℝ f4BasisSpan = 52 := by
  rw [f4BasisSpan_eq_H3ZornF4Derivations]
  exact finrank_H3ZornF4Derivations

/-- **Exact Linear Independence of all 52 `f4Basis` Derivations** (intrinsic algebraic proof). -/
theorem f4Basis_linearIndependent :
    LinearIndependent ℝ (fun i : Fin 52 => (f4Basis i).1) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum_F4 : (∑ i : Fin 52, g i • f4Basis i : H3ZornF4Derivations).1 =
      ∑ i : Fin 52, g i • (f4Basis i).1 := by
    have hgen : ∀ (s : Finset (Fin 52)) (u : Fin 52 → H3ZornF4Derivations),
        (∑ x ∈ s, u x).1 = ∑ x ∈ s, (u x).1 := by
      intro s u
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          exact congrArg (_ + ·) ih
    rw [hgen]
    rfl
  have hgF4 : (∑ i : Fin 52, g i • f4Basis i : H3ZornF4Derivations) = 0 := by
    apply Subtype.ext
    rw [hsum_F4]
    exact hg
  have heval := congrArg peirceEval hgF4
  rw [map_zero, map_sum] at heval
  have hpart : ∀ i : Fin 52, peirceEval (f4Basis i) =
      if h1 : i.1 < 8 then ((-1 / 4 : ℝ) • zorn_basis ⟨i.1, h1⟩, (0, 0))
      else if h2 : i.1 < 16 then (0, (0, (-1 / 4 : ℝ) • zorn_basis ⟨i.1 - 8, by omega⟩))
      else if h3 : i.1 < 24 then (0, ((-1 / 4 : ℝ) • zorn_basis ⟨i.1 - 16, by omega⟩, 0))
      else 0 := by
    intro i
    by_cases h1 : i.1 < 8
    · rw [dite_eq_left h1]
      have hmem : f4Basis i = innerDerivF4 h3_diag₁ (mkOff12 (zorn_basis ⟨i.1, h1⟩)) :=
        Subtype.ext (f4Basis_shift_12 ⟨i.1, h1⟩)
      rw [hmem, innerD_diag1_off12_eval]
    · by_cases h2 : i.1 < 16
      · rw [dite_eq_right h1, dite_eq_left h2]
        have hmem : f4Basis i = innerDerivF4 h3_diag₁ (mkOff31 (zorn_basis ⟨i.1 - 8, by omega⟩)) := by
          apply Subtype.ext
          let k : Fin 8 := ⟨i.1 - 8, by omega⟩
          have hid : i = ⟨8 + k.1, by omega⟩ := by ext; dsimp [k]; omega
          conv_lhs => rw [hid]
          exact f4Basis_shift_31 k
        rw [hmem, innerD_diag1_off31_eval]
      · by_cases h3 : i.1 < 24
        · rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]
          have hmem : f4Basis i = innerDerivF4 h3_diag₂ (mkOff23 (zorn_basis ⟨i.1 - 16, by omega⟩)) := by
            apply Subtype.ext
            let k : Fin 8 := ⟨i.1 - 16, by omega⟩
            have hid : i = ⟨16 + k.1, by omega⟩ := by ext; dsimp [k]; omega
            conv_lhs => rw [hid]
            exact f4Basis_shift_23 k
          rw [hmem, innerD_diag2_off23_eval]
        · rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3]
          have htri : (f4Basis i).1 ∈ trialitySubmodule := by
            refine Submodule.subset_span ⟨⟨i.1 - 24, by omega⟩, ?_⟩
            dsimp only
            have hid : (⟨24 + (i.1 - 24), by omega⟩ : Fin 52) = i := by ext; dsimp; omega
            rw [hid]
          exact LinearMap.mem_ker.mp ((trialitySubmodule_eq_ker_peirceEval (f4Basis i)).mpr htri)
  have hg12 : ∀ k : Fin 8, g ⟨k.1, by omega⟩ = 0 := by
    intro k
    have hfst := congrArg (fun p : Zorn × (Zorn × Zorn) => zornBilin (zornDualBasis k) p.1) heval
    simp only [map_smul, Prod.fst_sum, Prod.smul_fst, Prod.fst_zero, zornBilin_zero_right,
      zornBilin_sum_right] at hfst
    have hterm : ∀ i : Fin 52,
        zornBilin (zornDualBasis k) (g i • (peirceEval (f4Basis i)).1) =
          if i = ⟨k.1, by omega⟩ then (-1 / 4 : ℝ) * g i else 0 := by
      intro i
      rw [hpart i, zornBilin_smul_right]
      by_cases h1 : i.1 < 8
      · rw [dite_eq_left h1, zornBilin_smul_right, zornBilin_dualBasis_basis]
        by_cases hik : i = ⟨k.1, by omega⟩
        · have hk : k = ⟨i.1, h1⟩ := by ext; have := congrArg Fin.val hik; exact this.symm
          rw [if_pos hk, if_pos hik]; ring
        · have hneq : k ≠ ⟨i.1, h1⟩ := fun heq => hik (by ext; exact (congrArg Fin.val heq).symm)
          simp [hik, hneq]
      · have hik : i ≠ ⟨k.1, by omega⟩ := fun heq => h1 (by rw [heq]; exact k.isLt)
        by_cases h2 : i.1 < 16
        · rw [dite_eq_right h1, dite_eq_left h2]; simp [hik]
        · by_cases h3 : i.1 < 24
          · rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]; simp [hik]
          · rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3]; simp [hik]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq'] at hfst
    simp only [Finset.mem_univ, ↓reduceIte] at hfst
    linarith
  have hg31 : ∀ k : Fin 8, g ⟨8 + k.1, by omega⟩ = 0 := by
    intro k
    have hsnd := congrArg (fun p : Zorn × (Zorn × Zorn) => zornBilin (zornDualBasis k) p.2.2) heval
    simp only [map_smul, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero, zornBilin_zero_right,
      zornBilin_sum_right] at hsnd
    have hterm : ∀ i : Fin 52,
        zornBilin (zornDualBasis k) (g i • (peirceEval (f4Basis i)).2.2) =
          if i = ⟨8 + k.1, by omega⟩ then (-1 / 4 : ℝ) * g i else 0 := by
      intro i
      rw [hpart i, zornBilin_smul_right]
      by_cases h1 : i.1 < 8
      · have hik : i ≠ ⟨8 + k.1, by omega⟩ := fun heq => by
          have hval : i.1 = 8 + k.1 := by simpa using congrArg Fin.val heq
          omega
        rw [dite_eq_left h1]; simp [hik]
      · by_cases h2 : i.1 < 16
        · rw [dite_eq_right h1, dite_eq_left h2,
            zornBilin_smul_right, zornBilin_dualBasis_basis]
          by_cases hik : i = ⟨8 + k.1, by omega⟩
          · have hval : i.1 = 8 + k.1 := by simpa using congrArg Fin.val hik
            have hk : k = ⟨i.1 - 8, by omega⟩ := by ext; dsimp; omega
            rw [if_pos hk, if_pos hik]; ring
          · have hneq : k ≠ ⟨i.1 - 8, by omega⟩ := fun heq => hik (by
              ext; have hval : k.1 = i.1 - 8 := by simpa using congrArg Fin.val heq
              dsimp; omega)
            simp [hik, hneq]
        · have hik : i ≠ ⟨8 + k.1, by omega⟩ := fun heq => h2 (by
            have hval : i.1 = 8 + k.1 := by simpa using congrArg Fin.val heq
            omega)
          by_cases h3 : i.1 < 24
          · rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]; simp [hik]
          · rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3]; simp [hik]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq'] at hsnd
    simp only [Finset.mem_univ, ↓reduceIte] at hsnd
    linarith
  have hg23 : ∀ k : Fin 8, g ⟨16 + k.1, by omega⟩ = 0 := by
    intro k
    have hmid := congrArg (fun p : Zorn × (Zorn × Zorn) => zornBilin (zornDualBasis k) p.2.1) heval
    simp only [map_smul, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst,
      Prod.snd_zero, Prod.fst_zero, zornBilin_zero_right, zornBilin_sum_right] at hmid
    have hterm : ∀ i : Fin 52,
        zornBilin (zornDualBasis k) (g i • (peirceEval (f4Basis i)).2.1) =
          if i = ⟨16 + k.1, by omega⟩ then (-1 / 4 : ℝ) * g i else 0 := by
      intro i
      rw [hpart i, zornBilin_smul_right]
      by_cases h1 : i.1 < 8
      · have hik : i ≠ ⟨16 + k.1, by omega⟩ := fun heq => by
          have hval : i.1 = 16 + k.1 := by simpa using congrArg Fin.val heq
          omega
        rw [dite_eq_left h1]; simp [hik]
      · by_cases h2 : i.1 < 16
        · have hik : i ≠ ⟨16 + k.1, by omega⟩ := fun heq => by
            have hval : i.1 = 16 + k.1 := by simpa using congrArg Fin.val heq
            omega
          rw [dite_eq_right h1, dite_eq_left h2]; simp [hik]
        · by_cases h3 : i.1 < 24
          · rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3,
              zornBilin_smul_right, zornBilin_dualBasis_basis]
            by_cases hik : i = ⟨16 + k.1, by omega⟩
            · have hval : i.1 = 16 + k.1 := by simpa using congrArg Fin.val hik
              have hk : k = ⟨i.1 - 16, by omega⟩ := by ext; dsimp; omega
              rw [if_pos hk, if_pos hik]; ring
            · have hneq : k ≠ ⟨i.1 - 16, by omega⟩ := fun heq => hik (by
                ext; have hval : k.1 = i.1 - 16 := by simpa using congrArg Fin.val heq
                dsimp; omega)
              simp [hik, hneq]
          · have hik : i ≠ ⟨16 + k.1, by omega⟩ := fun heq => h3 (by
              have hval : i.1 = 16 + k.1 := by simpa using congrArg Fin.val heq
              omega)
            rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3]; simp [hik]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq'] at hmid
    simp only [Finset.mem_univ, ↓reduceIte] at hmid
    linarith
  have hg_lt24 : ∀ i : Fin 52, i.1 < 24 → g i = 0 := by
    intro i hi
    by_cases h1 : i.1 < 8
    · exact hg12 ⟨i.1, h1⟩
    · by_cases h2 : i.1 < 16
      · convert hg31 ⟨i.1 - 8, by omega⟩ using 2; ext; dsimp; omega
      · convert hg23 ⟨i.1 - 16, by omega⟩ using 2; ext; dsimp; omega
  have hsum_eval_a : ∀ (s : Finset (Fin 28)) (f : Fin 28 → EndH3) (u v : Zorn),
      zornBilin u ((∑ t ∈ s, f t) (mkOff12 v)).a =
        ∑ t ∈ s, zornBilin u ((f t) (mkOff12 v)).a := by
    intro s f u v
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        have hadd : ∀ A B : H3, (A + B).a = A.a + B.a := fun _ _ => rfl
        rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply,
          hadd, zornBilin_add_right, ih]
  have hg_ge24 : ∀ idx : Fin 28, g ⟨24 + idx.1, by omega⟩ = 0 := by
    intro idx
    have hzero : (∑ t : Fin 28, g ⟨24 + t.1, by omega⟩ • (f4Basis ⟨24 + t.1, by omega⟩).1) = 0 := by
      have hsplit : ∑ i : Fin 52, g i • (f4Basis i).1 =
          (∑ i : Fin 24, g (Fin.castAdd 28 i) • (f4Basis (Fin.castAdd 28 i)).1) +
            ∑ t : Fin 28, g (Fin.natAdd 24 t) • (f4Basis (Fin.natAdd 24 t)).1 :=
        Fin.sum_univ_add (a := 24) (b := 28) (fun i => g i • (f4Basis i).1)
      have hz1 : ∑ i : Fin 24, g (Fin.castAdd 28 i) • (f4Basis (Fin.castAdd 28 i)).1 = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hg_lt24 _ i.isLt, zero_smul]
      have hnat : ∀ t : Fin 28, (⟨24 + t.1, by omega⟩ : Fin 52) = Fin.natAdd 24 t :=
        fun t => by ext; dsimp
      have hg2 := hg
      rw [hsplit, hz1, zero_add] at hg2
      simp_rw [hnat]
      exact hg2
    let p := (trialityPair idx).1.1
    let q := (trialityPair idx).1.2
    have hpq : p < q := (trialityPair idx).2
    have hprobe := congrArg
      (fun D : EndH3 => zornBilin (zornDualBasis p) (D (mkOff12 (zornDualBasis q))).a) hzero
    rw [LinearMap.zero_apply] at hprobe
    change _ = zornBilin (zornDualBasis p) 0 at hprobe
    rw [zornBilin_zero_right] at hprobe
    rw [hsum_eval_a Finset.univ _ (zornDualBasis p) (zornDualBasis q)] at hprobe
    have hcoeff : ∀ t : Fin 28,
        zornBilin (zornDualBasis p)
          ((g ⟨24 + t.1, by omega⟩ • (f4Basis ⟨24 + t.1, by omega⟩).1)
            (mkOff12 (zornDualBasis q))).a =
        if t = idx then (1 / 2 : ℝ) * g ⟨24 + idx.1, by omega⟩ else 0 := by
      intro t
      rw [LinearMap.smul_apply, smul_readback, ← zvm_smul_def, zornBilin_smul_right,
        f4Basis_triality_eq t]
      change g ⟨24 + t.1, by omega⟩ * zornBilin (zornDualBasis p)
        (((h3ZornJordanInnerDerivation (mkOff12 (zorn_basis (trialityPair t).1.1))
          (mkOff12 (zorn_basis (trialityPair t).1.2)) : EndH3)
          (mkOff12 (zornDualBasis q))).a) = _
      rw [innerD_off12_off12_apply_off12]
      simp only [mkOff12, zornBilin_smul_right]
      rw [zornBilin_symm (zornDualBasis p) (_ - _), zornBilin_sub_left,
        zornBilin_smul_left, zornBilin_smul_left,
        zornBilin_basis_dualBasis, zornBilin_basis_dualBasis,
        zornBilin_basis_dualBasis, zornBilin_basis_dualBasis]
      by_cases ht : t = idx
      · subst ht
        have hne : p ≠ q := ne_of_lt hpq
        simp [p, q, hne, hne.symm]; ring
      · have hpair_ne : trialityPair t ≠ trialityPair idx := fun heq => ht (trialityPair_injective heq)
        have h1 : ¬ ((trialityPair t).1.2 = q ∧ (trialityPair t).1.1 = p) := by
          rintro ⟨h2, h1⟩
          apply hpair_ne; apply Subtype.ext; apply Prod.ext <;> [exact h1; exact h2]
        have h2 : ¬ ((trialityPair t).1.1 = q ∧ (trialityPair t).1.2 = p) := by
          rintro ⟨h1, h2⟩
          have htlt : (trialityPair t).1.1 < (trialityPair t).1.2 := (trialityPair t).2
          omega
        simp only [ht, ↓reduceIte]
        by_cases hA : (trialityPair t).1.2 = q
        · have hB : (trialityPair t).1.1 ≠ p := fun h => h1 ⟨hA, h⟩
          by_cases hC : (trialityPair t).1.1 = q
          · have hD : (trialityPair t).1.2 ≠ p := fun h => h2 ⟨hC, h⟩
            simp [hA, hB, hB.symm, hC, hD, hD.symm]
          · simp [hA, hB, hB.symm, hC]
        · by_cases hC : (trialityPair t).1.1 = q
          · have hD : (trialityPair t).1.2 ≠ p := fun h => h2 ⟨hC, h⟩
            simp [hA, hC, hD, hD.symm]
          · simp [hA, hC]
    rw [Finset.sum_congr rfl fun t _ => hcoeff t, Finset.sum_ite_eq'] at hprobe
    simp only [Finset.mem_univ, ↓reduceIte] at hprobe
    linarith
  intro i
  by_cases hi : i.1 < 24
  · exact hg_lt24 i hi
  · convert hg_ge24 ⟨i.1 - 24, by omega⟩ using 2
    ext; dsimp; omega

end InfoGeometry.Canonical.SplitAlbertF4DimensionClosure
