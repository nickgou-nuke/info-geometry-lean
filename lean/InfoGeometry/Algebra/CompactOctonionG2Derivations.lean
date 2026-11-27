/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Lie.BaseChange
import InfoGeometry.Algebra.CompactOctonion
import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.Lie.SplitOctonionStandardDerivationCovariance
import InfoGeometry.Algebra.H3OctonionZornComplexification
import InfoGeometry.Canonical.NativeTitsE8Carrier
import InfoGeometry.Lie.CanonicalZornDerivationDimension

/-!
# Compact `𝔤₂(-14)` Derivations of the Compact Octonions `𝕆`

This module formalizes the 14-dimensional compact Lie algebra `CompactOctonionDerivations`
(`𝔤₂(-14)`) of derivations of `CompactOctonion ℝ`, without registering any global `Mul`
instance on `CompactOctonion`.

Specifically, we prove:
1. Fundamental derivation properties: `D 1 = 0`, `trace (D x) = 0`, skew-symmetry with
   respect to `CompactOctonion.bilin`, and commutation with `CompactOctonion.conj`.
2. Construction of the standard inner derivations `compactOctStanDer a b` via a `private`
   `CompactOctAlg` `NonUnitalNonAssocRing` wrapper reusing `AlternativeDerivations.stanDerMap_isLeibniz`,
   `stanDerMap_apply_normal_form`, and `NonAssocDerivation.stanDerMap_covariant`.
3. The 7-dimensional trace-zero submodule `CompactOctonionTraceZero` and all decoupled 7D
   octonionic identities required downstream by the Tits Magic Square (`CompactE8MagicSquare`).
4. Compactness (`Tr(D²) ≤ 0`, `Tr(D²) = 0 ↔ D = 0`) and the operator-trace law
   `Tr(compactG2Inner a b ∘ D) = 6 * bilin a (D b)` for `(3, -6, 1)` ad-invariance.
5. Diamond-free complexification isomorphism
   `compactG2BaseChangeEquiv : ℂ ⊗[ℝ] CompactOctonionDerivations ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] zornDerivations`
   and unconditional dimension `Module.finrank ℝ CompactOctonionDerivations = 14`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open scoped TensorProduct BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-! ## 1. Bilinear Pairing Helpers & `CompactOctonionDerivations` -/

section BilinHelpers

theorem compactOctonion_bilin_symm (x y : CompactOctonion ℝ) :
    CompactOctonion.bilin x y = CompactOctonion.bilin y x :=
  CompactOctonion.trace_mul_conj_comm x y

theorem compactOctonion_bilin_add_left (x₁ x₂ y : CompactOctonion ℝ) :
    CompactOctonion.bilin (x₁ + x₂) y =
      CompactOctonion.bilin x₁ y + CompactOctonion.bilin x₂ y := by
  simp [CompactOctonion.bilin, CompactOctonion.add_mul, CompactOctonion.trace_add]

theorem compactOctonion_bilin_smul_left (r : ℝ) (x y : CompactOctonion ℝ) :
    CompactOctonion.bilin (r • x) y = r * CompactOctonion.bilin x y := by
  simp [CompactOctonion.bilin, CompactOctonion.smul_mul, CompactOctonion.trace_smul]

theorem compactOctonion_bilin_add_right (x y₁ y₂ : CompactOctonion ℝ) :
    CompactOctonion.bilin x (y₁ + y₂) =
      CompactOctonion.bilin x y₁ + CompactOctonion.bilin x y₂ := by
  simp [CompactOctonion.bilin, CompactOctonion.conj_add, CompactOctonion.mul_add,
    CompactOctonion.trace_add]

theorem compactOctonion_bilin_smul_right (r : ℝ) (x y : CompactOctonion ℝ) :
    CompactOctonion.bilin x (r • y) = r * CompactOctonion.bilin x y := by
  simp [CompactOctonion.bilin, CompactOctonion.conj_smul, CompactOctonion.mul_smul,
    CompactOctonion.trace_smul]

theorem compactOctonion_bilin_sub_left (x₁ x₂ y : CompactOctonion ℝ) :
    CompactOctonion.bilin (x₁ - x₂) y =
      CompactOctonion.bilin x₁ y - CompactOctonion.bilin x₂ y := by
  simp [CompactOctonion.bilin, CompactOctonion.sub_mul, CompactOctonion.trace_sub]

theorem compactOctonion_bilin_sub_right (x y₁ y₂ : CompactOctonion ℝ) :
    CompactOctonion.bilin x (y₁ - y₂) =
      CompactOctonion.bilin x y₁ - CompactOctonion.bilin x y₂ := by
  simp [CompactOctonion.bilin, CompactOctonion.conj_sub, CompactOctonion.mul_sub,
    CompactOctonion.trace_sub]

@[simp] theorem compactOctonion_bilin_zero_left (y : CompactOctonion ℝ) :
    CompactOctonion.bilin 0 y = 0 := by
  simp [CompactOctonion.bilin]

@[simp] theorem compactOctonion_bilin_zero_right (x : CompactOctonion ℝ) :
    CompactOctonion.bilin x 0 = 0 := by
  simp [CompactOctonion.bilin]

end BilinHelpers

section CompactDerivations

/-- The compact real Lie algebra `𝔤₂(-14)` of derivations of `CompactOctonion ℝ`,
defined directly via `CompactOctonion.mul` without installing a global `Mul` instance. -/
def CompactOctonionDerivations : LieSubalgebra ℝ (Module.End ℝ (CompactOctonion ℝ)) where
  carrier := {D | ∀ x y : CompactOctonion ℝ,
    D (CompactOctonion.mul x y) =
      CompactOctonion.mul (D x) y + CompactOctonion.mul x (D y)}
  zero_mem' := by
    intro x y
    simp only [LinearMap.zero_apply, CompactOctonion.zero_mul, CompactOctonion.mul_zero,
      add_zero]
  add_mem' := by
    intro D₁ D₂ h₁ h₂ x y
    simp only [LinearMap.add_apply]
    rw [h₁ x y, h₂ x y, CompactOctonion.add_mul, CompactOctonion.mul_add]
    abel
  smul_mem' := by
    intro r D h x y
    simp only [LinearMap.smul_apply]
    rw [h x y, smul_add, CompactOctonion.smul_mul, CompactOctonion.mul_smul]
  lie_mem' := by
    intro D₁ D₂ h₁ h₂ x y
    rw [LieRing.of_associative_ring_bracket]
    change D₁ (D₂ (CompactOctonion.mul x y)) - D₂ (D₁ (CompactOctonion.mul x y)) =
      CompactOctonion.mul (D₁ (D₂ x) - D₂ (D₁ x)) y +
        CompactOctonion.mul x (D₁ (D₂ y) - D₂ (D₁ y))
    rw [h₂ x y, map_add, h₁ (D₂ x) y, h₁ x (D₂ y),
      h₁ x y, map_add, h₂ (D₁ x) y, h₂ x (D₁ y),
      CompactOctonion.sub_mul, CompactOctonion.mul_sub]
    abel

@[simp] theorem mem_compactOctonionDerivations (D : Module.End ℝ (CompactOctonion ℝ)) :
    D ∈ CompactOctonionDerivations ↔
      ∀ x y : CompactOctonion ℝ,
        D (CompactOctonion.mul x y) =
          CompactOctonion.mul (D x) y + CompactOctonion.mul x (D y) :=
  Iff.rfl

theorem compactOctonion_derivation_apply_one_eq_zero (D : CompactOctonionDerivations) :
    D.1 1 = 0 := by
  have h := D.2 1 1
  simp only [CompactOctonion.mul_one, CompactOctonion.one_mul] at h
  calc D.1 1 = D.1 1 + D.1 1 - D.1 1 := (add_sub_cancel_right _ _).symm
    _ = D.1 1 - D.1 1 := by rw [← h]
    _ = 0 := sub_self _

theorem compactOctonion_mul_add_mul_comm (x y : CompactOctonion ℝ) :
    CompactOctonion.mul x y + CompactOctonion.mul y x =
      CompactOctonion.trace x • y + CompactOctonion.trace y • x -
        CompactOctonion.bilin x y • (1 : CompactOctonion ℝ) := by
  ext <;> simp [CompactOctonion.mul, CompactOctonion.trace,
    CompactOctonion.bilin, CompactOctonion.conj, sub_eq_add_neg] <;> ring

theorem compactOctonion_derivation_trace_zero (D : CompactOctonionDerivations)
    (x : CompactOctonion ℝ) :
    CompactOctonion.trace (D.1 x) = 0 := by
  have hbas_rel : ∀ z : CompactOctonion ℝ,
      CompactOctonion.trace (D.1 z) • z =
        CompactOctonion.bilin (D.1 z) z • (1 : CompactOctonion ℝ) := by
    intro z
    have hq := congrArg D.1 (CompactOctonion.mul_self_sub_trace_add_norm z)
    rw [map_zero, map_add, map_sub, map_smul, map_smul,
      compactOctonion_derivation_apply_one_eq_zero D, smul_zero, add_zero, D.2 z z,
      compactOctonion_mul_add_mul_comm (D.1 z) z] at hq
    have hq' : CompactOctonion.trace (D.1 z) • z -
        CompactOctonion.bilin (D.1 z) z • (1 : CompactOctonion ℝ) = 0 := by
      calc CompactOctonion.trace (D.1 z) • z -
              CompactOctonion.bilin (D.1 z) z • (1 : CompactOctonion ℝ)
          = (CompactOctonion.trace (D.1 z) • z + CompactOctonion.trace z • D.1 z -
              CompactOctonion.bilin (D.1 z) z • (1 : CompactOctonion ℝ)) -
              CompactOctonion.trace z • D.1 z := by abel
        _ = 0 := hq
    exact sub_eq_zero.mp hq'
  have hbas : ∀ i : Fin 8, CompactOctonion.trace (D.1 (CompactOctonion.basisVec i)) = 0 := by
    intro i
    have hr := hbas_rel (CompactOctonion.basisVec i)
    fin_cases i
    · change CompactOctonion.trace (D.1 1) = 0
      rw [compactOctonion_derivation_apply_one_eq_zero D, CompactOctonion.trace_zero]
    · have h := congrArg CompactOctonion.e1 hr; simpa [CompactOctonion.basisVec] using h
    · have h := congrArg CompactOctonion.e2 hr; simpa [CompactOctonion.basisVec] using h
    · have h := congrArg CompactOctonion.e3 hr; simpa [CompactOctonion.basisVec] using h
    · have h := congrArg CompactOctonion.e4 hr; simpa [CompactOctonion.basisVec] using h
    · have h := congrArg CompactOctonion.e5 hr; simpa [CompactOctonion.basisVec] using h
    · have h := congrArg CompactOctonion.e6 hr; simpa [CompactOctonion.basisVec] using h
    · have h := congrArg CompactOctonion.e7 hr; simpa [CompactOctonion.basisVec] using h
  rw [← CompactOctonion.basisVec_decomposition x, map_sum]
  have htr_sum : ∀ (s : Finset (Fin 8)) (f : Fin 8 → CompactOctonion ℝ),
      CompactOctonion.trace (∑ j ∈ s, f j) = ∑ j ∈ s, CompactOctonion.trace (f j) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha, CompactOctonion.trace_add, ih]
  rw [htr_sum]
  exact Finset.sum_eq_zero fun i _ => by
    rw [map_smul, CompactOctonion.trace_smul, hbas i, mul_zero]

theorem compactOctonion_derivation_bilin_skew (D : CompactOctonionDerivations)
    (x y : CompactOctonion ℝ) :
    CompactOctonion.bilin (D.1 x) y + CompactOctonion.bilin x (D.1 y) = 0 := by
  have hself : ∀ z : CompactOctonion ℝ, CompactOctonion.bilin (D.1 z) z = 0 := by
    intro z
    have hq := congrArg D.1 (CompactOctonion.mul_self_sub_trace_add_norm z)
    rw [map_zero, map_add, map_sub, map_smul, map_smul,
      compactOctonion_derivation_apply_one_eq_zero D, smul_zero, add_zero, D.2 z z,
      compactOctonion_mul_add_mul_comm (D.1 z) z,
      compactOctonion_derivation_trace_zero D z, zero_smul, zero_add] at hq
    have he0 := congrArg CompactOctonion.e0 hq
    change (CompactOctonion.trace z • D.1 z -
        CompactOctonion.bilin (D.1 z) z • (1 : CompactOctonion ℝ) -
        CompactOctonion.trace z • D.1 z).e0 = 0 at he0
    simp only [sub_eq_add_neg, CompactOctonion.add_e0, CompactOctonion.neg_e0,
      CompactOctonion.smul_e0, CompactOctonion.one_e0] at he0
    linarith
  have hsum := hself (x + y)
  rw [map_add, compactOctonion_bilin_add_left, compactOctonion_bilin_add_right,
    compactOctonion_bilin_add_right, hself x, hself y,
    compactOctonion_bilin_symm (D.1 y) x] at hsum
  linarith

theorem compactOctonion_derivation_conj (D : CompactOctonionDerivations)
    (x : CompactOctonion ℝ) :
    D.1 (CompactOctonion.conj x) = CompactOctonion.conj (D.1 x) := by
  have h1 := congrArg D.1 (CompactOctonion.add_conj_eq_trace x)
  rw [map_add, map_smul, compactOctonion_derivation_apply_one_eq_zero D, smul_zero] at h1
  have h2 := CompactOctonion.add_conj_eq_trace (D.1 x)
  rw [compactOctonion_derivation_trace_zero D x, zero_smul] at h2
  have h1' : D.1 (CompactOctonion.conj x) = -D.1 x := eq_neg_of_add_eq_zero_right h1
  have h2' : CompactOctonion.conj (D.1 x) = -D.1 x := eq_neg_of_add_eq_zero_right h2
  exact h1'.trans h2'.symm

end CompactDerivations

/-! ## 2. Private `CompactOctAlg` Wrapper & Standard Inner Derivations `compactOctStanDer` -/

section StandardDerivations

private structure CompactOctAlg where
  val : CompactOctonion ℝ

private instance : Inhabited CompactOctAlg := ⟨⟨0⟩⟩

@[ext] private theorem CompactOctAlg.ext {x y : CompactOctAlg} (h : x.val = y.val) : x = y := by
  cases x; cases y; congr

private instance : AddCommGroup CompactOctAlg where
  add x y := ⟨x.val + y.val⟩
  add_assoc x y z := by apply CompactOctAlg.ext; exact add_assoc _ _ _
  zero := ⟨0⟩
  zero_add x := by apply CompactOctAlg.ext; exact zero_add _
  add_zero x := by apply CompactOctAlg.ext; exact add_zero _
  neg x := ⟨-x.val⟩
  neg_add_cancel x := by apply CompactOctAlg.ext; exact neg_add_cancel _
  nsmul n x := ⟨n • x.val⟩
  nsmul_zero x := by apply CompactOctAlg.ext; exact zero_smul ℕ x.val
  nsmul_succ n x := by apply CompactOctAlg.ext; exact succ_nsmul x.val n
  zsmul z x := ⟨z • x.val⟩
  zsmul_zero' x := by apply CompactOctAlg.ext; exact zero_smul ℤ x.val
  zsmul_succ' n x := by
    apply CompactOctAlg.ext
    change ((n.succ : ℤ) • x.val) = ((n : ℤ) • x.val) + x.val
    rw [← add_one_zsmul]
    rfl
  zsmul_neg' n x := by
    apply CompactOctAlg.ext
    change ((Int.negSucc n) • x.val) = -(((n + 1 : ℕ) : ℤ) • x.val)
    rw [Int.negSucc_eq, neg_zsmul]
    rfl
  add_comm x y := by apply CompactOctAlg.ext; exact add_comm _ _

private instance : Module ℝ CompactOctAlg where
  smul r x := ⟨r • x.val⟩
  one_smul x := by apply CompactOctAlg.ext; exact one_smul ℝ _
  mul_smul r s x := by apply CompactOctAlg.ext; exact mul_smul r s _
  smul_zero r := by apply CompactOctAlg.ext; exact smul_zero r
  smul_add r x y := by apply CompactOctAlg.ext; exact smul_add r _ _
  add_smul r s x := by apply CompactOctAlg.ext; exact add_smul r s _
  zero_smul x := by apply CompactOctAlg.ext; exact zero_smul ℝ _

private instance : NonUnitalNonAssocRing CompactOctAlg where
  mul x y := ⟨CompactOctonion.mul x.val y.val⟩
  zero_mul x := by apply CompactOctAlg.ext; exact CompactOctonion.zero_mul x.val
  mul_zero x := by apply CompactOctAlg.ext; exact CompactOctonion.mul_zero x.val
  left_distrib x y z := by apply CompactOctAlg.ext; exact CompactOctonion.mul_add x.val y.val z.val
  right_distrib x y z := by apply CompactOctAlg.ext; exact CompactOctonion.add_mul x.val y.val z.val

private instance : IsScalarTower ℝ CompactOctAlg CompactOctAlg where
  smul_assoc r x y := by apply CompactOctAlg.ext; exact CompactOctonion.smul_mul r x.val y.val

private instance : SMulCommClass ℝ CompactOctAlg CompactOctAlg where
  smul_comm r x y := by apply CompactOctAlg.ext; exact (CompactOctonion.mul_smul r x.val y.val).symm

private def compactOctAlgEquiv : CompactOctonion ℝ ≃ₗ[ℝ] CompactOctAlg where
  toFun x := ⟨x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem compactOctAlg_left_alt (x y : CompactOctAlg) :
    (x * x) * y = x * (x * y) := by
  apply CompactOctAlg.ext
  exact CompactOctonion.left_alternative x.val y.val

private theorem compactOctAlg_right_alt (x y : CompactOctAlg) :
    (y * x) * x = y * (x * x) := by
  apply CompactOctAlg.ext
  exact CompactOctonion.right_alternative y.val x.val

private def toCompactOctNonAssocDeriv (D : CompactOctonionDerivations) :
    NonAssocDerivation ℝ CompactOctAlg where
  toLinearMap := compactOctAlgEquiv.conj D.1
  leibniz' x y := by
    apply CompactOctAlg.ext
    change D.1 (CompactOctonion.mul x.val y.val) =
      CompactOctonion.mul (D.1 x.val) y.val + CompactOctonion.mul x.val (D.1 y.val)
    exact D.2 x.val y.val

/-- Associator `(a * b) * c - a * (b * c)` in `CompactOctonion R`. -/
def compactOctAssociator {R : Type*} [CommRing R] (a b c : CompactOctonion R) :
    CompactOctonion R :=
  CompactOctonion.mul (CompactOctonion.mul a b) c -
    CompactOctonion.mul a (CompactOctonion.mul b c)

/-- Standard derivation `D_{a,b} = [L_a, L_b] + [L_a, R_b] + [R_a, R_b]` on
`CompactOctonion ℝ`, proved to be a derivation via `AlternativeDerivations.stanDerMap_isLeibniz`. -/
def compactOctStanDer (a b : CompactOctonion ℝ) : CompactOctonionDerivations where
  val := compactOctAlgEquiv.symm.conj
    (stanDerMap (R := ℝ) (compactOctAlgEquiv a) (compactOctAlgEquiv b))
  property := by
    intro x y
    have hleib := stanDerMap_isLeibniz (R := ℝ)
      compactOctAlg_left_alt compactOctAlg_right_alt
      (compactOctAlgEquiv a) (compactOctAlgEquiv b)
      (compactOctAlgEquiv x) (compactOctAlgEquiv y)
    exact congrArg CompactOctAlg.val hleib

@[simp] theorem compactOctStanDer_apply (a b x : CompactOctonion ℝ) :
    (compactOctStanDer a b).1 x =
      (stanDerMap (R := ℝ) (compactOctAlgEquiv a) (compactOctAlgEquiv b)
        (compactOctAlgEquiv x)).val := rfl

theorem compactOctStanDer_add_left (a₁ a₂ b : CompactOctonion ℝ) :
    compactOctStanDer (a₁ + a₂) b = compactOctStanDer a₁ b + compactOctStanDer a₂ b := by
  apply Subtype.ext; apply LinearMap.ext; intro x
  exact congrArg CompactOctAlg.val
    (stanDerMap_add_left (R := ℝ) (compactOctAlgEquiv a₁) (compactOctAlgEquiv a₂)
      (compactOctAlgEquiv b) (compactOctAlgEquiv x))

theorem compactOctStanDer_smul_left (r : ℝ) (a b : CompactOctonion ℝ) :
    compactOctStanDer (r • a) b = r • compactOctStanDer a b := by
  apply Subtype.ext; apply LinearMap.ext; intro x
  exact congrArg CompactOctAlg.val
    (stanDerMap_smul_left (R := ℝ) r (compactOctAlgEquiv a)
      (compactOctAlgEquiv b) (compactOctAlgEquiv x))

theorem compactOctStanDer_add_right (a b₁ b₂ : CompactOctonion ℝ) :
    compactOctStanDer a (b₁ + b₂) = compactOctStanDer a b₁ + compactOctStanDer a b₂ := by
  apply Subtype.ext; apply LinearMap.ext; intro x
  exact congrArg CompactOctAlg.val
    (stanDerMap_add_right (R := ℝ) (compactOctAlgEquiv a)
      (compactOctAlgEquiv b₁) (compactOctAlgEquiv b₂) (compactOctAlgEquiv x))

theorem compactOctStanDer_smul_right (r : ℝ) (a b : CompactOctonion ℝ) :
    compactOctStanDer a (r • b) = r • compactOctStanDer a b := by
  apply Subtype.ext; apply LinearMap.ext; intro x
  exact congrArg CompactOctAlg.val
    (stanDerMap_smul_right (R := ℝ) r (compactOctAlgEquiv a)
      (compactOctAlgEquiv b) (compactOctAlgEquiv x))

/-- Kleinfeld's normal form `D_{a,b}(x) = [[a,b],x] - 3(a,b,x)` for `compactOctStanDer`. -/
theorem compactOctStanDer_normal_form (a b x : CompactOctonion ℝ) :
    (compactOctStanDer a b).1 x =
      (CompactOctonion.mul (CompactOctonion.mul a b - CompactOctonion.mul b a) x -
        CompactOctonion.mul x (CompactOctonion.mul a b - CompactOctonion.mul b a)) -
      3 • compactOctAssociator a b x := by
  have h := stanDerMap_apply_normal_form (R := ℝ)
    compactOctAlg_left_alt compactOctAlg_right_alt
    (compactOctAlgEquiv a) (compactOctAlgEquiv b) (compactOctAlgEquiv x)
  exact congrArg CompactOctAlg.val h

/-- Lie covariance `[D, stanDer(a, b)] = stanDer(D a, b) + stanDer(a, D b)`. -/
theorem compactOctStanDer_covariant (D : CompactOctonionDerivations) (a b : CompactOctonion ℝ) :
    ⁅D, compactOctStanDer a b⁆ =
      compactOctStanDer (D.1 a) b + compactOctStanDer a (D.1 b) := by
  apply Subtype.ext; apply LinearMap.ext; intro x
  have hc := NonAssocDerivation.stanDerMap_covariant (toCompactOctNonAssocDeriv D)
    (compactOctAlgEquiv a) (compactOctAlgEquiv b) (compactOctAlgEquiv x)
  exact congrArg CompactOctAlg.val hc

/-- Antisymmetry `stanDer(b, a) = -stanDer(a, b)`. -/
theorem compactOctStanDer_swap (a b : CompactOctonion ℝ) :
    compactOctStanDer b a = -compactOctStanDer a b := by
  apply Subtype.ext; apply LinearMap.ext; intro x
  have h12 := alternative_associator_swap12 (A := CompactOctAlg) compactOctAlg_left_alt
    (compactOctAlgEquiv b) (compactOctAlgEquiv a) (compactOctAlgEquiv x)
  have h12' : compactOctAssociator b a x = -compactOctAssociator a b x :=
    congrArg CompactOctAlg.val h12
  change (compactOctStanDer b a).1 x = -(compactOctStanDer a b).1 x
  rw [compactOctStanDer_normal_form, compactOctStanDer_normal_form, h12']
  have hcomm : CompactOctonion.mul b a - CompactOctonion.mul a b =
      -(CompactOctonion.mul a b - CompactOctonion.mul b a) := by abel
  rw [hcomm, CompactOctonion.neg_mul, CompactOctonion.mul_neg, smul_neg]
  abel

theorem compactOctStanDer_self (a : CompactOctonion ℝ) : compactOctStanDer a a = 0 := by
  have h := compactOctStanDer_swap a a
  have h2 : (2 : ℝ) • compactOctStanDer a a = 0 := by
    rw [two_smul]
    nth_rw 2 [h]
    exact add_neg_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

end StandardDerivations

/-! ## 3. 7D Trace-Zero Submodule `CompactOctonionTraceZero` & Magic Square Octonion Identities -/

section TraceZeroAndMagicSquareLaws

/-- Scalar trace functional `CompactOctonion ℝ →ₗ[ℝ] ℝ`. -/
def compactOctTraceLinear : CompactOctonion ℝ →ₗ[ℝ] ℝ where
  toFun := CompactOctonion.trace
  map_add' := CompactOctonion.trace_add
  map_smul' r x := by
    simp [CompactOctonion.trace_smul]

theorem compactOctTraceLinear_ne_zero : compactOctTraceLinear ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : CompactOctonion ℝ →ₗ[ℝ] ℝ => f 1) h
  norm_num [compactOctTraceLinear] at h1

/-- The 7-dimensional pure-imaginary (trace-zero) submodule `Im(𝕆) = ker Tr` of `CompactOctonion ℝ`. -/
def CompactOctonionTraceZero : Submodule ℝ (CompactOctonion ℝ) :=
  LinearMap.ker compactOctTraceLinear

theorem finrank_compactOctonionTraceZero :
    Module.finrank ℝ CompactOctonionTraceZero = 7 := by
  change Module.finrank ℝ (LinearMap.ker compactOctTraceLinear) = 7
  let _inst : FiniteDimensional ℝ (CompactOctonion ℝ) :=
    CompactOctonion.compactOctonionBasis.finiteDimensional_of_finite
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero compactOctTraceLinear_ne_zero
  rw [CompactOctonion.finrank_compactOctonion] at h
  omega

/-- Trace-zero commutator `[a, b]₀ = a * b - b * a` on `CompactOctonionTraceZero`. -/
def compactOctComm0 (a b : CompactOctonionTraceZero) : CompactOctonionTraceZero :=
  ⟨CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1, by
    change CompactOctonion.trace (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) = 0
    rw [CompactOctonion.trace_sub, CompactOctonion.trace_mul_comm a.1 b.1, sub_self]⟩

@[simp] theorem compactOctComm0_coe (a b : CompactOctonionTraceZero) :
    (compactOctComm0 a b : CompactOctonion ℝ) =
      CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1 := rfl

/-- Bilinear `ℝ`-linear map version of `compactOctComm0`. -/
def compactOctComm0LM :
    CompactOctonionTraceZero →ₗ[ℝ] CompactOctonionTraceZero →ₗ[ℝ] CompactOctonionTraceZero :=
  LinearMap.mk₂ ℝ compactOctComm0
    (fun a₁ a₂ b => by
      apply Subtype.ext
      change CompactOctonion.mul (a₁.1 + a₂.1) b.1 - CompactOctonion.mul b.1 (a₁.1 + a₂.1) =
        (CompactOctonion.mul a₁.1 b.1 - CompactOctonion.mul b.1 a₁.1) +
          (CompactOctonion.mul a₂.1 b.1 - CompactOctonion.mul b.1 a₂.1)
      rw [CompactOctonion.add_mul, CompactOctonion.mul_add]
      abel)
    (fun r a b => by
      apply Subtype.ext
      change CompactOctonion.mul (r • a.1) b.1 - CompactOctonion.mul b.1 (r • a.1) =
        r • (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1)
      rw [CompactOctonion.smul_mul, CompactOctonion.mul_smul, smul_sub])
    (fun a b₁ b₂ => by
      apply Subtype.ext
      change CompactOctonion.mul a.1 (b₁.1 + b₂.1) - CompactOctonion.mul (b₁.1 + b₂.1) a.1 =
        (CompactOctonion.mul a.1 b₁.1 - CompactOctonion.mul b₁.1 a.1) +
          (CompactOctonion.mul a.1 b₂.1 - CompactOctonion.mul b₂.1 a.1)
      rw [CompactOctonion.mul_add, CompactOctonion.add_mul]
      abel)
    (fun r a b => by
      apply Subtype.ext
      change CompactOctonion.mul a.1 (r • b.1) - CompactOctonion.mul (r • b.1) a.1 =
        r • (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1)
      rw [CompactOctonion.mul_smul, CompactOctonion.smul_mul, smul_sub])

@[simp] theorem compactOctComm0LM_apply (a b : CompactOctonionTraceZero) :
    compactOctComm0LM a b = compactOctComm0 a b := rfl

theorem compactOctComm0_self (a : CompactOctonionTraceZero) :
    compactOctComm0 a a = 0 := by
  apply Subtype.ext
  exact sub_self _

theorem compactOctComm0_antisymm (a b : CompactOctonionTraceZero) :
    compactOctComm0 b a = -compactOctComm0 a b := by
  apply Subtype.ext
  change CompactOctonion.mul b.1 a.1 - CompactOctonion.mul a.1 b.1 =
    -(CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1)
  abel

/-- Action of `CompactOctonionDerivations` on `CompactOctonionTraceZero`. -/
def compactG2Act (D : CompactOctonionDerivations) (a : CompactOctonionTraceZero) :
    CompactOctonionTraceZero :=
  ⟨D.1 a.1, compactOctonion_derivation_trace_zero D a.1⟩

@[simp] theorem compactG2Act_coe (D : CompactOctonionDerivations) (a : CompactOctonionTraceZero) :
    (compactG2Act D a : CompactOctonion ℝ) = D.1 a.1 := rfl

/-- Bilinear `ℝ`-linear action of `CompactOctonionDerivations` on `CompactOctonionTraceZero`. -/
def compactG2ActLM :
    CompactOctonionDerivations →ₗ[ℝ] CompactOctonionTraceZero →ₗ[ℝ] CompactOctonionTraceZero :=
  LinearMap.mk₂ ℝ compactG2Act
    (fun D₁ D₂ a => by apply Subtype.ext; rfl)
    (fun r D a => by apply Subtype.ext; rfl)
    (fun D a₁ a₂ => by apply Subtype.ext; exact D.1.map_add a₁.1 a₂.1)
    (fun r D a => by apply Subtype.ext; exact D.1.map_smul r a.1)

@[simp] theorem compactG2ActLM_apply (D : CompactOctonionDerivations)
    (a : CompactOctonionTraceZero) :
    compactG2ActLM D a = compactG2Act D a := rfl

theorem compactG2Act_lie (D E : CompactOctonionDerivations) (a : CompactOctonionTraceZero) :
    compactG2Act ⁅D, E⁆ a = compactG2Act D (compactG2Act E a) - compactG2Act E (compactG2Act D a) := by
  apply Subtype.ext
  rfl

theorem compactG2Act_comm0 (D : CompactOctonionDerivations) (a b : CompactOctonionTraceZero) :
    compactG2Act D (compactOctComm0 a b) =
      compactOctComm0 (compactG2Act D a) b + compactOctComm0 a (compactG2Act D b) := by
  apply Subtype.ext
  simp only [compactG2Act_coe, compactOctComm0_coe, Submodule.coe_add]
  rw [D.1.map_sub, D.2 a.1 b.1, D.2 b.1 a.1]
  abel

/-- Inner derivation `D_{a, b}` in `CompactOctonionDerivations`. -/
def compactG2Inner (a b : CompactOctonionTraceZero) : CompactOctonionDerivations :=
  compactOctStanDer a.1 b.1

/-- Bilinear `ℝ`-linear inner derivation map into `CompactOctonionDerivations`. -/
def compactG2InnerLM :
    CompactOctonionTraceZero →ₗ[ℝ] CompactOctonionTraceZero →ₗ[ℝ] CompactOctonionDerivations :=
  LinearMap.mk₂ ℝ compactG2Inner
    (fun a₁ a₂ b => compactOctStanDer_add_left a₁.1 a₂.1 b.1)
    (fun r a b => compactOctStanDer_smul_left r a.1 b.1)
    (fun a b₁ b₂ => compactOctStanDer_add_right a.1 b₁.1 b₂.1)
    (fun r a b => compactOctStanDer_smul_right r a.1 b.1)

@[simp] theorem compactG2InnerLM_apply (a b : CompactOctonionTraceZero) :
    compactG2InnerLM a b = compactG2Inner a b := rfl

theorem compactG2Inner_self (a : CompactOctonionTraceZero) :
    compactG2Inner a a = 0 :=
  compactOctStanDer_self a.1

theorem compactG2Inner_antisymm (a b : CompactOctonionTraceZero) :
    compactG2Inner b a = -compactG2Inner a b :=
  compactOctStanDer_swap a.1 b.1

/-- Bilinear pairing `CompactOctonion.bilin` restricted to `CompactOctonionTraceZero`. -/
def compactOctBilin0LM :
    CompactOctonionTraceZero →ₗ[ℝ] CompactOctonionTraceZero →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a b => CompactOctonion.bilin a.1 b.1)
    (fun a₁ a₂ b => compactOctonion_bilin_add_left a₁.1 a₂.1 b.1)
    (fun r a b => compactOctonion_bilin_smul_left r a.1 b.1)
    (fun a b₁ b₂ => compactOctonion_bilin_add_right a.1 b₁.1 b₂.1)
    (fun r a b => compactOctonion_bilin_smul_right r a.1 b.1)

@[simp] theorem compactOctBilin0LM_apply (a b : CompactOctonionTraceZero) :
    compactOctBilin0LM a b = CompactOctonion.bilin a.1 b.1 := rfl

theorem compactOct_conj_eq_neg (a : CompactOctonionTraceZero) :
    CompactOctonion.conj a.1 = -a.1 := by
  have h := CompactOctonion.add_conj_eq_trace a.1
  have htr : CompactOctonion.trace a.1 = 0 := a.2
  rw [htr, zero_smul] at h
  exact eq_neg_of_add_eq_zero_right h

theorem compactOct_sq_eq_neg_norm_smul_one (a : CompactOctonionTraceZero) :
    CompactOctonion.mul a.1 a.1 = -(CompactOctonion.norm a.1) • (1 : CompactOctonion ℝ) := by
  have ch := CompactOctonion.mul_self_sub_trace_add_norm a.1
  have htr : CompactOctonion.trace a.1 = 0 := a.2
  rw [htr, zero_smul, sub_zero] at ch
  exact (eq_neg_of_add_eq_zero_left ch).trans (by rw [neg_smul])

theorem compactOct_anticommutator_traceZero (a b : CompactOctonionTraceZero) :
    CompactOctonion.mul a.1 b.1 + CompactOctonion.mul b.1 a.1 =
      -(CompactOctonion.bilin a.1 b.1) • (1 : CompactOctonion ℝ) := by
  have hsum := compactOct_sq_eq_neg_norm_smul_one (a + b)
  have ha := compactOct_sq_eq_neg_norm_smul_one a
  have hb := compactOct_sq_eq_neg_norm_smul_one b
  have hnorm : CompactOctonion.norm (a.1 + b.1) =
      CompactOctonion.norm a.1 + CompactOctonion.norm b.1 + CompactOctonion.bilin a.1 b.1 :=
    CompactOctonion.norm_add a.1 b.1
  change CompactOctonion.mul (a.1 + b.1) (a.1 + b.1) =
    -(CompactOctonion.norm (a.1 + b.1)) • (1 : CompactOctonion ℝ) at hsum
  rw [CompactOctonion.add_mul, CompactOctonion.mul_add, CompactOctonion.mul_add,
    ha, hb, hnorm] at hsum
  have h1 : (-(CompactOctonion.norm a.1) • (1 : CompactOctonion ℝ)) +
        CompactOctonion.mul a.1 b.1 +
        (CompactOctonion.mul b.1 a.1 + -(CompactOctonion.norm b.1) • (1 : CompactOctonion ℝ)) =
      CompactOctonion.mul a.1 b.1 + CompactOctonion.mul b.1 a.1 +
        (-(CompactOctonion.norm a.1) • (1 : CompactOctonion ℝ) +
          -(CompactOctonion.norm b.1) • (1 : CompactOctonion ℝ)) := by abel
  have h2 : -(CompactOctonion.norm a.1 + CompactOctonion.norm b.1 +
        CompactOctonion.bilin a.1 b.1) • (1 : CompactOctonion ℝ) =
      -(CompactOctonion.bilin a.1 b.1) • (1 : CompactOctonion ℝ) +
        (-(CompactOctonion.norm a.1) • (1 : CompactOctonion ℝ) +
          -(CompactOctonion.norm b.1) • (1 : CompactOctonion ℝ)) := by
    simp only [neg_add, add_smul, neg_smul]
    abel
  rw [h1, h2] at hsum
  exact add_right_cancel hsum

theorem compactOctBilin_deriv_skew (D : CompactOctonionDerivations)
    (a b : CompactOctonionTraceZero) :
    CompactOctonion.bilin (D.1 a.1) b.1 + CompactOctonion.bilin a.1 (D.1 b.1) = 0 :=
  compactOctonion_derivation_bilin_skew D a.1 b.1

theorem compactOctBilin_comm_cyclic (a b c : CompactOctonionTraceZero) :
    CompactOctonion.bilin a.1 (compactOctComm0 b c).1 =
      CompactOctonion.bilin b.1 (compactOctComm0 c a).1 := by
  have h1 : ∀ u v w : CompactOctonionTraceZero,
      CompactOctonion.bilin u.1 (compactOctComm0 v w).1 =
        -CompactOctonion.trace (CompactOctonion.mul u.1 (CompactOctonion.mul v.1 w.1)) +
          CompactOctonion.trace (CompactOctonion.mul u.1 (CompactOctonion.mul w.1 v.1)) := by
    intro u v w
    change CompactOctonion.trace
      (CompactOctonion.mul u.1 (CompactOctonion.conj (compactOctComm0 v w).1)) = _
    rw [compactOct_conj_eq_neg (compactOctComm0 v w), compactOctComm0_coe,
      CompactOctonion.mul_neg, CompactOctonion.trace_neg,
      CompactOctonion.mul_sub, CompactOctonion.trace_sub]
    ring
  rw [h1 a b c, h1 b c a]
  have cyc1 :
      CompactOctonion.trace (CompactOctonion.mul a.1 (CompactOctonion.mul b.1 c.1)) =
        CompactOctonion.trace (CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1)) := by
    rw [← CompactOctonion.trace_mul_assoc, CompactOctonion.trace_mul_cyclic,
      CompactOctonion.trace_mul_assoc]
  have cyc2 :
      CompactOctonion.trace (CompactOctonion.mul a.1 (CompactOctonion.mul c.1 b.1)) =
        CompactOctonion.trace (CompactOctonion.mul b.1 (CompactOctonion.mul a.1 c.1)) := by
    rw [← CompactOctonion.trace_mul_assoc, ← CompactOctonion.trace_mul_cyclic,
      CompactOctonion.trace_mul_assoc]
  rw [cyc1, cyc2]

theorem compactG2_covariant (D : CompactOctonionDerivations) (a b : CompactOctonionTraceZero) :
    ⁅D, compactG2Inner a b⁆ =
      compactG2Inner (compactG2Act D a) b + compactG2Inner a (compactG2Act D b) :=
  compactOctStanDer_covariant D a.1 b.1

theorem compactOct_jacobiator_eq_neg_six_assoc (a b c : CompactOctonion ℝ) :
    (CompactOctonion.mul a (CompactOctonion.mul b c - CompactOctonion.mul c b) -
        CompactOctonion.mul (CompactOctonion.mul b c - CompactOctonion.mul c b) a) +
      (CompactOctonion.mul b (CompactOctonion.mul c a - CompactOctonion.mul a c) -
        CompactOctonion.mul (CompactOctonion.mul c a - CompactOctonion.mul a c) b) +
      (CompactOctonion.mul c (CompactOctonion.mul a b - CompactOctonion.mul b a) -
        CompactOctonion.mul (CompactOctonion.mul a b - CompactOctonion.mul b a) c) =
      (-6 : ℝ) • compactOctAssociator a b c := by
  let A := compactOctAlgEquiv a
  let B := compactOctAlgEquiv b
  let C := compactOctAlgEquiv c
  have h12 := alternative_associator_swap12 (A := CompactOctAlg) compactOctAlg_left_alt
  have h23 := alternative_associator_swap23 (A := CompactOctAlg) compactOctAlg_right_alt
  have hcyc := alternative_associator_cycle (A := CompactOctAlg)
    compactOctAlg_left_alt compactOctAlg_right_alt
  have halg :
      (A * (B * C - C * B) - (B * C - C * B) * A) +
        (B * (C * A - A * C) - (C * A - A * C) * B) +
        (C * (A * B - B * A) - (A * B - B * A) * C) =
      (-6 : ℝ) • _root_.associator A B C := by
    have hexp :
        (A * (B * C - C * B) - (B * C - C * B) * A) +
          (B * (C * A - A * C) - (C * A - A * C) * B) +
          (C * (A * B - B * A) - (A * B - B * A) * C) =
        (-_root_.associator A B C - _root_.associator B C A - _root_.associator C A B) +
          (_root_.associator A C B + _root_.associator B A C + _root_.associator C B A) := by
      simp only [_root_.associator_apply, mul_sub, sub_mul]
      abel
    have hBCA : _root_.associator B C A = _root_.associator A B C := hcyc A B C
    have hCAB : _root_.associator C A B = _root_.associator A B C := (hcyc B C A).trans hBCA
    have hACB : _root_.associator A C B = -_root_.associator A B C := h23 A C B
    have hBAC : _root_.associator B A C = -_root_.associator A B C := h12 B A C
    have hCBA : _root_.associator C B A = -_root_.associator A B C :=
      (h23 C B A).trans (congrArg Neg.neg hCAB)
    rw [hexp, hBCA, hCAB, hACB, hBAC, hCBA]
    module
  exact congrArg CompactOctAlg.val halg

/-- Decoupled 7D Compact Octonion Double-Commutator Identity:
`[b, [c, a]] - [c, [a, b]] + 6 ⟨b, c⟩ a = 2 (⟨b, c⟩ a + ⟨c, a⟩ b + ⟨a, b⟩ c)`. -/
theorem compactOct_comm_double_identity (a b c : CompactOctonionTraceZero) :
    (CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) -
        CompactOctonion.mul (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) b.1) -
      (CompactOctonion.mul c.1 (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) -
        CompactOctonion.mul (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) c.1) +
      (6 : ℝ) • (CompactOctonion.bilin b.1 c.1 • a.1) =
    (2 : ℝ) • (CompactOctonion.bilin b.1 c.1 • a.1 +
      CompactOctonion.bilin c.1 a.1 • b.1 + CompactOctonion.bilin a.1 b.1 • c.1) := by
  have hca : CompactOctonion.mul a.1 c.1 =
      -(CompactOctonion.mul c.1 a.1) - CompactOctonion.bilin c.1 a.1 • (1 : CompactOctonion ℝ) := by
    have h := compactOct_anticommutator_traceZero c a
    rw [eq_sub_of_add_eq' h]
    module
  have hab : CompactOctonion.mul a.1 b.1 =
      -(CompactOctonion.mul b.1 a.1) - CompactOctonion.bilin a.1 b.1 • (1 : CompactOctonion ℝ) := by
    have h := compactOct_anticommutator_traceZero a b
    rw [eq_sub_of_add_eq' h]
    module
  have hbc : CompactOctonion.mul b.1 c.1 + CompactOctonion.mul c.1 b.1 =
      -(CompactOctonion.bilin b.1 c.1) • (1 : CompactOctonion ℝ) :=
    compactOct_anticommutator_traceZero b c
  have hL : CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1) +
        CompactOctonion.mul c.1 (CompactOctonion.mul b.1 a.1) =
      -(CompactOctonion.bilin b.1 c.1) • a.1 := by
    have h := congrArg CompactOctAlg.val
      (alternative_left_linearized (A := CompactOctAlg) compactOctAlg_left_alt
        (compactOctAlgEquiv b.1) (compactOctAlgEquiv c.1) (compactOctAlgEquiv a.1))
    change CompactOctonion.mul (CompactOctonion.mul b.1 c.1) a.1 +
        CompactOctonion.mul (CompactOctonion.mul c.1 b.1) a.1 =
      CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1) +
        CompactOctonion.mul c.1 (CompactOctonion.mul b.1 a.1) at h
    rw [← CompactOctonion.add_mul, hbc, neg_smul, CompactOctonion.neg_mul,
      CompactOctonion.smul_mul, CompactOctonion.one_mul] at h
    rw [neg_smul]
    exact h.symm
  have hR : CompactOctonion.mul (CompactOctonion.mul a.1 b.1) c.1 +
        CompactOctonion.mul (CompactOctonion.mul a.1 c.1) b.1 =
      -(CompactOctonion.bilin b.1 c.1) • a.1 := by
    have h := congrArg CompactOctAlg.val
      (alternative_right_linearized (A := CompactOctAlg) compactOctAlg_right_alt
        (compactOctAlgEquiv b.1) (compactOctAlgEquiv c.1) (compactOctAlgEquiv a.1))
    change CompactOctonion.mul (CompactOctonion.mul a.1 b.1) c.1 +
        CompactOctonion.mul (CompactOctonion.mul a.1 c.1) b.1 =
      CompactOctonion.mul a.1 (CompactOctonion.mul b.1 c.1) +
        CompactOctonion.mul a.1 (CompactOctonion.mul c.1 b.1) at h
    rw [← CompactOctonion.mul_add, hbc, neg_smul, CompactOctonion.mul_neg,
      CompactOctonion.mul_smul, CompactOctonion.mul_one] at h
    rw [neg_smul]
    exact h
  have h1 : CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1 =
      (2 : ℝ) • CompactOctonion.mul c.1 a.1 +
        CompactOctonion.bilin c.1 a.1 • (1 : CompactOctonion ℝ) := by
    rw [hca]; module
  have h2 : CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1 =
      -((2 : ℝ) • CompactOctonion.mul b.1 a.1) -
        CompactOctonion.bilin a.1 b.1 • (1 : CompactOctonion ℝ) := by
    rw [hab]; module
  have hR' : -(CompactOctonion.mul (CompactOctonion.mul c.1 a.1) b.1) -
        CompactOctonion.mul (CompactOctonion.mul b.1 a.1) c.1 =
      -(CompactOctonion.bilin b.1 c.1) • a.1 + CompactOctonion.bilin c.1 a.1 • b.1 +
        CompactOctonion.bilin a.1 b.1 • c.1 := by
    have hca_b : CompactOctonion.mul (CompactOctonion.mul a.1 c.1) b.1 =
        -(CompactOctonion.mul (CompactOctonion.mul c.1 a.1) b.1) -
          CompactOctonion.bilin c.1 a.1 • b.1 := by
      rw [hca, CompactOctonion.sub_mul, CompactOctonion.neg_mul,
        CompactOctonion.smul_mul, CompactOctonion.one_mul]
    have hab_c : CompactOctonion.mul (CompactOctonion.mul a.1 b.1) c.1 =
        -(CompactOctonion.mul (CompactOctonion.mul b.1 a.1) c.1) -
          CompactOctonion.bilin a.1 b.1 • c.1 := by
      rw [hab, CompactOctonion.sub_mul, CompactOctonion.neg_mul,
        CompactOctonion.smul_mul, CompactOctonion.one_mul]
    rw [hca_b, hab_c] at hR
    have hR0 : (-(CompactOctonion.mul (CompactOctonion.mul c.1 a.1) b.1) -
          CompactOctonion.mul (CompactOctonion.mul b.1 a.1) c.1) -
        (CompactOctonion.bilin c.1 a.1 • b.1 + CompactOctonion.bilin a.1 b.1 • c.1) =
        -(CompactOctonion.bilin b.1 c.1) • a.1 := by
      rw [← hR]; abel
    rw [← hR0]; abel
  rw [h1, h2]
  simp only [CompactOctonion.mul_add, CompactOctonion.add_mul, CompactOctonion.mul_sub,
    CompactOctonion.sub_mul, CompactOctonion.mul_neg, CompactOctonion.neg_mul,
    CompactOctonion.smul_mul, CompactOctonion.mul_smul,
    CompactOctonion.mul_one, CompactOctonion.one_mul]
  have hcomb :
      ((2 : ℝ) • CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1) +
          CompactOctonion.bilin c.1 a.1 • b.1 -
        ((2 : ℝ) • CompactOctonion.mul (CompactOctonion.mul c.1 a.1) b.1 +
          CompactOctonion.bilin c.1 a.1 • b.1)) -
      (-((2 : ℝ) • CompactOctonion.mul c.1 (CompactOctonion.mul b.1 a.1)) -
          CompactOctonion.bilin a.1 b.1 • c.1 -
        (-((2 : ℝ) • CompactOctonion.mul (CompactOctonion.mul b.1 a.1) c.1) -
          CompactOctonion.bilin a.1 b.1 • c.1)) =
      (2 : ℝ) • (CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1) +
          CompactOctonion.mul c.1 (CompactOctonion.mul b.1 a.1)) +
        (2 : ℝ) • (-(CompactOctonion.mul (CompactOctonion.mul c.1 a.1) b.1) -
          CompactOctonion.mul (CompactOctonion.mul b.1 a.1) c.1) := by
    module
  rw [hcomb, hL, hR']
  module

theorem compactOct_associator_comm_cyclic (a b c w : CompactOctonion ℝ) :
    compactOctAssociator a (CompactOctonion.mul b c - CompactOctonion.mul c b) w +
      compactOctAssociator b (CompactOctonion.mul c a - CompactOctonion.mul a c) w +
      compactOctAssociator c (CompactOctonion.mul a b - CompactOctonion.mul b a) w =
    (-2 : ℝ) • (CompactOctonion.mul (compactOctAssociator a b c) w -
      CompactOctonion.mul w (compactOctAssociator a b c)) := by
  let A := compactOctAlgEquiv a
  let B := compactOctAlgEquiv b
  let C := compactOctAlgEquiv c
  let W := compactOctAlgEquiv w
  have h12 := alternative_associator_swap12 (A := CompactOctAlg) compactOctAlg_left_alt
  have h23 := alternative_associator_swap23 (A := CompactOctAlg) compactOctAlg_right_alt
  have hcyc := alternative_associator_cycle (A := CompactOctAlg)
    compactOctAlg_left_alt compactOctAlg_right_alt
  let T (P Q R S : CompactOctAlg) : CompactOctAlg :=
    _root_.associator (P * Q) R S - _root_.associator P (Q * R) S +
      _root_.associator P Q (R * S) - P * _root_.associator Q R S - _root_.associator P Q R * S
  have hT (P Q R S : CompactOctAlg) : T P Q R S = 0 := by
    have hc := associator_cocycle P Q R S
    have h_eq : T P Q R S =
      -(P * _root_.associator Q R S - _root_.associator (P * Q) R S +
        _root_.associator P (Q * R) S - _root_.associator P Q (R * S) +
        _root_.associator P Q R * S) := by
      dsimp [T]; abel
    rw [h_eq, hc, neg_zero]
  have hS4 (x y z : CompactOctAlg) :
      T x y z W - T x z y W =
        (_root_.associator (x * y) z W - _root_.associator (x * z) y W) -
        _root_.associator x (y * z - z * y) W +
        (_root_.associator x y (z * W) - _root_.associator x z (y * W)) -
        (2 : ℝ) • (x * _root_.associator y z W) -
        (2 : ℝ) • (_root_.associator x y z * W) := by
    dsimp [T]
    have hassoc_sub (p q r s : CompactOctAlg) :
        _root_.associator p (q - r) s = _root_.associator p q s - _root_.associator p r s := by
      simp only [_root_.associator_apply, mul_sub, sub_mul]; abel
    rw [hassoc_sub, h23 x z y, h12 z y W, _root_.mul_neg, _root_.neg_mul]
    have h2r (p : CompactOctAlg) : (2 : ℝ) • p = p + p := two_smul ℝ p
    rw [h2r, h2r]
    abel
  have hS1 (x y z : CompactOctAlg) :
      T W x y z - T W x z y =
        (2 : ℝ) • _root_.associator (W * x) y z -
        (_root_.associator W (x * y) z - _root_.associator W (x * z) y) +
        _root_.associator W x (y * z - z * y) -
        (2 : ℝ) • (W * _root_.associator x y z) -
        (_root_.associator W x y * z - _root_.associator W x z * y) := by
    dsimp [T]
    have hassoc_sub (p q r s : CompactOctAlg) :
        _root_.associator p q (r - s) = _root_.associator p q r - _root_.associator p q s := by
      simp only [_root_.associator_apply, mul_sub]; abel
    rw [hassoc_sub, h23 (W * x) z y, h23 x z y, _root_.mul_neg]
    have h2r (p : CompactOctAlg) : (2 : ℝ) • p = p + p := two_smul ℝ p
    rw [h2r, h2r]
    abel
  have hS3 (x y z : CompactOctAlg) :
      T x y W z - T x z W y =
        (_root_.associator (x * y) W z - _root_.associator (x * z) W y) -
        (_root_.associator x (y * W) z - _root_.associator x (z * W) y) +
        (_root_.associator x y (W * z) - _root_.associator x z (W * y)) -
        (x * _root_.associator y W z - x * _root_.associator z W y) -
        (_root_.associator x y W * z - _root_.associator x z W * y) := by
    dsimp [T]; abel
  have hsum :
      (T A B C W - T A C B W) + (T B C A W - T B A C W) + (T C A B W - T C B A W) -
      ((T W A B C - T W A C B) + (T W B C A - T W B A C) + (T W C A B - T W C B A)) +
      ((T A B W C - T A C W B) + (T B C W A - T B A W C) + (T C A W B - T C B W A)) = 0 := by
    simp only [hT, sub_self, add_zero]
  rw [hS4 A B C, hS4 B C A, hS4 C A B,
      hS1 A B C, hS1 B C A, hS1 C A B,
      hS3 A B C, hS3 B C A, hS3 C A B] at hsum
  have hw1 (u v : CompactOctAlg) : _root_.associator W u v = _root_.associator u v W :=
    (hcyc W u v).symm
  have hw2 (u v : CompactOctAlg) : _root_.associator u W v = -_root_.associator u v W :=
    h23 u W v
  have habc1 : _root_.associator B C A = _root_.associator A B C := hcyc A B C
  have habc2 : _root_.associator C A B = _root_.associator A B C := (hcyc B C A).trans habc1
  simp only [hw1, hw2] at hsum
  have hwx1 : _root_.associator (W * A) B C = _root_.associator B C (W * A) :=
    (hcyc (W * A) B C).symm
  have hwx2 : _root_.associator (W * B) C A = _root_.associator C A (W * B) :=
    (hcyc (W * B) C A).symm
  have hwx3 : _root_.associator (W * C) A B = _root_.associator A B (W * C) :=
    (hcyc (W * C) A B).symm
  rw [hwx1, hwx2, hwx3] at hsum
  have hyw1 : _root_.associator A (B * W) C = _root_.associator C A (B * W) := hcyc C A (B * W)
  have hyw2 : _root_.associator A (C * W) B = _root_.associator B A (C * W) := hcyc B A (C * W)
  have hyw3 : _root_.associator B (C * W) A = _root_.associator A B (C * W) := hcyc A B (C * W)
  have hyw4 : _root_.associator B (A * W) C = _root_.associator C B (A * W) := hcyc C B (A * W)
  have hyw5 : _root_.associator C (A * W) B = _root_.associator B C (A * W) := hcyc B C (A * W)
  have hyw6 : _root_.associator C (B * W) A = _root_.associator A C (B * W) := hcyc A C (B * W)
  rw [hyw1, hyw2, hyw3, hyw4, hyw5, hyw6] at hsum
  have hflip1 (p : CompactOctAlg) : _root_.associator B A p = -_root_.associator A B p := h12 B A p
  have hflip2 (p : CompactOctAlg) : _root_.associator C B p = -_root_.associator B C p := h12 C B p
  have hflip3 (p : CompactOctAlg) : _root_.associator A C p = -_root_.associator C A p := h12 A C p
  simp only [hflip1, hflip2, hflip3] at hsum
  rw [habc1, habc2] at hsum
  have hassoc_sub_mid (p q r s : CompactOctAlg) :
      _root_.associator p (q - r) s = _root_.associator p q s - _root_.associator p r s := by
    simp only [_root_.associator_apply, mul_sub, sub_mul]; abel
  have hpq1 : _root_.associator (A * B) C W = -_root_.associator C (A * B) W := h12 _ _ _
  have hpq2 : _root_.associator (A * C) B W = -_root_.associator B (A * C) W := h12 _ _ _
  have hpq3 : _root_.associator (B * C) A W = -_root_.associator A (B * C) W := h12 _ _ _
  have hpq4 : _root_.associator (B * A) C W = -_root_.associator C (B * A) W := h12 _ _ _
  have hpq5 : _root_.associator (C * A) B W = -_root_.associator B (C * A) W := h12 _ _ _
  have hpq6 : _root_.associator (C * B) A W = -_root_.associator A (C * B) W := h12 _ _ _
  rw [hpq1, hpq2, hpq3, hpq4, hpq5, hpq6] at hsum
  simp only [hassoc_sub_mid] at hsum
  simp only [neg_neg, _root_.mul_neg, _root_.neg_mul, sub_neg_eq_add] at hsum
  have h3 : (3 : ℝ) • (_root_.associator A (B * C - C * B) W +
      _root_.associator B (C * A - A * C) W +
      _root_.associator C (A * B - B * A) W) =
    (-6 : ℝ) • (_root_.associator A B C * W - W * _root_.associator A B C) := by
    simp only [hassoc_sub_mid]
    refine sub_eq_zero.mp (Eq.trans ?_ ((congrArg Neg.neg hsum).trans neg_zero))
    module
  have hinv := congrArg (fun z : CompactOctAlg => (1 / 3 : ℝ) • z) h3
  simp only [smul_smul] at hinv
  norm_num at hinv
  rw [← neg_smul] at hinv
  exact congrArg CompactOctAlg.val hinv

/-- Decoupled 7D Compact Octonion Identity 1:
`D_{a, [b, c]} + D_{b, [c, a]} + D_{c, [a, b]} = 0`. -/
theorem compactOct_stanDer_comm_cyclic_zero (a b c : CompactOctonionTraceZero) :
    compactG2Inner a (compactOctComm0 b c) +
      compactG2Inner b (compactOctComm0 c a) +
      compactG2Inner c (compactOctComm0 a b) = 0 := by
  apply Subtype.ext; apply LinearMap.ext; intro w
  change (compactOctStanDer a.1 (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1)).1 w +
      (compactOctStanDer b.1 (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1)).1 w +
      (compactOctStanDer c.1 (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1)).1 w = 0
  rw [compactOctStanDer_normal_form, compactOctStanDer_normal_form,
    compactOctStanDer_normal_form]
  have hjac := compactOct_jacobiator_eq_neg_six_assoc a.1 b.1 c.1
  have hassoc :
      (CompactOctonion.mul (CompactOctonion.mul a.1 (CompactOctonion.mul b.1 c.1 -
          CompactOctonion.mul c.1 b.1) -
          CompactOctonion.mul (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1) w -
        CompactOctonion.mul w (CompactOctonion.mul a.1 (CompactOctonion.mul b.1 c.1 -
          CompactOctonion.mul c.1 b.1) -
          CompactOctonion.mul (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1)) +
      (CompactOctonion.mul (CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1 -
          CompactOctonion.mul a.1 c.1) -
          CompactOctonion.mul (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) b.1) w -
        CompactOctonion.mul w (CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1 -
          CompactOctonion.mul a.1 c.1) -
          CompactOctonion.mul (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) b.1)) +
      (CompactOctonion.mul (CompactOctonion.mul c.1 (CompactOctonion.mul a.1 b.1 -
          CompactOctonion.mul b.1 a.1) -
          CompactOctonion.mul (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) c.1) w -
        CompactOctonion.mul w (CompactOctonion.mul c.1 (CompactOctonion.mul a.1 b.1 -
          CompactOctonion.mul b.1 a.1) -
          CompactOctonion.mul (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) c.1)) =
      (-6 : ℝ) • (CompactOctonion.mul (compactOctAssociator a.1 b.1 c.1) w -
        CompactOctonion.mul w (compactOctAssociator a.1 b.1 c.1)) := by
    have hsum :
        CompactOctonion.mul
          ((CompactOctonion.mul a.1 (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) -
            CompactOctonion.mul (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1) +
           (CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) -
            CompactOctonion.mul (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) b.1) +
           (CompactOctonion.mul c.1 (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) -
            CompactOctonion.mul (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) c.1)) w -
        CompactOctonion.mul w
          ((CompactOctonion.mul a.1 (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) -
            CompactOctonion.mul (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1) +
           (CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) -
            CompactOctonion.mul (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) b.1) +
           (CompactOctonion.mul c.1 (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) -
            CompactOctonion.mul (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) c.1)) =
        (-6 : ℝ) • (CompactOctonion.mul (compactOctAssociator a.1 b.1 c.1) w -
          CompactOctonion.mul w (compactOctAssociator a.1 b.1 c.1)) := by
      rw [hjac, CompactOctonion.smul_mul, CompactOctonion.mul_smul, smul_sub]
    simp only [CompactOctonion.add_mul, CompactOctonion.mul_add] at hsum
    rw [← hsum]
    abel
  have hcyc := compactOct_associator_comm_cyclic a.1 b.1 c.1 w
  have h3_comm :
      (3 : ℕ) • compactOctAssociator a.1
          (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) w +
        (3 : ℕ) • compactOctAssociator b.1
          (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) w +
        (3 : ℕ) • compactOctAssociator c.1
          (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) w =
      (-6 : ℝ) • (CompactOctonion.mul (compactOctAssociator a.1 b.1 c.1) w -
        CompactOctonion.mul w (compactOctAssociator a.1 b.1 c.1)) := by
    have h3s : ∀ u : CompactOctonion ℝ, (3 : ℕ) • u = (3 : ℝ) • u := fun u => by module
    rw [h3s, h3s, h3s, ← smul_add, ← smul_add, hcyc, smul_smul]
    norm_num
  have hre :
      ((CompactOctonion.mul (CompactOctonion.mul a.1 (CompactOctonion.mul b.1 c.1 -
            CompactOctonion.mul c.1 b.1) -
            CompactOctonion.mul (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1) w -
          CompactOctonion.mul w (CompactOctonion.mul a.1 (CompactOctonion.mul b.1 c.1 -
            CompactOctonion.mul c.1 b.1) -
            CompactOctonion.mul (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1)) -
        (3 : ℕ) • compactOctAssociator a.1
          (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) w) +
      ((CompactOctonion.mul (CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1 -
            CompactOctonion.mul a.1 c.1) -
            CompactOctonion.mul (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) b.1) w -
          CompactOctonion.mul w (CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1 -
            CompactOctonion.mul a.1 c.1) -
            CompactOctonion.mul (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) b.1)) -
        (3 : ℕ) • compactOctAssociator b.1
          (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) w) +
      ((CompactOctonion.mul (CompactOctonion.mul c.1 (CompactOctonion.mul a.1 b.1 -
            CompactOctonion.mul b.1 a.1) -
            CompactOctonion.mul (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) c.1) w -
          CompactOctonion.mul w (CompactOctonion.mul c.1 (CompactOctonion.mul a.1 b.1 -
            CompactOctonion.mul b.1 a.1) -
            CompactOctonion.mul (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) c.1)) -
        (3 : ℕ) • compactOctAssociator c.1
          (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) w) =
      ((CompactOctonion.mul (CompactOctonion.mul a.1 (CompactOctonion.mul b.1 c.1 -
            CompactOctonion.mul c.1 b.1) -
            CompactOctonion.mul (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1) w -
          CompactOctonion.mul w (CompactOctonion.mul a.1 (CompactOctonion.mul b.1 c.1 -
            CompactOctonion.mul c.1 b.1) -
            CompactOctonion.mul (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1)) +
        (CompactOctonion.mul (CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1 -
            CompactOctonion.mul a.1 c.1) -
            CompactOctonion.mul (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) b.1) w -
          CompactOctonion.mul w (CompactOctonion.mul b.1 (CompactOctonion.mul c.1 a.1 -
            CompactOctonion.mul a.1 c.1) -
            CompactOctonion.mul (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) b.1)) +
        (CompactOctonion.mul (CompactOctonion.mul c.1 (CompactOctonion.mul a.1 b.1 -
            CompactOctonion.mul b.1 a.1) -
            CompactOctonion.mul (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) c.1) w -
          CompactOctonion.mul w (CompactOctonion.mul c.1 (CompactOctonion.mul a.1 b.1 -
            CompactOctonion.mul b.1 a.1) -
            CompactOctonion.mul (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) c.1))) -
        ((3 : ℕ) • compactOctAssociator a.1
            (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) w +
          (3 : ℕ) • compactOctAssociator b.1
            (CompactOctonion.mul c.1 a.1 - CompactOctonion.mul a.1 c.1) w +
          (3 : ℕ) • compactOctAssociator c.1
            (CompactOctonion.mul a.1 b.1 - CompactOctonion.mul b.1 a.1) w) := by abel
  rw [hre, hassoc, h3_comm, sub_self]

/-- Kleinfeld's trace-zero combination law:
`-(a, b, c) - (1/3) [a, [b, c]] - (1/3) D_{b,c}(a) = 0`. -/
theorem compactOct_kleinfeld_traceZero_combo (a b c : CompactOctonionTraceZero) :
    -(compactOctAssociator a.1 b.1 c.1) -
      (1 / 3 : ℝ) • (CompactOctonion.mul a.1
          (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) -
        CompactOctonion.mul
          (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1) -
      (1 / 3 : ℝ) • (compactG2Act (compactG2Inner b c) a).1 = 0 := by
  change -compactOctAssociator a.1 b.1 c.1 -
      (1 / 3 : ℝ) • (CompactOctonion.mul a.1
          (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) -
        CompactOctonion.mul
          (CompactOctonion.mul b.1 c.1 - CompactOctonion.mul c.1 b.1) a.1) -
      (1 / 3 : ℝ) • (compactOctStanDer b.1 c.1).1 a.1 = 0
  rw [compactOctStanDer_normal_form]
  have hcyc : compactOctAssociator b.1 c.1 a.1 = compactOctAssociator a.1 b.1 c.1 := by
    have h := congrArg CompactOctAlg.val
      (alternative_associator_cycle (A := CompactOctAlg)
        compactOctAlg_left_alt compactOctAlg_right_alt
        (compactOctAlgEquiv a.1) (compactOctAlgEquiv b.1) (compactOctAlgEquiv c.1))
    exact h
  rw [hcyc]
  have h3 : (3 : ℕ) • compactOctAssociator a.1 b.1 c.1 =
      (3 : ℝ) • compactOctAssociator a.1 b.1 c.1 := by module
  rw [h3]
  module

end TraceZeroAndMagicSquareLaws

/-! ## 4. Compactness (`Tr(D²) ≤ 0`) & Operator-Trace Law for `(3, -6, 1)` Ad-Invariance -/

section CompactnessAndOperatorTrace

theorem compactOct_operatorTrace_eq_sum (A : Module.End ℝ (CompactOctonion ℝ)) :
    LinearMap.trace ℝ (CompactOctonion ℝ) A =
      ∑ k : Fin 8, (1 / 2 : ℝ) *
        CompactOctonion.bilin (CompactOctonion.basisVec k) (A (CompactOctonion.basisVec k)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ CompactOctonion.compactOctonionBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    CompactOctonion.compactOctonionBasis_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcoord : CompactOctonion.compactOctonionBasis.repr (A (CompactOctonion.basisVec k)) k =
      CompactOctonion.coordFun (A (CompactOctonion.basisVec k)) k := rfl
  rw [hcoord]
  fin_cases k <;>
    simp [CompactOctonion.bilin_eq, CompactOctonion.basisVec, CompactOctonion.coordFun]

/-- **Compactness of `𝔤₂(-14)`**: `Tr(D²) ≤ 0` for all `D ∈ CompactOctonionDerivations`. -/
theorem compactG2_trace_sq_nonpos (D : CompactOctonionDerivations) :
    LinearMap.trace ℝ (CompactOctonion ℝ) (D.1 * D.1) ≤ 0 := by
  rw [compactOct_operatorTrace_eq_sum]
  have hterm : ∀ k : Fin 8,
      (1 / 2 : ℝ) * CompactOctonion.bilin (CompactOctonion.basisVec k)
          ((D.1 * D.1) (CompactOctonion.basisVec k)) =
        -CompactOctonion.norm (D.1 (CompactOctonion.basisVec k)) := by
    intro k
    change (1 / 2 : ℝ) * CompactOctonion.bilin (CompactOctonion.basisVec k)
        (D.1 (D.1 (CompactOctonion.basisVec k))) = _
    have hsk := compactOctonion_derivation_bilin_skew D
      (CompactOctonion.basisVec k) (D.1 (CompactOctonion.basisVec k))
    have hneg : CompactOctonion.bilin (CompactOctonion.basisVec k)
          (D.1 (D.1 (CompactOctonion.basisVec k))) =
        -CompactOctonion.bilin (D.1 (CompactOctonion.basisVec k))
          (D.1 (CompactOctonion.basisVec k)) := by linarith [hsk]
    rw [hneg, CompactOctonion.bilin_self]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_neg_distrib, neg_nonpos]
  exact Finset.sum_nonneg fun k _ => CompactOctonion.norm_nonneg _

/-- **Definiteness of `𝔤₂(-14)`**: `Tr(D²) = 0 ↔ D = 0`. -/
theorem compactG2_trace_sq_eq_zero_iff (D : CompactOctonionDerivations) :
    LinearMap.trace ℝ (CompactOctonion ℝ) (D.1 * D.1) = 0 ↔ D = 0 := by
  constructor
  · intro htr
    rw [compactOct_operatorTrace_eq_sum] at htr
    have hterm : ∀ k : Fin 8,
        (1 / 2 : ℝ) * CompactOctonion.bilin (CompactOctonion.basisVec k)
            ((D.1 * D.1) (CompactOctonion.basisVec k)) =
          -CompactOctonion.norm (D.1 (CompactOctonion.basisVec k)) := by
      intro k
      change (1 / 2 : ℝ) * CompactOctonion.bilin (CompactOctonion.basisVec k)
          (D.1 (D.1 (CompactOctonion.basisVec k))) = _
      have hsk := compactOctonion_derivation_bilin_skew D
        (CompactOctonion.basisVec k) (D.1 (CompactOctonion.basisVec k))
      have hneg : CompactOctonion.bilin (CompactOctonion.basisVec k)
            (D.1 (D.1 (CompactOctonion.basisVec k))) =
          -CompactOctonion.bilin (D.1 (CompactOctonion.basisVec k))
            (D.1 (CompactOctonion.basisVec k)) := by linarith [hsk]
      rw [hneg, CompactOctonion.bilin_self]
      ring
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_neg_distrib, neg_eq_zero] at htr
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      CompactOctonion.norm_nonneg (D.1 (CompactOctonion.basisVec k))).mp htr
    have hbas : ∀ k : Fin 8, D.1 (CompactOctonion.basisVec k) = 0 := fun k =>
      (CompactOctonion.norm_eq_zero_iff _).mp (hall k (Finset.mem_univ k))
    apply Subtype.ext; apply LinearMap.ext; intro x
    rw [← CompactOctonion.basisVec_decomposition x, map_sum]
    exact Finset.sum_eq_zero fun k _ => by rw [map_smul, hbas k, smul_zero]
  · rintro rfl
    simp

private def mulLeftEnd (x : CompactOctonion ℝ) : Module.End ℝ (CompactOctonion ℝ) where
  toFun y := CompactOctonion.mul x y
  map_add' := CompactOctonion.mul_add x
  map_smul' r y := CompactOctonion.mul_smul r x y

private def mulRightEnd (x : CompactOctonion ℝ) : Module.End ℝ (CompactOctonion ℝ) where
  toFun y := CompactOctonion.mul y x
  map_add' y₁ y₂ := CompactOctonion.add_mul y₁ y₂ x
  map_smul' r y := CompactOctonion.smul_mul r y x

private theorem trace_mulLeft_mulLeft (x y : CompactOctonionTraceZero) :
    LinearMap.trace ℝ (CompactOctonion ℝ) (mulLeftEnd x.1 * mulLeftEnd y.1) =
      -4 * CompactOctonion.bilin x.1 y.1 := by
  rw [compactOct_operatorTrace_eq_sum]
  have hx0 : x.1.e0 = 0 := by
    have hx := x.2
    change CompactOctonion.trace x.1 = 0 at hx
    simp only [CompactOctonion.trace] at hx
    linarith
  have hy0 : y.1.e0 = 0 := by
    have hy := y.2
    change CompactOctonion.trace y.1 = 0 at hy
    simp only [CompactOctonion.trace] at hy
    linarith
  rw [Fin.sum_univ_eight]
  simp only [Module.End.mul_apply, mulLeftEnd, LinearMap.coe_mk, AddHom.coe_mk,
    CompactOctonion.bilin_eq, CompactOctonion.basisVec, CompactOctonion.mul, hx0, hy0]
  ring

private theorem trace_mulRight_mulLeft (x y : CompactOctonionTraceZero) :
    LinearMap.trace ℝ (CompactOctonion ℝ) (mulRightEnd x.1 * mulLeftEnd y.1) =
      2 * CompactOctonion.bilin x.1 y.1 := by
  rw [compactOct_operatorTrace_eq_sum]
  have hx0 : x.1.e0 = 0 := by
    have hx := x.2
    change CompactOctonion.trace x.1 = 0 at hx
    simp only [CompactOctonion.trace] at hx
    linarith
  have hy0 : y.1.e0 = 0 := by
    have hy := y.2
    change CompactOctonion.trace y.1 = 0 at hy
    simp only [CompactOctonion.trace] at hy
    linarith
  rw [Fin.sum_univ_eight]
  simp only [Module.End.mul_apply, mulLeftEnd, mulRightEnd, LinearMap.coe_mk, AddHom.coe_mk,
    CompactOctonion.bilin_eq, CompactOctonion.basisVec, CompactOctonion.mul, hx0, hy0]
  ring

private theorem trace_mulRight_mulRight (x y : CompactOctonionTraceZero) :
    LinearMap.trace ℝ (CompactOctonion ℝ) (mulRightEnd x.1 * mulRightEnd y.1) =
      -4 * CompactOctonion.bilin x.1 y.1 := by
  rw [compactOct_operatorTrace_eq_sum]
  have hx0 : x.1.e0 = 0 := by
    have hx := x.2
    change CompactOctonion.trace x.1 = 0 at hx
    simp only [CompactOctonion.trace] at hx
    linarith
  have hy0 : y.1.e0 = 0 := by
    have hy := y.2
    change CompactOctonion.trace y.1 = 0 at hy
    simp only [CompactOctonion.trace] at hy
    linarith
  rw [Fin.sum_univ_eight]
  simp only [Module.End.mul_apply, mulRightEnd, LinearMap.coe_mk, AddHom.coe_mk,
    CompactOctonion.bilin_eq, CompactOctonion.basisVec, CompactOctonion.mul, hx0, hy0]
  ring

private theorem trace_comm_comp_eq (X Y D : Module.End ℝ (CompactOctonion ℝ)) :
    LinearMap.trace ℝ (CompactOctonion ℝ) ((X * Y - Y * X) * D) =
      LinearMap.trace ℝ (CompactOctonion ℝ) (Y * (D * X - X * D)) := by
  rw [sub_mul, map_sub, mul_sub, map_sub]
  have h1 : LinearMap.trace ℝ (CompactOctonion ℝ) ((X * Y) * D) =
      LinearMap.trace ℝ (CompactOctonion ℝ) (Y * (D * X)) := by
    have hc := LinearMap.trace_mul_comm ℝ X (Y * D)
    rw [mul_assoc X Y D, hc, mul_assoc Y D X]
  rw [h1, mul_assoc Y X D]

/-- Operator trace law for `CompactOctonionDerivations`, powering `(3, -6, 1)` ad-invariance:
`Tr(stanDer(a, b) ∘ D) = 6 * CompactOctonion.bilin a (D b)`. -/
theorem compactOct_trace_stanDer_comp (a b : CompactOctonionTraceZero)
    (D : CompactOctonionDerivations) :
    LinearMap.trace ℝ (CompactOctonion ℝ) ((compactG2Inner a b).1 * D.1) =
      6 * CompactOctonion.bilin a.1 (D.1 b.1) := by
  have hdecomp : (compactG2Inner a b).1 =
      (mulLeftEnd a.1 * mulLeftEnd b.1 - mulLeftEnd b.1 * mulLeftEnd a.1) +
      (mulLeftEnd a.1 * mulRightEnd b.1 - mulRightEnd b.1 * mulLeftEnd a.1) +
      (mulRightEnd a.1 * mulRightEnd b.1 - mulRightEnd b.1 * mulRightEnd a.1) := by
    apply LinearMap.ext; intro x
    rfl
  have hcommL : D.1 * mulLeftEnd a.1 - mulLeftEnd a.1 * D.1 = mulLeftEnd (D.1 a.1) := by
    apply LinearMap.ext; intro x
    change D.1 (CompactOctonion.mul a.1 x) - CompactOctonion.mul a.1 (D.1 x) =
      CompactOctonion.mul (D.1 a.1) x
    rw [D.2 a.1 x]
    abel
  have hcommR : D.1 * mulRightEnd a.1 - mulRightEnd a.1 * D.1 = mulRightEnd (D.1 a.1) := by
    apply LinearMap.ext; intro x
    change D.1 (CompactOctonion.mul x a.1) - CompactOctonion.mul (D.1 x) a.1 =
      CompactOctonion.mul x (D.1 a.1)
    rw [D.2 x a.1]
    abel
  rw [hdecomp, add_mul, add_mul, map_add, map_add,
    trace_comm_comp_eq, trace_comm_comp_eq, trace_comm_comp_eq,
    hcommL, hcommR]
  have hda_mem : D.1 a.1 ∈ CompactOctonionTraceZero :=
    compactOctonion_derivation_trace_zero D a.1
  let Da : CompactOctonionTraceZero := ⟨D.1 a.1, hda_mem⟩
  change LinearMap.trace ℝ (CompactOctonion ℝ) (mulLeftEnd b.1 * mulLeftEnd Da.1) +
      LinearMap.trace ℝ (CompactOctonion ℝ) (mulRightEnd b.1 * mulLeftEnd Da.1) +
      LinearMap.trace ℝ (CompactOctonion ℝ) (mulRightEnd b.1 * mulRightEnd Da.1) =
    6 * CompactOctonion.bilin a.1 (D.1 b.1)
  rw [trace_mulLeft_mulLeft b Da, trace_mulRight_mulLeft b Da, trace_mulRight_mulRight b Da]
  have hsk := compactOctonion_derivation_bilin_skew D a.1 b.1
  have hsym : CompactOctonion.bilin b.1 (D.1 a.1) = CompactOctonion.bilin (D.1 a.1) b.1 :=
    compactOctonion_bilin_symm b.1 (D.1 a.1)
  change -4 * CompactOctonion.bilin b.1 (D.1 a.1) +
      2 * CompactOctonion.bilin b.1 (D.1 a.1) +
      -4 * CompactOctonion.bilin b.1 (D.1 a.1) =
    6 * CompactOctonion.bilin a.1 (D.1 b.1)
  linarith [hsk, hsym]

end CompactnessAndOperatorTrace

/-! ## 5. Complexification `ℂ ⊗[ℝ] CompactOctonionDerivations ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] zornDerivations` & `finrank = 14` -/

section ComplexificationAndDimension

@[simp] theorem rePartCompactOctonion_ofReal (x : CompactOctonion ℝ) :
    rePartCompactOctonion (ofRealCompactOctonion x) = x := by
  ext <;> rfl

@[simp] theorem imPartCompactOctonion_ofReal (x : CompactOctonion ℝ) :
    imPartCompactOctonion (ofRealCompactOctonion x) = 0 := by
  ext <;> rfl

theorem ofReal_rePart_add_I_imPart_CompactOctonion (x : CompactOctonion ℂ) :
    ofRealCompactOctonion (rePartCompactOctonion x) +
      Complex.I • ofRealCompactOctonion (imPartCompactOctonion x) = x := by
  ext <;> simp [ofRealCompactOctonion, rePartCompactOctonion, imPartCompactOctonion,
    mul_comm Complex.I]

@[simp] theorem rePartCompactOctonion_I_smul (x : CompactOctonion ℂ) :
    rePartCompactOctonion (Complex.I • x) = -imPartCompactOctonion x := by
  ext <;> simp [rePartCompactOctonion, imPartCompactOctonion]

@[simp] theorem imPartCompactOctonion_I_smul (x : CompactOctonion ℂ) :
    imPartCompactOctonion (Complex.I • x) = rePartCompactOctonion x := by
  ext <;> simp [rePartCompactOctonion, imPartCompactOctonion]

@[simp] theorem rePartZornVectorMatrix_ofReal (X : ZornVectorMatrix ℝ) :
    rePartZornVectorMatrix (ofRealZornVectorMatrix X) = X := by
  ext i <;> rfl

@[simp] theorem imPartZornVectorMatrix_ofReal (X : ZornVectorMatrix ℝ) :
    imPartZornVectorMatrix (ofRealZornVectorMatrix X) = 0 := by
  ext i <;> rfl

theorem ofReal_rePart_add_I_imPart_ZornVectorMatrix (X : ZornVectorMatrix ℂ) :
    ofRealZornVectorMatrix (rePartZornVectorMatrix X) +
      Complex.I • ofRealZornVectorMatrix (imPartZornVectorMatrix X) = X := by
  ext i <;> simp [ofRealZornVectorMatrix, rePartZornVectorMatrix, imPartZornVectorMatrix,
    ZornVectorMatrix.add, ZornVectorMatrix.smul, mul_comm Complex.I]

@[simp] theorem rePartZornVectorMatrix_I_smul (X : ZornVectorMatrix ℂ) :
    rePartZornVectorMatrix (Complex.I • X) = -imPartZornVectorMatrix X := by
  ext i <;> simp [rePartZornVectorMatrix, imPartZornVectorMatrix, ZornVectorMatrix.smul,
    ZornVectorMatrix.neg]

@[simp] theorem imPartZornVectorMatrix_I_smul (X : ZornVectorMatrix ℂ) :
    imPartZornVectorMatrix (Complex.I • X) = rePartZornVectorMatrix X := by
  ext i <;> simp [rePartZornVectorMatrix, imPartZornVectorMatrix, ZornVectorMatrix.smul]

/-- `ℂ`-linear equivalence `ℂ ⊗[ℝ] CompactOctonion ℝ ≃ₗ[ℂ] CompactOctonion ℂ`. -/
def tensorEquivCompactOctonion : ℂ ⊗[ℝ] CompactOctonion ℝ ≃ₗ[ℂ] CompactOctonion ℂ :=
  mkComplexTensorEquiv ofRealCompactOctonion rePartCompactOctonion imPartCompactOctonion
    rePartCompactOctonion_ofReal imPartCompactOctonion_ofReal
    ofReal_rePart_add_I_imPart_CompactOctonion rePartCompactOctonion_I_smul
    imPartCompactOctonion_I_smul

/-- `ℂ`-linear equivalence `ℂ ⊗[ℝ] ZornVectorMatrix ℝ ≃ₗ[ℂ] ZornVectorMatrix ℂ`. -/
def tensorEquivZornVectorMatrix : ℂ ⊗[ℝ] ZornVectorMatrix ℝ ≃ₗ[ℂ] ZornVectorMatrix ℂ :=
  mkComplexTensorEquiv ofRealZornVectorMatrix rePartZornVectorMatrix imPartZornVectorMatrix
    rePartZornVectorMatrix_ofReal imPartZornVectorMatrix_ofReal
    ofReal_rePart_add_I_imPart_ZornVectorMatrix rePartZornVectorMatrix_I_smul
    imPartZornVectorMatrix_I_smul

@[simp] theorem tensorEquivCompactOctonion_tmul (z : ℂ) (x : CompactOctonion ℝ) :
    tensorEquivCompactOctonion (z ⊗ₜ[ℝ] x) = z • ofRealCompactOctonion x := rfl

@[simp] theorem tensorEquivZornVectorMatrix_tmul (z : ℂ) (X : ZornVectorMatrix ℝ) :
    tensorEquivZornVectorMatrix (z ⊗ₜ[ℝ] X) = z • ofRealZornVectorMatrix X := rfl

section TraceZeroComplexification

private def compactOctTraceLinearℂ : CompactOctonion ℂ →ₗ[ℂ] ℂ where
  toFun := CompactOctonion.trace
  map_add' := CompactOctonion.trace_add
  map_smul' z x := by
    simp [CompactOctonion.trace_smul]

private def zornTraceLinearℂ : ZornVectorMatrix ℂ →ₗ[ℂ] ℂ where
  toFun := ZornVectorMatrix.trace
  map_add' X Y := by
    simp [ZornVectorMatrix.trace, ZornVectorMatrix.add]
    ring
  map_smul' z X := by
    simp [ZornVectorMatrix.trace, ZornVectorMatrix.smul]
    ring

/-- Complexified pure-imaginary compact octonions `ker Tr ⊆ CompactOctonion ℂ`. -/
def compactOctonionTraceZeroℂ : Submodule ℂ (CompactOctonion ℂ) :=
  LinearMap.ker compactOctTraceLinearℂ

/-- Complexified pure-imaginary split octonions `ker Tr ⊆ ZornVectorMatrix ℂ`. -/
def splitOctonionTraceZeroℂ : Submodule ℂ (ZornVectorMatrix ℂ) :=
  LinearMap.ker zornTraceLinearℂ

private def ofRealCompactOctonion0 :
    CompactOctonionTraceZero →ₗ[ℝ] compactOctonionTraceZeroℂ where
  toFun a := ⟨ofRealCompactOctonion a.1, by
    change CompactOctonion.trace (ofRealCompactOctonion a.1) = 0
    rw [ofRealCompactOctonion_trace]
    have ha : CompactOctonion.trace a.1 = 0 := a.2
    rw [ha, Complex.ofReal_zero]⟩
  map_add' a b := by apply Subtype.ext; exact ofRealCompactOctonion.map_add a.1 b.1
  map_smul' r a := by
    apply Subtype.ext
    change ofRealCompactOctonion (r • a.1) = (r : ℂ) • ofRealCompactOctonion a.1
    rw [ofRealCompactOctonion.map_smul, Complex.coe_smul]

private def rePartCompactOctonion0 :
    compactOctonionTraceZeroℂ →ₗ[ℝ] CompactOctonionTraceZero where
  toFun a := ⟨rePartCompactOctonion a.1, by
    change CompactOctonion.trace (rePartCompactOctonion a.1) = 0
    have htr : CompactOctonion.trace (rePartCompactOctonion a.1) =
        (CompactOctonion.trace a.1).re := by
      simp [CompactOctonion.trace, rePartCompactOctonion]
    have ha : CompactOctonion.trace a.1 = 0 := a.2
    rw [htr, ha, Complex.zero_re]⟩
  map_add' a b := by apply Subtype.ext; exact rePartCompactOctonion.map_add a.1 b.1
  map_smul' r a := by apply Subtype.ext; exact rePartCompactOctonion.map_smul r a.1

private def imPartCompactOctonion0 :
    compactOctonionTraceZeroℂ →ₗ[ℝ] CompactOctonionTraceZero where
  toFun a := ⟨imPartCompactOctonion a.1, by
    change CompactOctonion.trace (imPartCompactOctonion a.1) = 0
    have htr : CompactOctonion.trace (imPartCompactOctonion a.1) =
        (CompactOctonion.trace a.1).im := by
      simp [CompactOctonion.trace, imPartCompactOctonion]
    have ha : CompactOctonion.trace a.1 = 0 := a.2
    rw [htr, ha, Complex.zero_im]⟩
  map_add' a b := by apply Subtype.ext; exact imPartCompactOctonion.map_add a.1 b.1
  map_smul' r a := by apply Subtype.ext; exact imPartCompactOctonion.map_smul r a.1

private def ofRealZorn0 :
    InfoGeometry.Canonical.NativeTitsE8Carrier.splitOctonionTraceZero →ₗ[ℝ]
      splitOctonionTraceZeroℂ where
  toFun a := ⟨ofRealZornVectorMatrix a.1, by
    change ZornVectorMatrix.trace (ofRealZornVectorMatrix a.1) = 0
    rw [ofRealZornVectorMatrix_trace]
    have ha : ZornVectorMatrix.trace a.1 = 0 := a.2
    rw [ha, Complex.ofReal_zero]⟩
  map_add' a b := by apply Subtype.ext; exact ofRealZornVectorMatrix.map_add a.1 b.1
  map_smul' r a := by
    apply Subtype.ext
    change ofRealZornVectorMatrix (r • a.1) = (r : ℂ) • ofRealZornVectorMatrix a.1
    rw [ofRealZornVectorMatrix.map_smul, Complex.coe_smul]

private def rePartZorn0 :
    splitOctonionTraceZeroℂ →ₗ[ℝ]
      InfoGeometry.Canonical.NativeTitsE8Carrier.splitOctonionTraceZero where
  toFun a := ⟨rePartZornVectorMatrix a.1, by
    change ZornVectorMatrix.trace (rePartZornVectorMatrix a.1) = 0
    have htr : ZornVectorMatrix.trace (rePartZornVectorMatrix a.1) =
        (ZornVectorMatrix.trace a.1).re := by
      simp [ZornVectorMatrix.trace, rePartZornVectorMatrix]
    have ha : ZornVectorMatrix.trace a.1 = 0 := a.2
    rw [htr, ha, Complex.zero_re]⟩
  map_add' a b := by apply Subtype.ext; exact rePartZornVectorMatrix.map_add a.1 b.1
  map_smul' r a := by apply Subtype.ext; exact rePartZornVectorMatrix.map_smul r a.1

private def imPartZorn0 :
    splitOctonionTraceZeroℂ →ₗ[ℝ]
      InfoGeometry.Canonical.NativeTitsE8Carrier.splitOctonionTraceZero where
  toFun a := ⟨imPartZornVectorMatrix a.1, by
    change ZornVectorMatrix.trace (imPartZornVectorMatrix a.1) = 0
    have htr : ZornVectorMatrix.trace (imPartZornVectorMatrix a.1) =
        (ZornVectorMatrix.trace a.1).im := by
      simp [ZornVectorMatrix.trace, imPartZornVectorMatrix]
    have ha : ZornVectorMatrix.trace a.1 = 0 := a.2
    rw [htr, ha, Complex.zero_im]⟩
  map_add' a b := by apply Subtype.ext; exact imPartZornVectorMatrix.map_add a.1 b.1
  map_smul' r a := by apply Subtype.ext; exact imPartZornVectorMatrix.map_smul r a.1

/-- `ℂ`-linear equivalence `ℂ ⊗[ℝ] CompactOctonionTraceZero ≃ₗ[ℂ] compactOctonionTraceZeroℂ`. -/
def tensorEquivCompactOctonionTraceZeroℂ :
    ℂ ⊗[ℝ] CompactOctonionTraceZero ≃ₗ[ℂ] compactOctonionTraceZeroℂ :=
  mkComplexTensorEquiv ofRealCompactOctonion0 rePartCompactOctonion0 imPartCompactOctonion0
    (fun a => Subtype.ext (rePartCompactOctonion_ofReal a.1))
    (fun a => Subtype.ext (imPartCompactOctonion_ofReal a.1))
    (fun w => Subtype.ext (ofReal_rePart_add_I_imPart_CompactOctonion w.1))
    (fun w => Subtype.ext (rePartCompactOctonion_I_smul w.1))
    (fun w => Subtype.ext (imPartCompactOctonion_I_smul w.1))

/-- `ℂ`-linear equivalence `ℂ ⊗[ℝ] splitOctonionTraceZero ≃ₗ[ℂ] splitOctonionTraceZeroℂ`. -/
def tensorEquivSplitOctonionTraceZeroℂ :
    ℂ ⊗[ℝ] InfoGeometry.Canonical.NativeTitsE8Carrier.splitOctonionTraceZero ≃ₗ[ℂ]
      splitOctonionTraceZeroℂ :=
  mkComplexTensorEquiv ofRealZorn0 rePartZorn0 imPartZorn0
    (fun a => Subtype.ext (rePartZornVectorMatrix_ofReal a.1))
    (fun a => Subtype.ext (imPartZornVectorMatrix_ofReal a.1))
    (fun w => Subtype.ext (ofReal_rePart_add_I_imPart_ZornVectorMatrix w.1))
    (fun w => Subtype.ext (rePartZornVectorMatrix_I_smul w.1))
    (fun w => Subtype.ext (imPartZornVectorMatrix_I_smul w.1))

/-- `ℂ`-linear equivalence `compactOctonionTraceZeroℂ ≃ₗ[ℂ] splitOctonionTraceZeroℂ`
induced by `octonionComplexEquiv`. -/
def octonionTraceZeroComplexEquiv :
    compactOctonionTraceZeroℂ ≃ₗ[ℂ] splitOctonionTraceZeroℂ where
  toFun a := ⟨octonionComplexEquiv a.1, by
    change ZornVectorMatrix.trace (octonionComplexEquiv a.1) = 0
    rw [octonionComplexEquiv_trace]
    exact a.2⟩
  invFun X := ⟨octonionComplexEquiv.symm X.1, by
    change CompactOctonion.trace (octonionComplexEquiv.symm X.1) = 0
    rw [octonionComplexEquiv_symm_trace]
    exact X.2⟩
  left_inv a := by apply Subtype.ext; exact octonionComplexEquiv.left_inv a.1
  right_inv X := by apply Subtype.ext; exact octonionComplexEquiv.right_inv X.1
  map_add' a b := by apply Subtype.ext; exact octonionComplexEquiv.map_add a.1 b.1
  map_smul' z a := by apply Subtype.ext; exact octonionComplexEquiv.map_smul z a.1

/-- `ℂ`-linear equivalence `ℂ ⊗[ℝ] CompactOctonionTraceZero ≃ₗ[ℂ] ℂ ⊗[ℝ] splitOctonionTraceZero`. -/
def tensorEquivCompactOctonionTraceZero :
    ℂ ⊗[ℝ] CompactOctonionTraceZero ≃ₗ[ℂ]
      ℂ ⊗[ℝ] InfoGeometry.Canonical.NativeTitsE8Carrier.splitOctonionTraceZero :=
  tensorEquivCompactOctonionTraceZeroℂ.trans
    (octonionTraceZeroComplexEquiv.trans tensorEquivSplitOctonionTraceZeroℂ.symm)

@[simp] theorem tensorEquivCompactOctonionTraceZeroℂ_tmul (z : ℂ) (a : CompactOctonionTraceZero) :
    (tensorEquivCompactOctonionTraceZeroℂ (z ⊗ₜ[ℝ] a)).1 = z • ofRealCompactOctonion a.1 := rfl

@[simp] theorem tensorEquivSplitOctonionTraceZeroℂ_tmul (z : ℂ)
    (a : InfoGeometry.Canonical.NativeTitsE8Carrier.splitOctonionTraceZero) :
    (tensorEquivSplitOctonionTraceZeroℂ (z ⊗ₜ[ℝ] a)).1 = z • ofRealZornVectorMatrix a.1 := rfl

end TraceZeroComplexification

/-- Derivations of `ZornVectorMatrix ℝ` as a `LieSubalgebra ℝ (Module.End ℝ (ZornVectorMatrix ℝ))`. -/
def zornDerivations : LieSubalgebra ℝ (Module.End ℝ (ZornVectorMatrix ℝ)) where
  carrier := {D | ∀ X Y : ZornVectorMatrix ℝ,
    D (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.add (ZornVectorMatrix.mul (D X) Y) (ZornVectorMatrix.mul X (D Y))}
  zero_mem' := by
    intro X Y
    change (0 : ZornVectorMatrix ℝ) =
      ZornVectorMatrix.add (ZornVectorMatrix.mul ZornVectorMatrix.zero Y)
        (ZornVectorMatrix.mul X ZornVectorMatrix.zero)
    rw [ZornVectorMatrix.zero_mul, ZornVectorMatrix.mul_zero, ZornVectorMatrix.add_zero]
    rfl
  add_mem' := by
    intro D₁ D₂ h₁ h₂ X Y
    have hadd_def : ∀ A B : ZornVectorMatrix ℝ, A + B = ZornVectorMatrix.add A B :=
      fun _ _ => rfl
    change D₁ (ZornVectorMatrix.mul X Y) + D₂ (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.mul (D₁ X + D₂ X) Y)
        (ZornVectorMatrix.mul X (D₁ Y + D₂ Y))
    rw [hadd_def, h₁ X Y, h₂ X Y, hadd_def (D₁ X), hadd_def (D₁ Y),
      ZornVectorMatrix.add_mul, ZornVectorMatrix.mul_add]
    simp only [← hadd_def]
    abel
  smul_mem' := by
    intro r D h X Y
    have hadd_def : ∀ A B : ZornVectorMatrix ℝ, A + B = ZornVectorMatrix.add A B :=
      fun _ _ => rfl
    have hsmul_def : ∀ (c : ℝ) (A : ZornVectorMatrix ℝ), c • A = ZornVectorMatrix.smul c A :=
      fun _ _ => rfl
    change r • D (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.mul (r • D X) Y)
        (ZornVectorMatrix.mul X (r • D Y))
    rw [hsmul_def, h X Y, ZornVectorMatrix.smul_add,
      hsmul_def r (D X), hsmul_def r (D Y),
      ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul]
  lie_mem' := by
    intro D₁ D₂ h₁ h₂ X Y
    rw [LieRing.of_associative_ring_bracket]
    have hadd_def : ∀ A B : ZornVectorMatrix ℝ, A + B = ZornVectorMatrix.add A B :=
      fun _ _ => rfl
    have hsub_def : ∀ A B : ZornVectorMatrix ℝ, A - B = ZornVectorMatrix.sub A B :=
      fun _ _ => rfl
    change D₁ (D₂ (ZornVectorMatrix.mul X Y)) - D₂ (D₁ (ZornVectorMatrix.mul X Y)) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.mul (D₁ (D₂ X) - D₂ (D₁ X)) Y)
        (ZornVectorMatrix.mul X (D₁ (D₂ Y) - D₂ (D₁ Y)))
    rw [h₂ X Y, ← hadd_def, map_add, h₁ (D₂ X) Y, h₁ X (D₂ Y), h₁ X Y]
    simp only [← hadd_def]
    rw [map_add, h₂ (D₁ X) Y, h₂ X (D₁ Y)]
    simp only [hsub_def, ZornVectorMatrix.sub_mul, ZornVectorMatrix.mul_sub]
    simp only [← hadd_def, ← hsub_def]
    abel

private def vDerToEnd (D : InfoGeometry.Canonical.NativeTitsE8Carrier.G2DerivationCarrier) :
    Module.End ℝ (ZornVectorMatrix ℝ) where
  toFun := D.toFun
  map_add' := D.map_add'
  map_smul' := D.map_smul'

private def endToVDer (D : zornDerivations) :
    InfoGeometry.Canonical.NativeTitsE8Carrier.G2DerivationCarrier where
  toFun := D.1.toFun
  map_add' := D.1.map_add'
  map_smul' := D.1.map_smul'
  map_mul' := D.2

/-- Real Lie algebra isomorphism `G2DerivationCarrier ≃ₗ⁅ℝ⁆ zornDerivations`. -/
def vDerEquivZornDerivations :
    InfoGeometry.Canonical.NativeTitsE8Carrier.G2DerivationCarrier ≃ₗ⁅ℝ⁆ zornDerivations where
  toFun D := ⟨vDerToEnd D, D.map_mul'⟩
  invFun := endToVDer
  left_inv D := by
    apply ZornVectorMatrix.Derivation.ext
    intro X; rfl
  right_inv D := by
    apply Subtype.ext; apply LinearMap.ext; intro X; rfl
  map_add' D E := by
    apply Subtype.ext; apply LinearMap.ext; intro X; rfl
  map_smul' r D := by
    apply Subtype.ext; apply LinearMap.ext; intro X; rfl
  map_lie' {D E} := by
    apply Subtype.ext; apply LinearMap.ext; intro X
    change vDerToEnd ⁅D, E⁆ X =
      ((vDerToEnd D).comp (vDerToEnd E) - (vDerToEnd E).comp (vDerToEnd D)) X
    rfl

/-- Complexified Lie subalgebra of derivations on `CompactOctonion ℂ`. -/
def compactOctonionDerivationsℂ : LieSubalgebra ℂ (Module.End ℂ (CompactOctonion ℂ)) where
  carrier := {D | ∀ x y : CompactOctonion ℂ,
    D (CompactOctonion.mul x y) =
      CompactOctonion.mul (D x) y + CompactOctonion.mul x (D y)}
  zero_mem' := by
    intro x y
    simp only [LinearMap.zero_apply, CompactOctonion.zero_mul, CompactOctonion.mul_zero,
      add_zero]
  add_mem' := by
    intro D₁ D₂ h₁ h₂ x y
    simp only [LinearMap.add_apply]
    rw [h₁ x y, h₂ x y, CompactOctonion.add_mul, CompactOctonion.mul_add]
    abel
  smul_mem' := by
    intro z D h x y
    simp only [LinearMap.smul_apply]
    rw [h x y, smul_add, CompactOctonion.smul_mul, CompactOctonion.mul_smul]
  lie_mem' := by
    intro D₁ D₂ h₁ h₂ x y
    rw [LieRing.of_associative_ring_bracket]
    change D₁ (D₂ (CompactOctonion.mul x y)) - D₂ (D₁ (CompactOctonion.mul x y)) =
      CompactOctonion.mul (D₁ (D₂ x) - D₂ (D₁ x)) y +
        CompactOctonion.mul x (D₁ (D₂ y) - D₂ (D₁ y))
    rw [h₂ x y, map_add, h₁ (D₂ x) y, h₁ x (D₂ y),
      h₁ x y, map_add, h₂ (D₁ x) y, h₂ x (D₁ y),
      CompactOctonion.sub_mul, CompactOctonion.mul_sub]
    abel

/-- Complexified Lie subalgebra of derivations on `ZornVectorMatrix ℂ`. -/
def zornDerivationsℂ : LieSubalgebra ℂ (Module.End ℂ (ZornVectorMatrix ℂ)) where
  carrier := {D | ∀ X Y : ZornVectorMatrix ℂ,
    D (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.add (ZornVectorMatrix.mul (D X) Y) (ZornVectorMatrix.mul X (D Y))}
  zero_mem' := by
    intro X Y
    change (0 : ZornVectorMatrix ℂ) =
      ZornVectorMatrix.add (ZornVectorMatrix.mul ZornVectorMatrix.zero Y)
        (ZornVectorMatrix.mul X ZornVectorMatrix.zero)
    rw [ZornVectorMatrix.zero_mul, ZornVectorMatrix.mul_zero, ZornVectorMatrix.add_zero]
    rfl
  add_mem' := by
    intro D₁ D₂ h₁ h₂ X Y
    have hadd_def : ∀ A B : ZornVectorMatrix ℂ, A + B = ZornVectorMatrix.add A B :=
      fun _ _ => rfl
    change D₁ (ZornVectorMatrix.mul X Y) + D₂ (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.mul (D₁ X + D₂ X) Y)
        (ZornVectorMatrix.mul X (D₁ Y + D₂ Y))
    rw [hadd_def, h₁ X Y, h₂ X Y, hadd_def (D₁ X), hadd_def (D₁ Y),
      ZornVectorMatrix.add_mul, ZornVectorMatrix.mul_add]
    simp only [← hadd_def]
    abel
  smul_mem' := by
    intro z D h X Y
    have hadd_def : ∀ A B : ZornVectorMatrix ℂ, A + B = ZornVectorMatrix.add A B :=
      fun _ _ => rfl
    have hsmul_def : ∀ (c : ℂ) (A : ZornVectorMatrix ℂ), c • A = ZornVectorMatrix.smul c A :=
      fun _ _ => rfl
    change z • D (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.mul (z • D X) Y)
        (ZornVectorMatrix.mul X (z • D Y))
    rw [hsmul_def, h X Y, ZornVectorMatrix.smul_add,
      hsmul_def z (D X), hsmul_def z (D Y),
      ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul]
  lie_mem' := by
    intro D₁ D₂ h₁ h₂ X Y
    rw [LieRing.of_associative_ring_bracket]
    have hadd_def : ∀ A B : ZornVectorMatrix ℂ, A + B = ZornVectorMatrix.add A B :=
      fun _ _ => rfl
    have hsub_def : ∀ A B : ZornVectorMatrix ℂ, A - B = ZornVectorMatrix.sub A B :=
      fun _ _ => rfl
    change D₁ (D₂ (ZornVectorMatrix.mul X Y)) - D₂ (D₁ (ZornVectorMatrix.mul X Y)) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.mul (D₁ (D₂ X) - D₂ (D₁ X)) Y)
        (ZornVectorMatrix.mul X (D₁ (D₂ Y) - D₂ (D₁ Y)))
    rw [h₂ X Y, ← hadd_def, map_add, h₁ (D₂ X) Y, h₁ X (D₂ Y), h₁ X Y]
    simp only [← hadd_def]
    rw [map_add, h₂ (D₁ X) Y, h₂ X (D₁ Y)]
    simp only [hsub_def, ZornVectorMatrix.sub_mul, ZornVectorMatrix.mul_sub]
    simp only [← hadd_def, ← hsub_def]
    abel

private theorem liftEnd_compactOctonionDerivations
    (D : Module.End ℝ (CompactOctonion ℝ)) (hD : D ∈ CompactOctonionDerivations) :
    liftEnd tensorEquivCompactOctonion D ∈ compactOctonionDerivationsℂ := by
  intro x y
  rw [← ofReal_rePart_add_I_imPart_CompactOctonion x,
    ← ofReal_rePart_add_I_imPart_CompactOctonion y]
  have hreal : ∀ a b : CompactOctonion ℝ,
      liftEnd tensorEquivCompactOctonion D
          (CompactOctonion.mul (ofRealCompactOctonion a) (ofRealCompactOctonion b)) =
        CompactOctonion.mul
            (liftEnd tensorEquivCompactOctonion D (ofRealCompactOctonion a))
            (ofRealCompactOctonion b) +
          CompactOctonion.mul (ofRealCompactOctonion a)
            (liftEnd tensorEquivCompactOctonion D (ofRealCompactOctonion b)) := by
    intro a b
    rw [← ofRealCompactOctonion_mul,
      liftEnd_apply_ofReal tensorEquivCompactOctonion ofRealCompactOctonion
        tensorEquivCompactOctonion_tmul,
      liftEnd_apply_ofReal tensorEquivCompactOctonion ofRealCompactOctonion
        tensorEquivCompactOctonion_tmul,
      liftEnd_apply_ofReal tensorEquivCompactOctonion ofRealCompactOctonion
        tensorEquivCompactOctonion_tmul,
      hD a b, map_add, ofRealCompactOctonion_mul, ofRealCompactOctonion_mul]
  simp only [CompactOctonion.mul_add, CompactOctonion.add_mul,
    CompactOctonion.smul_mul, CompactOctonion.mul_smul, map_add, map_smul]
  rw [hreal (rePartCompactOctonion x) (rePartCompactOctonion y),
    hreal (rePartCompactOctonion x) (imPartCompactOctonion y),
    hreal (imPartCompactOctonion x) (rePartCompactOctonion y),
    hreal (imPartCompactOctonion x) (imPartCompactOctonion y)]
  simp only [smul_add]
  abel

private theorem split_compactOctonionDerivations
    (T : Module.End ℂ (CompactOctonion ℂ)) (hT : T ∈ compactOctonionDerivationsℂ) :
    reEnd ofRealCompactOctonion rePartCompactOctonion T ∈ CompactOctonionDerivations ∧
    imEnd ofRealCompactOctonion imPartCompactOctonion T ∈ CompactOctonionDerivations := by
  have hmul : ∀ a b : CompactOctonion ℝ,
      T (ofRealCompactOctonion (CompactOctonion.mul a b)) =
        CompactOctonion.mul (T (ofRealCompactOctonion a)) (ofRealCompactOctonion b) +
        CompactOctonion.mul (ofRealCompactOctonion a) (T (ofRealCompactOctonion b)) := by
    intro a b
    rw [ofRealCompactOctonion_mul]
    exact hT (ofRealCompactOctonion a) (ofRealCompactOctonion b)
  have hmul_decomp : ∀ a b : CompactOctonion ℝ,
      CompactOctonion.mul (T (ofRealCompactOctonion a)) (ofRealCompactOctonion b) +
        CompactOctonion.mul (ofRealCompactOctonion a) (T (ofRealCompactOctonion b)) =
      ofRealCompactOctonion
          (CompactOctonion.mul (rePartCompactOctonion (T (ofRealCompactOctonion a))) b +
            CompactOctonion.mul a (rePartCompactOctonion (T (ofRealCompactOctonion b)))) +
        Complex.I • ofRealCompactOctonion
          (CompactOctonion.mul (imPartCompactOctonion (T (ofRealCompactOctonion a))) b +
            CompactOctonion.mul a (imPartCompactOctonion (T (ofRealCompactOctonion b)))) := by
    intro a b
    conv_lhs =>
      rw [← ofReal_rePart_add_I_imPart_CompactOctonion (T (ofRealCompactOctonion a)),
        ← ofReal_rePart_add_I_imPart_CompactOctonion (T (ofRealCompactOctonion b))]
    simp only [CompactOctonion.add_mul, CompactOctonion.mul_add,
      CompactOctonion.smul_mul, CompactOctonion.mul_smul,
      ← ofRealCompactOctonion_mul, map_add, smul_add]
    abel
  constructor
  · intro a b
    have h0 := congrArg rePartCompactOctonion (hmul a b)
    rw [hmul_decomp, map_add, rePartCompactOctonion_ofReal,
      rePartCompactOctonion_I_smul, imPartCompactOctonion_ofReal, neg_zero, add_zero] at h0
    exact h0
  · intro a b
    have h0 := congrArg imPartCompactOctonion (hmul a b)
    rw [hmul_decomp, map_add, imPartCompactOctonion_ofReal,
      imPartCompactOctonion_I_smul, rePartCompactOctonion_ofReal, zero_add] at h0
    exact h0

private theorem liftEnd_zornDerivations
    (D : Module.End ℝ (ZornVectorMatrix ℝ)) (hD : D ∈ zornDerivations) :
    liftEnd tensorEquivZornVectorMatrix D ∈ zornDerivationsℂ := by
  intro X Y
  rw [← ofReal_rePart_add_I_imPart_ZornVectorMatrix X,
    ← ofReal_rePart_add_I_imPart_ZornVectorMatrix Y]
  have hreal : ∀ A B : ZornVectorMatrix ℝ,
      liftEnd tensorEquivZornVectorMatrix D
          (ZornVectorMatrix.mul (ofRealZornVectorMatrix A) (ofRealZornVectorMatrix B)) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul
            (liftEnd tensorEquivZornVectorMatrix D (ofRealZornVectorMatrix A))
            (ofRealZornVectorMatrix B))
          (ZornVectorMatrix.mul (ofRealZornVectorMatrix A)
            (liftEnd tensorEquivZornVectorMatrix D (ofRealZornVectorMatrix B))) := by
    intro A B
    rw [← ofRealZornVectorMatrix_mul,
      liftEnd_apply_ofReal tensorEquivZornVectorMatrix ofRealZornVectorMatrix
        tensorEquivZornVectorMatrix_tmul,
      liftEnd_apply_ofReal tensorEquivZornVectorMatrix ofRealZornVectorMatrix
        tensorEquivZornVectorMatrix_tmul,
      liftEnd_apply_ofReal tensorEquivZornVectorMatrix ofRealZornVectorMatrix
        tensorEquivZornVectorMatrix_tmul,
      hD A B, show ∀ P Q : ZornVectorMatrix ℝ, ZornVectorMatrix.add P Q = P + Q from fun _ _ => rfl,
      map_add, ofRealZornVectorMatrix_mul, ofRealZornVectorMatrix_mul]
    rfl
  have hadd_def : ∀ P Q : ZornVectorMatrix ℂ, P + Q = ZornVectorMatrix.add P Q := fun _ _ => rfl
  have hsmul_def : ∀ (z : ℂ) (P : ZornVectorMatrix ℂ), z • P = ZornVectorMatrix.smul z P :=
    fun _ _ => rfl
  simp only [map_add, map_smul]
  simp only [hadd_def, hsmul_def, ZornVectorMatrix.add_mul, ZornVectorMatrix.mul_add,
    ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul]
  simp only [← hadd_def, ← hsmul_def, map_add, map_smul]
  rw [hreal (rePartZornVectorMatrix X) (rePartZornVectorMatrix Y),
    hreal (rePartZornVectorMatrix X) (imPartZornVectorMatrix Y),
    hreal (imPartZornVectorMatrix X) (rePartZornVectorMatrix Y),
    hreal (imPartZornVectorMatrix X) (imPartZornVectorMatrix Y)]
  simp only [← hadd_def, smul_add]
  abel

private theorem split_zornDerivations
    (T : Module.End ℂ (ZornVectorMatrix ℂ)) (hT : T ∈ zornDerivationsℂ) :
    reEnd ofRealZornVectorMatrix rePartZornVectorMatrix T ∈ zornDerivations ∧
    imEnd ofRealZornVectorMatrix imPartZornVectorMatrix T ∈ zornDerivations := by
  have hadd_def : ∀ P Q : ZornVectorMatrix ℂ, P + Q = ZornVectorMatrix.add P Q := fun _ _ => rfl
  have hsmul_def : ∀ (z : ℂ) (P : ZornVectorMatrix ℂ), z • P = ZornVectorMatrix.smul z P :=
    fun _ _ => rfl
  have hmul : ∀ A B : ZornVectorMatrix ℝ,
      T (ofRealZornVectorMatrix (ZornVectorMatrix.mul A B)) =
        ZornVectorMatrix.mul (T (ofRealZornVectorMatrix A)) (ofRealZornVectorMatrix B) +
        ZornVectorMatrix.mul (ofRealZornVectorMatrix A) (T (ofRealZornVectorMatrix B)) := by
    intro A B
    rw [ofRealZornVectorMatrix_mul, hadd_def]
    exact hT (ofRealZornVectorMatrix A) (ofRealZornVectorMatrix B)
  have hmul_decomp : ∀ A B : ZornVectorMatrix ℝ,
      ZornVectorMatrix.mul (T (ofRealZornVectorMatrix A)) (ofRealZornVectorMatrix B) +
        ZornVectorMatrix.mul (ofRealZornVectorMatrix A) (T (ofRealZornVectorMatrix B)) =
      ofRealZornVectorMatrix
          (ZornVectorMatrix.add
            (ZornVectorMatrix.mul (rePartZornVectorMatrix (T (ofRealZornVectorMatrix A))) B)
            (ZornVectorMatrix.mul A (rePartZornVectorMatrix (T (ofRealZornVectorMatrix B))))) +
        Complex.I • ofRealZornVectorMatrix
          (ZornVectorMatrix.add
            (ZornVectorMatrix.mul (imPartZornVectorMatrix (T (ofRealZornVectorMatrix A))) B)
            (ZornVectorMatrix.mul A (imPartZornVectorMatrix (T (ofRealZornVectorMatrix B))))) := by
    intro A B
    conv_lhs =>
      rw [← ofReal_rePart_add_I_imPart_ZornVectorMatrix (T (ofRealZornVectorMatrix A)),
        ← ofReal_rePart_add_I_imPart_ZornVectorMatrix (T (ofRealZornVectorMatrix B))]
    simp only [hadd_def, hsmul_def, ZornVectorMatrix.add_mul, ZornVectorMatrix.mul_add,
      ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul, ← ofRealZornVectorMatrix_mul]
    simp only [← hadd_def, ← hsmul_def, ofRealZornVectorMatrix.map_add,
      show ∀ P Q : ZornVectorMatrix ℝ, ZornVectorMatrix.add P Q = P + Q from fun _ _ => rfl,
      smul_add]
    abel
  constructor
  · intro A B
    have h0 := congrArg rePartZornVectorMatrix (hmul A B)
    rw [hmul_decomp, map_add, rePartZornVectorMatrix_ofReal,
      rePartZornVectorMatrix_I_smul, imPartZornVectorMatrix_ofReal, neg_zero, add_zero] at h0
    exact h0
  · intro A B
    have h0 := congrArg imPartZornVectorMatrix (hmul A B)
    rw [hmul_decomp, map_add, imPartZornVectorMatrix_ofReal,
      imPartZornVectorMatrix_I_smul, rePartZornVectorMatrix_ofReal, zero_add] at h0
    exact h0

/-- `ℂ ⊗[ℝ] CompactOctonionDerivations ≃ₗ⁅ℂ⁆ compactOctonionDerivationsℂ`. -/
def compactOctonionDerivationsExtendEquiv :
    ℂ ⊗[ℝ] CompactOctonionDerivations ≃ₗ⁅ℂ⁆ compactOctonionDerivationsℂ :=
  mkBaseChangeLieEquiv tensorEquivCompactOctonion ofRealCompactOctonion
    rePartCompactOctonion imPartCompactOctonion
    tensorEquivCompactOctonion_tmul rePartCompactOctonion_ofReal imPartCompactOctonion_ofReal
    ofReal_rePart_add_I_imPart_CompactOctonion rePartCompactOctonion_I_smul
    imPartCompactOctonion_I_smul
    CompactOctonionDerivations compactOctonionDerivationsℂ
    liftEnd_compactOctonionDerivations split_compactOctonionDerivations

/-- `ℂ ⊗[ℝ] zornDerivations ≃ₗ⁅ℂ⁆ zornDerivationsℂ`. -/
def zornDerivationsExtendEquiv :
    ℂ ⊗[ℝ] zornDerivations ≃ₗ⁅ℂ⁆ zornDerivationsℂ :=
  mkBaseChangeLieEquiv tensorEquivZornVectorMatrix ofRealZornVectorMatrix
    rePartZornVectorMatrix imPartZornVectorMatrix
    tensorEquivZornVectorMatrix_tmul rePartZornVectorMatrix_ofReal imPartZornVectorMatrix_ofReal
    ofReal_rePart_add_I_imPart_ZornVectorMatrix rePartZornVectorMatrix_I_smul
    imPartZornVectorMatrix_I_smul
    zornDerivations zornDerivationsℂ
    liftEnd_zornDerivations split_zornDerivations

/-- Conjugation by `octonionComplexEquiv` induces
`compactOctonionDerivationsℂ ≃ₗ⁅ℂ⁆ zornDerivationsℂ`. -/
def compactOctonionDerivationsℂEquiv :
    compactOctonionDerivationsℂ ≃ₗ⁅ℂ⁆ zornDerivationsℂ :=
  LieEquiv.ofSubalgebras compactOctonionDerivationsℂ zornDerivationsℂ
    octonionComplexEquiv.lieConj
    (by
      ext D
      rw [LieSubalgebra.mem_map]
      constructor
      · rintro ⟨E, hE, rfl⟩ X Y
        obtain ⟨x, rfl⟩ := octonionComplexEquiv.surjective X
        obtain ⟨y, rfl⟩ := octonionComplexEquiv.surjective Y
        simp only [LieEquiv.coe_toLieHom, LinearEquiv.lieConj_apply, LinearEquiv.conj_apply_apply,
          LinearEquiv.symm_apply_apply, ← octonionComplexEquiv_mul, hE x y, map_add]
        rfl
      · intro hD
        refine ⟨octonionComplexEquiv.symm.lieConj D, ?_, ?_⟩
        · intro x y
          change (octonionComplexEquiv.symm.lieConj D) (CompactOctonion.mul x y) =
            CompactOctonion.mul ((octonionComplexEquiv.symm.lieConj D) x) y +
              CompactOctonion.mul x ((octonionComplexEquiv.symm.lieConj D) y)
          simp only [LinearEquiv.lieConj_apply, LinearEquiv.conj_apply_apply,
            LinearEquiv.symm_symm]
          rw [octonionComplexEquiv_mul, hD,
            show ∀ P Q : ZornVectorMatrix ℂ, ZornVectorMatrix.add P Q = P + Q from fun _ _ => rfl,
            map_add, octonionComplexEquiv_symm_mul, octonionComplexEquiv_symm_mul,
            LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
        · apply LinearMap.ext; intro X; simp [LinearEquiv.lieConj_apply])

/-- **Main Complexified `G₂` Lie Algebra Isomorphism**:
`ℂ ⊗[ℝ] CompactOctonionDerivations ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] zornDerivations`. -/
def compactG2BaseChangeEquiv :
    ℂ ⊗[ℝ] CompactOctonionDerivations ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] zornDerivations :=
  compactOctonionDerivationsExtendEquiv.trans
    (compactOctonionDerivationsℂEquiv.trans zornDerivationsExtendEquiv.symm)

/-- Transport a real Lie algebra equivalence `L₁ ≃ₗ⁅ℝ⁆ L₂` to `ℂ ⊗[ℝ] L₁ ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] L₂`. -/
def extendScalarsLieEquiv {L₁ L₂ : Type*} [LieRing L₁] [LieAlgebra ℝ L₁]
    [LieRing L₂] [LieAlgebra ℝ L₂] (e : L₁ ≃ₗ⁅ℝ⁆ L₂) :
    ℂ ⊗[ℝ] L₁ ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] L₂ :=
  let toFun : ℂ ⊗[ℝ] L₁ →ₗ[ℂ] ℂ ⊗[ℝ] L₂ :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ℂ →ₗ[ℂ] ℂ) e.toLinearEquiv.toLinearMap
  let invFun : ℂ ⊗[ℝ] L₂ →ₗ[ℂ] ℂ ⊗[ℝ] L₁ :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
      e.symm.toLinearEquiv.toLinearMap
  { toFun := toFun
    invFun := invFun
    map_add' := toFun.map_add'
    map_smul' := toFun.map_smul'
    left_inv := fun u => by
      induction u using TensorProduct.inductionOn with
      | tmul z x =>
        simp [toFun, invFun]
      | add a b ha hb => rw [map_add, map_add, ha, hb]
    right_inv := fun u => by
      induction u using TensorProduct.inductionOn with
      | tmul z y =>
        simp [toFun, invFun]
      | add a b ha hb => rw [map_add, map_add, ha, hb]
    map_lie' := fun {x y} => by
      induction x using TensorProduct.inductionOn generalizing y with
      | tmul z₁ x₁ =>
        induction y using TensorProduct.inductionOn with
        | tmul z₂ x₂ =>
          change toFun (⁅z₁ ⊗ₜ[ℝ] x₁, z₂ ⊗ₜ[ℝ] x₂⁆) =
            ⁅toFun (z₁ ⊗ₜ[ℝ] x₁), toFun (z₂ ⊗ₜ[ℝ] x₂)⁆
          simp [toFun, LieAlgebra.ExtendScalars.bracket_tmul, e.map_lie]
        | add a b ha hb =>
          simp only [lie_add, map_add] at ha hb ⊢
          rw [ha, hb]
      | add a b ha hb =>
        simp only [add_lie, map_add] at ha hb ⊢
        rw [ha, hb] }

/-- Complexified `G₂` isomorphism targeting `G2DerivationCarrier` (`VDer`) directly for `SplitE8Lie`. -/
def compactG2BaseChangeVDerEquiv :
    ℂ ⊗[ℝ] CompactOctonionDerivations ≃ₗ⁅ℂ⁆
      ℂ ⊗[ℝ] InfoGeometry.Canonical.NativeTitsE8Carrier.G2DerivationCarrier :=
  compactG2BaseChangeEquiv.trans (extendScalarsLieEquiv vDerEquivZornDerivations).symm

/-- **Unconditional 14-Dimensional Compact `𝔤₂(-14)` Theorem**:
`Module.finrank ℝ CompactOctonionDerivations = 14`. -/
theorem finrank_compactOctonionDerivations :
    Module.finrank ℝ CompactOctonionDerivations = 14 := by
  let _free1 : Module.Free ℝ CompactOctonionDerivations :=
    Module.Free.of_divisionRing ℝ CompactOctonionDerivations
  let _free2 : Module.Free ℝ zornDerivations :=
    Module.Free.of_divisionRing ℝ zornDerivations
  have h1 : Module.finrank ℂ (ℂ ⊗[ℝ] CompactOctonionDerivations) =
      Module.finrank ℝ CompactOctonionDerivations :=
    Module.finrank_baseChange
  have h2 : Module.finrank ℂ (ℂ ⊗[ℝ] CompactOctonionDerivations) =
      Module.finrank ℂ (ℂ ⊗[ℝ] zornDerivations) :=
    compactG2BaseChangeEquiv.toLinearEquiv.finrank_eq
  have h3 : Module.finrank ℂ (ℂ ⊗[ℝ] zornDerivations) =
      Module.finrank ℝ zornDerivations :=
    Module.finrank_baseChange
  have h4 : Module.finrank ℝ InfoGeometry.Canonical.NativeTitsE8Carrier.G2DerivationCarrier =
      Module.finrank ℝ zornDerivations :=
    vDerEquivZornDerivations.toLinearEquiv.finrank_eq
  rw [← h1, h2, h3, ← h4,
    InfoGeometry.Canonical.NativeTitsE8Carrier.finrank_g2DerivationCarrier]

end ComplexificationAndDimension

end InfoGeometry.Algebra
