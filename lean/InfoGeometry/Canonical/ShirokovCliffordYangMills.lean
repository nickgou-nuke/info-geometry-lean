/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KahlerAtiyahSpinConnection
import InfoGeometry.Canonical.ShirokovYangMillsTransfer
import InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions
import InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Clifford-vector specialization of Shirokov's Yang--Mills transfer

This is a conditional finite-coordinate form of Theorem 5.2. It combines the
Kähler--Atiyah Clifford action and its contracted cubic commutator with the
abstract `C + K` Yang--Mills transfer. Flatness and parallelness of the
background are hypotheses here; deriving them from a varying Clifford frame
is a separate open bridge.
-/

noncomputable section
set_option maxHeartbeats 500000

namespace InfoGeometry.Canonical.ShirokovCliffordYangMills

open InfoGeometry.Canonical.KahlerAtiyahCartanForms
open InfoGeometry.Canonical.KahlerAtiyahSpinConnection
open InfoGeometry.Canonical.ShirokovYangMillsTransfer
open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
open InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions

/-- The first two generators in the concrete negative-definite `Cl(0,2)`. -/
private def shirokovWitnessGen0 :
    CliffordAlgebra (cliffordNegSqForm ℝ 2) := cGen ℝ 2 0

private def shirokovWitnessGen1 :
    CliffordAlgebra (cliffordNegSqForm ℝ 2) := cGen ℝ 2 1

/-- Distinct orthogonal Clifford generators do not commute. -/
theorem shirokov_generators_noncommute :
    shirokovWitnessGen0 * shirokovWitnessGen1 ≠
      shirokovWitnessGen1 * shirokovWitnessGen0 := by
  exact cGen_noncomm ℝ (by norm_num) (by decide)

/-- A coordinate generator after an isometric change of frame in `Cl(0,n)`. -/
def shirokovIsometryFrameVector (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (i : Fin n) : CliffordAlgebra (cliffordNegSqForm ℝ n) :=
  CliffordAlgebra.ι (cliffordNegSqForm ℝ n) (e (Pi.single i (1 : ℝ)))

/-- The ascending ordered blade in the isometry-transformed frame. -/
def shirokovIsometryFrameBlade (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (S : Finset (Fin n)) : CliffordAlgebra (cliffordNegSqForm ℝ n) :=
  ((bladeList S).map (shirokovIsometryFrameVector n e)).prod

@[simp] theorem shirokovIsometryFrameVector_sq (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (i : Fin n) :
    shirokovIsometryFrameVector n e i * shirokovIsometryFrameVector n e i = -1 := by
  have h := congrArg (CliffordAlgebra.equivOfIsometry e) (cGen_sq ℝ n i)
  simpa [shirokovIsometryFrameVector, cGen] using h

theorem shirokovIsometryFrameVector_anticommute (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    {i j : Fin n} (hij : i ≠ j) :
    shirokovIsometryFrameVector n e i * shirokovIsometryFrameVector n e j +
      shirokovIsometryFrameVector n e j * shirokovIsometryFrameVector n e i = 0 := by
  have h := congrArg (CliffordAlgebra.equivOfIsometry e) (cGen_mul_swap hij)
  simpa [shirokovIsometryFrameVector, cGen] using h

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The commutator convention used in Shirokov's compatibility equation. -/
private def algebraCommutator {A : Type*} [Ring A] (x y : A) : A := x * y - y * x

private theorem derivation_map_commutator {A : Type*} [Ring A]
    (D : A →+ A) (hDmul : ∀ x y, D (x * y) = D x * y + x * D y)
    (x y : A) :
    D (algebraCommutator x y) =
      algebraCommutator (D x) y + algebraCommutator x (D y) := by
  simp only [algebraCommutator, map_sub, hDmul]
  noncomm_ring

/-- Compatibility with two commuting derivations forces the curvature defect
to commute with every coefficient. This is the algebraic consequence of
equation (1.7); concluding that the defect vanishes additionally requires a
center/grade argument. -/
theorem shirokov_compatibility_curvature_central
    {A : Type*} [Ring A]
    (D₁ D₂ : A →+ A) (C₁ C₂ : A)
    (hD₁mul : ∀ x y, D₁ (x * y) = D₁ x * y + x * D₁ y)
    (hD₂mul : ∀ x y, D₂ (x * y) = D₂ x * y + x * D₂ y)
    (hcomm : ∀ x, D₁ (D₂ x) = D₂ (D₁ x))
    (hcompat₁ : ∀ x, D₁ x = algebraCommutator C₁ x)
    (hcompat₂ : ∀ x, D₂ x = algebraCommutator C₂ x) :
    ∀ x, algebraCommutator
      (D₁ C₂ - D₂ C₁ - algebraCommutator C₁ C₂) x = 0 := by
  intro x
  have h := hcomm x
  rw [hcompat₂ x, derivation_map_commutator D₁ hD₁mul C₂ x,
    hcompat₁ x, derivation_map_commutator D₂ hD₂mul C₁ x,
    hcompat₂ x] at h
  calc
    algebraCommutator
        (D₁ C₂ - D₂ C₁ - algebraCommutator C₁ C₂) x =
        (D₁ C₂ * x - x * D₁ C₂ +
          (C₂ * (C₁ * x - x * C₁) - (C₁ * x - x * C₁) * C₂)) -
        (D₂ C₁ * x - x * D₂ C₁ +
          (C₁ * (C₂ * x - x * C₂) - (C₂ * x - x * C₂) * C₁)) := by
            dsimp [algebraCommutator]
            noncomm_ring
    _ = 0 := sub_eq_zero.mpr h

/-- Shirokov's compatibility equation on Clifford-vector generators implies
centrality of the coordinate curvature defect when the derivation directions
commute. The conclusion is centrality; eliminating the Clifford center still
requires the paper's grade restriction. -/
theorem shirokov_clifford_compatibility_curvature_central
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M)
    (K : DerivationLieLane ℝ (CliffordAlgebra Q))
    (C : OneForm K) (x y : K.L) (hxy : ⁅x, y⁆ = 0)
    (hgen₁ : ∀ v : M,
      covariantDerivative K (-C) x (CliffordAlgebra.ι Q v) = 0)
    (hgen₂ : ∀ v : M,
      covariantDerivative K (-C) y (CliffordAlgebra.ι Q v) = 0) :
    ∀ a : CliffordAlgebra Q,
      algebraCommutator
        (K.operatorAction x (C y) - K.operatorAction y (C x) -
          algebraCommutator (C x) (C y)) a = 0 := by
  have hparallel₁ := covariantDerivative_zero_of_clifford_generators
    (Q := Q) (Kcl := K) (-C) x hgen₁
  have hparallel₂ := covariantDerivative_zero_of_clifford_generators
    (Q := Q) (Kcl := K) (-C) y hgen₂
  have hcompat₁ : ∀ a : CliffordAlgebra Q,
      K.operatorAction x a = algebraCommutator (C x) a := by
    intro a
    have h : K.operatorAction x a + -(C x * a) + a * C x = 0 := by
      simpa [covariantDerivative] using hparallel₁ a
    have h' : K.operatorAction x a = C x * a + -(a * C x) := by
      calc
        K.operatorAction x a =
            (K.operatorAction x a + -(C x * a) + a * C x) +
              (C x * a + -(a * C x)) := by abel
        _ = C x * a + -(a * C x) := by rw [h]; simp
    simpa [algebraCommutator, sub_eq_add_neg] using h'
  have hcompat₂ : ∀ a : CliffordAlgebra Q,
      K.operatorAction y a = algebraCommutator (C y) a := by
    intro a
    have h : K.operatorAction y a + -(C y * a) + a * C y = 0 := by
      simpa [covariantDerivative] using hparallel₂ a
    have h' : K.operatorAction y a = C y * a + -(a * C y) := by
      calc
        K.operatorAction y a =
            (K.operatorAction y a + -(C y * a) + a * C y) +
              (C y * a + -(a * C y)) := by abel
        _ = C y * a + -(a * C y) := by rw [h]; simp
    simpa [algebraCommutator, sub_eq_add_neg] using h'
  have hcomm : ∀ a : CliffordAlgebra Q,
      K.operatorAction x (K.operatorAction y a) =
        K.operatorAction y (K.operatorAction x a) := by
    intro a
    have h := K.operatorAction_commutator_apply x y a
    rw [hxy] at h
    simp only [map_zero, LinearMap.zero_apply] at h
    exact sub_eq_zero.mp h.symm
  exact shirokov_compatibility_curvature_central
    (K.operatorAction x).toAddMonoidHom
    (K.operatorAction y).toAddMonoidHom (C x) (C y)
    (fun a b => K.operatorAction_leibniz x a b)
    (fun a b => K.operatorAction_leibniz y a b)
    hcomm hcompat₁ hcompat₂

/-- Under the file's compatibility convention
`Dᵢ a = [Cᵢ,a]`, the curvature-defect expression reduces algebraically to
`[C₁,C₂]`. Generator compatibility suffices because the covariant derivative
is a derivation on the Clifford algebra. -/
theorem shirokov_curvature_defect_eq_connection_commutator
    {n : ℕ}
    (K : DerivationLieLane ℝ
      (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (C : OneForm K) (x y : K.L)
    (hgen₁ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) x
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hgen₂ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) y
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0) :
    K.operatorAction x (C y) - K.operatorAction y (C x) -
        algebraCommutator (C x) (C y) = algebraCommutator (C x) (C y) := by
  have hparallel₁ := covariantDerivative_zero_of_clifford_generators
    (Q := cliffordNegSqForm ℝ n) (Kcl := K) (-C) x hgen₁
  have hparallel₂ := covariantDerivative_zero_of_clifford_generators
    (Q := cliffordNegSqForm ℝ n) (Kcl := K) (-C) y hgen₂
  have hcompat₁ : ∀ a : CliffordAlgebra (cliffordNegSqForm ℝ n),
      K.operatorAction x a = algebraCommutator (C x) a := by
    intro a
    have h : K.operatorAction x a + -(C x * a) + a * C x = 0 := by
      simpa [covariantDerivative] using hparallel₁ a
    have h' : K.operatorAction x a = C x * a + -(a * C x) := by
      calc
        K.operatorAction x a =
            (K.operatorAction x a + -(C x * a) + a * C x) +
              (C x * a + -(a * C x)) := by abel
        _ = C x * a + -(a * C x) := by rw [h]; simp
    simpa [algebraCommutator, sub_eq_add_neg] using h'
  have hcompat₂ : ∀ a : CliffordAlgebra (cliffordNegSqForm ℝ n),
      K.operatorAction y a = algebraCommutator (C y) a := by
    intro a
    have h : K.operatorAction y a + -(C y * a) + a * C y = 0 := by
      simpa [covariantDerivative] using hparallel₂ a
    have h' : K.operatorAction y a = C y * a + -(a * C y) := by
      calc
        K.operatorAction y a =
            (K.operatorAction y a + -(C y * a) + a * C y) +
              (C y * a + -(a * C y)) := by abel
        _ = C y * a + -(a * C y) := by rw [h]; simp
    simpa [algebraCommutator, sub_eq_add_neg] using h'
  rw [hcompat₁ (C y), hcompat₂ (C x)]
  dsimp [algebraCommutator]
  noncomm_ring

/-- Shirokov Theorem 2.1 on an ordered frame: compatibility on each frame
generator propagates to every ordered product, with no commutativity assumption
on the coefficient algebra. -/
theorem shirokov_theorem_2_1_ordered_frame_products
    {R A ι : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (C : OneForm K) (x : K.L)
    (frame : ι → A)
    (hframe : ∀ i : ι,
      covariantDerivative K (-C) x (frame i) = 0) :
    ∀ word : List ι,
      K.operatorAction x ((word.map frame).prod) =
        algebraCommutator (C x) ((word.map frame).prod) := by
  intro word
  have hprod := covariantDerivative_list_prod_zero K (-C) x
    (word.map frame) (by
      intro a ha
      rcases List.mem_map.mp ha with ⟨i, hi, hEq⟩
      subst a
      exact hframe i)
  have h : K.operatorAction x ((word.map frame).prod) +
      -(C x * (word.map frame).prod) + (word.map frame).prod * C x = 0 := by
    simpa [covariantDerivative] using hprod
  have h' : K.operatorAction x ((word.map frame).prod) =
      C x * (word.map frame).prod + -((word.map frame).prod * C x) := by
    calc
      K.operatorAction x ((word.map frame).prod) =
          (K.operatorAction x ((word.map frame).prod) +
            -(C x * (word.map frame).prod) + (word.map frame).prod * C x) +
            (C x * (word.map frame).prod + -((word.map frame).prod * C x)) := by
              abel
      _ = C x * (word.map frame).prod + -((word.map frame).prod * C x) := by
            rw [h]
            simp
  simpa [algebraCommutator, sub_eq_add_neg] using h'

/-- The final algebraic reduction in Shirokov's Theorem 2.2. For an indexed
dual frame, compatibility and the stated Reynolds average imply the averaged
connection formula modulo the center projection. The Clifford-specific
Reynolds identity and the fact that the connection has zero center component
are separate obligations. -/
theorem shirokov_theorem_2_2_average_reduction
    {R A ι : Type*} [CommRing R] [Ring A] [Algebra R A] [Fintype ι]
    (D : A → A) (C : A) (centerProj : A → A) (frame : ι → Aˣ)
    (hcompat : ∀ i, D (frame i : A) =
      C * (frame i : A) - (frame i : A) * C)
    (haverage : ∑ i : ι,
      (frame i : A) * C * (↑((frame i)⁻¹) : A) =
        Fintype.card ι • centerProj C) :
    ∑ i : ι, D (frame i : A) * (↑((frame i)⁻¹) : A) =
      Fintype.card ι • (C - centerProj C) := by
  have hterm (i : ι) :
      D (frame i : A) * (↑((frame i)⁻¹) : A) =
        C - (frame i : A) * C * (↑((frame i)⁻¹) : A) := by
    rw [hcompat i]
    have hu : (frame i : A) * (↑((frame i)⁻¹) : A) = 1 := by simp
    calc
      (C * (frame i : A) - (frame i : A) * C) *
          (↑((frame i)⁻¹) : A) =
        C * ((frame i : A) * (↑((frame i)⁻¹) : A)) -
          (frame i : A) * C * (↑((frame i)⁻¹) : A) := by noncomm_ring
      _ = C - (frame i : A) * C * (↑((frame i)⁻¹) : A) := by rw [hu, mul_one]
  calc
    ∑ i : ι, D (frame i : A) * (↑((frame i)⁻¹) : A) =
        ∑ i : ι, (C - (frame i : A) * C * (↑((frame i)⁻¹) : A)) := by
          exact Finset.sum_congr rfl fun i _ => hterm i
    _ = (∑ _i : ι, C) -
        ∑ i : ι, (frame i : A) * C * (↑((frame i)⁻¹) : A) := by
          rw [Finset.sum_sub_distrib]
    _ = Fintype.card ι • C - Fintype.card ι • centerProj C := by
          rw [Finset.sum_const, Finset.card_univ, haverage]
    _ = Fintype.card ι • (C - centerProj C) := by rw [nsmul_sub]

/-- The Clifford blade swap law gives an explicit conjugation coefficient.
This is the finite combinatorial input needed for the standard-frame Reynolds
average; it is stated for the repository's negative-definite `Cl(0,n)` blade
owner and does not yet identify the average with the center projection. -/
theorem shirokov_blade_conjugation_sign
    {R : Type*} [CommRing R] (n : ℕ) (S T : Finset (Fin n)) :
    cBlade R n S * cBlade R n T * cBlade R n S =
      ((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2 +
        S.card * (S.card + 1) / 2)) • cBlade R n T := by
  obtain ⟨_, hswap⟩ := cBlade_mul_swap_overlap R n S T
  calc
    cBlade R n S * cBlade R n T * cBlade R n S =
        (cBlade R n S * cBlade R n T) * cBlade R n S := by noncomm_ring
    _ = (((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2)) •
        (cBlade R n T * cBlade R n S)) * cBlade R n S := by rw [hswap]
    _ = ((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2)) •
        (cBlade R n T * (cBlade R n S * cBlade R n S)) := by
          rw [smul_mul_assoc]; congr 1; noncomm_ring
    _ = ((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2)) •
        (((-1 : R) ^ (S.card * (S.card + 1) / 2)) • cBlade R n T) := by
          rw [cBlade_sq, mul_smul_comm, mul_one]
    _ = ((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2 +
          S.card * (S.card + 1) / 2)) • cBlade R n T := by
          calc
            _ = (((-1 : R) ^ (S.card * T.card - (S ∩ T).card ^ 2)) *
                (-1 : R) ^ (S.card * (S.card + 1) / 2)) • cBlade R n T :=
                  smul_smul _ _ _
            _ = _ := by rw [← pow_add]

/-- The Reynolds character sum factors as a coordinatewise product. This is
the combinatorial cancellation mechanism for the standard blade frame; a
separate parity lemma identifies these factors with the conjugation signs. -/
theorem shirokov_reynolds_character_sum (n : ℕ) (T : Finset (Fin n)) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ∏ i ∈ S, (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0)) =
      ∏ i ∈ (Finset.univ : Finset (Fin n)),
        (1 + (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0)) := by
  simpa using (Finset.prod_one_add
    (f := fun i : Fin n => (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0))
    (Finset.univ : Finset (Fin n))).symm

/-- Every noncentral blade character has zero standard-frame average: an even
nonempty blade is killed at a coordinate in it; an odd non-top blade is killed
at a coordinate outside it. -/
theorem shirokov_noncentral_blade_character_vanishes (n : ℕ)
    (T : Finset (Fin n))
    (hcase : (Even T.card ∧ T.Nonempty) ∨ (Odd T.card ∧
      T ≠ (Finset.univ : Finset (Fin n)))) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ∏ i ∈ S, (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0)) = 0 := by
  rw [shirokov_reynolds_character_sum]
  obtain hEven | hOdd := hcase
  · obtain ⟨i, hi⟩ := hEven.2
    have hfactor : 1 + (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0) = 0 := by
      obtain ⟨k, hk⟩ := hEven.1
      simp [hi, hk]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hfactor
  · have hout : ∃ i : Fin n, i ∉ T := by
      by_contra h
      push Not at h
      apply hOdd.2
      ext i
      simp only [Finset.mem_univ]
      exact ⟨fun _ => trivial, fun _ => h i⟩
    obtain ⟨i, hi⟩ := hout
    have hfactor : 1 + (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0) = 0 := by
      obtain ⟨k, hk⟩ := hOdd.1
      simp [hi, hk, pow_add, pow_mul]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hfactor

/-- The product character is exactly the sign from swapping two Clifford
blades; `k^2` and `k` have the same parity for the overlap cardinality `k`. -/
theorem shirokov_blade_character_product (n : ℕ)
    (S T : Finset (Fin n)) :
    ∏ i ∈ S, (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0) =
      (-1 : ℤ) ^ (S.card * T.card + (S ∩ T).card) := by
  rw [Finset.prod_pow_eq_pow_sum]
  have hsum :
      (∑ i ∈ S, (T.card + if i ∈ T then 1 else 0)) =
        S.card * T.card + (S ∩ T).card := by
    simp [Finset.sum_add_distrib, Finset.sum_const]
  rw [hsum]

/-- The overlap exponent in the Clifford blade swap law is the same sign
character that factors over coordinates in the standard-frame average. -/
theorem shirokov_blade_swap_sign_character (n : ℕ)
    (S T : Finset (Fin n)) :
    (-1 : ℤ) ^ (S.card * T.card - (S ∩ T).card ^ 2) =
      ∏ i ∈ S, (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0) := by
  have hle := (cBlade_mul_swap_overlap ℤ n S T).1
  have hmod : S.card * T.card - (S ∩ T).card ^ 2 ≡
      S.card * T.card + (S ∩ T).card [MOD 2] := by
    have hk : (S ∩ T).card ^ 2 + (S ∩ T).card =
        (S ∩ T).card * ((S ∩ T).card + 1) := by ring
    have heven : 2 ∣ (S ∩ T).card * ((S ∩ T).card + 1) := by
      rcases Nat.even_or_odd (S ∩ T).card with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact ⟨j * ((S ∩ T).card + 1), by rw [hj]; ring⟩
      · exact ⟨(S ∩ T).card * (j + 1), by rw [hj]; ring⟩
    rw [Nat.ModEq]
    omega
  rw [neg_one_pow_eq_of_modEq (R := ℤ) hmod,
    shirokov_blade_character_product]

/-- In `Cl(0,n)`, the ordered blade inverse is its square sign times itself. -/
theorem shirokov_blade_inverse_formula (n : ℕ) (S : Finset (Fin n)) :
    let b := cBlade ℝ n S
    let ε : ℝ := (-1) ^ (S.card * (S.card + 1) / 2)
    (ε • b) * b = 1 ∧ b * (ε • b) = 1 := by
  dsimp
  let ε : ℝ := (-1) ^ (S.card * (S.card + 1) / 2)
  have hε : ε * ε = 1 := by
    calc
      ε * ε = (-1 : ℝ) ^
          (S.card * (S.card + 1) / 2 + S.card * (S.card + 1) / 2) := by
            dsimp [ε]
            rw [← pow_add]
      _ = (-1 : ℝ) ^ (2 * (S.card * (S.card + 1) / 2)) := by
            congr 1 <;> omega
      _ = ((-1 : ℝ) ^ 2) ^ (S.card * (S.card + 1) / 2) := by rw [pow_mul]
      _ = 1 := by norm_num
  have hsq : cBlade ℝ n S * cBlade ℝ n S = ε • (1 : CliffordAlgebra
      (cliffordNegSqForm ℝ n)) := by
    simpa [ε] using cBlade_sq ℝ n S
  constructor
  · calc
      (ε • cBlade ℝ n S) * cBlade ℝ n S =
          ε • (cBlade ℝ n S * cBlade ℝ n S) := smul_mul_assoc _ _ _
      _ = ε • (ε • (1 : CliffordAlgebra (cliffordNegSqForm ℝ n))) := by rw [hsq]
      _ = (ε * ε) • (1 : CliffordAlgebra (cliffordNegSqForm ℝ n)) := smul_smul _ _ _
      _ = 1 := by rw [hε]; simp
  · calc
      cBlade ℝ n S * (ε • cBlade ℝ n S) =
          ε • (cBlade ℝ n S * cBlade ℝ n S) := mul_smul_comm _ _ _
      _ = ε • (ε • (1 : CliffordAlgebra (cliffordNegSqForm ℝ n))) := by rw [hsq]
      _ = (ε * ε) • (1 : CliffordAlgebra (cliffordNegSqForm ℝ n)) := smul_smul _ _ _
      _ = 1 := by rw [hε]; simp

/-- Conjugation by the actual inverse blade acts by the overlap sign, with the
blade-square sign canceled. -/
theorem shirokov_inverse_blade_conjugation_sign (n : ℕ)
    (S T : Finset (Fin n)) :
    let b := cBlade ℝ n S
    let ε : ℝ := (-1) ^ (S.card * (S.card + 1) / 2)
    (ε • b) * cBlade ℝ n T * b =
      ((-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) • cBlade ℝ n T := by
  dsimp
  let ε : ℝ := (-1) ^ (S.card * (S.card + 1) / 2)
  have hconj := shirokov_blade_conjugation_sign (R := ℝ) n S T
  calc
    (ε • cBlade ℝ n S) * cBlade ℝ n T * cBlade ℝ n S =
        ε • (cBlade ℝ n S * cBlade ℝ n T * cBlade ℝ n S) := by
          simp only [smul_mul_assoc]
    _ = ε • (((-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2 +
          S.card * (S.card + 1) / 2)) • cBlade ℝ n T) := by rw [hconj]
    _ = (ε * (-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2 +
          S.card * (S.card + 1) / 2)) • cBlade ℝ n T := smul_smul _ _ _
    _ = ((-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) • cBlade ℝ n T := by
          dsimp [ε]
          rw [← pow_add]
          have hmod : S.card * (S.card + 1) / 2 +
              (S.card * T.card - (S ∩ T).card ^ 2 +
                S.card * (S.card + 1) / 2) ≡
              S.card * T.card - (S ∩ T).card ^ 2 [MOD 2] := by
            have hprodEven : 2 ∣ S.card * (S.card + 1) := by
              rcases Nat.even_or_odd S.card with ⟨j, hj⟩ | ⟨j, hj⟩
              · exact ⟨j * (S.card + 1), by rw [hj]; ring⟩
              · exact ⟨S.card * (j + 1), by rw [hj]; ring⟩
            have hdiv : 2 * (S.card * (S.card + 1) / 2) = S.card * (S.card + 1) :=
              Nat.mul_div_cancel' hprodEven
            rw [Nat.ModEq]
            omega
          rw [neg_one_pow_eq_of_modEq (R := ℝ) hmod]

/-- The signed overlap coefficients from the Clifford blade swap law cancel
for all grades except the scalar and, in odd dimension, the top grade. -/
theorem shirokov_blade_swap_average_vanishes (n : ℕ)
    (T : Finset (Fin n))
    (hcase : (Even T.card ∧ T.Nonempty) ∨ (Odd T.card ∧
      T ≠ (Finset.univ : Finset (Fin n)))) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      (-1 : ℤ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) = 0 := by
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (-1 : ℤ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∏ i ∈ S, (-1 : ℤ) ^ (T.card + if i ∈ T then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro S hS
          exact shirokov_blade_swap_sign_character n S T
    _ = 0 := shirokov_noncentral_blade_character_vanishes n T hcase

/-- The actual inverse-blade Reynolds sum annihilates every noncentral blade
in the standard `Cl(0,n)` basis. The scalar and odd-dimensional top grades
are excluded by `hcase` and require the corresponding fixed-point calculation. -/
theorem shirokov_noncentral_blade_reynolds_vanishes (n : ℕ)
    (T : Finset (Fin n))
    (hcase : (Even T.card ∧ T.Nonempty) ∨ (Odd T.card ∧
      T ≠ (Finset.univ : Finset (Fin n)))) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
        cBlade ℝ n T * cBlade ℝ n S) = 0 := by
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
          cBlade ℝ n T * cBlade ℝ n S) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) • cBlade ℝ n T := by
          apply Finset.sum_congr rfl
          intro S hS
          exact shirokov_inverse_blade_conjugation_sign n S T
    _ = (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          (-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) • cBlade ℝ n T := by
          rw [← Finset.sum_smul]
    _ = 0 := by
          have hcoef :
              (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
                (-1 : ℝ) ^ (S.card * T.card - (S ∩ T).card ^ 2)) = 0 := by
            exact_mod_cast shirokov_blade_swap_average_vanishes n T hcase
          rw [hcoef]
          simp

/-- The standard inverse-blade Reynolds average fixes the scalar blade with
the expected orbit-count factor `2^n`. -/
theorem shirokov_scalar_blade_reynolds_average (n : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
        cBlade ℝ n ∅ * cBlade ℝ n S) =
      (2 ^ n : ℝ) • cBlade ℝ n ∅ := by
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
          cBlade ℝ n ∅ * cBlade ℝ n S) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (1 : ℝ) • cBlade ℝ n ∅ := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [shirokov_inverse_blade_conjugation_sign]
          simp [cBlade_empty]
    _ = (2 ^ n : ℝ) • cBlade ℝ n ∅ := by
          rw [← Finset.sum_smul]
          simp

/-- In odd dimension, the standard inverse-blade Reynolds average fixes the
top-grade pseudoscalar as well as the scalar blade. -/
theorem shirokov_odd_pseudoscalar_reynolds_average (n : ℕ) (hn : Odd n) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
        cBlade ℝ n (Finset.univ : Finset (Fin n)) * cBlade ℝ n S) =
      (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) := by
  have hnCard : Odd (Finset.univ : Finset (Fin n)).card := by simpa using hn
  obtain ⟨k, hk⟩ := hnCard
  have hkN : n = 2 * k + 1 := by simpa using hk
  have hfactor (i : Fin n) :
      (-1 : ℝ) ^ ((Finset.univ : Finset (Fin n)).card +
        if i ∈ (Finset.univ : Finset (Fin n)) then 1 else 0) = 1 := by
    simp only [Finset.mem_univ, if_true, Finset.card_univ, Fintype.card_fin]
    rw [hkN]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
          cBlade ℝ n (Finset.univ : Finset (Fin n)) * cBlade ℝ n S) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (1 : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [shirokov_inverse_blade_conjugation_sign]
          have hsign : (-1 : ℝ) ^
              (S.card * (Finset.univ : Finset (Fin n)).card -
                (S ∩ (Finset.univ : Finset (Fin n))).card ^ 2) = 1 := by
            have hchar := shirokov_blade_swap_sign_character n S
              (Finset.univ : Finset (Fin n))
            have hreal : (-1 : ℝ) ^
                (S.card * (Finset.univ : Finset (Fin n)).card -
                  (S ∩ (Finset.univ : Finset (Fin n))).card ^ 2) =
                ∏ i ∈ S, (-1 : ℝ) ^
                  ((Finset.univ : Finset (Fin n)).card +
                    if i ∈ (Finset.univ : Finset (Fin n)) then 1 else 0) := by
              exact_mod_cast hchar
            rw [hreal]
            simp only [hfactor, Finset.prod_const_one]
          rw [hsign]
    _ = (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) := by
          rw [← Finset.sum_smul]
          simp

/-- The standard inverse-blade Reynolds average on any blade: only the scalar
and (in odd dimension) the top-grade blade survive. -/
theorem shirokov_blade_reynolds_formula (n : ℕ) (T : Finset (Fin n)) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
        cBlade ℝ n T * cBlade ℝ n S) =
      if T = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
      if Odd n ∧ T = Finset.univ then
        (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0 := by
  by_cases hEmpty : T = ∅
  · subst T
    simp only [if_pos rfl]
    exact shirokov_scalar_blade_reynolds_average n
  by_cases hTop : Odd n ∧ T = Finset.univ
  · rw [if_neg hEmpty, if_pos hTop]
    simpa [hTop.2] using shirokov_odd_pseudoscalar_reynolds_average n hTop.1
  rw [if_neg hEmpty, if_neg hTop]
  have hne : T.Nonempty := by
    by_contra h
    apply hEmpty
    exact Finset.not_nonempty_iff_eq_empty.mp h
  have hcase : (Even T.card ∧ T.Nonempty) ∨
      (Odd T.card ∧ T ≠ (Finset.univ : Finset (Fin n))) := by
    rcases Nat.even_or_odd T.card with hEven | hOdd
    · exact Or.inl ⟨hEven, hne⟩
    · exact Or.inr ⟨hOdd, fun h => hTop ⟨by simpa [h] using hOdd, h⟩⟩
  exact shirokov_noncentral_blade_reynolds_vanishes n T hcase

/-- The unnormalized standard-frame Reynolds operator on `Cl(0,n)`, written
using the explicit inverse-blade formula. -/
def shirokovReynolds (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    CliffordAlgebra (cliffordNegSqForm ℝ n) :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
    ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) * x *
      cBlade ℝ n S

/-- Reynolds averaging acts coefficientwise on finite blade expansions. -/
theorem shirokov_reynolds_blade_expansion (n : ℕ)
    (a : Finset (Fin n) → ℝ) :
    shirokovReynolds n
      (∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        a T • cBlade ℝ n T) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        a T • shirokovReynolds n (cBlade ℝ n T) := by
  simp only [shirokovReynolds, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
          (a T • cBlade ℝ n T) * cBlade ℝ n S) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        a T • (((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
          cBlade ℝ n T * cBlade ℝ n S) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [mul_smul_comm, smul_mul_assoc]
    _ = a T • shirokovReynolds n (cBlade ℝ n T) := by
          rw [← Finset.smul_sum]
          rfl

/-- Explicit Reynolds action on an arbitrary finite linear combination of
ordered blades: the coefficient is retained only at scalar and odd top grade. -/
theorem shirokov_reynolds_finite_blade_support (n : ℕ)
    (a : Finset (Fin n) → ℝ) :
    shirokovReynolds n
      (∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        a T • cBlade ℝ n T) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        a T • (if T = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
          if Odd n ∧ T = Finset.univ then
            (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0) := by
  rw [shirokov_reynolds_blade_expansion]
  apply Finset.sum_congr rfl
  intro T hT
  change a T • (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) *
        cBlade ℝ n T * cBlade ℝ n S) = _
  rw [shirokov_blade_reynolds_formula]

/-- Coordinate readout of `Cl(0,n)` in the ordered blade family. -/
def shirokovBladeCoordinates (n : ℕ) :
    CliffordAlgebra (cliffordNegSqForm ℝ n) →ₗ[ℝ] Finset (Fin n) → ℝ where
  toFun := bladeRepr ℝ n
  map_add' x y := by simp [bladeRepr]
  map_smul' r x := by simp [bladeRepr]

@[simp]
theorem shirokovBladeCoordinates_cBlade (n : ℕ) (S : Finset (Fin n)) :
    shirokovBladeCoordinates n (cBlade ℝ n S) = Pi.single S 1 :=
  bladeRepr_cBlade ℝ n S

/-- The ordered blades span the full `Cl(0,n)` carrier: the coordinate readout
is onto, and the source and coordinate space have the same finite dimension. -/
theorem shirokov_blade_coordinates_injective (n : ℕ) :
    Function.Injective (shirokovBladeCoordinates n) := by
  let eBasis := (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra
  letI : FiniteDimensional ℝ (ExteriorAlgebra ℝ (Fin n → ℝ)) :=
    eBasis.finiteDimensional_of_finite
  letI : FiniteDimensional ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) :=
    (cliffordToExterior n).symm.finiteDimensional
  have hdim : Module.finrank ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) =
      Module.finrank ℝ (Finset (Fin n) → ℝ) := by
    calc
      Module.finrank ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) =
          Module.finrank ℝ (ExteriorAlgebra ℝ (Fin n → ℝ)) :=
        LinearEquiv.finrank_eq (cliffordToExterior n)
      _ = Fintype.card (Finset (Fin n)) := Module.finrank_eq_card_basis eBasis
      _ = Module.finrank ℝ (Finset (Fin n) → ℝ) :=
        (Module.finrank_eq_card_basis (Pi.basisFun ℝ (Finset (Fin n)))).symm
  have hsurj : Function.Surjective (shirokovBladeCoordinates n) := by
    intro f
    refine ⟨∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      f S • cBlade ℝ n S, ?_⟩
    ext T
    simp [Pi.single_apply]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj

/-- Every element of `Cl(0,n)` has its canonical finite ordered-blade expansion. -/
theorem shirokov_blade_expansion (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    x = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      bladeRepr ℝ n x S • cBlade ℝ n S := by
  apply shirokov_blade_coordinates_injective n
  simp only [map_sum, map_smul, shirokovBladeCoordinates_cBlade]
  ext T
  change bladeRepr ℝ n x T = _
  simp [Pi.single_apply]

/-- Reynolds average on every element of the finite-stage Clifford algebra, in
ordered-blade coordinates. Its support is scalar, plus odd top grade. -/
theorem shirokov_reynolds_all_elements (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    shirokovReynolds n x =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        bladeRepr ℝ n x T • (if T = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
          if Odd n ∧ T = Finset.univ then
            (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0) := by
  calc
    shirokovReynolds n x = shirokovReynolds n
        (∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
          bladeRepr ℝ n x T • cBlade ℝ n T) :=
            congrArg (shirokovReynolds n) (shirokov_blade_expansion n x)
    _ = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        bladeRepr ℝ n x T • (if T = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
          if Odd n ∧ T = Finset.univ then
            (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0) :=
              shirokov_reynolds_finite_blade_support n (bladeRepr ℝ n x)

/-- Non-scalar, non-top blade coordinates of the Reynolds average vanish. This
is the support statement supplied by the finite-frame average; identifying
its range with the algebraic center still requires centrality of the odd top
blade. -/
theorem shirokov_reynolds_noncentral_coordinate_zero (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) (T : Finset (Fin n))
    (hEmpty : T ≠ ∅)
    (hTop : ¬ (Odd n ∧ T = (Finset.univ : Finset (Fin n)))) :
    bladeRepr ℝ n (shirokovReynolds n x) T = 0 := by
  change (shirokovBladeCoordinates n (shirokovReynolds n x)) T = 0
  rw [shirokov_reynolds_all_elements]
  simp only [map_sum, map_smul]
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro S hS
  have hcoord : (shirokovBladeCoordinates n
      (if S = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
        if Odd n ∧ S = (Finset.univ : Finset (Fin n)) then
          (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0)) T = 0 := by
    by_cases hSempty : S = ∅
    · subst S
      have hscalar : (shirokovBladeCoordinates n (cBlade ℝ n ∅)) T = 0 := by
        rw [shirokovBladeCoordinates_cBlade]
        simp [Pi.single_apply, hEmpty]
      have hscaled :
          (shirokovBladeCoordinates n ((2 ^ n : ℝ) • cBlade ℝ n ∅)) T = 0 := by
        rw [map_smul, Pi.smul_apply, hscalar]
        simp
      change (shirokovBladeCoordinates n ((2 ^ n : ℝ) • cBlade ℝ n ∅)) T = 0
      exact hscaled
    · by_cases hStop : Odd n ∧ S = (Finset.univ : Finset (Fin n))
      · rcases hStop with ⟨hn, hSall⟩
        subst S
        have htopcond : Odd n ∧ (Finset.univ : Finset (Fin n)) = Finset.univ :=
          ⟨hn, rfl⟩
        have hT : T ≠ (Finset.univ : Finset (Fin n)) := by
          intro hT
          exact hTop ⟨hn, hT⟩
        have htopcoord :
            (shirokovBladeCoordinates n (cBlade ℝ n (Finset.univ : Finset (Fin n)))) T = 0 := by
          simp [shirokovBladeCoordinates_cBlade, Pi.single_apply, hT]
        have hscaled :
            (shirokovBladeCoordinates n
              ((2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)))) T = 0 := by
          rw [map_smul, Pi.smul_apply, htopcoord]
          simp
        rw [if_neg hSempty, if_pos htopcond]
        exact hscaled
      · simp [hSempty, hStop]
  change bladeRepr ℝ n x S *
    (shirokovBladeCoordinates n
      (if S = ∅ then (2 ^ n : ℝ) • cBlade ℝ n ∅ else
        if Odd n ∧ S = (Finset.univ : Finset (Fin n)) then
          (2 ^ n : ℝ) • cBlade ℝ n (Finset.univ : Finset (Fin n)) else 0)) T = 0
  rw [hcoord]
  simp

/-- In odd dimension, the top ordered blade commutes with every Clifford
generator, hence with the full algebra generated by those vectors. -/
theorem shirokov_odd_top_blade_mem_center (n : ℕ) (hn : Odd n) :
    cBlade ℝ n (Finset.univ : Finset (Fin n)) ∈
      Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
  have hsign : (-1 : ℝ) ^ (n + 1) = 1 := by
    obtain ⟨k, hk⟩ := hn
    rw [hk]
    norm_num [pow_add, pow_mul]
  have hcommGen : ∀ r : Fin n,
      cGen ℝ n r * cBlade ℝ n (Finset.univ : Finset (Fin n)) =
        cBlade ℝ n (Finset.univ : Finset (Fin n)) * cGen ℝ n r := by
    intro r
    have h := cGen_mul_cBlade ℝ n r (Finset.univ : Finset (Fin n))
    simpa [Finset.card_fin, hsign] using h
  have hcommVec : ∀ v : Fin n → ℝ,
      cBlade ℝ n (Finset.univ : Finset (Fin n)) *
          CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v =
        CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v *
          cBlade ℝ n (Finset.univ : Finset (Fin n)) := by
    intro v
    have hv : v = ∑ r : Fin n, v r • (Pi.single r (1 : ℝ)) := by
      ext i
      simp [Pi.single_apply]
    rw [hv]
    simp only [map_sum, map_smul]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_mul_assoc, mul_smul_comm]
    change v r • (cBlade ℝ n Finset.univ * cGen ℝ n r) =
      v r • (cGen ℝ n r * cBlade ℝ n Finset.univ)
    rw [← hcommGen r]
  rw [Subalgebra.mem_center_iff]
  intro x
  have hx : x ∈ Algebra.adjoin ℝ
      (Set.range (CliffordAlgebra.ι (cliffordNegSqForm ℝ n))) := by
    rw [CliffordAlgebra.adjoin_range_ι (Q := cliffordNegSqForm ℝ n)]
    trivial
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
  · intro v hv
    rcases hv with ⟨v, rfl⟩
    exact (hcommVec v).symm
  · intro r
    exact Algebra.commutes r (cBlade ℝ n (Finset.univ : Finset (Fin n)))
  · intro a b ha hb hxa hxb
    rw [add_mul, mul_add, hxa, hxb]
  · intro a b ha hb hxa hxb
    calc
      (a * b) * cBlade ℝ n (Finset.univ : Finset (Fin n)) =
          a * (b * cBlade ℝ n (Finset.univ : Finset (Fin n))) := by rw [mul_assoc]
      _ = a * (cBlade ℝ n (Finset.univ : Finset (Fin n)) * b) := by rw [hxb]
      _ = (a * cBlade ℝ n (Finset.univ : Finset (Fin n))) * b := by rw [← mul_assoc]
      _ = (cBlade ℝ n (Finset.univ : Finset (Fin n)) * a) * b := by rw [hxa]
      _ = cBlade ℝ n (Finset.univ : Finset (Fin n)) * (a * b) := by rw [mul_assoc]

/-- The finite-frame Reynolds average is central: its coordinate support is
scalar, with the odd top blade central in odd dimension. -/
theorem shirokov_reynolds_mem_center (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    shirokovReynolds n x ∈
      Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
  let C := Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n))
  rw [shirokov_reynolds_all_elements]
  apply Subalgebra.sum_mem
  intro T hT
  apply Subalgebra.smul_mem
  by_cases hEmpty : T = ∅
  · subst T
    simp only [if_pos rfl]
    rw [cBlade_empty]
    exact Subalgebra.smul_mem C (Subalgebra.one_mem C) (2 ^ n : ℝ)
  · by_cases hTop : Odd n ∧ T = (Finset.univ : Finset (Fin n))
    · rcases hTop with ⟨hn, rfl⟩
      rw [if_neg hEmpty, if_pos ⟨hn, rfl⟩]
      exact Subalgebra.smul_mem C (shirokov_odd_top_blade_mem_center n hn)
        (2 ^ n : ℝ)
    · simp [hEmpty, hTop]

/-- The unnormalized Reynolds average acts as multiplication by the number of
frame blades on every element of the algebraic center. -/
theorem shirokov_reynolds_eq_card_smul_of_mem_center (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : x ∈ Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n))) :
    shirokovReynolds n x = (2 ^ n : ℝ) • x := by
  unfold shirokovReynolds
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) * x *
          cBlade ℝ n S) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, x := by
        apply Finset.sum_congr rfl
        intro S hS
        let b := cBlade ℝ n S
        let ε : ℝ := (-1) ^ (S.card * (S.card + 1) / 2)
        have hcomm := (Subalgebra.mem_center_iff.mp hx) b
        have hinv := (shirokov_blade_inverse_formula n S).1
        change (ε • b) * x * b = x
        calc
          (ε • b) * x * b = ε • (b * x * b) := by simp only [smul_mul_assoc]
          _ = ε • (x * b * b) := by rw [hcomm]
          _ = x * ((ε • b) * b) := by noncomm_ring
          _ = x := by simpa [b, ε] using congrArg (fun z => x * z) hinv
    _ = (2 ^ n : ℝ) • x := by
      simp only [Finset.sum_const, Finset.card_powerset, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Algebra.smul_def]
      congr 1
      norm_cast

/-- The normalized standard-frame Reynolds operator, valued in the algebraic
center of the finite-stage Clifford algebra. -/
def shirokovCenterProjection (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    CliffordAlgebra (cliffordNegSqForm ℝ n) :=
  ((2 ^ n : ℝ)⁻¹) • shirokovReynolds n x

theorem shirokovCenterProjection_mem_center (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    shirokovCenterProjection n x ∈
      Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
  apply Subalgebra.smul_mem _ (shirokov_reynolds_mem_center n x)

theorem shirokovCenterProjection_fixes_center (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : x ∈ Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n))) :
    shirokovCenterProjection n x = x := by
  have hpow : (2 ^ n : ℝ) ≠ 0 := pow_ne_zero _ (by norm_num)
  change ((2 ^ n : ℝ)⁻¹) • shirokovReynolds n x = x
  rw [shirokov_reynolds_eq_card_smul_of_mem_center n x hx, smul_smul]
  simp [hpow]

theorem shirokovCenterProjection_idempotent (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    shirokovCenterProjection n (shirokovCenterProjection n x) =
      shirokovCenterProjection n x :=
  shirokovCenterProjection_fixes_center n _
    (shirokovCenterProjection_mem_center n x)

/-- Central elements of the finite-stage `Cl(0,n)` have no blade coordinates
outside the scalar and odd-dimensional top grades. -/
theorem shirokov_center_coordinate_support (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : x ∈ Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (T : Finset (Fin n)) (hEmpty : T ≠ ∅)
    (hTop : ¬ (Odd n ∧ T = (Finset.univ : Finset (Fin n)))) :
    bladeRepr ℝ n x T = 0 := by
  have hfix := shirokovCenterProjection_fixes_center n x hx
  have hzero := shirokov_reynolds_noncentral_coordinate_zero n x T hEmpty hTop
  change (shirokovBladeCoordinates n (shirokovReynolds n x)) T = 0 at hzero
  change (shirokovBladeCoordinates n x) T = 0
  rw [← hfix]
  change (shirokovBladeCoordinates n
      (((2 ^ n : ℝ)⁻¹) • shirokovReynolds n x)) T = 0
  rw [map_smul, Pi.smul_apply, hzero]
  simp

/-- A central element of the finite-stage `Cl(0,n)` is determined by its
scalar coordinate and, in odd dimension, its top-blade coordinate. -/
theorem shirokov_center_two_coordinate_expansion (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : x ∈ Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n))) :
    x = bladeRepr ℝ n x ∅ • cBlade ℝ n ∅ +
      if Odd n then
        bladeRepr ℝ n x (Finset.univ : Finset (Fin n)) •
          cBlade ℝ n (Finset.univ : Finset (Fin n))
      else 0 := by
  classical
  apply shirokov_blade_coordinates_injective
  ext T
  simp only [map_add, map_smul, shirokovBladeCoordinates_cBlade,
    Pi.smul_apply, Pi.single_apply]
  change bladeRepr ℝ n x T = _
  have hsupport (hEmpty : T ≠ ∅)
      (hTop : ¬ (Odd n ∧ T = (Finset.univ : Finset (Fin n)))) :
      bladeRepr ℝ n x T = 0 :=
    shirokov_center_coordinate_support n x hx T hEmpty hTop
  by_cases hEmpty : T = ∅
  · subst T
    by_cases hOdd : Odd n
    · have hnpos : 0 < n := hOdd.pos
      have hne : (Finset.univ : Finset (Fin n)) ≠ ∅ := by
        intro h
        have hmem : (⟨0, hnpos⟩ : Fin n) ∈
            (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
        rw [h] at hmem
        simpa using hmem
      simp [hOdd, hne]
    · simp [hOdd]
  · by_cases hOdd : Odd n
    · by_cases hTop : T = (Finset.univ : Finset (Fin n))
      · subst T
        have hne : (Finset.univ : Finset (Fin n)) ≠ ∅ := by
          intro h
          have hnpos : 0 < n := hOdd.pos
          have hmem : (⟨0, hnpos⟩ : Fin n) ∈
              (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
          rw [h] at hmem
          simpa using hmem
        simp [hOdd, hEmpty, hne]
      · have hcoord := hsupport hEmpty (by simp [hOdd, hTop])
        simp [hOdd, hEmpty, hTop, hcoord]
    · have hcoord := hsupport hEmpty (by simp [hOdd])
      simp [hOdd, hEmpty, hcoord]

/-- A central element of `Cl(0,n)` supported only in blade grade two is zero.
The scalar center coordinate and the odd-dimensional top coordinate cannot
occur in grade two. -/
theorem shirokov_center_grade_two_eq_zero (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hx : x ∈ Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (hgrade : ∀ T : Finset (Fin n), bladeRepr ℝ n x T ≠ 0 → T.card = 2) :
    x = 0 := by
  apply shirokov_blade_coordinates_injective
  ext T
  rw [map_zero]
  change bladeRepr ℝ n x T = 0
  have hcoord : bladeRepr ℝ n x T = 0 := by
    by_contra hne
    have hcard := hgrade T hne
    have hEmpty : T ≠ ∅ := by
      intro h
      subst T
      simp at hcard
    have hTop : ¬ (Odd n ∧ T = (Finset.univ : Finset (Fin n))) := by
      rintro ⟨hn, rfl⟩
      have hcard' : n = 2 := by simpa using hcard
      subst n
      norm_num at hn
    exact hne (shirokov_center_coordinate_support n x hx T hEmpty hTop)
  exact hcoord

/-- Conditional flatness consequence for Shirokov's compatibility equation
in the negative-definite finite-stage Clifford algebra. Generator compatibility
and commuting derivation directions centralize the curvature defect; the
explicit grade-two support hypothesis then forces that central defect to zero.
This isolates the remaining geometric obligation: deriving `hgrade` from the
paper's frame hypotheses. -/
theorem shirokov_clifford_compatibility_curvature_eq_zero_of_grade_two
    (n : ℕ)
    (K : DerivationLieLane ℝ
      (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (C : OneForm K) (x y : K.L) (hxy : ⁅x, y⁆ = 0)
    (hgen₁ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) x
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hgen₂ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) y
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hgrade : ∀ T : Finset (Fin n),
      bladeRepr ℝ n
        (K.operatorAction x (C y) - K.operatorAction y (C x) -
          algebraCommutator (C x) (C y)) T ≠ 0 → T.card = 2) :
    K.operatorAction x (C y) - K.operatorAction y (C x) -
      algebraCommutator (C x) (C y) = 0 := by
  apply shirokov_center_grade_two_eq_zero n
    (K.operatorAction x (C y) - K.operatorAction y (C x) -
      algebraCommutator (C x) (C y))
  · apply Subalgebra.mem_center_iff.mpr
    intro a
    have hcentral := shirokov_clifford_compatibility_curvature_central
      (Q := cliffordNegSqForm ℝ n) (K := K) (C := C) x y hxy hgen₁ hgen₂ a
    change
      (K.operatorAction x (C y) - K.operatorAction y (C x) -
        algebraCommutator (C x) (C y)) * a -
        a * (K.operatorAction x (C y) - K.operatorAction y (C x) -
          algebraCommutator (C x) (C y)) = 0 at hcentral
    exact (sub_eq_zero.mp hcentral).symm
  · exact hgrade

/-- If the connection values have a grade-two commutator, compatibility and
commuting directions force the curvature defect to vanish on `Cl(0,n)`. This
reduces the remaining geometric grade argument to bivector commutator closure. -/
theorem shirokov_curvature_flat_of_grade_two_connection_commutator
    (n : ℕ)
    (K : DerivationLieLane ℝ
      (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (C : OneForm K) (x y : K.L) (hxy : ⁅x, y⁆ = 0)
    (hgen₁ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) x
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hgen₂ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) y
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hbracket : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (algebraCommutator (C x) (C y)) T ≠ 0 → T.card = 2) :
    K.operatorAction x (C y) - K.operatorAction y (C x) -
      algebraCommutator (C x) (C y) = 0 := by
  have hcentral := shirokov_clifford_compatibility_curvature_central
    (Q := cliffordNegSqForm ℝ n) (K := K) (C := C) x y hxy hgen₁ hgen₂
  have hdef := shirokov_curvature_defect_eq_connection_commutator
    K C x y hgen₁ hgen₂
  have hcenter : algebraCommutator (C x) (C y) ∈
      Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
    rw [Subalgebra.mem_center_iff]
    intro a
    have h := hcentral a
    change algebraCommutator
      (K.operatorAction x (C y) - K.operatorAction y (C x) -
        algebraCommutator (C x) (C y)) a = 0 at h
    rw [hdef] at h
    exact (sub_eq_zero.mp h).symm
  have hzero := shirokov_center_grade_two_eq_zero n
    (algebraCommutator (C x) (C y)) hcenter hbracket
  rw [hdef]
  exact hzero

/-- Subtraction preserves ordered-blade grade-two support. This packages the
linear-coordinate step needed to obtain support of a curvature expression
from support of its individual terms. -/
theorem shirokov_grade_two_support_sub (n : ℕ)
    (a b : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (ha : ∀ T : Finset (Fin n), bladeRepr ℝ n a T ≠ 0 → T.card = 2)
    (hb : ∀ T : Finset (Fin n), bladeRepr ℝ n b T ≠ 0 → T.card = 2) :
    ∀ T : Finset (Fin n), bladeRepr ℝ n (a - b) T ≠ 0 → T.card = 2 := by
  intro T hT
  by_contra hcard
  have haT : bladeRepr ℝ n a T = 0 := by
    by_contra hne
    exact hcard (ha T hne)
  have hbT : bladeRepr ℝ n b T = 0 := by
    by_contra hne
    exact hcard (hb T hne)
  have hcoord : bladeRepr ℝ n (a - b) T =
      bladeRepr ℝ n a T - bladeRepr ℝ n b T := by
    simp [bladeRepr]
  exact hT (by rw [hcoord, haT, hbT]; simp)

/-- The curvature defect is grade two if its two differentiated connection
terms and the connection commutator are grade two. Together with compatibility,
this yields the conditional flatness result without a monolithic support premise.
The three support inputs remain the geometric obligations to derive. -/
theorem shirokov_clifford_compatibility_curvature_eq_zero_of_component_grade_two
    (n : ℕ)
    (K : DerivationLieLane ℝ
      (CliffordAlgebra (cliffordNegSqForm ℝ n)))
    (C : OneForm K) (x y : K.L) (hxy : ⁅x, y⁆ = 0)
    (hgen₁ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) x
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (hgen₂ : ∀ v : Fin n → ℝ,
      covariantDerivative K (-C) y
        (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) = 0)
    (h₁ : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (K.operatorAction x (C y)) T ≠ 0 → T.card = 2)
    (h₂ : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (K.operatorAction y (C x)) T ≠ 0 → T.card = 2)
    (hbracket : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (algebraCommutator (C x) (C y)) T ≠ 0 → T.card = 2) :
    K.operatorAction x (C y) - K.operatorAction y (C x) -
      algebraCommutator (C x) (C y) = 0 := by
  apply shirokov_clifford_compatibility_curvature_eq_zero_of_grade_two
    n K C x y hxy hgen₁ hgen₂
  have hsplit : K.operatorAction x (C y) - K.operatorAction y (C x) -
      algebraCommutator (C x) (C y) = K.operatorAction x (C y) -
        (K.operatorAction y (C x) + algebraCommutator (C x) (C y)) := by
    noncomm_ring
  rw [hsplit]
  apply shirokov_grade_two_support_sub n
    (K.operatorAction x (C y))
    (K.operatorAction y (C x) + algebraCommutator (C x) (C y)) h₁
  intro T hT
  by_contra hcard
  have h₂T : bladeRepr ℝ n (K.operatorAction y (C x)) T = 0 := by
    by_contra hne
    exact hcard (h₂ T hne)
  have hbrT : bladeRepr ℝ n (algebraCommutator (C x) (C y)) T = 0 := by
    by_contra hne
    exact hcard (hbracket T hne)
  have hcoord : bladeRepr ℝ n
      (K.operatorAction y (C x) + algebraCommutator (C x) (C y)) T =
        bladeRepr ℝ n (K.operatorAction y (C x)) T +
          bladeRepr ℝ n (algebraCommutator (C x) (C y)) T := by
    simp [bladeRepr]
  exact hT (by rw [hcoord, h₂T, hbrT]; simp)

/-- A grade-two Clifford coefficient is uniquely determined by its commutator
action on all Clifford vectors. The difference centralizes the generators,
hence the generated algebra, and the center/grade-two intersection is zero.
This is the uniqueness component of Shirokov's spin-valued commutator system
on the fixed negative-definite finite-stage carrier. -/
theorem shirokov_grade_two_unique_of_vector_commutators (n : ℕ)
    (A B : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hA : ∀ T : Finset (Fin n), bladeRepr ℝ n A T ≠ 0 → T.card = 2)
    (hB : ∀ T : Finset (Fin n), bladeRepr ℝ n B T ≠ 0 → T.card = 2)
    (hcomm : ∀ v : Fin n → ℝ,
      algebraCommutator A (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v) =
        algebraCommutator B (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v)) :
    A = B := by
  have hcentralVec : ∀ v : Fin n → ℝ,
      (A - B) * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v =
        CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * (A - B) := by
    intro v
    have h := hcomm v
    dsimp [algebraCommutator] at h
    calc
      (A - B) * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v =
          A * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v -
            B * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v := by rw [sub_mul]
      _ = CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * A -
          CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B := by
            calc
              _ = (A * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v -
                  CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * A) -
                    (B * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v -
                      CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B) +
                    (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * A -
                      CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B) := by abel
              _ = (B * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v -
                  CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B) -
                    (B * CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v -
                      CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B) +
                    (CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * A -
                      CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B) := by rw [h]
              _ = CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * A -
                    CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * B := by abel
      _ = CliffordAlgebra.ι (cliffordNegSqForm ℝ n) v * (A - B) := by rw [mul_sub]
  have hcenter : A - B ∈
      Subalgebra.center ℝ (CliffordAlgebra (cliffordNegSqForm ℝ n)) := by
    rw [Subalgebra.mem_center_iff]
    intro z
    have hz : z ∈ Algebra.adjoin ℝ
        (Set.range (CliffordAlgebra.ι (cliffordNegSqForm ℝ n))) := by
      rw [CliffordAlgebra.adjoin_range_ι (Q := cliffordNegSqForm ℝ n)]
      trivial
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
    · intro v hv
      rcases hv with ⟨v, rfl⟩
      exact (hcentralVec v).symm
    · intro r
      exact Algebra.commutes r (A - B)
    · intro x y hx hy hxc hyc
      rw [add_mul, mul_add, hxc, hyc]
    · intro x y hx hy hxc hyc
      calc
        (x * y) * (A - B) = x * (y * (A - B)) := by rw [mul_assoc]
        _ = x * ((A - B) * y) := by rw [hyc]
        _ = (x * (A - B)) * y := by rw [← mul_assoc]
        _ = ((A - B) * x) * y := by rw [hxc]
        _ = (A - B) * (x * y) := by rw [mul_assoc]
  have hgrade := shirokov_grade_two_support_sub n A B hA hB
  have hzero := shirokov_center_grade_two_eq_zero n (A - B) hcenter hgrade
  exact sub_eq_zero.mp hzero

/-- The standard-frame center projection annihilates elements supported only
in grade two, because the Reynolds average retains only scalar and odd-top
coordinates. -/
theorem shirokov_center_projection_eq_zero_of_grade_two (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hgrade : ∀ T : Finset (Fin n), bladeRepr ℝ n x T ≠ 0 → T.card = 2) :
    shirokovCenterProjection n x = 0 := by
  have hReynolds : shirokovReynolds n x = 0 := by
    rw [shirokov_reynolds_all_elements]
    apply Finset.sum_eq_zero
    intro T hT
    by_cases hzero : bladeRepr ℝ n x T = 0
    · simp [hzero]
    · have hcard := hgrade T hzero
      have hEmpty : T ≠ ∅ := by
        intro h
        subst T
        simp at hcard
      have hTop : ¬ (Odd n ∧ T = (Finset.univ : Finset (Fin n))) := by
        rintro ⟨hn, rfl⟩
        have hcard' : n = 2 := by simpa using hcard
        subst n
        norm_num at hn
      simp [hEmpty, hTop]
  simp [shirokovCenterProjection, hReynolds]

/-- Each inverse ordered blade is a unit; this is the standard finite frame
used by the Reynolds average. -/
noncomputable def shirokovInverseBladeUnit (n : ℕ) (S : Finset (Fin n)) :
    (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ :=
  Units.mk
    (((-1 : ℝ) ^ (S.card * (S.card + 1) / 2)) • cBlade ℝ n S)
    (cBlade ℝ n S)
    (shirokov_blade_inverse_formula n S).1
    (shirokov_blade_inverse_formula n S).2

@[simp] theorem shirokovInverseBladeUnit_val (n : ℕ) (S : Finset (Fin n)) :
    (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) =
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2)) • cBlade ℝ n S := rfl

@[simp] theorem shirokovInverseBladeUnit_inv_val (n : ℕ) (S : Finset (Fin n)) :
    (((shirokovInverseBladeUnit n S)⁻¹ :
      (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
        CliffordAlgebra (cliffordNegSqForm ℝ n)) = cBlade ℝ n S := rfl

/-- The unit-conjugation average over the standard inverse-blade frame is the
normalized center projection, with the expected frame cardinality. -/
theorem shirokov_standard_frame_average (n : ℕ)
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    (∑ S : Finset (Fin n),
      (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) * x *
        (((shirokovInverseBladeUnit n S)⁻¹ :
          (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
            CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      Fintype.card (Finset (Fin n)) • shirokovCenterProjection n x := by
  classical
  have hpowerset : (Finset.univ : Finset (Fin n)).powerset =
      (Finset.univ : Finset (Finset (Fin n))) := by
    ext S
    simp
  have hcard : Fintype.card (Finset (Fin n)) = 2 ^ n := by
    calc
      Fintype.card (Finset (Fin n)) =
          (Finset.univ : Finset (Finset (Fin n))).card := rfl
      _ = ((Finset.univ : Finset (Fin n)).powerset).card := by rw [hpowerset]
      _ = 2 ^ n := by simp [Finset.card_powerset]
  calc
    (∑ S : Finset (Fin n),
        (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) * x *
          (((shirokovInverseBladeUnit n S)⁻¹ :
            (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
              CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2) • cBlade ℝ n S) * x *
          cBlade ℝ n S := by
            change (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))),
              (shirokovInverseBladeUnit n S :
                CliffordAlgebra (cliffordNegSqForm ℝ n)) * x *
                (((shirokovInverseBladeUnit n S)⁻¹ :
                  (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
                    CliffordAlgebra (cliffordNegSqForm ℝ n))) = _
            rw [← hpowerset]
            simp only [shirokovInverseBladeUnit_val, shirokovInverseBladeUnit_inv_val]
    _ = shirokovReynolds n x := rfl
    _ = Fintype.card (Finset (Fin n)) • shirokovCenterProjection n x := by
      change shirokovReynolds n x =
        (Fintype.card (Finset (Fin n)) : ℝ) •
          (((2 ^ n : ℝ)⁻¹) • shirokovReynolds n x)
      rw [hcard, smul_smul]
      have hpow : ((2 ^ n : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
      have hcast : ((2 ^ n : ℕ) : ℝ) = (2 ^ n : ℝ) := by norm_cast
      rw [hcast]
      have hpowReal : (2 ^ n : ℝ) ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [mul_inv_cancel₀ hpowReal, one_smul]

/-- The Reynolds identity transports to any frame obtained by applying a real
Clifford algebra automorphism to the standard inverse-blade frame. -/
theorem shirokov_automorphism_frame_average (n : ℕ)
    (φ : CliffordAlgebra (cliffordNegSqForm ℝ n) ≃ₐ[ℝ]
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (x : CliffordAlgebra (cliffordNegSqForm ℝ n)) :
    (∑ S : Finset (Fin n),
      (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
        CliffordAlgebra (cliffordNegSqForm ℝ n)) * x *
        (↑((Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S))⁻¹) :
          CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      Fintype.card (Finset (Fin n)) •
        φ (shirokovCenterProjection n (φ.symm x)) := by
  calc
    _ = ∑ S : Finset (Fin n),
        φ ((shirokovInverseBladeUnit n S :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) *
          (φ.symm x) * cBlade ℝ n S) := by
            apply Finset.sum_congr rfl
            intro S hS
            change φ (shirokovInverseBladeUnit n S :
              CliffordAlgebra (cliffordNegSqForm ℝ n)) * x * φ (cBlade ℝ n S) =
              φ ((shirokovInverseBladeUnit n S :
                CliffordAlgebra (cliffordNegSqForm ℝ n)) *
                (φ.symm x) * cBlade ℝ n S)
            simp only [map_mul, AlgEquiv.apply_symm_apply]
    _ = φ (∑ S : Finset (Fin n),
        (shirokovInverseBladeUnit n S :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) *
          (φ.symm x) * cBlade ℝ n S) := by rw [map_sum]
    _ = φ (Fintype.card (Finset (Fin n)) •
        shirokovCenterProjection n (φ.symm x)) := by
          congr 1
          simpa only [shirokovInverseBladeUnit_inv_val] using
            shirokov_standard_frame_average n (φ.symm x)
    _ = Fintype.card (Finset (Fin n)) •
        φ (shirokovCenterProjection n (φ.symm x)) := by
          rw [map_nsmul]

/-- The isometry-induced Clifford automorphism sends each ordered coordinate
blade to the ordered product of the corresponding transformed frame vectors. -/
theorem shirokov_isometry_map_blade
    (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (S : Finset (Fin n)) :
    CliffordAlgebra.equivOfIsometry e (cBlade ℝ n S) =
      shirokovIsometryFrameBlade n e S := by
  simp only [cBlade, map_list_prod, List.map_map, Function.comp_def, cGen,
    CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
  rfl

/-- Inverse ordered blade unit associated to a quadratic-form isometry frame. -/
noncomputable def shirokovIsometryInverseBladeUnit (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (S : Finset (Fin n)) : (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ :=
  Units.map (CliffordAlgebra.equivOfIsometry e).toMonoidHom
    (shirokovInverseBladeUnit n S)

@[simp] theorem shirokovIsometryInverseBladeUnit_val (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (S : Finset (Fin n)) :
    (shirokovIsometryInverseBladeUnit n e S :
      CliffordAlgebra (cliffordNegSqForm ℝ n)) =
      ((-1 : ℝ) ^ (S.card * (S.card + 1) / 2)) •
        shirokovIsometryFrameBlade n e S := by
  change CliffordAlgebra.equivOfIsometry e
    (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) = _
  rw [shirokovInverseBladeUnit_val, map_smul,
    shirokov_isometry_map_blade]

@[simp] theorem shirokovIsometryInverseBladeUnit_inv_val (n : ℕ)
    (e : (cliffordNegSqForm ℝ n).IsometryEquiv (cliffordNegSqForm ℝ n))
    (S : Finset (Fin n)) :
    (((shirokovIsometryInverseBladeUnit n e S)⁻¹ :
      (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
        CliffordAlgebra (cliffordNegSqForm ℝ n)) =
      shirokovIsometryFrameBlade n e S := by
  change CliffordAlgebra.equivOfIsometry e
    ((((shirokovInverseBladeUnit n S)⁻¹ :
      (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
        CliffordAlgebra (cliffordNegSqForm ℝ n))) = _
  rw [shirokovInverseBladeUnit_inv_val, shirokov_isometry_map_blade]

/-- Theorem 2.2 for an automorphism-transported standard frame. The connection
coefficient is assumed grade two after pulling it back to the standard frame. -/
theorem shirokov_theorem_2_2_automorphism_frame_grade_two
    (n : ℕ)
    (φ : CliffordAlgebra (cliffordNegSqForm ℝ n) ≃ₐ[ℝ]
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (D : CliffordAlgebra (cliffordNegSqForm ℝ n) →
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (C : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hcompat : ∀ S : Finset (Fin n),
      D (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) =
        C * (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) -
          (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
            CliffordAlgebra (cliffordNegSqForm ℝ n)) * C)
    (hgrade : ∀ T : Finset (Fin n),
      bladeRepr ℝ n (φ.symm C) T ≠ 0 → T.card = 2) :
    (∑ S : Finset (Fin n),
      D (Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S) :
          CliffordAlgebra (cliffordNegSqForm ℝ n)) *
        (↑((Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S))⁻¹) :
          CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      Fintype.card (Finset (Fin n)) • C := by
  let transportedCenterProjection :
      CliffordAlgebra (cliffordNegSqForm ℝ n) →
        CliffordAlgebra (cliffordNegSqForm ℝ n) :=
    fun z => φ (shirokovCenterProjection n (φ.symm z))
  have haverage := shirokov_automorphism_frame_average n φ C
  have hzero : transportedCenterProjection C = 0 := by
    dsimp [transportedCenterProjection]
    rw [shirokov_center_projection_eq_zero_of_grade_two n (φ.symm C) hgrade]
    exact map_zero φ
  have hresult := shirokov_theorem_2_2_average_reduction
    (R := ℝ) (A := CliffordAlgebra (cliffordNegSqForm ℝ n))
    (ι := Finset (Fin n)) D C transportedCenterProjection
    (fun S => Units.map φ.toMonoidHom (shirokovInverseBladeUnit n S))
    hcompat (by simpa [transportedCenterProjection] using haverage)
  rw [hzero] at hresult
  simpa using hresult

/-- Theorem 2.2 for the standard inverse-blade frame: compatibility and
grade-two support remove the center-projection term from the average formula.
Transport to the paper's varying dual frame is a separate result. -/
theorem shirokov_theorem_2_2_standard_frame_grade_two
    (n : ℕ)
    (D : CliffordAlgebra (cliffordNegSqForm ℝ n) →
      CliffordAlgebra (cliffordNegSqForm ℝ n))
    (C : CliffordAlgebra (cliffordNegSqForm ℝ n))
    (hcompat : ∀ S : Finset (Fin n),
      D (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) =
        C * (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) -
          (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) * C)
    (hgrade : ∀ T : Finset (Fin n), bladeRepr ℝ n C T ≠ 0 → T.card = 2) :
    (∑ S : Finset (Fin n),
      D (shirokovInverseBladeUnit n S : CliffordAlgebra (cliffordNegSqForm ℝ n)) *
        (((shirokovInverseBladeUnit n S)⁻¹ :
          (CliffordAlgebra (cliffordNegSqForm ℝ n))ˣ) :
            CliffordAlgebra (cliffordNegSqForm ℝ n))) =
      Fintype.card (Finset (Fin n)) • C := by
  have haverage := shirokov_standard_frame_average n C
  have hzero := shirokov_center_projection_eq_zero_of_grade_two n C hgrade
  have hresult := shirokov_theorem_2_2_average_reduction
    (R := ℝ) (A := CliffordAlgebra (cliffordNegSqForm ℝ n))
    (ι := Finset (Fin n)) D C
    (shirokovCenterProjection n) (shirokovInverseBladeUnit n) hcompat haverage
  rw [hzero] at hresult
  simpa using hresult

private theorem endCommutator_double_scaled (A B : FormEnd V) (r s : ℝ) :
    endCommutator A (endCommutator (r • A) (s • B)) =
      s • (r • endCommutator A (endCommutator A B)) := by
  have hinner : endCommutator (r • A) (s • B) =
      (r * s) • endCommutator A B := by
    rw [endCommutator_smul_left, endCommutator_smul_right, smul_smul]
  calc
    endCommutator A (endCommutator (r • A) (s • B)) =
        (r * s) • endCommutator A (endCommutator A B) := by
          rw [hinner, endCommutator_smul_right]
    _ = s • (r • endCommutator A (endCommutator A B)) := by
          rw [smul_smul, mul_comm]

/-- Conditional Shirokov Theorem 5.2 on the literal exterior-form Clifford
action. For a pseudo-orthonormal frame, `B = C + σ c(e_i)` has the asserted
curvature and cubic current, provided the background is flat and the scaled
frame is covariantly constant. -/
theorem shirokov_clifford_vector_yang_mills
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (D : DerivationFamily (ι := ι) (A := FormEnd V))
    (C : ι → FormEnd V) (σ : ℝ)
    (hflat : ∀ i j,
      D.apply i (C j) - D.apply j (C i) - commutator (C i) (C j) = 0)
    (hparallel : ∀ i j,
      D.apply i (σ • cartanCliffordAction g (b j)) =
        commutator (C i) (σ • cartanCliffordAction g (b j))) :
    (∀ i j,
      fieldStrength D (fun k => C k + σ • cartanCliffordAction g (b k)) i j =
        -commutator (σ • cartanCliffordAction g (b i))
          (σ • cartanCliffordAction g (b j))) ∧
    (∀ j,
      yangMillsCurrent D (fun k => C k + σ • cartanCliffordAction g (b k))
        (fieldStrength D
          (fun k => C k + σ • cartanCliffordAction g (b k))) j =
        ((4 * (Fintype.card ι - 1 : ℕ) : ℝ) * σ ^ 3) •
          cartanCliffordAction g (b j)) := by
  constructor
  · intro i j
    exact fieldStrength_background_plus_parallel D C
      (fun k => σ • cartanCliffordAction g (b k)) hflat hparallel i j
  · intro j
    rw [yangMillsCurrent_background_plus_parallel D C
      (fun k => σ • cartanCliffordAction g (b k)) hflat hparallel j]
    simpa only [InfoGeometry.Canonical.ShirokovYangMillsTransfer.commutator,
      endCommutator] using
      scaled_orthonormal_frame_double_commutator_sum b g hg horth j σ

/-- Pseudo-Euclidean version of the conditional Clifford-vector theorem. The
raised-index current acts on the raised output generator `ε j • c(e_j)`. -/
theorem shirokov_pseudo_clifford_vector_yang_mills
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, g (b i) (b j) = if i = j then ε i else 0)
    (D : DerivationFamily (ι := ι) (A := FormEnd V))
    (C : ι → FormEnd V) (σ : ℝ)
    (hflat : ∀ i j,
      D.apply i (C j) - D.apply j (C i) - commutator (C i) (C j) = 0)
    (hparallel : ∀ i j,
      D.apply i (σ • cartanCliffordAction g (b j)) =
        commutator (C i) (σ • cartanCliffordAction g (b j))) :
    ∀ j,
      pseudoYangMillsCurrent D ε
        (fun k => C k + σ • cartanCliffordAction g (b k))
        (fieldStrength D
          (fun k => C k + σ • cartanCliffordAction g (b k))) j =
        ((4 * (Fintype.card ι - 1 : ℕ) : ℝ) * σ ^ 3) •
          (ε j • cartanCliffordAction g (b j)) := by
  intro j
  rw [pseudoYangMillsCurrent_background_plus_parallel D C
    (fun k => σ • cartanCliffordAction g (b k)) hflat hparallel ε j]
  have hscale (i : ι) := endCommutator_double_scaled
    (σ • cartanCliffordAction g (b i))
    (σ • cartanCliffordAction g (b j)) (ε i) (ε j)
  have hsum :
      (∑ i : ι,
        endCommutator (σ • cartanCliffordAction g (b i))
          (endCommutator (ε i • (σ • cartanCliffordAction g (b i)))
            (ε j • (σ • cartanCliffordAction g (b j)))) : FormEnd V) =
        ε j • ∑ i : ι, ε i •
          endCommutator (σ • cartanCliffordAction g (b i))
            (endCommutator (σ • cartanCliffordAction g (b i))
              (σ • cartanCliffordAction g (b j))) := by
    calc
      _ = ∑ i : ι, ε j • (ε i •
          endCommutator (σ • cartanCliffordAction g (b i))
            (endCommutator (σ • cartanCliffordAction g (b i))
              (σ • cartanCliffordAction g (b j)))) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hscale i
      _ = ε j • ∑ i : ι, ε i •
          endCommutator (σ • cartanCliffordAction g (b i))
            (endCommutator (σ • cartanCliffordAction g (b i))
              (σ • cartanCliffordAction g (b j))) := by rw [Finset.smul_sum]
  change ε j • ∑ i : ι, ε i •
      endCommutator (σ • cartanCliffordAction g (b i))
        (endCommutator (σ • cartanCliffordAction g (b i))
          (σ • cartanCliffordAction g (b j))) =
      ((4 * (Fintype.card ι - 1 : ℕ) : ℝ) * σ ^ 3) •
        (ε j • cartanCliffordAction g (b j))
  rw [← hsum]
  exact scaled_pseudoOrthonormal_frame_contracted_double_commutator
    b g hg ε hε horth j σ

/-- Conditional Theorem 5.3 transfer for a frame-derived spin connection.
The frame derivative identity supplies parallelness through the metric-skew
spin lift; flatness remains an explicit hypothesis. -/
theorem shirokov_pseudo_frame_derivative_yang_mills
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hgsymm : ∀ x y, g x y = g y x)
    (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, g (b i) (b j) = if i = j then ε i else 0)
    (d : ι → ι → V)
    (hcompat : ∀ μ i j,
      g (d μ i) (b j) + g (b i) (d μ j) = 0)
    (D : DerivationFamily (ι := ι) (A := FormEnd V)) (σ : ℝ)
    (hflat : ∀ i j,
      D.apply i (spinConnectionFromFrameDerivative b g hg d j) -
        D.apply j (spinConnectionFromFrameDerivative b g hg d i) -
          commutator (spinConnectionFromFrameDerivative b g hg d i)
            (spinConnectionFromFrameDerivative b g hg d j) = 0)
    (hframeDerivative : ∀ i j,
      D.apply i (σ • cartanCliffordAction g (b j)) =
        σ • cartanCliffordAction g (d i j)) :
    (∀ i j,
      fieldStrength D
        (fun k => spinConnectionFromFrameDerivative b g hg d k +
          σ • cartanCliffordAction g (b k)) i j =
        -commutator (σ • cartanCliffordAction g (b i))
          (σ • cartanCliffordAction g (b j))) ∧
    (∀ j,
      pseudoYangMillsCurrent D ε
        (fun k => spinConnectionFromFrameDerivative b g hg d k +
          σ • cartanCliffordAction g (b k))
        (fieldStrength D
          (fun k => spinConnectionFromFrameDerivative b g hg d k +
            σ • cartanCliffordAction g (b k))) j =
        ((4 * (Fintype.card ι - 1 : ℕ) : ℝ) * σ ^ 3) •
          (ε j • cartanCliffordAction g (b j))) := by
  let C := fun i => spinConnectionFromFrameDerivative b g hg d i
  have hskew (i : ι) :
      ∀ x y, g (frameDerivativeMap b (d i) x) y +
        g x (frameDerivativeMap b (d i) y) = 0 :=
    frameDerivativeMap_metricSkew b g (d i) (hcompat i)
  have hparallel : ∀ i j,
      D.apply i (σ • cartanCliffordAction g (b j)) =
        commutator (C i) (σ • cartanCliffordAction g (b j)) := by
    intro i j
    rw [hframeDerivative i j]
    change σ • cartanCliffordAction g (d i j) =
      endCommutator (metricSkewSpinLift b g hg
        (frameDerivativeMap b (d i)))
        (σ • cartanCliffordAction g (b j))
    rw [endCommutator_smul_right]
    rw [metricSkewSpinLift_comm_cartanCliffordAction b g hg hgsymm
      (frameDerivativeMap b (d i)) (hskew i) (b j)]
    rw [frameDerivativeMap_apply_basis]
  constructor
  · intro i j
    exact fieldStrength_background_plus_parallel D C
      (fun k => σ • cartanCliffordAction g (b k)) hflat hparallel i j
  · exact shirokov_pseudo_clifford_vector_yang_mills b g hgsymm ε hε horth
      D C σ hflat hparallel

end InfoGeometry.Canonical.ShirokovCliffordYangMills
