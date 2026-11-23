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
