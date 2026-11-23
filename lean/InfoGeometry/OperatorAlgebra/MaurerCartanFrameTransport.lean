/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Constructed Maurer--Cartan frames in a noncommutative algebra

The existing native Chevalley--Eilenberg differential is used unchanged.
For a genuine unit g, the form g^-1 D(g) is constructed and its flatness
is proved, including the bracket of derivation directions. Covariant
transport is an exact identity, not an assumed compatibility field.

Extensions formalized here:
1. Canonical `ℤ/2`-graded Peirce splitting `θ = ϖ + e` (`ϖ = evenGrade P ∘ θ`,
   `e = oddGrade P ∘ θ`, division-free over any associative ring) and its
   parity-automorphism (`α : A ≃ₐ[R] A`) counterpart, unconditionally deriving
   both `R_ϖ = -e ∧ e` and `de + ϖ ∧ e + e ∧ ϖ = 0` from flatness under
   grading-preserving derivations (`K.operatorAction x P = 0`).
2. `SolderingOneForm`, a data-carrying structure recording oddness, non-trivial
   `H`-equivariance via `frameTransport`, and nondegeneracy/bijectivity onto
   the Peirce-odd subspace, together with isotropy gauge covariance and a
   concrete non-abelian witness with three sharp separation theorems.
3. Algebraic separation (`gaugeForm_product_general_separation`) isolating the
   general nonabelian logarithmic-derivative identity
   `θ_L(g * h) = h⁻¹ * θ_L(g) * h + θ_L(h)` from external `ζ`/von Mangoldt
   arithmetic (`Canonical.MaurerCartanVonMangoldtBridge`,
   `Arithmetic.MaurerCartanVonMangoldtBridge`) and smooth principal/spin-curve
   geometry (`Canonical.SmoothPrincipalCartanBundleClosure`,
   `Erlangen.SmoothCartanGeometry`).
-/

namespace InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

section RingTransport

variable {A : Type*} [Ring A]

/-- Coordinate transport of an algebra element by the frame unit. -/
def frameTransport (g : Aˣ) (a : A) : A := (↑g⁻¹ : A) * a * ↑g

theorem frameTransport_mul (g : Aˣ) (a b : A) :
    frameTransport g (a * b) = frameTransport g a * frameTransport g b := by
  simp [frameTransport, mul_assoc]

theorem frameTransport_idempotent (g : Aˣ) (p : A) (hp : p * p = p) :
    frameTransport g p * frameTransport g p = frameTransport g p := by
  rw [← frameTransport_mul, hp]

theorem frameTransport_square_zero (g : Aˣ) (a : A) (ha : a * a = 0) :
    frameTransport g a * frameTransport g a = 0 := by
  rw [← frameTransport_mul, ha]
  simp [frameTransport]

end RingTransport

section DerivationLane

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- Every represented Leibniz operator kills the unit. -/
theorem action_one (x : K.L) : K.operatorAction x (1 : A) = 0 := by
  have h := K.operatorAction_leibniz x (1 : A) 1
  simp only [mul_one, one_mul] at h
  have hh : K.operatorAction x 1 + K.operatorAction x 1 = K.operatorAction x 1 + 0 := by
    simpa using h.symm
  exact add_left_cancel hh

/-- Inverse differentiation with the noncommutative order retained. -/
theorem action_inverse (x : K.L) (g : Aˣ) :
    K.operatorAction x (↑g⁻¹ : A) =
      -(↑g⁻¹ * K.operatorAction x (↑g : A) * ↑g⁻¹) := by
  have h : K.operatorAction x (↑g : A) * ↑g⁻¹ +
      (↑g : A) * K.operatorAction x (↑g⁻¹ : A) = 0 := by
    calc
      K.operatorAction x (↑g : A) * ↑g⁻¹ +
          (↑g : A) * K.operatorAction x (↑g⁻¹ : A) =
          K.operatorAction x ((↑g : A) * ↑g⁻¹) := by
            rw [K.operatorAction_leibniz]
      _ = 0 := by rw [Units.mul_inv]; exact action_one K x
  have hh := congrArg (fun z : A => (↑g⁻¹ : A) * z) h
  simp only [mul_add, ← mul_assoc, Units.inv_mul, one_mul, mul_zero] at hh
  calc K.operatorAction x (↑g⁻¹ : A) =
      (↑g⁻¹ * K.operatorAction x (↑g : A) * ↑g⁻¹ +
        K.operatorAction x (↑g⁻¹ : A)) -
          ↑g⁻¹ * K.operatorAction x (↑g : A) * ↑g⁻¹ := by abel
    _ = _ := by rw [hh, zero_sub]

/-- A genuine operator-valued one-form on the existing Lie lane. -/
def gaugeForm (g : Aˣ) : OneForm K where
  toFun x := (↑g⁻¹ : A) * K.operatorAction x (↑g : A)
  map_add' x y := by simp [mul_add]
  map_smul' c x := by simp

@[simp] theorem gaugeForm_apply (g : Aˣ) (x : K.L) :
    gaugeForm K g x = (↑g⁻¹ : A) * K.operatorAction x (↑g : A) := rfl

/-- The nonabelian product law for logarithmic derivatives. -/
theorem gaugeForm_product (g h : Aˣ) (x : K.L) :
    gaugeForm K (g * h) x =
      (↑h⁻¹ : A) * gaugeForm K g x * ↑h + gaugeForm K h x := by
  simp [gaugeForm, K.operatorAction_leibniz, mul_add, mul_assoc]

/-- Maurer--Cartan is derived, not added as a hypothesis. -/
theorem gaugeForm_flat (g : Aˣ) : connectionCurvature K (gaugeForm K g) = 0 := by
  apply Subtype.ext
  ext x y
  change connectionCurvature K (gaugeForm K g) x y = 0
  rw [connectionCurvature_apply]
  simp only [gaugeForm_apply, K.operatorAction_leibniz,
    action_inverse, K.operatorAction_commutator_apply]
  noncomm_ring

/-- The connection transforms actual operators, with no commuting approximation. -/
theorem covariant_frameTransport (g : Aˣ) (x : K.L) (a : A) :
    covariantDerivative K (gaugeForm K g) x (frameTransport g a) =
      frameTransport g (K.operatorAction x a) := by
  simp only [covariantDerivative, frameTransport, gaugeForm_apply]
  rw [K.operatorAction_leibniz x ((↑g⁻¹ : A) * a) (↑g : A)]
  rw [K.operatorAction_leibniz x (↑g⁻¹ : A) a]
  rw [action_inverse K x g]
  have hunit : (↑g : A) * (↑g⁻¹ : A) = 1 := Units.mul_inv g
  have hlast : (↑g⁻¹ : A) * a * ↑g *
      ((↑g⁻¹ : A) * K.operatorAction x (↑g : A)) =
      (↑g⁻¹ : A) * a * K.operatorAction x (↑g : A) := by
    calc
      (↑g⁻¹ : A) * a * ↑g *
          ((↑g⁻¹ : A) * K.operatorAction x (↑g : A)) =
          (↑g⁻¹ : A) * a * ((↑g : A) * (↑g⁻¹ : A)) *
            K.operatorAction x (↑g : A) := by noncomm_ring
      _ = (↑g⁻¹ : A) * a * K.operatorAction x (↑g : A) := by
        rw [hunit, mul_one]
  rw [hlast]
  noncomm_ring

/-- Constant charge or projector data become covariantly constant. -/
theorem covariant_frameTransport_zero (g : Aˣ) (x : K.L) (a : A)
    (ha : K.operatorAction x a = 0) :
    covariantDerivative K (gaugeForm K g) x (frameTransport g a) = 0 := by
  rw [covariant_frameTransport, ha]
  simp [frameTransport]

/-- Parallel frame generators have parallel ordered products. This is the
finite-product form of the compatibility propagation used in Shirokov's
Theorem 2.1; the derivation action remains noncommutative. -/
theorem covariant_frameTransport_list_product_zero (g : Aˣ) (x : K.L)
    (xs : List A) (hxs : ∀ a ∈ xs, K.operatorAction x a = 0) :
    covariantDerivative K (gaugeForm K g) x ((xs.map (frameTransport g)).prod) = 0 := by
  induction xs with
  | nil =>
      simp [covariantDerivative, action_one K x]
  | cons a xs ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [covariantDerivative_leibniz]
      rw [covariant_frameTransport_zero K g x a (hxs a (by simp))]
      rw [ih (fun b hb => hxs b (by simp [hb]))]
      simp

/-- Covariant parallelness propagates from a finite list of factors to their
ordered product. This is the product step in extending Clifford-frame
compatibility to the algebra generated by the frame. -/
theorem covariantDerivative_list_prod_zero
    (θ : OneForm K) (x : K.L) (xs : List A)
    (hxs : ∀ a ∈ xs, covariantDerivative K θ x a = 0) :
    covariantDerivative K θ x xs.prod = 0 := by
  induction xs with
  | nil =>
      simp [covariantDerivative, action_one K x]
  | cons a xs ih =>
      simp only [List.prod_cons]
      rw [covariantDerivative_leibniz]
      rw [hxs a (by simp)]
      rw [ih (fun b hb => hxs b (by simp [hb]))]
      simp

/-- A covariant derivation vanishing on a set vanishes on the algebra it
generates. This retains the coefficient algebra and its noncommutative product. -/
theorem covariantDerivative_zero_of_algebra_generators
    (θ : OneForm K) (x : K.L) (S : Set A)
    (hgen : ∀ a ∈ S, covariantDerivative K θ x a = 0)
    (hS : Algebra.adjoin R S = ⊤) :
    ∀ a : A, covariantDerivative K θ x a = 0 := by
  intro a
  have ha : a ∈ Algebra.adjoin R S := by rw [hS]; simp
  induction ha using Algebra.adjoin_induction with
  | mem z hz => exact hgen z hz
  | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      have hcentral : θ x * (r • (1 : A)) = (r • (1 : A)) * θ x := by
        rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      unfold covariantDerivative
      rw [map_smul, action_one K x, smul_zero, zero_add, hcentral]
      simp
  | add a b ha hb ih₁ ih₂ =>
      have hlin : covariantDerivative K θ x (a + b) =
          covariantDerivative K θ x a + covariantDerivative K θ x b := by
        simp only [covariantDerivative, map_add, mul_add, add_mul]
        abel
      rw [hlin, ih₁, ih₂]
      simp
  | mul a b ha hb ih₁ ih₂ =>
      rw [covariantDerivative_leibniz, ih₁, ih₂]
      simp

/-- In a Clifford algebra, covariant compatibility on the generating vectors
extends to every algebra element, by its universal algebra-generation theorem. -/
theorem covariantDerivative_zero_of_clifford_generators
    {M : Type*} [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M)
    (Kcl : DerivationLieLane R (CliffordAlgebra Q))
    (θ : OneForm Kcl) (x : Kcl.L)
    (hgen : ∀ v : M,
      covariantDerivative Kcl θ x (CliffordAlgebra.ι Q v) = 0) :
    ∀ a : CliffordAlgebra Q, covariantDerivative Kcl θ x a = 0 := by
  apply covariantDerivative_zero_of_algebra_generators Kcl θ x
    (Set.range (CliffordAlgebra.ι Q)) ?_ ?_
  · rintro _ ⟨v, rfl⟩
    exact hgen v
  · rw [CliffordAlgebra.adjoin_range_ι]

/-- Chevalley--Eilenberg curvature decomposition for a split one-form `θ = ϖ + e`:
when `θ` is flat and the odd covariant exterior derivative vanishes, horizontal curvature
satisfies Cartan's structural equation `R_ϖ(x, y) = -(e(x) e(y) - e(y) e(x))`. -/
theorem connectionCurvature_split_and_cartan_horizontal_from_flat
    (ϖ e : OneForm K) (x y : K.L) :
    (connectionCurvature K (ϖ + e) x y =
      (connectionCurvature K ϖ x y + (e x * e y - e y * e x)) +
        (exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
          (ϖ y * e x - e x * ϖ y))) ∧
    (connectionCurvature K (ϖ + e) x y = 0 →
      exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
        (ϖ y * e x - e x * ϖ y) = 0 →
      connectionCurvature K ϖ x y = -(e x * e y - e y * e x)) := by
  have hsplit :
      connectionCurvature K (ϖ + e) x y =
        (connectionCurvature K ϖ x y + (e x * e y - e y * e x)) +
          (exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
            (ϖ y * e x - e x * ϖ y)) := by
    simp only [connectionCurvature_apply, exteriorDerivativeOne_apply,
      LinearMap.add_apply, map_add]
    noncomm_ring
  refine ⟨hsplit, ?_⟩
  intro hflat hcov
  rw [hflat, hcov, add_zero] at hsplit
  exact eq_neg_of_add_eq_zero_left hsplit.symm

/-- For any Maurer--Cartan pure-gauge connection decomposed as `gaugeForm K g = ϖ + e`,
flatness (`gaugeForm_flat K g`) and vanishing odd covariant exterior derivative directly force
`R_ϖ(x, y) = -(e(x) e(y) - e(y) e(x))`. -/
theorem gaugeForm_split_cartan_horizontal_curvature
    (g : Aˣ) (ϖ e : OneForm K) (hge : gaugeForm K g = ϖ + e) (x y : K.L)
    (hcov : exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
      (ϖ y * e x - e x * ϖ y) = 0) :
    connectionCurvature K ϖ x y = -(e x * e y - e y * e x) := by
  have hflat : connectionCurvature K (ϖ + e) x y = 0 := by
    rw [← hge, gaugeForm_flat K g]
    rfl
  exact (connectionCurvature_split_and_cartan_horizontal_from_flat K ϖ e x y).2 hflat hcov

/-! ## F9: Canonical ℤ/2-graded Peirce and parity-automorphism splitting -/

section GradedSplitting

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- Peirce-even (`block-diagonal`) projection as an `R`-linear endomorphism of `A`. -/
def peirceEvenLinearMap (P : A) : A →ₗ[R] A where
  toFun a := evenGrade P a
  map_add' a b := evenGrade_add P a b
  map_smul' r a := by
    simp only [evenGrade, RingHom.id_apply, smul_add, mul_smul_comm, smul_mul_assoc]

/-- Peirce-odd (`off-diagonal`) projection as an `R`-linear endomorphism of `A`. -/
def peirceOddLinearMap (P : A) : A →ₗ[R] A where
  toFun a := oddGrade P a
  map_add' a b := oddGrade_add P a b
  map_smul' r a := by
    simp only [oddGrade, RingHom.id_apply, smul_add, mul_smul_comm, smul_mul_assoc]

/-- Even (`block-diagonal`) component `ϖ = evenGrade P ∘ θ` of a one-form `θ`. -/
def peirceEvenOneForm (P : A) (θ : OneForm K) : OneForm K :=
  (peirceEvenLinearMap (R := R) P).comp θ

/-- Odd (`off-diagonal`) component `e = oddGrade P ∘ θ` of a one-form `θ`. -/
def peirceOddOneForm (P : A) (θ : OneForm K) : OneForm K :=
  (peirceOddLinearMap (R := R) P).comp θ

@[simp] theorem peirceEvenOneForm_apply (P : A) (θ : OneForm K) (x : K.L) :
    peirceEvenOneForm K P θ x = evenGrade P (θ x) := rfl

@[simp] theorem peirceOddOneForm_apply (P : A) (θ : OneForm K) (x : K.L) :
    peirceOddOneForm K P θ x = oddGrade P (θ x) := rfl

theorem peirceEvenOneForm_add_peirceOddOneForm {P : A} (hP : P * P = P) (θ : OneForm K) :
    peirceEvenOneForm K P θ + peirceOddOneForm K P θ = θ := by
  ext x
  exact (grade_projection_laws hP (θ x)).2.2.2.2

theorem evenGrade_neg (P a : A) : evenGrade P (-a) = -evenGrade P a := by
  simp only [evenGrade, mul_neg, neg_mul, neg_add]

theorem evenGrade_sub (P a b : A) : evenGrade P (a - b) = evenGrade P a - evenGrade P b := by
  rw [sub_eq_add_neg, evenGrade_add, evenGrade_neg, ← sub_eq_add_neg]

theorem oddGrade_neg (P a : A) : oddGrade P (-a) = -oddGrade P a := by
  simp only [oddGrade, mul_neg, neg_mul, neg_add]

theorem oddGrade_sub (P a b : A) : oddGrade P (a - b) = oddGrade P a - oddGrade P b := by
  rw [sub_eq_add_neg, oddGrade_add, oddGrade_neg, ← sub_eq_add_neg]

theorem operatorAction_evenGrade_of_kill {P : A}
    (hKP : ∀ x : K.L, K.operatorAction x P = 0) (x : K.L) (a : A) :
    K.operatorAction x (evenGrade P a) = evenGrade P (K.operatorAction x a) := by
  have h1P : K.operatorAction x (1 - P) = 0 := by
    rw [map_sub, action_one K x, hKP x, sub_zero]
  simp only [evenGrade, map_add, K.operatorAction_leibniz,
    hKP x, h1P, zero_mul, mul_zero, zero_add, add_zero]

theorem operatorAction_oddGrade_of_kill {P : A}
    (hKP : ∀ x : K.L, K.operatorAction x P = 0) (x : K.L) (a : A) :
    K.operatorAction x (oddGrade P a) = oddGrade P (K.operatorAction x a) := by
  have h1P : K.operatorAction x (1 - P) = 0 := by
    rw [map_sub, action_one K x, hKP x, sub_zero]
  simp only [oddGrade, map_add, K.operatorAction_leibniz,
    hKP x, h1P, zero_mul, mul_zero, zero_add, add_zero]

/-- A Lie derivation lane preserves the Peirce grading iff every direction kills `P`. -/
theorem operatorAction_kill_iff_evenGrade {P : A} (hP : P * P = P) :
    (∀ x : K.L, K.operatorAction x P = 0) ↔
      (∀ (x : K.L) (a : A),
        K.operatorAction x (evenGrade P a) = evenGrade P (K.operatorAction x a)) := by
  constructor
  · exact fun hKP => operatorAction_evenGrade_of_kill K hKP
  · intro hcomm x
    have hPP : evenGrade P P = P := by
      peirce_nf hP
    have hleib : K.operatorAction x P =
        K.operatorAction x P * P + P * K.operatorAction x P := by
      conv_lhs => rw [← hP, K.operatorAction_leibniz]
    have hdiag1 : P * K.operatorAction x P * P = 0 := by
      have h := congrArg (fun z => P * z * P) hleib
      have h' : P * K.operatorAction x P * P =
          P * K.operatorAction x P * P + P * K.operatorAction x P * P := by
        calc P * K.operatorAction x P * P
            = P * (K.operatorAction x P * P + P * K.operatorAction x P) * P := h
          _ = P * K.operatorAction x P * (P * P) + (P * P) * K.operatorAction x P * P := by
                noncomm_ring
          _ = P * K.operatorAction x P * P + P * K.operatorAction x P * P := by rw [hP]
      exact add_left_cancel (by simpa only [add_zero] using h'.symm)
    have hdiag0 : (1 - P) * K.operatorAction x P * (1 - P) = 0 := by
      have hP1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
      have h1P : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
      calc (1 - P) * K.operatorAction x P * (1 - P)
          = (1 - P) * (K.operatorAction x P * P + P * K.operatorAction x P) * (1 - P) := by
              rw [← hleib]
        _ = (1 - P) * K.operatorAction x P * (P * (1 - P)) +
              ((1 - P) * P) * K.operatorAction x P * (1 - P) := by noncomm_ring
        _ = 0 := by rw [hP1, h1P]; simp
    have heven0 : evenGrade P (K.operatorAction x P) = 0 := by
      simp only [evenGrade, hdiag1, hdiag0, add_zero]
    rw [← hPP, hcomm x P, heven0]

/-- Unconditional Cartan structural equations for any flat `ϖ + e` with `ϖ` Peirce-even,
`e` Peirce-odd, and `K` preserving the grading (`K.operatorAction x P = 0`).
Zero `hcov` or `Invertible 2` hypothesis is assumed. -/
theorem peirce_split_cartan_equations_of_parts
    {P : A} (hP : P * P = P) (hKP : ∀ x : K.L, K.operatorAction x P = 0)
    (ϖ e : OneForm K)
    (hϖ : ∀ x : K.L, evenGrade P (ϖ x) = ϖ x)
    (he : ∀ x : K.L, oddGrade P (e x) = e x)
    (hflat : connectionCurvature K (ϖ + e) = 0) (x y : K.L) :
    connectionCurvature K ϖ x y = -(e x * e y - e y * e x) ∧
    exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
      (ϖ y * e x - e x * ϖ y) = 0 := by
  have hϖ_odd : ∀ z : K.L, oddGrade P (ϖ z) = 0 := by
    intro z
    rw [← hϖ z]
    exact (grade_projection_laws hP (ϖ z)).2.2.1
  have he_even : ∀ z : K.L, evenGrade P (e z) = 0 := by
    intro z
    rw [← he z]
    exact (grade_projection_laws hP (e z)).2.1
  let E : A := connectionCurvature K ϖ x y + (e x * e y - e y * e x)
  let O : A := exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
    (ϖ y * e x - e x * ϖ y)
  have hsplit : connectionCurvature K (ϖ + e) x y = E + O :=
    (connectionCurvature_split_and_cartan_horizontal_from_flat K ϖ e x y).1
  have hEO : E + O = 0 := by
    rw [← hsplit, hflat]
    rfl
  have hE_odd : oddGrade P E = 0 := by
    have hcurv : oddGrade P (connectionCurvature K ϖ x y) = 0 := by
      rw [connectionCurvature_apply, oddGrade_add, oddGrade_sub, oddGrade_sub,
        ← operatorAction_oddGrade_of_kill K hKP x (ϖ y),
        ← operatorAction_oddGrade_of_kill K hKP y (ϖ x),
        hϖ_odd y, hϖ_odd x, hϖ_odd ⁅x, y⁆, map_zero, map_zero, sub_zero, sub_zero,
        oddGrade_sub, oddGrade_mul hP, oddGrade_mul hP, hϖ_odd x, hϖ_odd y]
      simp only [mul_zero, zero_mul, add_zero, sub_self]
    have hee : oddGrade P (e x * e y - e y * e x) = 0 := by
      rw [oddGrade_sub, oddGrade_mul hP, oddGrade_mul hP, he_even x, he_even y]
      simp only [zero_mul, mul_zero, add_zero, sub_self]
    dsimp only [E]
    rw [oddGrade_add, hcurv, hee, add_zero]
  have hO_even : evenGrade P O = 0 := by
    have hde : evenGrade P (exteriorDerivativeOne K e x y) = 0 := by
      rw [exteriorDerivativeOne_apply, evenGrade_sub, evenGrade_sub,
        ← operatorAction_evenGrade_of_kill K hKP x (e y),
        ← operatorAction_evenGrade_of_kill K hKP y (e x),
        he_even y, he_even x, he_even ⁅x, y⁆, map_zero, map_zero, sub_zero, sub_zero]
    have hwe1 : evenGrade P (ϖ x * e y - e y * ϖ x) = 0 := by
      rw [evenGrade_sub, evenGrade_mul hP, evenGrade_mul hP, he_even y, hϖ_odd x]
      simp only [mul_zero, zero_mul, add_zero, sub_self]
    have hwe2 : evenGrade P (ϖ y * e x - e x * ϖ y) = 0 := by
      rw [evenGrade_sub, evenGrade_mul hP, evenGrade_mul hP, he_even x, hϖ_odd y]
      simp only [mul_zero, zero_mul, add_zero, sub_self]
    dsimp only [O]
    rw [evenGrade_sub, evenGrade_add, hde, hwe1, hwe2, add_zero, sub_zero]
  have hE_even : evenGrade P E = E := by
    have hsum := (grade_projection_laws hP E).2.2.2.2
    rw [hE_odd, add_zero] at hsum
    exact hsum
  have hO_odd : oddGrade P O = O := by
    have hsum := (grade_projection_laws hP O).2.2.2.2
    rw [hO_even, zero_add] at hsum
    exact hsum
  have hE_zero : E = 0 := by
    have h := congrArg (evenGrade P) hEO
    rw [evenGrade_add, hE_even, hO_even, add_zero,
      show evenGrade P (0 : A) = 0 by simp [evenGrade]] at h
    exact h
  have hO_zero : O = 0 := by
    have h := congrArg (oddGrade P) hEO
    rw [oddGrade_add, hE_odd, hO_odd, zero_add,
      show oddGrade P (0 : A) = 0 by simp [oddGrade]] at h
    exact h
  exact ⟨eq_neg_of_add_eq_zero_left hE_zero, hO_zero⟩

/-- **F9 Primary Theorem (Division-free Peirce splitting)**:
For any flat 1-form `θ` (`connectionCurvature K θ = 0`) and grading-preserving derivations
(`K.operatorAction x P = 0`), the canonical Peirce splitting `θ = ϖ + e` (`ϖ = evenGrade P ∘ θ`,
`e = oddGrade P ∘ θ`) unconditionally forces both `R_ϖ = -e ∧ e` and `de + ϖ ∧ e + e ∧ ϖ = 0`. -/
theorem graded_split_flat_cartan_equations
    {P : A} (hP : P * P = P) (hKP : ∀ x : K.L, K.operatorAction x P = 0)
    (θ : OneForm K) (hflat : connectionCurvature K θ = 0) (x y : K.L) :
    let ϖ := peirceEvenOneForm K P θ
    let e := peirceOddOneForm K P θ
    θ = ϖ + e ∧
    connectionCurvature K ϖ x y = -(e x * e y - e y * e x) ∧
    exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
      (ϖ y * e x - e x * ϖ y) = 0 := by
  let ϖ := peirceEvenOneForm K P θ
  let e := peirceOddOneForm K P θ
  have hsum : θ = ϖ + e := (peirceEvenOneForm_add_peirceOddOneForm K hP θ).symm
  have hflat' : connectionCurvature K (ϖ + e) = 0 := by
    rw [← hsum]
    exact hflat
  have hparts := peirce_split_cartan_equations_of_parts K hP hKP ϖ e
    (fun z => (grade_projection_laws hP (θ z)).1)
    (fun z => (grade_projection_laws hP (θ z)).2.2.2.1)
    hflat' x y
  exact ⟨hsum, hparts.1, hparts.2⟩

/-- Specialization of `graded_split_flat_cartan_equations` to any pure-gauge
Maurer--Cartan form `gaugeForm K g`. -/
theorem gaugeForm_graded_split_cartan_equations
    {P : A} (hP : P * P = P) (hKP : ∀ x : K.L, K.operatorAction x P = 0)
    (g : Aˣ) (x y : K.L) :
    let ϖ := peirceEvenOneForm K P (gaugeForm K g)
    let e := peirceOddOneForm K P (gaugeForm K g)
    gaugeForm K g = ϖ + e ∧
    connectionCurvature K ϖ x y = -(e x * e y - e y * e x) ∧
    exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
      (ϖ y * e x - e x * ϖ y) = 0 :=
  graded_split_flat_cartan_equations K hP hKP (gaugeForm K g) (gaugeForm_flat K g) x y

/-- Involutive parity `R`-algebra automorphism `a ↦ (2 * P - 1) * a * (2 * P - 1)`
induced by an idempotent `P : A`. -/
def peirceParityAlgEquiv (P : A) (hP : P * P = P) : A ≃ₐ[R] A :=
  let S : A := 2 * P - 1
  have hS2 : S * S = 1 := by
    calc S * S = 4 * (P * P) - 4 * P + 1 := by simp only [S]; noncomm_ring
      _ = 1 := by rw [hP]; noncomm_ring
  { toFun := fun a => S * a * S
    invFun := fun a => S * a * S
    left_inv := fun a => by
      calc S * (S * a * S) * S = (S * S) * a * (S * S) := by noncomm_ring
        _ = a := by rw [hS2, one_mul, mul_one]
    right_inv := fun a => by
      calc S * (S * a * S) * S = (S * S) * a * (S * S) := by noncomm_ring
        _ = a := by rw [hS2, one_mul, mul_one]
    map_mul' := fun a b => by
      calc S * (a * b) * S = S * a * 1 * b * S := by noncomm_ring
        _ = S * a * (S * S) * b * S := by rw [hS2]
        _ = (S * a * S) * (S * b * S) := by noncomm_ring
    map_add' := fun a b => by noncomm_ring
    commutes' := fun r => by
      calc S * algebraMap R A r * S = algebraMap R A r * (S * S) := by
            rw [← Algebra.commutes r S, mul_assoc]
        _ = algebraMap R A r := by rw [hS2, mul_one] }

theorem peirceParityAlgEquiv_involutive (P : A) (hP : P * P = P) (a : A) :
    peirceParityAlgEquiv (R := R) P hP (peirceParityAlgEquiv (R := R) P hP a) = a :=
  (peirceParityAlgEquiv (R := R) P hP).left_inv a

theorem peirceParityAlgEquiv_apply_eq (P : A) (hP : P * P = P) (a : A) :
    peirceParityAlgEquiv (R := R) P hP a = evenGrade P a - oddGrade P a := by
  change (2 * P - 1) * a * (2 * P - 1) = evenGrade P a - oddGrade P a
  have hS : (2 * P - 1 : A) = P - (1 - P) := by noncomm_ring
  rw [hS]
  peirce_nf hP

section ParityAutomorphism

variable [Invertible (2 : R)]

/-- Even projection `a ↦ ⅟2 • (a + α a)` for an involutive `R`-algebra automorphism `α`. -/
def parityEvenLinearMap (α : A ≃ₐ[R] A) : A →ₗ[R] A where
  toFun a := (⅟(2 : R)) • (a + α a)
  map_add' a b := by
    simp only [map_add, smul_add]
    abel
  map_smul' r a := by
    simp only [RingHom.id_apply, map_smul, ← smul_add, smul_comm (⅟(2 : R)) r]

/-- Odd projection `a ↦ ⅟2 • (a - α a)` for an involutive `R`-algebra automorphism `α`. -/
def parityOddLinearMap (α : A ≃ₐ[R] A) : A →ₗ[R] A where
  toFun a := (⅟(2 : R)) • (a - α a)
  map_add' a b := by
    calc (⅟(2 : R)) • ((a + b) - α (a + b))
        = (⅟(2 : R)) • ((a - α a) + (b - α b)) := by
          rw [map_add]
          congr 1
          abel
      _ = (⅟(2 : R)) • (a - α a) + (⅟(2 : R)) • (b - α b) := smul_add _ _ _
  map_smul' r a := by
    simp only [RingHom.id_apply, map_smul, ← smul_sub, smul_comm (⅟(2 : R)) r]

/-- Even component `ϖ = parityEvenLinearMap α ∘ θ` of a one-form `θ`. -/
def parityEvenOneForm (α : A ≃ₐ[R] A) (θ : OneForm K) : OneForm K :=
  (parityEvenLinearMap (R := R) (A := A) α).comp θ

/-- Odd component `e = parityOddLinearMap α ∘ θ` of a one-form `θ`. -/
def parityOddOneForm (α : A ≃ₐ[R] A) (θ : OneForm K) : OneForm K :=
  (parityOddLinearMap (R := R) (A := A) α).comp θ

@[simp] theorem parityEvenOneForm_apply (α : A ≃ₐ[R] A) (θ : OneForm K) (x : K.L) :
    parityEvenOneForm K α θ x = (⅟(2 : R)) • (θ x + α (θ x)) := rfl

@[simp] theorem parityOddOneForm_apply (α : A ≃ₐ[R] A) (θ : OneForm K) (x : K.L) :
    parityOddOneForm K α θ x = (⅟(2 : R)) • (θ x - α (θ x)) := rfl

theorem parityEvenOneForm_add_parityOddOneForm (α : A ≃ₐ[R] A) (θ : OneForm K) :
    parityEvenOneForm K α θ + parityOddOneForm K α θ = θ := by
  ext x
  simp only [LinearMap.add_apply, parityEvenOneForm_apply, parityOddOneForm_apply, ← smul_add]
  have hsum : (θ x + α (θ x)) + (θ x - α (θ x)) = (2 : R) • θ x := by
    rw [two_smul]
    abel
  rw [hsum, smul_smul, invOf_mul_self, one_smul]

theorem parityEvenOneForm_fixed (α : A ≃ₐ[R] A) (hα : ∀ a : A, α (α a) = a)
    (θ : OneForm K) (x : K.L) :
    α (parityEvenOneForm K α θ x) = parityEvenOneForm K α θ x := by
  simp only [parityEvenOneForm_apply, map_smul, map_add, hα, add_comm]

theorem parityOddOneForm_neg (α : A ≃ₐ[R] A) (hα : ∀ a : A, α (α a) = a)
    (θ : OneForm K) (x : K.L) :
    α (parityOddOneForm K α θ x) = -parityOddOneForm K α θ x := by
  simp only [parityOddOneForm_apply, map_smul, map_sub, hα, ← smul_neg, neg_sub]

/-- Parity-automorphism counterpart of `graded_split_flat_cartan_equations`:
if `α : A ≃ₐ[R] A` is involutive and commutes with `K.operatorAction`, then the
`+1`/`-1` eigenspace splitting `θ = ϖ + e` of any flat 1-form `θ` unconditionally
satisfies both `R_ϖ = -e ∧ e` and `de + ϖ ∧ e + e ∧ ϖ = 0`. -/
theorem parity_graded_split_flat_cartan_equations
    (α : A ≃ₐ[R] A) (hα : ∀ a : A, α (α a) = a)
    (hKα : ∀ (x : K.L) (a : A), α (K.operatorAction x a) = K.operatorAction x (α a))
    (θ : OneForm K) (hflat : connectionCurvature K θ = 0) (x y : K.L) :
    let ϖ := parityEvenOneForm K α θ
    let e := parityOddOneForm K α θ
    θ = ϖ + e ∧
    connectionCurvature K ϖ x y = -(e x * e y - e y * e x) ∧
    exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
      (ϖ y * e x - e x * ϖ y) = 0 := by
  let ϖ := parityEvenOneForm K α θ
  let e := parityOddOneForm K α θ
  have hsum : θ = ϖ + e := (parityEvenOneForm_add_parityOddOneForm K α θ).symm
  have hϖ_fix : ∀ z : K.L, α (ϖ z) = ϖ z := parityEvenOneForm_fixed K α hα θ
  have he_neg : ∀ z : K.L, α (e z) = -e z := parityOddOneForm_neg K α hα θ
  let E : A := connectionCurvature K ϖ x y + (e x * e y - e y * e x)
  let O : A := exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
    (ϖ y * e x - e x * ϖ y)
  have hsplit : connectionCurvature K (ϖ + e) x y = E + O :=
    (connectionCurvature_split_and_cartan_horizontal_from_flat K ϖ e x y).1
  have hEO : E + O = 0 := by
    rw [← hsplit, ← hsum, hflat]
    rfl
  have hE_fix : α E = E := by
    dsimp only [E]
    simp only [connectionCurvature_apply, map_add, map_sub, map_mul,
      hKα, hϖ_fix, he_neg, neg_mul, mul_neg, neg_neg]
  have hO_neg : α O = -O := by
    dsimp only [O]
    simp only [exteriorDerivativeOne_apply, map_add, map_sub, map_mul,
      hKα, hϖ_fix, he_neg, LinearMap.map_neg, neg_mul, mul_neg]
    abel
  have hdiff : E - O = 0 := by
    have h := congrArg α hEO
    rw [map_add, hE_fix, hO_neg, map_zero, ← sub_eq_add_neg] at h
    exact h
  have hE_zero : E = 0 := by
    have h2 : (2 : R) • E = 0 := by
      calc (2 : R) • E = E + E := two_smul R E
        _ = (E + O) + (E - O) := by abel
        _ = 0 := by rw [hEO, hdiff, add_zero]
    calc E = (⅟(2 : R) * (2 : R)) • E := by rw [invOf_mul_self, one_smul]
      _ = (⅟(2 : R)) • ((2 : R) • E) := by rw [smul_smul]
      _ = 0 := by rw [h2, smul_zero]
  have hO_zero : O = 0 := by
    calc O = (E + O) - E := by abel
      _ = 0 := by rw [hEO, hE_zero, sub_zero]
  exact ⟨hsum, eq_neg_of_add_eq_zero_left hE_zero, hO_zero⟩

/-- Compatibility between the parity-automorphism even splitting (`peirceParityAlgEquiv`)
and the division-free Peirce even splitting. -/
theorem parityEvenOneForm_peirceParityAlgEquiv {P : A} (hP : P * P = P) (θ : OneForm K) :
    parityEvenOneForm K (peirceParityAlgEquiv (R := R) P hP) θ = peirceEvenOneForm K P θ := by
  ext x
  simp only [parityEvenOneForm_apply, peirceEvenOneForm_apply,
    peirceParityAlgEquiv_apply_eq (R := R) P hP]
  have hsum := (grade_projection_laws hP (θ x)).2.2.2.2
  have hadd : θ x + (evenGrade P (θ x) - oddGrade P (θ x)) = (2 : R) • evenGrade P (θ x) := by
    have h0 : (evenGrade P (θ x) + oddGrade P (θ x)) +
        (evenGrade P (θ x) - oddGrade P (θ x)) = (2 : R) • evenGrade P (θ x) := by
      rw [two_smul]
      abel
    rwa [hsum] at h0
  rw [hadd, smul_smul, invOf_mul_self, one_smul]

/-- Compatibility between the parity-automorphism odd splitting (`peirceParityAlgEquiv`)
and the division-free Peirce odd splitting. -/
theorem parityOddOneForm_peirceParityAlgEquiv {P : A} (hP : P * P = P) (θ : OneForm K) :
    parityOddOneForm K (peirceParityAlgEquiv (R := R) P hP) θ = peirceOddOneForm K P θ := by
  ext x
  simp only [parityOddOneForm_apply, peirceOddOneForm_apply,
    peirceParityAlgEquiv_apply_eq (R := R) P hP]
  have hsum := (grade_projection_laws hP (θ x)).2.2.2.2
  have hsub : θ x - (evenGrade P (θ x) - oddGrade P (θ x)) = (2 : R) • oddGrade P (θ x) := by
    have h0 : (evenGrade P (θ x) + oddGrade P (θ x)) -
        (evenGrade P (θ x) - oddGrade P (θ x)) = (2 : R) • oddGrade P (θ x) := by
      rw [two_smul]
      abel
    rwa [hsum] at h0
  rw [hsub, smul_smul, invOf_mul_self, one_smul]

end ParityAutomorphism

end GradedSplitting

/-! ## F10: `SolderingOneForm`, isotropy gauge covariance, and nondegeneracy -/

section Soldering

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- Peirce-odd submodule `𝔪 = { a : A | oddGrade P a = a }`. -/
def peirceOddSubmodule (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    (P : A) : Submodule R A where
  carrier := { a : A | oddGrade P a = a }
  zero_mem' := by simp [oddGrade]
  add_mem' ha hb := by rw [Set.mem_ofPred_eq, oddGrade_add, ha, hb]
  smul_mem' r a ha := by
    change oddGrade P (r • a) = r • a
    have hsmul := (peirceOddLinearMap (R := R) P).map_smul r a
    change oddGrade P (r • a) = r • oddGrade P a at hsmul
    rw [hsmul, ha]

@[simp] theorem mem_peirceOddSubmodule {P a : A} :
    a ∈ peirceOddSubmodule R A P ↔ oddGrade P a = a := Iff.rfl

/-- Isotropy subgroup `H = { h : Aˣ | Commute (h : A) P }` preserving the Peirce grading. -/
def peirceIsotropySubgroup (A : Type*) [Ring A] (P : A) : Subgroup Aˣ where
  carrier := { h : Aˣ | Commute (h : A) P }
  mul_mem' {a b} ha hb := by
    change Commute ((a * b : Aˣ) : A) P
    rw [Units.val_mul]
    exact ha.mul_left hb
  one_mem' := Commute.one_left P
  inv_mem' {h} hh := by
    change (↑h⁻¹ : A) * P = P * (↑h⁻¹ : A)
    calc (↑h⁻¹ : A) * P
        = (↑h⁻¹ : A) * P * ((↑h : A) * (↑h⁻¹ : A)) := by rw [Units.mul_inv, mul_one]
      _ = (↑h⁻¹ : A) * (P * (↑h : A)) * (↑h⁻¹ : A) := by simp only [mul_assoc]
      _ = (↑h⁻¹ : A) * ((↑h : A) * P) * (↑h⁻¹ : A) := by rw [hh.eq]
      _ = ((↑h⁻¹ : A) * (↑h : A)) * P * (↑h⁻¹ : A) := by simp only [mul_assoc]
      _ = P * (↑h⁻¹ : A) := by rw [Units.inv_mul, one_mul]

@[simp] theorem mem_peirceIsotropySubgroup {P : A} {h : Aˣ} :
    h ∈ peirceIsotropySubgroup A P ↔ Commute (h : A) P := Iff.rfl

theorem commute_inv_of_commute {h : Aˣ} {P : A} (hh : Commute (h : A) P) :
    Commute (↑h⁻¹ : A) P :=
  (peirceIsotropySubgroup A P).inv_mem hh

theorem frameTransport_evenGrade {h : Aˣ} {P : A} (hh : Commute (h : A) P) (a : A) :
    frameTransport h (evenGrade P a) = evenGrade P (frameTransport h a) := by
  have hinv := (commute_inv_of_commute hh).eq
  have h1P : (↑h : A) * (1 - P) = (1 - P) * (↑h : A) := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hh.eq]
  have hinv1P : (↑h⁻¹ : A) * (1 - P) = (1 - P) * (↑h⁻¹ : A) := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hinv]
  simp only [frameTransport, evenGrade, mul_add, add_mul]
  congr 1
  · calc (↑h⁻¹ : A) * (P * a * P) * (↑h : A)
        = ((↑h⁻¹ : A) * P) * a * (P * (↑h : A)) := by simp only [mul_assoc]
      _ = (P * (↑h⁻¹ : A)) * a * ((↑h : A) * P) := by rw [hinv, hh.eq]
      _ = P * ((↑h⁻¹ : A) * a * (↑h : A)) * P := by simp only [mul_assoc]
  · calc (↑h⁻¹ : A) * ((1 - P) * a * (1 - P)) * (↑h : A)
        = ((↑h⁻¹ : A) * (1 - P)) * a * ((1 - P) * (↑h : A)) := by simp only [mul_assoc]
      _ = ((1 - P) * (↑h⁻¹ : A)) * a * ((↑h : A) * (1 - P)) := by rw [hinv1P, h1P]
      _ = (1 - P) * ((↑h⁻¹ : A) * a * (↑h : A)) * (1 - P) := by simp only [mul_assoc]

theorem frameTransport_oddGrade {h : Aˣ} {P : A} (hh : Commute (h : A) P) (a : A) :
    frameTransport h (oddGrade P a) = oddGrade P (frameTransport h a) := by
  have hinv := (commute_inv_of_commute hh).eq
  have h1P : (↑h : A) * (1 - P) = (1 - P) * (↑h : A) := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hh.eq]
  have hinv1P : (↑h⁻¹ : A) * (1 - P) = (1 - P) * (↑h⁻¹ : A) := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hinv]
  simp only [frameTransport, oddGrade, mul_add, add_mul]
  congr 1
  · calc (↑h⁻¹ : A) * (P * a * (1 - P)) * (↑h : A)
        = ((↑h⁻¹ : A) * P) * a * ((1 - P) * (↑h : A)) := by simp only [mul_assoc]
      _ = (P * (↑h⁻¹ : A)) * a * ((↑h : A) * (1 - P)) := by rw [hinv, h1P]
      _ = P * ((↑h⁻¹ : A) * a * (↑h : A)) * (1 - P) := by simp only [mul_assoc]
  · calc (↑h⁻¹ : A) * ((1 - P) * a * P) * (↑h : A)
        = ((↑h⁻¹ : A) * (1 - P)) * a * (P * (↑h : A)) := by simp only [mul_assoc]
      _ = ((1 - P) * (↑h⁻¹ : A)) * a * ((↑h : A) * P) := by rw [hinv1P, hh.eq]
      _ = (1 - P) * ((↑h⁻¹ : A) * a * (↑h : A)) * P := by simp only [mul_assoc]

/-- Under grading-preserving derivations, any pure-gauge form of an isotropy unit
`h ∈ peirceIsotropySubgroup A P` is purely Peirce-even. -/
theorem gaugeForm_mem_even_of_isotropy
    {P : A} (hP : P * P = P) (hKP : ∀ x : K.L, K.operatorAction x P = 0)
    {h : Aˣ} (hh : h ∈ peirceIsotropySubgroup A P) (x : K.L) :
    oddGrade P (gaugeForm K h x) = 0 ∧ evenGrade P (gaugeForm K h x) = gaugeForm K h x := by
  have hcomm_deriv : K.operatorAction x (h : A) * P = P * K.operatorAction x (h : A) := by
    have hl := K.operatorAction_leibniz x (h : A) P
    have hr := K.operatorAction_leibniz x P (h : A)
    rw [hh.eq] at hl
    rw [hl, hKP x, mul_zero, zero_mul, add_zero, zero_add] at hr
    exact hr
  have hcomm_gauge : gaugeForm K h x * P = P * gaugeForm K h x := by
    have hinv := (commute_inv_of_commute hh).eq
    simp only [gaugeForm_apply]
    calc (↑h⁻¹ : A) * K.operatorAction x (↑h : A) * P
        = (↑h⁻¹ : A) * (K.operatorAction x (↑h : A) * P) := by simp only [mul_assoc]
      _ = (↑h⁻¹ : A) * (P * K.operatorAction x (↑h : A)) := by rw [hcomm_deriv]
      _ = ((↑h⁻¹ : A) * P) * K.operatorAction x (↑h : A) := by simp only [mul_assoc]
      _ = (P * (↑h⁻¹ : A)) * K.operatorAction x (↑h : A) := by rw [hinv]
      _ = P * ((↑h⁻¹ : A) * K.operatorAction x (↑h : A)) := by simp only [mul_assoc]
  have hodd : oddGrade P (gaugeForm K h x) = 0 := by
    have h1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
    have h2 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
    calc oddGrade P (gaugeForm K h x)
        = P * gaugeForm K h x * (1 - P) + (1 - P) * gaugeForm K h x * P := rfl
      _ = (P * gaugeForm K h x) * (1 - P) + (1 - P) * (gaugeForm K h x * P) := by
            simp only [mul_assoc]
      _ = (gaugeForm K h x * P) * (1 - P) + (1 - P) * (P * gaugeForm K h x) := by
            rw [hcomm_gauge]
      _ = gaugeForm K h x * (P * (1 - P)) + ((1 - P) * P) * gaugeForm K h x := by
            simp only [mul_assoc]
      _ = 0 := by rw [h1, h2, mul_zero, zero_mul, add_zero]
  have heven : evenGrade P (gaugeForm K h x) = gaugeForm K h x := by
    have hsum := (grade_projection_laws hP (gaugeForm K h x)).2.2.2.2
    rw [hodd, add_zero] at hsum
    exact hsum
  exact ⟨hodd, heven⟩

/-- Under a right gauge change `g ↦ g * h` by `h ∈ peirceIsotropySubgroup A P`,
the Peirce-even part `ϖ` transforms as an inhomogeneous connection while the
Peirce-odd part `e` transforms homogeneously (tensorially) as a soldering form. -/
theorem peirceSplit_gaugeForm_isotropy_transform
    {P : A} (hP : P * P = P) (hKP : ∀ x : K.L, K.operatorAction x P = 0)
    (g : Aˣ) {h : Aˣ} (hh : h ∈ peirceIsotropySubgroup A P) (x : K.L) :
    peirceEvenOneForm K P (gaugeForm K (g * h)) x =
      frameTransport h (peirceEvenOneForm K P (gaugeForm K g) x) + gaugeForm K h x ∧
    peirceOddOneForm K P (gaugeForm K (g * h)) x =
      frameTransport h (peirceOddOneForm K P (gaugeForm K g) x) := by
  have hg := gaugeForm_mem_even_of_isotropy K hP hKP hh x
  have hprod : gaugeForm K (g * h) x =
      frameTransport h (gaugeForm K g x) + gaugeForm K h x :=
    gaugeForm_product K g h x
  refine ⟨?_, ?_⟩
  · rw [peirceEvenOneForm_apply, hprod, evenGrade_add,
      ← frameTransport_evenGrade hh (gaugeForm K g x), hg.2]
    rfl
  · rw [peirceOddOneForm_apply, hprod, oddGrade_add,
      ← frameTransport_oddGrade hh (gaugeForm K g x), hg.1, add_zero]
    rfl

/-- Data-carrying algebraic soldering one-form: a `OneForm K` taking values in the
Peirce-odd subspace, equivariant with respect to a right `H`-action on `K.L` and
`frameTransport` on `A`, and inducing a linear isomorphism onto `peirceOddSubmodule R A P`. -/
structure SolderingOneForm {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (P : A) (H : Subgroup Aˣ) where
  toOneForm : OneForm K
  odd : ∀ x : K.L, oddGrade P (toOneForm x) = toOneForm x
  baseRightAct : H → K.L →ₗ[R] K.L
  baseRightAct_one : ∀ x : K.L, baseRightAct 1 x = x
  baseRightAct_mul : ∀ (h₁ h₂ : H) (x : K.L),
    baseRightAct (h₁ * h₂) x = baseRightAct h₂ (baseRightAct h₁ x)
  equivariant : ∀ (h : H) (x : K.L),
    toOneForm (baseRightAct h x) = frameTransport (h.1 : Aˣ) (toOneForm x)
  injective : Function.Injective toOneForm
  surjective_odd : ∀ m : A, oddGrade P m = m → ∃ x : K.L, toOneForm x = m

namespace SolderingOneForm

theorem ker_eq_bot {K : DerivationLieLane R A} {P : A} {H : Subgroup Aˣ}
    (S : SolderingOneForm K P H) :
    LinearMap.ker S.toOneForm = ⊥ :=
  LinearMap.ker_eq_bot.mpr S.injective

theorem range_eq_odd {K : DerivationLieLane R A} {P : A} {H : Subgroup Aˣ}
    (S : SolderingOneForm K P H) :
    LinearMap.range S.toOneForm = peirceOddSubmodule R A P := by
  ext m
  simp only [LinearMap.mem_range, mem_peirceOddSubmodule]
  constructor
  · rintro ⟨x, rfl⟩
    exact S.odd x
  · intro hm
    exact S.surjective_odd m hm

/-- The frame linear equivalence `K.L ≃ₗ[R] peirceOddSubmodule R A P` induced by
a `SolderingOneForm`. -/
noncomputable def frameEquiv {K : DerivationLieLane R A} {P : A} {H : Subgroup Aˣ}
    (S : SolderingOneForm K P H) :
    K.L ≃ₗ[R] peirceOddSubmodule R A P :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (peirceOddSubmodule R A P) S.toOneForm S.odd)
    ⟨fun _ _ h => S.injective (congrArg Subtype.val h),
     fun ⟨m, hm⟩ => let ⟨x, hx⟩ := S.surjective_odd m hm; ⟨x, Subtype.ext hx⟩⟩

@[simp] theorem frameEquiv_apply {K : DerivationLieLane R A} {P : A} {H : Subgroup Aˣ}
    (S : SolderingOneForm K P H) (x : K.L) :
    ((S.frameEquiv x : peirceOddSubmodule R A P) : A) = S.toOneForm x := rfl

end SolderingOneForm

end Soldering

/-! ## F12: Logarithmic derivative algebraic separation -/

section LogarithmicDerivativeSeparation

/-- **F12 General Algebraic Separation**:
Over an arbitrary associative `R`-algebra `A` with derivation Lie lane `K`, the left
logarithmic derivative `gaugeForm K g x = g⁻¹ * K.operatorAction x g` satisfies:
1. the nonabelian cocycle product law `gaugeForm_product` (with `frameTransport h`);
2. unit normalization `gaugeForm K 1 x = 0`;
3. exact inverse law `gaugeForm K g⁻¹ x = -(g * gaugeForm K g x * g⁻¹)`;
4. unconditional flatness `connectionCurvature K (gaugeForm K (g * h)) = 0`;
5. explicit noncommutativity defect `gaugeForm K (g * h) x - (gaugeForm K g x + gaugeForm K h x) = frameTransport h (gaugeForm K g x) - gaugeForm K g x`;
6. collapse to additivity when `↑h` commutes with `gaugeForm K g x` (the special
   commutative regime of Dirichlet series `ArithmeticFunction ℝ` in
   `MaurerCartanVonMangoldtBridge`).

No `ArithmeticFunction`, `VonMangoldt`, `riemannZeta`, or smooth spin-curve manifold
hypotheses are imported or assumed. -/
theorem gaugeForm_product_general_separation (g h : Aˣ) (x : K.L) :
    gaugeForm K (g * h) x = frameTransport h (gaugeForm K g x) + gaugeForm K h x ∧
    gaugeForm K (1 : Aˣ) x = 0 ∧
    gaugeForm K g⁻¹ x = -((↑g : A) * gaugeForm K g x * (↑g⁻¹ : A)) ∧
    connectionCurvature K (gaugeForm K (g * h)) = 0 ∧
    gaugeForm K (g * h) x - (gaugeForm K g x + gaugeForm K h x) =
      frameTransport h (gaugeForm K g x) - gaugeForm K g x ∧
    (Commute (↑h : A) (gaugeForm K g x) →
      gaugeForm K (g * h) x = gaugeForm K g x + gaugeForm K h x) := by
  have hprod := gaugeForm_product K g h x
  have hone : gaugeForm K (1 : Aˣ) x = 0 := by
    simp only [gaugeForm_apply, Units.val_one, inv_one, one_mul, action_one K x]
  have hinv : gaugeForm K g⁻¹ x = -((↑g : A) * gaugeForm K g x * (↑g⁻¹ : A)) := by
    simp only [gaugeForm_apply, inv_inv, action_inverse K x g]
    calc (↑g : A) * -((↑g⁻¹ : A) * K.operatorAction x (↑g : A) * (↑g⁻¹ : A)) =
          -((↑g : A) * ((↑g⁻¹ : A) * K.operatorAction x (↑g : A)) * (↑g⁻¹ : A)) := by
          noncomm_ring
      _ = -((↑g : A) * (↑g⁻¹ * K.operatorAction x (↑g : A)) * (↑g⁻¹ : A)) := rfl
  have hflat : connectionCurvature K (gaugeForm K (g * h)) = 0 := gaugeForm_flat K (g * h)
  have hdef : gaugeForm K (g * h) x - (gaugeForm K g x + gaugeForm K h x) =
      frameTransport h (gaugeForm K g x) - gaugeForm K g x := by
    rw [hprod]
    change (frameTransport h (gaugeForm K g x) + gaugeForm K h x) -
        (gaugeForm K g x + gaugeForm K h x) =
      frameTransport h (gaugeForm K g x) - gaugeForm K g x
    abel
  refine ⟨hprod, hone, hinv, hflat, hdef, ?_⟩
  intro hcomm
  rw [hprod]
  have htr : frameTransport h (gaugeForm K g x) = gaugeForm K g x := by
    unfold frameTransport
    rw [mul_assoc, ← hcomm.eq, ← mul_assoc, Units.inv_mul, one_mul]
  change frameTransport h (gaugeForm K g x) + gaugeForm K h x = gaugeForm K g x + gaugeForm K h x
  rw [htr]

end LogarithmicDerivativeSeparation

end DerivationLane

/-! ## Concrete non-abelian witnesses and separation theorems (F10, F12, Trap T16) -/

namespace Witnesses

open InfoGeometry.OperatorAlgebra.PeirceSpine

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev PairMat2 := Mat2 × Mat2

def mat2E01 : Mat2 := !![0, 1; 0, 0]
def mat2E10 : Mat2 := !![0, 0; 1, 0]

/-- Explicit `Fin 2` real matrix non-commutativity witness (Trap T16). -/
theorem mat2_noncommutative : mat2E01 * mat2E10 ≠ mat2E10 * mat2E01 := by
  intro h
  have hh := congrArg (fun M : Mat2 => M 0 0) h
  norm_num [mat2E01, mat2E10, Matrix.mul_apply, Fin.sum_univ_two] at hh

/-- Two-dimensional non-abelian upper-triangular affine Lie algebra `⁅⟨u₁, v₁⟩, ⟨u₂, v₂⟩⁆ = ⟨0, u₁ v₂ - u₂ v₁⟩`. -/
@[ext] structure UpperAff2 where
  u : ℝ
  v : ℝ

def witnessUpperAff2Zero : UpperAff2 := ⟨0, 0⟩

instance : Zero UpperAff2 := ⟨⟨0, 0⟩⟩
instance : Add UpperAff2 := ⟨fun x y => ⟨x.u + y.u, x.v + y.v⟩⟩
instance : Neg UpperAff2 := ⟨fun x => ⟨-x.u, -x.v⟩⟩
instance : Sub UpperAff2 := ⟨fun x y => ⟨x.u - y.u, x.v - y.v⟩⟩
instance : SMul ℝ UpperAff2 := ⟨fun c x => ⟨c * x.u, c * x.v⟩⟩

private theorem upperAff2_add_assoc (x y z : UpperAff2) : x + y + z = x + (y + z) := by
  ext <;> exact add_assoc _ _ _

private theorem upperAff2_zero_add (x : UpperAff2) : 0 + x = x := by
  ext <;> exact zero_add _

private theorem upperAff2_add_zero (x : UpperAff2) : x + 0 = x := by
  ext <;> exact add_zero _

private theorem upperAff2_neg_add_cancel (x : UpperAff2) : -x + x = 0 := by
  ext <;> exact neg_add_cancel _

private theorem upperAff2_add_comm (x y : UpperAff2) : x + y = y + x := by
  ext <;> exact add_comm _ _

instance : AddCommGroup UpperAff2 where
  add_assoc := upperAff2_add_assoc
  zero_add := upperAff2_zero_add
  add_zero := upperAff2_add_zero
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := upperAff2_neg_add_cancel
  add_comm := upperAff2_add_comm

instance : Module ℝ UpperAff2 where
  one_smul x := by ext <;> exact one_mul _
  mul_smul c₁ c₂ x := by ext <;> exact mul_assoc _ _ _
  smul_zero c := by ext <;> exact mul_zero _
  smul_add c x y := by ext <;> exact mul_add _ _ _
  add_smul c₁ c₂ x := by ext <;> exact add_mul _ _ _
  zero_smul x := by ext <;> exact zero_mul _

def upperMat (x : UpperAff2) : Mat2 := !![x.u, x.v; 0, 0]

private theorem upperMat_injective : Function.Injective upperMat := by
  intro x y h
  have hu : x.u = y.u := congrArg (fun M : Mat2 => M 0 0) h
  have hv : x.v = y.v := congrArg (fun M : Mat2 => M 0 1) h
  exact UpperAff2.ext hu hv

instance : Bracket UpperAff2 UpperAff2 :=
  ⟨fun x y => ⟨0, x.u * y.v - y.u * x.v⟩⟩

private theorem upperMat_bracket (x y : UpperAff2) :
    upperMat ⁅x, y⁆ = upperMat x * upperMat y - upperMat y * upperMat x := by
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    (dsimp [upperMat, Bracket.bracket]; ring)

@[simp] private theorem upperAff2_zero_u : (0 : UpperAff2).u = 0 := rfl
@[simp] private theorem upperAff2_zero_v : (0 : UpperAff2).v = 0 := rfl
@[simp] private theorem upperAff2_add_u (x y : UpperAff2) : (x + y).u = x.u + y.u := rfl
@[simp] private theorem upperAff2_add_v (x y : UpperAff2) : (x + y).v = x.v + y.v := rfl
@[simp] private theorem upperAff2_smul_u (c : ℝ) (x : UpperAff2) : (c • x).u = c * x.u := rfl
@[simp] private theorem upperAff2_smul_v (c : ℝ) (x : UpperAff2) : (c • x).v = c * x.v := rfl
@[simp] private theorem upperAff2_bracket_u (x y : UpperAff2) : ⁅x, y⁆.u = 0 := rfl
@[simp] private theorem upperAff2_bracket_v (x y : UpperAff2) :
    ⁅x, y⁆.v = x.u * y.v - y.u * x.v := rfl

private theorem upperAff2_add_lie (x y z : UpperAff2) : ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := by
  ext <;> (simp; try ring)

private theorem upperAff2_lie_add (x y z : UpperAff2) : ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := by
  ext <;> (simp; try ring)

private theorem upperAff2_lie_self (x : UpperAff2) : ⁅x, x⁆ = 0 := by
  ext <;> simp

private theorem upperAff2_leibniz_lie (x y z : UpperAff2) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  ext <;> (simp; try ring)

instance : LieRing UpperAff2 where
  add_lie := upperAff2_add_lie
  lie_add := upperAff2_lie_add
  lie_self := upperAff2_lie_self
  leibniz_lie := upperAff2_leibniz_lie

instance : LieAlgebra ℝ UpperAff2 where
  lie_smul c x y := by
    ext <;> (simp; try ring)

private theorem upperAff2_nonabelian :
    ⁅(⟨1, 0⟩ : UpperAff2), (⟨0, 1⟩ : UpperAff2)⁆ ≠ 0 := by
  intro h
  have hv := congrArg UpperAff2.v h
  simp only [upperAff2_bracket_v, upperAff2_zero_v] at hv
  norm_num at hv

private def witnessActFun (x : UpperAff2) : NonAssocDerivation.derivations ℝ PairMat2 :=
  ⟨{ toFun := fun p => (0, upperMat x * p.2 - p.2 * upperMat x)
     map_add' := fun p q => by
       ext1
       · simp
       · simp only [Prod.snd_add, mul_add, add_mul]; abel
     map_smul' := fun c p => by
       ext1
       · simp
       · change upperMat x * (c • p.2) - (c • p.2) * upperMat x =
           c • (upperMat x * p.2 - p.2 * upperMat x)
         simp only [mul_smul_comm, smul_mul_assoc, smul_sub] },
   by
     intro p q
     ext1
     · simp
     · simp only [Prod.snd_mul, Prod.snd_add, LinearMap.coe_mk, AddHom.coe_mk]
       noncomm_ring⟩

private def witnessAct : UpperAff2 →ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ PairMat2 where
  toFun := witnessActFun
  map_add' x y := by
    apply Subtype.ext
    apply LinearMap.ext
    intro p
    ext1
    · simp [witnessActFun]
    · change upperMat (x + y) * p.2 - p.2 * upperMat (x + y) =
        (upperMat x * p.2 - p.2 * upperMat x) + (upperMat y * p.2 - p.2 * upperMat y)
      have hadd : upperMat (x + y) = upperMat x + upperMat y := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [upperMat]
      rw [hadd]
      noncomm_ring
  map_smul' c x := by
    apply Subtype.ext
    apply LinearMap.ext
    intro p
    ext1
    · simp [witnessActFun]
    · change upperMat (c • x) * p.2 - p.2 * upperMat (c • x) =
        c • (upperMat x * p.2 - p.2 * upperMat x)
      have hsmul : upperMat (c • x) = c • upperMat x := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [upperMat]
      rw [hsmul, smul_mul_assoc, mul_smul_comm, ← smul_sub]
  map_lie' {x y} := by
    apply Subtype.ext
    apply LinearMap.ext
    intro p
    ext1
    · simp [witnessActFun]
    · change upperMat ⁅x, y⁆ * p.2 - p.2 * upperMat ⁅x, y⁆ =
        (upperMat x * (upperMat y * p.2 - p.2 * upperMat y) -
          (upperMat y * p.2 - p.2 * upperMat y) * upperMat x) -
        (upperMat y * (upperMat x * p.2 - p.2 * upperMat x) -
          (upperMat x * p.2 - p.2 * upperMat x) * upperMat y)
      rw [upperMat_bracket]
      noncomm_ring

/-- Faithful derivation Lie lane of `UpperAff2` acting on the second factor of `Mat2 × Mat2`. -/
abbrev witnessLane : DerivationLieLane ℝ PairMat2 where
  L := UpperAff2
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := witnessAct
  faithful := by
    intro x y h
    have heval := congrArg (fun D : NonAssocDerivation.derivations ℝ PairMat2 =>
      ((D : Module.End ℝ PairMat2) (0, !![0, 0; 1, 0])).2) h
    change upperMat x * !![0, 0; 1, 0] - !![0, 0; 1, 0] * upperMat x =
      upperMat y * !![0, 0; 1, 0] - !![0, 0; 1, 0] * upperMat y at heval
    have hv : x.v = y.v := by
      have h00 := congrArg (fun M : Mat2 => M 0 0) heval
      simpa [upperMat, Matrix.mul_apply, Fin.sum_univ_two] using h00
    have hu : x.u = y.u := by
      have h10 := congrArg (fun M : Mat2 => M 1 0) heval
      simpa [upperMat, Matrix.mul_apply, Fin.sum_univ_two] using h10
    exact UpperAff2.ext hu hv

def witnessP : PairMat2 := (!![1, 0; 0, 0], 1)

theorem witnessP_idempotent : witnessP * witnessP = witnessP := by
  ext1
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [witnessP, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [witnessP]

theorem witnessLane_kills_witnessP (x : UpperAff2) :
    witnessLane.operatorAction x witnessP = 0 := by
  ext1
  · simp [witnessLane, DerivationLieLane.operatorAction, witnessAct, witnessActFun]
  · change upperMat x * (1 : Mat2) - (1 : Mat2) * upperMat x = 0
    simp

abbrev witnessH : Subgroup PairMat2ˣ := peirceIsotropySubgroup PairMat2 witnessP

private theorem oddGrade_witnessP_eq (M N : Mat2) :
    oddGrade witnessP (M, N) = (!![0, M 0 1; M 1 0, 0], 0) := by
  ext1
  · ext i j
    change (witnessP.1 * M * (1 - witnessP.1) + (1 - witnessP.1) * M * witnessP.1) i j =
      (!![0, M 0 1; M 1 0, 0] : Mat2) i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
      Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      norm_num [witnessP]
  · simp [oddGrade, witnessP]

private def witnessOneForm : OneForm witnessLane where
  toFun (x : UpperAff2) := (!![0, x.u; x.v, 0], 0)
  map_add' (x y : UpperAff2) := by
    ext1
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · simp
  map_smul' c (x : UpperAff2) := by
    ext1
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · simp

private theorem witnessOneForm_odd (x : UpperAff2) :
    oddGrade witnessP (witnessOneForm x) = witnessOneForm x := by
  change oddGrade witnessP (!![0, x.u; x.v, 0], 0) = (!![0, x.u; x.v, 0], 0)
  rw [oddGrade_witnessP_eq]
  rfl

private def witnessBaseRightAct (h : witnessH) : witnessLane.L →ₗ[ℝ] witnessLane.L where
  toFun (x : UpperAff2) :=
    UpperAff2.mk
      (((frameTransport (h.1 : PairMat2ˣ) (witnessOneForm x)).1) 0 1)
      (((frameTransport (h.1 : PairMat2ˣ) (witnessOneForm x)).1) 1 0)
  map_add' (x y : UpperAff2) := by
    apply UpperAff2.ext <;> simp [frameTransport, mul_add, add_mul]
  map_smul' c (x : UpperAff2) := by
    apply UpperAff2.ext <;> simp [frameTransport]

private theorem witnessBaseRightAct_one (x : UpperAff2) :
    witnessBaseRightAct 1 x = x := by
  apply UpperAff2.ext <;> simp [witnessBaseRightAct, frameTransport, witnessOneForm]

private theorem witness_frameTransport_eq (h : witnessH) (x : UpperAff2) :
    witnessOneForm (witnessBaseRightAct h x) =
      frameTransport (h.1 : PairMat2ˣ) (witnessOneForm x) := by
  have hodd : oddGrade witnessP (frameTransport (h.1 : PairMat2ˣ) (witnessOneForm x)) =
      frameTransport (h.1 : PairMat2ˣ) (witnessOneForm x) := by
    rw [← frameTransport_oddGrade h.2 (witnessOneForm x), witnessOneForm_odd x]
  have hshape :
      oddGrade witnessP (frameTransport (h.1 : PairMat2ˣ) (witnessOneForm x)) =
        (!![0, (frameTransport (h.1 : PairMat2ˣ) (witnessOneForm x)).1 0 1;
            (frameTransport (h.1 : PairMat2ˣ) (witnessOneForm x)).1 1 0, 0], 0) :=
    oddGrade_witnessP_eq _ _
  rw [← hodd, hshape]
  rfl

private theorem witnessBaseRightAct_mul (h₁ h₂ : witnessH) (x : UpperAff2) :
    witnessBaseRightAct (h₁ * h₂) x = witnessBaseRightAct h₂ (witnessBaseRightAct h₁ x) := by
  have hEq :
      witnessOneForm (witnessBaseRightAct (h₁ * h₂) x) =
        witnessOneForm (witnessBaseRightAct h₂ (witnessBaseRightAct h₁ x)) := by
    rw [witness_frameTransport_eq (h₁ * h₂) x,
      witness_frameTransport_eq h₂ (witnessBaseRightAct h₁ x),
      witness_frameTransport_eq h₁ x]
    simp only [frameTransport, Subgroup.coe_mul, Units.val_mul, mul_inv_rev, mul_assoc]
  apply UpperAff2.ext
  · exact congrArg (fun p : PairMat2 => p.1 0 1) hEq
  · exact congrArg (fun p : PairMat2 => p.1 1 0) hEq

private theorem witnessOneForm_injective : Function.Injective witnessOneForm := by
  intro (x : UpperAff2) (y : UpperAff2) h
  have hu : x.u = y.u := congrArg (fun p : PairMat2 => p.1 0 1) h
  have hv : x.v = y.v := congrArg (fun p : PairMat2 => p.1 1 0) h
  exact UpperAff2.ext hu hv

private theorem witnessOneForm_surjective_odd (m : PairMat2)
    (hm : oddGrade witnessP m = m) :
    ∃ x : witnessLane.L, witnessOneForm x = m := by
  refine ⟨UpperAff2.mk (m.1 0 1) (m.1 1 0), ?_⟩
  have hshape : oddGrade witnessP m = (!![0, m.1 0 1; m.1 1 0, 0], 0) :=
    oddGrade_witnessP_eq m.1 m.2
  rw [← hm, hshape]
  rfl

/-- Concrete non-abelian `SolderingOneForm` witness over `UpperAff2` and `Mat2 × Mat2`. -/
def witnessSoldering : SolderingOneForm witnessLane witnessP witnessH where
  toOneForm := witnessOneForm
  odd := witnessOneForm_odd
  baseRightAct := witnessBaseRightAct
  baseRightAct_one := witnessBaseRightAct_one
  baseRightAct_mul := witnessBaseRightAct_mul
  equivariant := witness_frameTransport_eq
  injective := witnessOneForm_injective
  surjective_odd := witnessOneForm_surjective_odd

private noncomputable def witnessDiagUnit : PairMat2ˣ where
  val := (!![2, 0; 0, 1], 1)
  inv := (!![(2⁻¹ : ℝ), 0; 0, 1], 1)
  val_inv := by
    ext1
    · ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · simp
  inv_val := by
    ext1
    · ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · simp

private theorem witnessDiagUnit_mem_H : witnessDiagUnit ∈ witnessH := by
  change Commute witnessDiagUnit.val witnessP
  ext1
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [witnessDiagUnit, witnessP, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [witnessDiagUnit, witnessP]

/-- **F10 Separation 1 (Equivariance is independent of oddness & bijectivity)**:
`e_swapped ⟨u, v⟩ := (!![0, v; u, 0], 0)` is odd and bijective onto
`peirceOddSubmodule ℝ PairMat2 witnessP`, yet violates `witnessH`-equivariance
for `witnessSoldering.baseRightAct`. -/
theorem witness_odd_bijective_not_equivariant :
    ∃ e_swapped : OneForm witnessLane,
      (∀ x, oddGrade witnessP (e_swapped x) = e_swapped x) ∧
      Function.Injective e_swapped ∧
      (∀ m : PairMat2, oddGrade witnessP m = m → ∃ x : witnessLane.L, e_swapped x = m) ∧
      (∃ (h : witnessH) (x : witnessLane.L),
        e_swapped (witnessSoldering.baseRightAct h x) ≠
          frameTransport (h.1 : PairMat2ˣ) (e_swapped x)) := by
  let e_swapped : OneForm witnessLane :=
    { toFun := fun (x : UpperAff2) => (!![0, x.v; x.u, 0], 0)
      map_add' := fun (x y : UpperAff2) => by
        ext1
        · ext i j; fin_cases i <;> fin_cases j <;> simp
        · simp
      map_smul' := fun c (x : UpperAff2) => by
        ext1
        · ext i j; fin_cases i <;> fin_cases j <;> simp
        · simp }
  refine ⟨e_swapped, ?_, ?_, ?_, ?_⟩
  · intro (x : UpperAff2)
    change oddGrade witnessP (!![0, x.v; x.u, 0], 0) = (!![0, x.v; x.u, 0], 0)
    rw [oddGrade_witnessP_eq]
    rfl
  · intro (x : UpperAff2) (y : UpperAff2) h
    have hv : x.v = y.v := congrArg (fun p : PairMat2 => p.1 0 1) h
    have hu : x.u = y.u := congrArg (fun p : PairMat2 => p.1 1 0) h
    exact UpperAff2.ext hu hv
  · intro m hm
    refine ⟨UpperAff2.mk (m.1 1 0) (m.1 0 1), ?_⟩
    have hshape : oddGrade witnessP m = (!![0, m.1 0 1; m.1 1 0, 0], 0) :=
      oddGrade_witnessP_eq m.1 m.2
    rw [← hm, hshape]
    rfl
  · refine ⟨⟨witnessDiagUnit, witnessDiagUnit_mem_H⟩, UpperAff2.mk 1 0, ?_⟩
    intro hEq
    have h10 := congrArg (fun p : PairMat2 => p.1 1 0) hEq
    norm_num [e_swapped, witnessSoldering, witnessBaseRightAct, witnessOneForm,
      frameTransport, witnessDiagUnit, Matrix.mul_apply, Fin.sum_univ_two] at h10

/-- **F10 Separation 2 (Trivial `H`-action is impossible for any soldering form)**:
No `SolderingOneForm witnessLane witnessP witnessH` can have `baseRightAct h x = x`
for all `h` and `x`, because `frameTransport` acts nontrivially on `peirceOddSubmodule`. -/
theorem witness_trivial_action_impossible :
    ¬ ∃ S : SolderingOneForm witnessLane witnessP witnessH,
      ∀ (h : witnessH) (x : witnessLane.L), S.baseRightAct h x = x := by
  rintro ⟨S, htriv⟩
  have hsurj := S.surjective_odd (!![0, 1; 0, 0], 0) (by
    rw [oddGrade_witnessP_eq]
    rfl)
  rcases hsurj with ⟨x, hx⟩
  have heq := S.equivariant ⟨witnessDiagUnit, witnessDiagUnit_mem_H⟩ x
  rw [htriv, hx] at heq
  have h01 := congrArg (fun p : PairMat2 => p.1 0 1) heq
  norm_num [frameTransport, witnessDiagUnit, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- **F10 Separation 3 (Oddness + `H`-equivariance do not imply bijectivity/nondegeneracy)**:
`e_upper ⟨u, v⟩ := (!![0, u; 0, 0], 0)` is odd and `witnessH`-equivariant for
`witnessSoldering.baseRightAct`, yet fails both injectivity and surjectivity onto
`peirceOddSubmodule ℝ PairMat2 witnessP`. -/
theorem witness_odd_equivariant_not_bijective :
    ∃ e_upper : OneForm witnessLane,
      (∀ x, oddGrade witnessP (e_upper x) = e_upper x) ∧
      (∀ (h : witnessH) (x : witnessLane.L),
        e_upper (witnessSoldering.baseRightAct h x) =
          frameTransport (h.1 : PairMat2ˣ) (e_upper x)) ∧
      ¬ Function.Injective e_upper ∧
      LinearMap.range e_upper ≠ peirceOddSubmodule ℝ PairMat2 witnessP := by
  let e_upper : OneForm witnessLane :=
    { toFun := fun (x : UpperAff2) => (!![0, x.u; 0, 0], 0)
      map_add' := fun (x y : UpperAff2) => by
        ext1
        · ext i j; fin_cases i <;> fin_cases j <;> simp
        · simp
      map_smul' := fun c (x : UpperAff2) => by
        ext1
        · ext i j; fin_cases i <;> fin_cases j <;> simp
        · simp }
  refine ⟨e_upper, ?_, ?_, ?_, ?_⟩
  · intro (x : UpperAff2)
    change oddGrade witnessP (!![0, x.u; 0, 0], 0) = (!![0, x.u; 0, 0], 0)
    rw [oddGrade_witnessP_eq]
    rfl
  · intro h (x : UpperAff2)
    have hcomm : Commute (h.1.val.1 : Mat2) (!![1, 0; 0, 0] : Mat2) :=
      congrArg Prod.fst h.2.eq
    have hodd : oddGrade witnessP (frameTransport (h.1 : PairMat2ˣ) (e_upper x)) =
        frameTransport (h.1 : PairMat2ˣ) (e_upper x) := by
      rw [← frameTransport_oddGrade h.2 (e_upper x)]
      change frameTransport (h.1 : PairMat2ˣ) (oddGrade witnessP (!![0, x.u; 0, 0], 0)) = _
      rw [oddGrade_witnessP_eq]
      rfl
    have hshape :
        oddGrade witnessP (frameTransport (h.1 : PairMat2ˣ) (e_upper x)) =
          (!![0, (frameTransport (h.1 : PairMat2ˣ) (e_upper x)).1 0 1;
              (frameTransport (h.1 : PairMat2ˣ) (e_upper x)).1 1 0, 0], 0) :=
      oddGrade_witnessP_eq _ _
    have h00 : (frameTransport (h.1 : PairMat2ˣ) (e_upper x)).1 0 0 = 0 := by
      have h00' := congrArg (fun p : PairMat2 => p.1 0 0) (hodd.symm.trans hshape)
      simpa using h00'
    have h11 : (frameTransport (h.1 : PairMat2ˣ) (e_upper x)).1 1 1 = 0 := by
      have h11' := congrArg (fun p : PairMat2 => p.1 1 1) (hodd.symm.trans hshape)
      simpa using h11'
    have h10_comm : (h.1.val.1 : Mat2) 1 0 = 0 := by
      have h10' := congrArg (fun M : Mat2 => M 1 0) hcomm.eq
      simpa [witnessP, Matrix.mul_apply, Fin.sum_univ_two] using h10'
    have hinv10_comm : ((h.1⁻¹ : PairMat2ˣ).val.1 : Mat2) 1 0 = 0 := by
      have hinv := congrArg Prod.fst (commute_inv_of_commute h.2).eq
      have h10' := congrArg (fun M : Mat2 => M 1 0) hinv
      simpa [witnessP, Matrix.mul_apply, Fin.sum_univ_two] using h10'
    have h10 : (frameTransport (h.1 : PairMat2ˣ) (e_upper x)).1 1 0 = 0 := by
      change (((h.1⁻¹ : PairMat2ˣ).val.1 : Mat2) * !![0, x.u; 0, 0] *
        (h.1.val.1 : Mat2)) 1 0 = 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, hinv10_comm, h10_comm]
      norm_num
    have h01_eq : (e_upper (witnessSoldering.baseRightAct h x)).1 0 1 =
        (frameTransport (h.1 : PairMat2ˣ) (e_upper x)).1 0 1 := by
      change (((h.1⁻¹ : PairMat2ˣ).val.1 : Mat2) * !![0, x.u; x.v, 0] *
        (h.1.val.1 : Mat2)) 0 1 =
        (((h.1⁻¹ : PairMat2ˣ).val.1 : Mat2) * !![0, x.u; 0, 0] *
          (h.1.val.1 : Mat2)) 0 1
      have h01_comm : (h.1.val.1 : Mat2) 0 1 = 0 := by
        have h01' := congrArg (fun M : Mat2 => M 0 1) hcomm.eq
        simpa [witnessP, Matrix.mul_apply, Fin.sum_univ_two] using h01'.symm
      have hinv01_comm : ((h.1⁻¹ : PairMat2ˣ).val.1 : Mat2) 0 1 = 0 := by
        have hinv := congrArg Prod.fst (commute_inv_of_commute h.2).eq
        have h01' := congrArg (fun M : Mat2 => M 0 1) hinv
        simpa [witnessP, Matrix.mul_apply, Fin.sum_univ_two] using h01'.symm
      simp only [Matrix.mul_apply, Fin.sum_univ_two, hinv01_comm, h01_comm]
      norm_num
    ext1
    · ext i j
      fin_cases i <;> fin_cases j
      · exact h00.symm
      · exact h01_eq
      · exact h10.symm
      · exact h11.symm
    · simp [frameTransport, e_upper]
  · intro hinj
    have hEq : e_upper (UpperAff2.mk 0 0) = e_upper (UpperAff2.mk 0 1) := by
      ext1
      · ext i j; fin_cases i <;> fin_cases j <;> rfl
      · rfl
    have h01 := congrArg UpperAff2.v (hinj hEq)
    norm_num at h01
  · intro hrange
    have hmem : (!![0, 0; 1, 0], (0 : Mat2)) ∈ peirceOddSubmodule ℝ PairMat2 witnessP := by
      rw [mem_peirceOddSubmodule, oddGrade_witnessP_eq]
      rfl
    rw [← hrange] at hmem
    rcases hmem with ⟨(x : UpperAff2), hx⟩
    have h10 := congrArg (fun p : PairMat2 => p.1 1 0) hx
    norm_num [e_upper] at h10

private noncomputable def fullMat2Lane : DerivationLieLane ℝ Mat2 where
  L := NonAssocDerivation.derivations ℝ Mat2
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := LieHom.id
  faithful := Function.injective_id

private noncomputable def innerDir (H : Mat2) : fullMat2Lane.L :=
  ⟨{ toFun := fun A => H * A - A * H
     map_add' := by intro A B; noncomm_ring
     map_smul' := by intro c A; simp [smul_sub] },
    by intro A B; dsimp; noncomm_ring⟩

private def shearG : Mat2ˣ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private noncomputable def diagH : Mat2ˣ where
  val := !![2, 0; 0, 1]
  inv := !![(2⁻¹ : ℝ), 0; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- **F12 Concrete Non-Abelian Witness**:
In `M₂(ℝ)`, the product law `gaugeForm_product` retains non-abelian conjugation
`(↑h⁻¹) * θ(g) * ↑h + θ(h)` and order non-commutativity (`θ(g * h) ≠ θ(h * g)` and
`θ(g * h) ≠ θ(g) + θ(h)`), distinguishing it from commutative Dirichlet series
(`ArithmeticFunction ℝ`). -/
theorem gaugeForm_product_nonabelian_witness :
    let x := innerDir !![1, 0; 0, 0]
    gaugeForm fullMat2Lane (shearG * diagH) x =
      (↑diagH⁻¹ : Mat2) * gaugeForm fullMat2Lane shearG x * ↑diagH +
        gaugeForm fullMat2Lane diagH x ∧
    gaugeForm fullMat2Lane (shearG * diagH) x ≠
      gaugeForm fullMat2Lane shearG x + gaugeForm fullMat2Lane diagH x ∧
    gaugeForm fullMat2Lane (shearG * diagH) x ≠
      gaugeForm fullMat2Lane (diagH * shearG) x ∧
    connectionCurvature fullMat2Lane (gaugeForm fullMat2Lane (shearG * diagH)) = 0 := by
  let x := innerDir !![1, 0; 0, 0]
  have hG : gaugeForm fullMat2Lane shearG x = !![0, 1; 0, 0] := by
    rw [gaugeForm_apply]
    change shearG.inv * (!![1, 0; 0, 0] * shearG.val - shearG.val * !![1, 0; 0, 0]) =
      !![0, 1; 0, 0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shearG, Matrix.mul_apply, Fin.sum_univ_two]
  have hH : gaugeForm fullMat2Lane diagH x = 0 := by
    rw [gaugeForm_apply]
    change diagH.inv * (!![1, 0; 0, 0] * diagH.val - diagH.val * !![1, 0; 0, 0]) = 0
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [diagH, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨gaugeForm_product fullMat2Lane shearG diagH x, ?_, ?_,
    gaugeForm_flat fullMat2Lane (shearG * diagH)⟩
  · intro hEq
    rw [gaugeForm_product fullMat2Lane shearG diagH x, hG, hH, add_zero] at hEq
    have h01 := congrArg (fun M : Mat2 => M 0 1) hEq
    norm_num [diagH, Matrix.mul_apply, Fin.sum_univ_two] at h01
  · intro hEq
    rw [gaugeForm_product fullMat2Lane shearG diagH x,
      gaugeForm_product fullMat2Lane diagH shearG x, hG, hH] at hEq
    have h01 := congrArg (fun M : Mat2 => M 0 1) hEq
    norm_num [shearG, diagH, Matrix.mul_apply, Fin.sum_univ_two] at h01

end Witnesses

end InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
