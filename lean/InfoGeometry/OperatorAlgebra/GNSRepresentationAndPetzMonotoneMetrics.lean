/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Prequantum.AlgebraicGNSState
import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.OperatorAlgebra.KadisonSchwarzAndQuantumCramerRao
import InfoGeometry.Categorical.MarkovCategoryAndColimitInformation
import InfoGeometry.Canonical.KuboMoriBogoliubovMetric
import InfoGeometry.QuantumGeometry.NoncommutativeSLDFisherMetric
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Constructive GNS Quotient Representation and Morozova–Chentsov–Petz Metric Hierarchy

This module bridges algebraic states (`Prequantum.AlgebraicGNSState`), discrete K-theory
(`Algebra.Grothendieck`), and noncommutative quantum Fisher metrics (`SLD`, `BKM`, `GM`, `RLD`):

1. **Constructive GNS Quotient Inner-Product Module, Star-Representation & `ClTower` Faithfulness**:
   - Equips `AlgebraicGNSState.RealAlgebraicState.GNSQuotient F` with `AddCommGroup`, `Module ℝ`,
     a bilinear, symmetric, **strictly positive-definite** inner product
     `gnsInner : F.GNSQuotient →ₗ[ℝ] F.GNSQuotient →ₗ[ℝ] ℝ` (`gnsInner F u u = 0 ↔ u = 0`),
     and Cauchy–Schwarz.
   - Constructs the left regular algebra star-representation
     `gnsRep F : A →ₐ[ℝ] Module.End ℝ F.GNSQuotient`, proves formal star-adjointness, cyclic
     generation, and cyclic state reconstruction `F.eval a = gnsInner F Ω (gnsRep F a Ω)`.
   - Instantiates `clTowerRealState n : RealAlgebraicState (ClTower ℝ n)` via
     `normalizedTowerTrace` and proves exact faithfulness `(clTowerRealState n).gnsNullSet = {0}`.
   - Connects orthogonal idempotents and Grothendieck difference groups via `grothendieckRealRank`.
2. **Strict Scalar Mean Inequality Chain (`harmonic ≤ geom ≤ log ≤ arith`)**:
   - Proves strict ordering of the four Petz spectral mean functions on `0 < p, q`, using
     `strictMonoOn_of_deriv_pos` on hyperbolic transforms for `√(pq) ≤ L(p,q) ≤ (p+q)/2`, with
     strict inequality whenever `p ≠ q`.
3. **Morozova–Chentsov–Petz Quantum Fisher Metric Hierarchy & Commutant Collapse**:
   - Defines `sldTangentMetric`, `bkmTangentMetric`, `geomTangentMetric`, and `rldTangentMetric`
     on complex tangent operators relative to `KuboMoriBogoliubov.FaithfulDensityState n`.
   - Constructs the explicit unique Lyapunov solver `sldLyapunovSolve ρ X` solving `SLD.IsSLD`
     and matching `SLD.sldFisherInner` on Hermitian variations, together with BKM Onsager duality
     matching `FaithfulDensityState.bkmInnerProduct`.
   - Proves `sldTangentMetric ρ X ≤ bkmTangentMetric ρ X ≤ geomTangentMetric ρ X ≤ rldTangentMetric ρ X`,
     characterizes equality `SLD = BKM` and `SLD = RLD` by `[ρ, X] = 0`, and shows collapse to
     the classical Chentsov–Fisher metric on diagonal observables.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.GNSRepresentationAndPetzMonotoneMetrics

open Matrix Finset
open scoped BigOperators
open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.OperatorAlgebra.KadisonSchwarzAndQuantumCramerRao
open InfoGeometry.Categorical.MarkovCategoryAndColimitInformation
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
open KuboMoriBogoliubov
open InfoGeometry.QuantumGeometry.SLD

/-! ### 1. Constructive GNS Quotient Inner-Product Module & Star-Representation -/

section GNSQuotientSpace

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]

lemma smul_mem_gnsNullSet (F : RealAlgebraicState A) (r : ℝ) {x : A}
    (hx : x ∈ F.gnsNullSet) : r • x ∈ F.gnsNullSet := by
  change F.eval (star (r • x) * (r • x)) = 0
  rw [star_smul, star_trivial r, smul_mul_assoc, mul_smul_comm, smul_smul, F.eval_smul]
  have hx0 : F.eval (star x * x) = 0 := hx
  rw [hx0, mul_zero]

lemma add_gnsEquiv_compat (F : RealAlgebraicState A) {x₁ x₂ y₁ y₂ : A}
    (hx : F.gnsEquiv x₁ x₂) (hy : F.gnsEquiv y₁ y₂) :
    F.gnsEquiv (x₁ + y₁) (x₂ + y₂) := by
  unfold RealAlgebraicState.gnsEquiv at hx hy ⊢
  have hid : (x₁ + y₁) - (x₂ + y₂) = (x₁ - x₂) + (y₁ - y₂) := by noncomm_ring
  rw [hid]
  exact F.add_mem_gnsNullSet hx hy

lemma neg_gnsEquiv_compat (F : RealAlgebraicState A) {x y : A}
    (h : F.gnsEquiv x y) : F.gnsEquiv (-x) (-y) := by
  unfold RealAlgebraicState.gnsEquiv at h ⊢
  have hid : (-x) - (-y) = -(x - y) := by noncomm_ring
  rw [hid]
  exact F.neg_mem_gnsNullSet h

lemma smul_gnsEquiv_compat (F : RealAlgebraicState A) (r : ℝ) {x y : A}
    (h : F.gnsEquiv x y) : F.gnsEquiv (r • x) (r • y) := by
  unfold RealAlgebraicState.gnsEquiv at h ⊢
  rw [← smul_sub]
  exact smul_mem_gnsNullSet F r h

lemma mul_left_gnsEquiv_compat (F : RealAlgebraicState A) (a : A) {x y : A}
    (h : F.gnsEquiv x y) : F.gnsEquiv (a * x) (a * y) := by
  unfold RealAlgebraicState.gnsEquiv at h ⊢
  rw [← mul_sub]
  exact F.mul_mem_gnsNullSet a h

private def gnsZero (F : RealAlgebraicState A) : F.GNSQuotient :=
  Quotient.mk F.gnsSetoid 0

private def gnsAdd (F : RealAlgebraicState A) : F.GNSQuotient → F.GNSQuotient → F.GNSQuotient :=
  Quotient.map₂ (· + ·) (fun _ _ hx _ _ hy => add_gnsEquiv_compat F hx hy)

private def gnsNeg (F : RealAlgebraicState A) : F.GNSQuotient → F.GNSQuotient :=
  Quotient.map (- ·) (fun _ _ h => neg_gnsEquiv_compat F h)

private def gnsSmul (F : RealAlgebraicState A) (r : ℝ) : F.GNSQuotient → F.GNSQuotient :=
  Quotient.map (r • ·) (fun _ _ h => smul_gnsEquiv_compat F r h)

private lemma gns_mk_eq_mk {F : RealAlgebraicState A} {x y : A}
    (h : F.gnsEquiv x y) :
    (Quotient.mk F.gnsSetoid x : F.GNSQuotient) = Quotient.mk F.gnsSetoid y :=
  Quotient.sound h

/-- Additive commutative group instance on the algebraic GNS quotient `F.GNSQuotient`. -/
instance instAddCommGroupGNSQuotient (F : RealAlgebraicState A) :
    AddCommGroup F.GNSQuotient :=
  letI : Zero F.GNSQuotient := ⟨gnsZero F⟩
  letI : Add F.GNSQuotient := ⟨gnsAdd F⟩
  letI : Neg F.GNSQuotient := ⟨gnsNeg F⟩
  { zero := gnsZero F
    add := gnsAdd F
    neg := gnsNeg F
    add_assoc := fun u v w => by
      refine Quotient.inductionOn₃ u v w (fun x y z => ?_)
      exact gns_mk_eq_mk (by dsimp only; rw [add_assoc]; exact F.gnsEquiv_refl _)
    zero_add := fun u => by
      refine Quotient.inductionOn u (fun x => ?_)
      exact gns_mk_eq_mk (by dsimp only; rw [zero_add]; exact F.gnsEquiv_refl _)
    add_zero := fun u => by
      refine Quotient.inductionOn u (fun x => ?_)
      exact gns_mk_eq_mk (by dsimp only; rw [add_zero]; exact F.gnsEquiv_refl _)
    neg_add_cancel := fun u => by
      refine Quotient.inductionOn u (fun x => ?_)
      exact gns_mk_eq_mk (by dsimp only; rw [neg_add_cancel]; exact F.gnsEquiv_refl _)
    add_comm := fun u v => by
      refine Quotient.inductionOn₂ u v (fun x y => ?_)
      exact gns_mk_eq_mk (by dsimp only; rw [add_comm]; exact F.gnsEquiv_refl _)
    nsmul := nsmulRec
    zsmul := zsmulRec }

/-- `ℝ`-module instance on the algebraic GNS quotient `F.GNSQuotient`. -/
instance instModuleRealGNSQuotient (F : RealAlgebraicState A) :
    Module ℝ F.GNSQuotient where
  smul := gnsSmul F
  one_smul u := by
    refine Quotient.inductionOn u (fun x => ?_)
    exact gns_mk_eq_mk (by dsimp only; rw [one_smul]; exact F.gnsEquiv_refl _)
  mul_smul r s u := by
    refine Quotient.inductionOn u (fun x => ?_)
    exact gns_mk_eq_mk (by dsimp only; rw [mul_smul]; exact F.gnsEquiv_refl _)
  smul_zero r := gns_mk_eq_mk (by dsimp only; rw [smul_zero]; exact F.gnsEquiv_refl _)
  smul_add r u v := by
    refine Quotient.inductionOn₂ u v (fun x y => ?_)
    exact gns_mk_eq_mk (by dsimp only; rw [smul_add]; exact F.gnsEquiv_refl _)
  add_smul r s u := by
    refine Quotient.inductionOn u (fun x => ?_)
    exact gns_mk_eq_mk (by dsimp only; rw [add_smul]; exact F.gnsEquiv_refl _)
  zero_smul u := by
    refine Quotient.inductionOn u (fun x => ?_)
    exact gns_mk_eq_mk (by dsimp only; rw [zero_smul]; exact F.gnsEquiv_refl _)

/-- Canonical surjective `ℝ`-linear quotient map `A →ₗ[ℝ] F.GNSQuotient`. -/
def gnsMkLinear (F : RealAlgebraicState A) : A →ₗ[ℝ] F.GNSQuotient where
  toFun x := Quotient.mk F.gnsSetoid x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma gnsMkLinear_eq_zero_iff (F : RealAlgebraicState A) (x : A) :
    gnsMkLinear F x = 0 ↔ x ∈ F.gnsNullSet := by
  change Quotient.mk F.gnsSetoid x = Quotient.mk F.gnsSetoid 0 ↔ x ∈ F.gnsNullSet
  constructor
  · intro h
    have hrel : F.gnsEquiv x 0 := Quotient.exact h
    unfold RealAlgebraicState.gnsEquiv at hrel
    simpa [sub_zero] using hrel
  · intro hx
    apply Quotient.sound
    change F.gnsEquiv x 0
    unfold RealAlgebraicState.gnsEquiv
    simpa [sub_zero] using hx

private lemma gns_inner_compat (F : RealAlgebraicState A) {x₁ x₂ y₁ y₂ : A}
    (hx : F.gnsEquiv x₁ x₂) (hy : F.gnsEquiv y₁ y₂) :
    F.eval (star x₁ * y₁) = F.eval (star x₂ * y₂) := by
  have hxnull : x₁ - x₂ ∈ F.gnsNullSet := hx
  have hynull : y₁ - y₂ ∈ F.gnsNullSet := hy
  have h1 : F.eval (star x₁ * (y₁ - y₂)) = 0 := by
    change F.toLinearMap (star x₁ * (y₁ - y₂)) = 0
    rw [← F.symmetric x₁ (y₁ - y₂)]
    exact F.state_null_product_zero x₁ (y₁ - y₂) hynull
  have h2 : F.eval (star (x₁ - x₂) * y₂) = 0 :=
    F.state_null_product_zero y₂ (x₁ - x₂) hxnull
  have hdiff : star x₁ * y₁ - star x₂ * y₂ = star x₁ * (y₁ - y₂) + star (x₁ - x₂) * y₂ := by
    rw [star_sub, mul_sub, sub_mul]
    noncomm_ring
  have hzero : F.eval (star x₁ * y₁ - star x₂ * y₂) = 0 := by
    rw [hdiff, F.eval_add, h1, h2, add_zero]
  have hsub : F.eval (star x₁ * y₁) - F.eval (star x₂ * y₂) = 0 := by
    simpa [RealAlgebraicState.eval] using hzero
  linarith

private def gnsInnerFun (F : RealAlgebraicState A) : F.GNSQuotient → F.GNSQuotient → ℝ :=
  Quotient.lift₂ (fun x y => F.eval (star x * y))
    (fun _ _ _ _ hx hy => gns_inner_compat F hx hy)

/-- Bilinear real inner product `F.GNSQuotient →ₗ[ℝ] F.GNSQuotient →ₗ[ℝ] ℝ` on the
algebraic GNS quotient. -/
def gnsInner (F : RealAlgebraicState A) : F.GNSQuotient →ₗ[ℝ] F.GNSQuotient →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => gnsInnerFun F u v
      map_add' := fun v₁ v₂ => by
        refine Quotient.inductionOn₃ u v₁ v₂ (fun x y₁ y₂ => ?_)
        change F.eval (star x * (y₁ + y₂)) = F.eval (star x * y₁) + F.eval (star x * y₂)
        rw [mul_add, F.eval_add]
      map_smul' := fun r v => by
        refine Quotient.inductionOn₂ u v (fun x y => ?_)
        change F.eval (star x * (r • y)) = r * F.eval (star x * y)
        rw [mul_smul_comm, F.eval_smul] }
  map_add' u₁ u₂ := by
    ext v
    refine Quotient.inductionOn₃ u₁ u₂ v (fun x₁ x₂ y => ?_)
    change F.eval (star (x₁ + x₂) * y) = F.eval (star x₁ * y) + F.eval (star x₂ * y)
    rw [star_add, add_mul, F.eval_add]
  map_smul' r u := by
    ext v
    refine Quotient.inductionOn₂ u v (fun x y => ?_)
    change F.eval (star (r • x) * y) = r * F.eval (star x * y)
    rw [star_smul, star_trivial r, smul_mul_assoc, F.eval_smul]

@[simp]
theorem gnsInner_mk (F : RealAlgebraicState A) (x y : A) :
    gnsInner F (gnsMkLinear F x) (gnsMkLinear F y) = F.eval (star x * y) := rfl

theorem gnsInner_symm (F : RealAlgebraicState A) (u v : F.GNSQuotient) :
    gnsInner F u v = gnsInner F v u := by
  refine Quotient.inductionOn₂ u v (fun x y => ?_)
  exact (F.symmetric x y).symm

theorem gnsInner_self_nonneg (F : RealAlgebraicState A) (u : F.GNSQuotient) :
    0 ≤ gnsInner F u u := by
  refine Quotient.inductionOn u (fun x => F.positive x)

/-- Strict positive definiteness of `gnsInner` on the GNS quotient `F.GNSQuotient`. -/
theorem gnsInner_self_eq_zero_iff (F : RealAlgebraicState A) (u : F.GNSQuotient) :
    gnsInner F u u = 0 ↔ u = 0 := by
  refine Quotient.inductionOn u (fun x => ?_)
  change F.eval (star x * x) = 0 ↔ gnsMkLinear F x = 0
  rw [gnsMkLinear_eq_zero_iff]
  rfl

/-- Cauchy–Schwarz inequality for `gnsInner` on the GNS quotient. -/
theorem gnsInner_cauchy_schwarz (F : RealAlgebraicState A) (u v : F.GNSQuotient) :
    gnsInner F u v ^ 2 ≤ gnsInner F u u * gnsInner F v v := by
  refine Quotient.inductionOn₂ u v (fun x y => ?_)
  change F.toLinearMap (star x * y) ^ 2 ≤
    F.toLinearMap (star x * x) * F.toLinearMap (star y * y)
  rcases lt_or_eq_of_le (F.positive y) with hy_pos | hy_zero
  · rw [F.symmetric y x]
    exact F.algebraic_cauchy_schwarz x y hy_pos
  · have hnull : y ∈ F.gnsNullSet := hy_zero.symm
    have hxy0 : F.toLinearMap (star x * y) = 0 := by
      rw [← F.symmetric x y]
      exact F.state_null_product_zero x y hnull
    rw [hxy0, ← hy_zero]
    norm_num

private def gnsRepMul (F : RealAlgebraicState A) (a : A) :
    F.GNSQuotient →ₗ[ℝ] F.GNSQuotient where
  toFun := Quotient.map (a * ·) (fun _ _ h => mul_left_gnsEquiv_compat F a h)
  map_add' u v := by
    refine Quotient.inductionOn₂ u v (fun x y => ?_)
    exact gns_mk_eq_mk (by dsimp only; rw [mul_add]; exact F.gnsEquiv_refl _)
  map_smul' r u := by
    refine Quotient.inductionOn u (fun x => ?_)
    exact gns_mk_eq_mk (by dsimp only; rw [mul_smul_comm]; exact F.gnsEquiv_refl _)

/-- **GNS Left Regular Algebra Representation** `A →ₐ[ℝ] Module.End ℝ F.GNSQuotient`. -/
def gnsRep (F : RealAlgebraicState A) : A →ₐ[ℝ] Module.End ℝ F.GNSQuotient where
  toFun a := gnsRepMul F a
  map_one' := by
    ext u
    refine Quotient.inductionOn u (fun x => ?_)
    exact gns_mk_eq_mk (by dsimp only; rw [one_mul]; exact F.gnsEquiv_refl _)
  map_mul' a b := by
    ext u
    refine Quotient.inductionOn u (fun x => ?_)
    exact gns_mk_eq_mk (by dsimp only; rw [mul_assoc]; exact F.gnsEquiv_refl _)
  map_zero' := by
    ext u
    refine Quotient.inductionOn u (fun x => ?_)
    exact gns_mk_eq_mk (by dsimp only; rw [zero_mul]; exact F.gnsEquiv_refl _)
  map_add' a b := by
    ext u
    refine Quotient.inductionOn u (fun x => ?_)
    exact gns_mk_eq_mk (by dsimp only; rw [add_mul]; exact F.gnsEquiv_refl _)
  commutes' r := by
    ext u
    refine Quotient.inductionOn u (fun x => ?_)
    change Quotient.mk F.gnsSetoid (algebraMap ℝ A r * x) =
      Quotient.mk F.gnsSetoid (r • x)
    exact gns_mk_eq_mk (by rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
                           exact F.gnsEquiv_refl _)

@[simp]
theorem gnsRep_mk (F : RealAlgebraicState A) (a x : A) :
    gnsRep F a (gnsMkLinear F x) = gnsMkLinear F (a * x) := rfl

/-- Formal star-adjointness of `gnsRep F` with respect to `gnsInner F`. -/
theorem gnsRep_star_adjoint (F : RealAlgebraicState A) (a : A) (u v : F.GNSQuotient) :
    gnsInner F (gnsRep F a u) v = gnsInner F u (gnsRep F (star a) v) := by
  refine Quotient.inductionOn₂ u v (fun x y => ?_)
  change F.eval (star (a * x) * y) = F.eval (star x * (star a * y))
  rw [star_mul, mul_assoc]

/-- Canonical GNS cyclic vacuum vector `Ω := [1]`. -/
def gnsCyclicVec (F : RealAlgebraicState A) : F.GNSQuotient :=
  gnsMkLinear F 1

theorem gnsCyclicVec_norm_one (F : RealAlgebraicState A) :
    gnsInner F (gnsCyclicVec F) (gnsCyclicVec F) = 1 :=
  F.gns_vacuum_norm_eq_one

theorem gnsRep_cyclic_surjective (F : RealAlgebraicState A) (u : F.GNSQuotient) :
    ∃ a : A, gnsRep F a (gnsCyclicVec F) = u := by
  refine Quotient.inductionOn u (fun x => ?_)
  refine ⟨x, ?_⟩
  change gnsMkLinear F (x * 1) = gnsMkLinear F x
  rw [mul_one]

/-- **GNS Cyclic State Reconstruction Theorem**: every real algebraic state is recovered as
a vector expectation `F.eval a = ⟪Ω, π_F(a) Ω⟫` in its constructed GNS representation. -/
theorem gns_state_reconstruction (F : RealAlgebraicState A) (a : A) :
    F.eval a = gnsInner F (gnsCyclicVec F) (gnsRep F a (gnsCyclicVec F)) := by
  change F.eval a = F.eval (star (1 : A) * (a * 1))
  rw [star_one, one_mul, mul_one]

/-- Construct a `RealAlgebraicState` from any normalized `IsPositiveStarFunctional ω`. -/
def realStateOfPosStarFunctional (ω : A →ₗ[ℝ] ℝ)
    (hω : IsPositiveStarFunctional ω) (h1 : ω 1 = 1) : RealAlgebraicState A where
  toLinearMap := ω
  normalized := h1
  positive := hω.1
  symmetric x y := by
    calc
      ω (star y * x) = ω (star (star x * y)) := by rw [star_mul, star_star]
      _ = ω (star x * y) := hω.2 (star x * y)

end GNSQuotientSpace

section ClTowerGNSAndGrothendieck

/-- Recursive `Algebra ℝ (ClTower ℝ n)` compatible with `instModuleClTower` and
`instRingClTower`. -/
@[reducible]
instance instAlgebraRealClTower : ∀ n : ℕ, Algebra ℝ (ClTower ℝ n)
  | 0 => inferInstanceAs (Algebra ℝ ℝ)
  | n + 1 => by
      letI : Ring (ClTower ℝ n) := instRingClTower n
      letI : Algebra ℝ (ClTower ℝ n) := instAlgebraRealClTower n
      exact inferInstanceAs (Algebra ℝ (Matrix (Fin 2) (Fin 2) (ClTower ℝ n)))

/-- Recursive `StarModule ℝ (ClTower ℝ n)` compatible with `instStarRingClTower`. -/
instance instStarModuleRealClTower : ∀ n : ℕ, StarModule ℝ (ClTower ℝ n)
  | 0 => inferInstanceAs (StarModule ℝ ℝ)
  | n + 1 => by
      let _ : Ring (ClTower ℝ n) := instRingClTower n
      let _ : StarRing (ClTower ℝ n) := instStarRingClTower n
      let _ : StarModule ℝ (ClTower ℝ n) := instStarModuleRealClTower n
      exact inferInstanceAs (StarModule ℝ (Matrix (Fin 2) (Fin 2) (ClTower ℝ n)))

lemma towerTrace_real_mul_comm :
    ∀ (n : ℕ) (X Y : ClTower ℝ n),
      towerTrace (n := n) (X * Y) = towerTrace (n := n) (Y * X)
  | 0, x, y => mul_comm x y
  | n + 1, X, Y => by
      dsimp [towerTrace]
      have h00 : (X * Y) 0 0 = X 0 0 * Y 0 0 + X 0 1 * Y 1 0 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      have h11 : (X * Y) 1 1 = X 1 0 * Y 0 1 + X 1 1 * Y 1 1 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      have k00 : (Y * X) 0 0 = Y 0 0 * X 0 0 + Y 0 1 * X 1 0 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      have k11 : (Y * X) 1 1 = Y 1 0 * X 0 1 + Y 1 1 * X 1 1 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [h00, h11, k00, k11, towerTrace_add, towerTrace_add, towerTrace_add, towerTrace_add,
        towerTrace_real_mul_comm n (X 0 0) (Y 0 0),
        towerTrace_real_mul_comm n (X 0 1) (Y 1 0),
        towerTrace_real_mul_comm n (X 1 0) (Y 0 1),
        towerTrace_real_mul_comm n (X 1 1) (Y 1 1)]
      abel

lemma towerTrace_real_star :
    ∀ (n : ℕ) (X : ClTower ℝ n),
      towerTrace (n := n) (star X) = towerTrace (n := n) X
  | 0, x => star_trivial x
  | n + 1, X => by
      dsimp [towerTrace]
      rw [towerTrace_real_star n (X 0 0), towerTrace_real_star n (X 1 1)]

lemma towerTrace_real_star_mul_self_eq_zero_iff :
    ∀ {n : ℕ} (X : ClTower ℝ n),
      towerTrace (n := n) (star X * X) = 0 ↔ X = 0
  | 0, x => by
      change x * x = 0 ↔ x = 0
      exact mul_self_eq_zero
  | n + 1, X => by
      constructor
      · intro hsum
        dsimp [towerTrace] at hsum
        have h00 : (star X * X) 0 0 = star (X 0 0) * X 0 0 + star (X 1 0) * X 1 0 := by
          simp [Matrix.mul_apply, Fin.sum_univ_two]
        have h11 : (star X * X) 1 1 = star (X 0 1) * X 0 1 + star (X 1 1) * X 1 1 := by
          simp [Matrix.mul_apply, Fin.sum_univ_two]
        rw [h00, h11, towerTrace_add, towerTrace_add] at hsum
        have ha : 0 ≤ towerTrace (n := n) (star (X 0 0) * X 0 0) := towerTrace_star_mul_self_nonneg _
        have hb : 0 ≤ towerTrace (n := n) (star (X 1 0) * X 1 0) := towerTrace_star_mul_self_nonneg _
        have hc : 0 ≤ towerTrace (n := n) (star (X 0 1) * X 0 1) := towerTrace_star_mul_self_nonneg _
        have hd : 0 ≤ towerTrace (n := n) (star (X 1 1) * X 1 1) := towerTrace_star_mul_self_nonneg _
        have h00' : towerTrace (n := n) (star (X 0 0) * X 0 0) = 0 := by linarith
        have h10' : towerTrace (n := n) (star (X 1 0) * X 1 0) = 0 := by linarith
        have h01' : towerTrace (n := n) (star (X 0 1) * X 0 1) = 0 := by linarith
        have h11' : towerTrace (n := n) (star (X 1 1) * X 1 1) = 0 := by linarith
        apply ext_fin2
        · exact (towerTrace_real_star_mul_self_eq_zero_iff (X 0 0)).mp h00'
        · exact (towerTrace_real_star_mul_self_eq_zero_iff (X 0 1)).mp h01'
        · exact (towerTrace_real_star_mul_self_eq_zero_iff (X 1 0)).mp h10'
        · exact (towerTrace_real_star_mul_self_eq_zero_iff (X 1 1)).mp h11'
      · intro hX
        subst hX
        have hz : towerTrace (n := n) (0 : ClTower ℝ n) = 0 := by
          have h := (towerTrace_real_star_mul_self_eq_zero_iff (0 : ClTower ℝ n)).mpr rfl
          simpa using h
        have hzero : star (0 : ClTower ℝ (n + 1)) * (0 : ClTower ℝ (n + 1)) = 0 := by simp
        rw [hzero]
        dsimp [towerTrace]
        simp only [hz, add_zero]

private lemma clTower_smul_def_eq :
    ∀ (n : ℕ) (r : ℝ) (X : ClTower ℝ n),
      (instAlgebraRealClTower n).toSMul.smul r X = (instModuleClTower n).toSMul.smul r X
  | 0, r, x => rfl
  | n + 1, r, X => by
      ext i j
      exact clTower_smul_def_eq n r (X i j)

private lemma normalizedTowerTrace_real_add (n : ℕ) (X Y : ClTower ℝ n) :
    normalizedTowerTrace ℝ n (X + Y) = normalizedTowerTrace ℝ n X + normalizedTowerTrace ℝ n Y :=
  (normalizedTowerTrace ℝ n).map_add X Y

private lemma normalizedTowerTrace_real_smul (n : ℕ) (r : ℝ) (X : ClTower ℝ n) :
    normalizedTowerTrace ℝ n ((instAlgebraRealClTower n).toSMul.smul r X) =
      r * normalizedTowerTrace ℝ n X := by
  rw [clTower_smul_def_eq n r X]
  exact (normalizedTowerTrace ℝ n).map_smul r X

private lemma normalizedTowerTrace_real_apply (n : ℕ) (X : ClTower ℝ n) :
    normalizedTowerTrace ℝ n X = (1 / 2 : ℝ) ^ n * towerTrace (n := n) X := by
  dsimp [normalizedTowerTrace, towerTraceLinear]

/-- Normalized tracial `RealAlgebraicState` on the `ClTower ℝ n` matrix tower, induced
by `normalizedTowerTrace ℝ n`. -/
def clTowerRealState (n : ℕ) : RealAlgebraicState (ClTower ℝ n) where
  toLinearMap :=
    letI : Module ℝ (ClTower ℝ n) := (instAlgebraRealClTower n).toModule
    { toFun := fun X => normalizedTowerTrace ℝ n X
      map_add' := fun X Y => normalizedTowerTrace_real_add n X Y
      map_smul' := fun r X => normalizedTowerTrace_real_smul n r X }
  normalized := normalizedTowerTrace_one ℝ n
  positive := normalizedTowerTrace_star_mul_self_nonneg ℝ n
  symmetric x y := by
    change normalizedTowerTrace ℝ n (star y * x) = normalizedTowerTrace ℝ n (star x * y)
    rw [normalizedTowerTrace_real_apply, normalizedTowerTrace_real_apply,
      ← towerTrace_real_star n (star y * x), star_mul, star_star]

/-- **Exact Faithfulness of `clTowerRealState`**: the GNS null ideal of `normalizedTowerTrace ℝ n`
on `ClTower ℝ n` reduces to `{0}` at every tower depth `n : ℕ`. -/
theorem clTowerRealState_gnsNullSet_eq_zero (n : ℕ) (X : ClTower ℝ n) :
    X ∈ (clTowerRealState n).gnsNullSet ↔ X = 0 := by
  change normalizedTowerTrace ℝ n (star X * X) = 0 ↔ X = 0
  rw [normalizedTowerTrace_real_apply]
  have hpow : (1 / 2 : ℝ) ^ n ≠ 0 := by positivity
  rw [mul_eq_zero, or_iff_right hpow]
  exact towerTrace_real_star_mul_self_eq_zero_iff X

/-- Canonical Grothendieck rank homomorphism `Grothendieck ℕ →+ ℝ` induced by `Nat.castAddMonoidHom ℝ`. -/
def grothendieckRealRank : Grothendieck ℕ →+ ℝ :=
  grothendieckLift (Nat.castAddMonoidHom ℝ)

@[simp]
theorem grothendieckRealRank_sub (m k : ℕ) :
    grothendieckRealRank (grothendieckMap ℕ m - grothendieckMap ℕ k) = (m : ℝ) - (k : ℝ) := by
  rw [grothendieck_sub_mk, grothendieckRealRank, grothendieckLift_mk]
  rfl

/-- Orthogonal idempotent trace/state additivity in any `RealAlgebraicState A`. -/
theorem orthogonal_idempotent_state_add {A : Type*} [Ring A] [Algebra ℝ A]
    [StarRing A] [StarModule ℝ A] (F : RealAlgebraicState A) {p q : A}
    (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0) :
    (p + q) * (p + q) = p + q ∧ F.eval (p + q) = F.eval p + F.eval q := by
  refine ⟨?_, F.eval_add p q⟩
  calc
    (p + q) * (p + q) = p * p + p * q + q * p + q * q := by noncomm_ring
    _ = p + 0 + 0 + q := by rw [hp, hpq, hqp, hq]
    _ = p + q := by abel

end ClTowerGNSAndGrothendieck

/-! ### 2. Strict Scalar Mean Hierarchy (`harmonic ≤ geom ≤ log ≤ arith`) -/

section ScalarMeans

/-- Harmonic mean `2 p q / (p + q)` (Morozova–Chentsov weight for RLD metric). -/
def harmonicMean (p q : ℝ) : ℝ :=
  2 * p * q / (p + q)

/-- Geometric mean `√(p q)` (Wigner–Yanase–Dyson symmetric geometric metric). -/
def geomMean (p q : ℝ) : ℝ :=
  Real.sqrt (p * q)

/-- Logarithmic mean `(p - q) / (log p - log q)` (Kubo–Mori–Bogoliubov weight). -/
def logMean (p q : ℝ) : ℝ :=
  if p = q then p else (p - q) / (Real.log p - Real.log q)

/-- Arithmetic mean `(p + q) / 2` (Helstrom–SLD metric weight). -/
def arithMean (p q : ℝ) : ℝ :=
  (p + q) / 2

lemma harmonicMean_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : 0 < harmonicMean p q := by
  unfold harmonicMean
  exact div_pos (mul_pos (mul_pos two_pos hp) hq) (add_pos hp hq)

lemma geomMean_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : 0 < geomMean p q :=
  Real.sqrt_pos.mpr (mul_pos hp hq)

lemma logMean_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : 0 < logMean p q := by
  unfold logMean
  split_ifs with h
  · exact hp
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · exact div_pos_of_neg_of_neg (sub_neg.mpr hlt) (sub_neg.mpr (Real.log_lt_log hp hlt))
    · exact div_pos (sub_pos.mpr hgt) (sub_pos.mpr (Real.log_lt_log hq hgt))

lemma arithMean_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : 0 < arithMean p q := by
  unfold arithMean
  exact div_pos (add_pos hp hq) two_pos

lemma logMean_symm (p q : ℝ) : logMean p q = logMean q p := by
  unfold logMean
  by_cases h : p = q
  · subst h; simp
  · have h' : q ≠ p := Ne.symm h
    simp only [h, h', ↓reduceIte]
    have hnum : p - q = -(q - p) := by ring
    have hden : Real.log p - Real.log q = -(Real.log q - Real.log p) := by ring
    rw [hnum, hden, neg_div_neg_eq]

lemma geomMean_symm (p q : ℝ) : geomMean p q = geomMean q p := by
  simp [geomMean, mul_comm]

lemma arithMean_symm (p q : ℝ) : arithMean p q = arithMean q p := by
  simp [arithMean, add_comm]

lemma harmonicMean_le_geomMean {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    harmonicMean p q ≤ geomMean p q := by
  unfold harmonicMean geomMean
  have hsq : 0 ≤ (Real.sqrt p - Real.sqrt q) ^ 2 := sq_nonneg _
  have hsum : 0 < p + q := by linarith
  have hid : p + q - 2 * Real.sqrt (p * q) = (Real.sqrt p - Real.sqrt q) ^ 2 := by
    rw [Real.sqrt_mul hp.le]
    nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hq.le]
  have hmul : 2 * p * q ≤ Real.sqrt (p * q) * (p + q) := by
    have hsp : Real.sqrt (p * q) * (Real.sqrt (p * q) * 2) = 2 * p * q := by
      nlinarith [Real.sq_sqrt (mul_nonneg hp.le hq.le)]
    have hge : 0 ≤ Real.sqrt (p * q) * (Real.sqrt p - Real.sqrt q) ^ 2 :=
      mul_nonneg (Real.sqrt_nonneg _) hsq
    nlinarith [hid, hsp, hge]
  exact (div_le_iff₀ hsum).mpr hmul

lemma harmonicMean_lt_geomMean_of_ne {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q) :
    harmonicMean p q < geomMean p q := by
  unfold harmonicMean geomMean
  have hsum : 0 < p + q := by linarith
  have hsne : Real.sqrt p ≠ Real.sqrt q := by
    intro heq
    exact hne ((Real.sqrt_inj hp.le hq.le).mp heq)
  have hsq_pos : 0 < (Real.sqrt p - Real.sqrt q) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hsne)
  have hid : p + q - 2 * Real.sqrt (p * q) = (Real.sqrt p - Real.sqrt q) ^ 2 := by
    rw [Real.sqrt_mul hp.le]
    nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hq.le]
  have hsp : Real.sqrt (p * q) * (Real.sqrt (p * q) * 2) = 2 * p * q := by
    nlinarith [Real.sq_sqrt (mul_nonneg hp.le hq.le)]
  have hlt : 0 < Real.sqrt (p * q) * (Real.sqrt p - Real.sqrt q) ^ 2 :=
    mul_pos (Real.sqrt_pos.mpr (mul_pos hp hq)) hsq_pos
  have hmul : 2 * p * q < Real.sqrt (p * q) * (p + q) := by nlinarith [hid, hsp, hlt]
  exact (div_lt_iff₀ hsum).mpr hmul

private lemma two_mul_lt_sinh_two {u : ℝ} (hu : 0 < u) :
    2 * u < Real.exp u - Real.exp (-u) := by
  let φ : ℝ → ℝ := fun x => Real.exp x - Real.exp (-x) - 2 * x
  have hderiv (x : ℝ) : HasDerivAt φ (Real.exp x + Real.exp (-x) - 2) x := by
    have h1 := Real.hasDerivAt_exp x
    have h2 : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-x)) x := by
      simpa [Function.comp_def] using (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg
    have h3 : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    simpa [φ, sub_eq_add_neg, add_assoc] using (h1.fun_sub h2).fun_sub h3
  have hcont : ContinuousOn φ (Set.Ici (0 : ℝ)) :=
    (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
  have hpos : ∀ x ∈ interior (Set.Ici (0 : ℝ)), 0 < deriv φ x := by
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hderiv x).deriv]
    have hhalf : Real.exp (-(x / 2)) < Real.exp (x / 2) := Real.exp_lt_exp.mpr (by linarith)
    have hsq : 0 < (Real.exp (x / 2) - Real.exp (-(x / 2))) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hhalf.ne')
    have hid :
        Real.exp x + Real.exp (-x) - 2 = (Real.exp (x / 2) - Real.exp (-(x / 2))) ^ 2 := by
      have e1 : Real.exp (x / 2) ^ 2 = Real.exp x := by
        rw [sq, ← Real.exp_add]; ring_nf
      have e2 : Real.exp (-(x / 2)) ^ 2 = Real.exp (-x) := by
        rw [sq, ← Real.exp_add]; ring_nf
      have e3 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [e1, e2, e3]
    rwa [hid]
  have hmono := strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) hcont hpos
  have hval := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu.le) hu
  dsimp [φ] at hval
  simp only [neg_zero, Real.exp_zero, sub_self, mul_zero] at hval
  linarith

private lemma sinh_two_lt_mul_cosh_two {u : ℝ} (hu : 0 < u) :
    Real.exp u - Real.exp (-u) < u * (Real.exp u + Real.exp (-u)) := by
  let ψ : ℝ → ℝ := fun x => x * (Real.exp x + Real.exp (-x)) - (Real.exp x - Real.exp (-x))
  have hderiv (x : ℝ) : HasDerivAt ψ (x * (Real.exp x - Real.exp (-x))) x := by
    have h1 := Real.hasDerivAt_exp x
    have h2 : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-x)) x := by
      simpa [Function.comp_def] using (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg
    have hsum : HasDerivAt (fun t => Real.exp t + Real.exp (-t)) (Real.exp x - Real.exp (-x)) x := by
      simpa [sub_eq_add_neg] using h1.fun_add h2
    have hprod := (hasDerivAt_id x).fun_mul hsum
    have hdiff : HasDerivAt (fun t => Real.exp t - Real.exp (-t)) (Real.exp x + Real.exp (-x)) x := by
      simpa [sub_eq_add_neg] using h1.fun_sub h2
    have hraw := hprod.fun_sub hdiff
    have hid :
        1 * (Real.exp x + Real.exp (-x)) + x * (Real.exp x - Real.exp (-x)) -
            (Real.exp x + Real.exp (-x)) =
          x * (Real.exp x - Real.exp (-x)) := by ring
    simpa [ψ, hid] using hraw
  have hcont : ContinuousOn ψ (Set.Ici (0 : ℝ)) :=
    (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
  have hpos : ∀ x ∈ interior (Set.Ici (0 : ℝ)), 0 < deriv ψ x := by
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hderiv x).deriv]
    have hx_gt : Real.exp (-x) < Real.exp x := Real.exp_lt_exp.mpr (by linarith)
    exact mul_pos hx (sub_pos.mpr hx_gt)
  have hmono := strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) hcont hpos
  have hval := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu.le) hu
  dsimp [ψ] at hval
  simp only [zero_mul, neg_zero, Real.exp_zero, sub_self] at hval
  linarith

private lemma geom_hyperbolic_decomp {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    let m := Real.sqrt (p * q)
    let u := (Real.log p - Real.log q) / 2
    p = m * Real.exp u ∧ q = m * Real.exp (-u) := by
  intro m u
  have hm_pos : 0 < m := Real.sqrt_pos.mpr (mul_pos hp hq)
  have h2u : 2 * u = Real.log p - Real.log q := by dsimp [u]; ring
  have he2u : Real.exp u ^ 2 = p / q := by
    rw [sq, ← Real.exp_add, show u + u = 2 * u by ring, h2u, Real.exp_sub,
      Real.exp_log hp, Real.exp_log hq]
  have hem2u : Real.exp (-u) ^ 2 = q / p := by
    rw [sq, ← Real.exp_add, show (-u) + (-u) = -(2 * u) by ring, Real.exp_neg, h2u,
      Real.exp_sub, Real.exp_log hp, Real.exp_log hq, inv_div]
  have hm_sq : m ^ 2 = p * q := Real.sq_sqrt (mul_pos hp hq).le
  have hp_sq : (m * Real.exp u) ^ 2 = p ^ 2 := by
    rw [mul_pow, hm_sq, he2u]
    field_simp [hq.ne']
  have hq_sq : (m * Real.exp (-u)) ^ 2 = q ^ 2 := by
    rw [mul_pow, hm_sq, hem2u]
    field_simp [hp.ne']
  refine ⟨?_, ?_⟩
  · exact (sq_eq_sq₀ hp.le (mul_pos hm_pos (Real.exp_pos u)).le).mp hp_sq.symm
  · exact (sq_eq_sq₀ hq.le (mul_pos hm_pos (Real.exp_pos (-u))).le).mp hq_sq.symm

lemma geomMean_lt_logMean_of_ne {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q) :
    geomMean p q < logMean p q := by
  suffices h : ∀ a b : ℝ, 0 < a → 0 < b → b < a → geomMean a b < logMean a b by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [geomMean_symm, logMean_symm]
      exact h q p hq hp hlt
    · exact h p q hp hq hgt
  intro a b ha hb hba
  let m := Real.sqrt (a * b)
  let u := (Real.log a - Real.log b) / 2
  have hu : 0 < u := div_pos (sub_pos.mpr (Real.log_lt_log hb hba)) two_pos
  have hm : 0 < m := Real.sqrt_pos.mpr (mul_pos ha hb)
  rcases geom_hyperbolic_decomp ha hb with ⟨ha_eq, hb_eq⟩
  have hsinh := two_mul_lt_sinh_two hu
  have hdiv : 1 < (Real.exp u - Real.exp (-u)) / (2 * u) :=
    (one_lt_div (by positivity)).mpr hsinh
  have hmul : m < m * ((Real.exp u - Real.exp (-u)) / (2 * u)) :=
    lt_mul_of_one_lt_right hm hdiv
  have hlogm : logMean a b = m * ((Real.exp u - Real.exp (-u)) / (2 * u)) := by
    unfold logMean
    simp only [hba.ne', ↓reduceIte]
    have ha' : a - b = m * (Real.exp u - Real.exp (-u)) := by nlinarith [ha_eq, hb_eq]
    have hden : Real.log a - Real.log b = 2 * u := by dsimp [u]; ring
    rw [ha', hden, mul_div_assoc]
  rw [hlogm]
  exact hmul

lemma geomMean_le_logMean {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    geomMean p q ≤ logMean p q := by
  by_cases h : p = q
  · subst h
    simp [geomMean, logMean, Real.sqrt_mul_self hp.le]
  · exact (geomMean_lt_logMean_of_ne hp hq h).le

lemma logMean_lt_arithMean_of_ne {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q) :
    logMean p q < arithMean p q := by
  suffices h : ∀ a b : ℝ, 0 < a → 0 < b → b < a → logMean a b < arithMean a b by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [logMean_symm, arithMean_symm]
      exact h q p hq hp hlt
    · exact h p q hp hq hgt
  intro a b ha hb hba
  let m := Real.sqrt (a * b)
  let u := (Real.log a - Real.log b) / 2
  have hu : 0 < u := div_pos (sub_pos.mpr (Real.log_lt_log hb hba)) two_pos
  have hm : 0 < m := Real.sqrt_pos.mpr (mul_pos ha hb)
  rcases geom_hyperbolic_decomp ha hb with ⟨ha_eq, hb_eq⟩
  have hcosh := sinh_two_lt_mul_cosh_two hu
  have hdiv : (Real.exp u - Real.exp (-u)) / (2 * u) < (Real.exp u + Real.exp (-u)) / 2 := by
    rw [div_lt_div_iff₀ (by positivity) two_pos]
    linarith
  have hmul : m * ((Real.exp u - Real.exp (-u)) / (2 * u)) < m * ((Real.exp u + Real.exp (-u)) / 2) :=
    mul_lt_mul_of_pos_left hdiv hm
  have hlogm : logMean a b = m * ((Real.exp u - Real.exp (-u)) / (2 * u)) := by
    unfold logMean
    simp only [hba.ne', ↓reduceIte]
    have ha' : a - b = m * (Real.exp u - Real.exp (-u)) := by nlinarith [ha_eq, hb_eq]
    have hden : Real.log a - Real.log b = 2 * u := by dsimp [u]; ring
    rw [ha', hden, mul_div_assoc]
  have harith : arithMean a b = m * ((Real.exp u + Real.exp (-u)) / 2) := by
    unfold arithMean
    have ha' : a + b = m * (Real.exp u + Real.exp (-u)) := by nlinarith [ha_eq, hb_eq]
    rw [ha', mul_div_assoc]
  rw [hlogm, harith]
  exact hmul

lemma logMean_le_arithMean {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    logMean p q ≤ arithMean p q := by
  by_cases h : p = q
  · subst h
    simp [logMean, arithMean]
  · exact (logMean_lt_arithMean_of_ne hp hq h).le

end ScalarMeans

/-! ### 3. Morozova–Chentsov–Petz Quantum Fisher Metric Hierarchy -/

section PetzMonotoneMetrics

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complex diagonal spectral representation `diag(ρ)` of `FaithfulDensityState n`. -/
def diagDensityMatrix (ρ : FaithfulDensityState n) : Matrix n n ℂ :=
  Matrix.diagonal (fun i => (ρ.eigenvalues i : ℂ))

lemma bkmWeight_eq_logMean (ρ : FaithfulDensityState n) (i j : n) :
    ρ.bkmWeight i j = logMean (ρ.eigenvalues i) (ρ.eigenvalues j) := rfl

/-- Helstrom–SLD tangent quantum Fisher metric on complex tangent variations `X`:
`∑_{i,j} |X_{ij}|^2 / ((p_i + p_j) / 2)`. -/
def sldTangentMetric (ρ : FaithfulDensityState n) (X : Matrix n n ℂ) : ℝ :=
  ∑ i : n, ∑ j : n, Complex.normSq (X i j) / arithMean (ρ.eigenvalues i) (ρ.eigenvalues j)

/-- Kubo–Mori–Bogoliubov (BKM) tangent quantum Fisher metric:
`∑_{i,j} |X_{ij}|^2 / logMean(p_i, p_j)`. -/
def bkmTangentMetric (ρ : FaithfulDensityState n) (X : Matrix n n ℂ) : ℝ :=
  ∑ i : n, ∑ j : n, Complex.normSq (X i j) / ρ.bkmWeight i j

/-- Symmetric geometric-mean (Wigner–Yanase–Dyson `α = 0` Petz) quantum Fisher metric:
`∑_{i,j} |X_{ij}|^2 / √(p_i p_j)`. -/
def geomTangentMetric (ρ : FaithfulDensityState n) (X : Matrix n n ℂ) : ℝ :=
  ∑ i : n, ∑ j : n, Complex.normSq (X i j) / geomMean (ρ.eigenvalues i) (ρ.eigenvalues j)

/-- Right Logarithmic Derivative (RLD) Petz tangent quantum Fisher metric:
`∑_{i,j} |X_{ij}|^2 / (2 p_i p_j / (p_i + p_j))`. -/
def rldTangentMetric (ρ : FaithfulDensityState n) (X : Matrix n n ℂ) : ℝ :=
  ∑ i : n, ∑ j : n, Complex.normSq (X i j) / harmonicMean (ρ.eigenvalues i) (ρ.eigenvalues j)

/-- Explicit spectral Lyapunov solver `L_{ij} = (2 / (p_i + p_j)) X_{ij}` inverting
`X = (1 / 2) {ρ, L}` for `diagDensityMatrix ρ`. -/
def sldLyapunovSolve (ρ : FaithfulDensityState n) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.of (fun i j => ((2 / (ρ.eigenvalues i + ρ.eigenvalues j) : ℝ) : ℂ) * X i j)

/-- `sldLyapunovSolve ρ X` genuinely solves the SLD Lyapunov equation
`IsSLD (diagDensityMatrix ρ) X (sldLyapunovSolve ρ X)`. -/
theorem sldLyapunovSolve_isSLD (ρ : FaithfulDensityState n) (X : Matrix n n ℂ) :
    IsSLD (diagDensityMatrix ρ) X (sldLyapunovSolve ρ X) := by
  unfold IsSLD InfoGeometry.QuantumGeometry.SLD.jordanProd diagDensityMatrix sldLyapunovSolve
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.of_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun k _ hki => by simp [hki.symm])
    (fun hm => (hm (Finset.mem_univ i)).elim)]
  rw [Finset.sum_eq_single j (fun k _ hkj => by simp [hkj])
    (fun hm => (hm (Finset.mem_univ j)).elim)]
  simp only [↓reduceIte]
  have hsum_pos : ρ.eigenvalues i + ρ.eigenvalues j ≠ 0 :=
    (add_pos (ρ.p_pos i) (ρ.p_pos j)).ne'
  have hc : ((ρ.eigenvalues i : ℂ) + (ρ.eigenvalues j : ℂ)) ≠ 0 := by
    exact_mod_cast hsum_pos
  have hid :
      ((1 / 2 : ℂ) * ((ρ.eigenvalues i : ℂ) * (((2 / (ρ.eigenvalues i + ρ.eigenvalues j) : ℝ) : ℂ) * X i j) +
          ((2 / (ρ.eigenvalues i + ρ.eigenvalues j) : ℝ) : ℂ) * X i j * (ρ.eigenvalues j : ℂ))) =
        X i j := by
    push_cast
    field_simp [hc]
  exact hid.symm

/-- Uniqueness of the SLD solution in the faithful spectral basis. -/
theorem sldLyapunovSolve_unique (ρ : FaithfulDensityState n) (X L : Matrix n n ℂ) :
    IsSLD (diagDensityMatrix ρ) X L ↔ L = sldLyapunovSolve ρ X := by
  constructor
  · intro hL
    ext i j
    have hij := congr_fun (congr_fun hL i) j
    dsimp [IsSLD, InfoGeometry.QuantumGeometry.SLD.jordanProd, diagDensityMatrix,
      sldLyapunovSolve] at hij ⊢
    simp only [Matrix.mul_apply, Matrix.diagonal_apply] at hij ⊢
    rw [Finset.sum_eq_single i (fun k _ hki => by simp [hki.symm])
      (fun hm => (hm (Finset.mem_univ i)).elim)] at hij
    rw [Finset.sum_eq_single j (fun k _ hkj => by simp [hkj])
      (fun hm => (hm (Finset.mem_univ j)).elim)] at hij
    simp only [↓reduceIte] at hij
    have hsum_pos : ρ.eigenvalues i + ρ.eigenvalues j ≠ 0 :=
      (add_pos (ρ.p_pos i) (ρ.p_pos j)).ne'
    have hc : ((ρ.eigenvalues i : ℂ) + (ρ.eigenvalues j : ℂ)) ≠ 0 := by
      exact_mod_cast hsum_pos
    have hmul : X i j = ((1 / 2 : ℂ) * ((ρ.eigenvalues i : ℂ) + (ρ.eigenvalues j : ℂ))) * L i j := by
      calc
        X i j = (1 / 2 : ℂ) * ((ρ.eigenvalues i : ℂ) * L i j + L i j * (ρ.eigenvalues j : ℂ)) := hij
        _ = (1 / 2 : ℂ) * ((ρ.eigenvalues i : ℂ) + (ρ.eigenvalues j : ℂ)) * L i j := by ring
    push_cast
    rw [hmul]
    field_simp [hc]
  · intro hEq
    rw [hEq]
    exact sldLyapunovSolve_isSLD ρ X

private lemma sld_re_term_aux (p q nx : ℝ) :
    p * (2 / (p + q) * (2 / (p + q)) * nx) = p * (4 / (p + q) ^ 2) * nx := by
  have h : (2 : ℝ) / (p + q) * (2 / (p + q)) = 4 / (p + q) ^ 2 := by
    rw [div_mul_div_comm, ← sq (p + q)]
    norm_num
  rw [h]
  ring

private lemma sld_avg_term_aux {p q : ℝ} (nx : ℝ) (hpos : p + q ≠ 0) :
    2 * (nx / ((p + q) / 2)) =
      p * (4 / (p + q) ^ 2) * nx + q * (4 / (p + q) ^ 2) * nx := by
  field_simp [hpos]
  ring

private lemma eq_of_two_mul_eq_add_self {a b : ℝ} (h : (2 : ℝ) * a = b + b) : b = a := by
  linarith [h]

private lemma onsager_term_aux {w : ℝ} (a : ℝ) (hw : w ≠ 0) :
    a * w * (a * w) / w = a * a * w := by
  field_simp [hw]

private lemma arithMean_self (p : ℝ) : arithMean p p = p := by
  unfold arithMean
  ring

private lemma harmonicMean_self {p : ℝ} (hp : p ≠ 0) : harmonicMean p p = p := by
  unfold harmonicMean
  field_simp [hp]
  ring

private lemma complex_mul_star_eq_normSq (z : ℂ) :
    z * star z = (Complex.normSq z : ℂ) := by
  apply Complex.ext
  · simp [Complex.normSq_apply]
  · simp
    ring

/-- On any Hermitian tangent operator `X` (`Xᴴ = X`), the Helstrom–SLD inner product
`sldFisherInner` evaluated on the Lyapunov solution `sldLyapunovSolve ρ X` equals
`sldTangentMetric ρ X` identically. -/
theorem sldFisherInner_sldLyapunovSolve_eq (ρ : FaithfulDensityState n)
    (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    (sldFisherInner (diagDensityMatrix ρ) (sldLyapunovSolve ρ X) (sldLyapunovSolve ρ X)).re =
      sldTangentMetric ρ X := by
  let L := sldLyapunovSolve ρ X
  rw [sldFisherInner_self_commuting (diagDensityMatrix ρ) L]
  have htr :
      Matrix.trace (diagDensityMatrix ρ * (L * L)) =
        ∑ i : n, (ρ.eigenvalues i : ℂ) * ∑ j : n, L i j * L j i := by
    unfold Matrix.trace Matrix.diag
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [diagDensityMatrix, Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [hki.symm]
    · intro hm
      exact (hm (Finset.mem_univ i)).elim
  have hL_herm (i j : n) : L j i = star (L i j) := by
    have hXj : X j i = star (X i j) := by
      have := congr_fun (congr_fun hX.eq j) i
      simpa [Matrix.conjTranspose_apply] using this.symm
    dsimp [L, sldLyapunovSolve]
    rw [map_mul, Complex.conj_ofReal, ← Complex.star_def, ← hXj, add_comm]
  have hmul_re (i j : n) :
      ((ρ.eigenvalues i : ℂ) * (L i j * L j i)).re =
        ρ.eigenvalues i * (4 / (ρ.eigenvalues i + ρ.eigenvalues j) ^ 2) * Complex.normSq (X i j) := by
    rw [hL_herm i j, complex_mul_star_eq_normSq]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
    dsimp [L, sldLyapunovSolve]
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    exact sld_re_term_aux (ρ.eigenvalues i) (ρ.eigenvalues j) (Complex.normSq (X i j))
  have hsum_re :
      (Matrix.trace (diagDensityMatrix ρ * (L * L))).re =
        ∑ i : n, ∑ j : n,
          ρ.eigenvalues i * (4 / (ρ.eigenvalues i + ρ.eigenvalues j) ^ 2) * Complex.normSq (X i j) := by
    rw [htr, Complex.re_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact hmul_re i j
  rw [hsum_re]
  have hnorm_symm (i j : n) : Complex.normSq (X j i) = Complex.normSq (X i j) := by
    have hXj : X j i = star (X i j) := by
      have := congr_fun (congr_fun hX.eq j) i
      simpa [Matrix.conjTranspose_apply] using this.symm
    rw [hXj, Complex.star_def, Complex.normSq_conj]
  let S := ∑ i : n, ∑ j : n,
      ρ.eigenvalues i * (4 / (ρ.eigenvalues i + ρ.eigenvalues j) ^ 2) * Complex.normSq (X i j)
  have hswap :
      S = ∑ i : n, ∑ j : n,
        ρ.eigenvalues j * (4 / (ρ.eigenvalues i + ρ.eigenvalues j) ^ 2) * Complex.normSq (X i j) := by
    dsimp [S]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hnorm_symm j i, add_comm (ρ.eigenvalues j) (ρ.eigenvalues i)]
  have havg : (2 : ℝ) * sldTangentMetric ρ X = S + S := by
    conv_rhs => rhs; rw [hswap]
    dsimp [S]
    simp_rw [← Finset.sum_add_distrib]
    unfold sldTangentMetric arithMean
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    have hpos : ρ.eigenvalues i + ρ.eigenvalues j ≠ 0 :=
      (add_pos (ρ.p_pos i) (ρ.p_pos j)).ne'
    exact sld_avg_term_aux (Complex.normSq (X i j)) hpos
  exact eq_of_two_mul_eq_add_self havg

/-- Onsager–Kubo–Mori tangent perturbation corresponding to observable `A : Matrix n n ℝ`:
`X_{ij} = A_{ji} * bkmWeight(p_i, p_j)`. -/
def bkmOnsagerVariation (ρ : FaithfulDensityState n) (A : Matrix n n ℝ) : Matrix n n ℂ :=
  Matrix.of (fun i j => ((A j i * ρ.bkmWeight i j : ℝ) : ℂ))

/-- Exact duality between `bkmTangentMetric` on tangent state perturbations and
`FaithfulDensityState.bkmInnerProduct` on dual observables. -/
theorem bkmTangentMetric_onsager_eq (ρ : FaithfulDensityState n) (A : Matrix n n ℝ) :
    bkmTangentMetric ρ (bkmOnsagerVariation ρ A) = ρ.bkmInnerProduct A A := by
  unfold bkmTangentMetric FaithfulDensityState.bkmInnerProduct bkmOnsagerVariation
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  simp only [Matrix.of_apply, Complex.normSq_ofReal]
  exact onsager_term_aux (A j i) (ne_of_gt (ρ.bkm_weight_pos i j))

/-- **Morozova–Chentsov–Petz Metric Hierarchy Theorem**: for every faithful density matrix `ρ`
and arbitrary complex tangent variation `X : Matrix n n ℂ`,
`SLD ≤ BKM ≤ GeomMean ≤ RLD`. -/
theorem petz_monotone_metric_hierarchy (ρ : FaithfulDensityState n) (X : Matrix n n ℂ) :
    sldTangentMetric ρ X ≤ bkmTangentMetric ρ X ∧
      bkmTangentMetric ρ X ≤ geomTangentMetric ρ X ∧
      geomTangentMetric ρ X ≤ rldTangentMetric ρ X := by
  refine ⟨?_, ?_, ?_⟩
  · refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    exact div_le_div_of_nonneg_left (Complex.normSq_nonneg _)
      (ρ.bkm_weight_pos i j) (logMean_le_arithMean (ρ.p_pos i) (ρ.p_pos j))
  · refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    exact div_le_div_of_nonneg_left (Complex.normSq_nonneg _)
      (geomMean_pos (ρ.p_pos i) (ρ.p_pos j)) (geomMean_le_logMean (ρ.p_pos i) (ρ.p_pos j))
  · refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    exact div_le_div_of_nonneg_left (Complex.normSq_nonneg _)
      (harmonicMean_pos (ρ.p_pos i) (ρ.p_pos j)) (harmonicMean_le_geomMean (ρ.p_pos i) (ρ.p_pos j))

/-- Spectral commutativity characterization `[diag(ρ), X] = 0` iff all off-eigenspace entries
vanish. -/
theorem diagDensityMatrix_commutes_iff (ρ : FaithfulDensityState n) (X : Matrix n n ℂ) :
    diagDensityMatrix ρ * X = X * diagDensityMatrix ρ ↔
      ∀ i j : n, ρ.eigenvalues i ≠ ρ.eigenvalues j → X i j = 0 := by
  constructor
  · intro hcomm i j hne
    have hij := congr_fun (congr_fun hcomm i) j
    simp only [diagDensityMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
    have hdiff : ((ρ.eigenvalues i : ℂ) - (ρ.eigenvalues j : ℂ)) * X i j = 0 := by
      linear_combination hij
    have hne_c : (ρ.eigenvalues i : ℂ) - (ρ.eigenvalues j : ℂ) ≠ 0 := by
      intro hz
      apply hne
      have hcz : (ρ.eigenvalues i : ℂ) = (ρ.eigenvalues j : ℂ) := sub_eq_zero.mp hz
      exact_mod_cast hcz
    exact (mul_eq_zero.mp hdiff).resolve_left hne_c
  · intro hzero
    ext i j
    simp only [diagDensityMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases heq : ρ.eigenvalues i = ρ.eigenvalues j
    · rw [heq, mul_comm]
    · rw [hzero i j heq, mul_zero, zero_mul]

/-- **Exact Quantum-to-Classical Metric Collapse (`SLD = BKM ↔ [ρ, X] = 0`)**:
the minimal Helstrom–SLD metric agrees with the Kubo–Mori–Bogoliubov metric on `X` if and only
if `X` commutes with `ρ`. -/
theorem sld_eq_bkm_iff_commutes (ρ : FaithfulDensityState n) (X : Matrix n n ℂ) :
    sldTangentMetric ρ X = bkmTangentMetric ρ X ↔
      diagDensityMatrix ρ * X = X * diagDensityMatrix ρ := by
  rw [diagDensityMatrix_commutes_iff]
  let gap (i j : n) : ℝ :=
    Complex.normSq (X i j) / ρ.bkmWeight i j -
      Complex.normSq (X i j) / arithMean (ρ.eigenvalues i) (ρ.eigenvalues j)
  have hgap_nonneg (i j : n) : 0 ≤ gap i j := by
    dsimp [gap]
    have hle := div_le_div_of_nonneg_left (Complex.normSq_nonneg (X i j))
      (ρ.bkm_weight_pos i j) (logMean_le_arithMean (ρ.p_pos i) (ρ.p_pos j))
    exact sub_nonneg.mpr hle
  have hsum_eq : bkmTangentMetric ρ X - sldTangentMetric ρ X = ∑ i : n, ∑ j : n, gap i j := by
    unfold bkmTangentMetric sldTangentMetric gap
    simp_rw [Finset.sum_sub_distrib]
  constructor
  · intro hEq i j hne
    have htot0 : ∑ i' : n, ∑ j' : n, gap i' j' = 0 := by rw [← hsum_eq, hEq, sub_self]
    have hi0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i' _ =>
      Finset.sum_nonneg (fun j' _ => hgap_nonneg i' j'))).mp htot0 i (Finset.mem_univ i)
    have hij0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j' _ => hgap_nonneg i j')).mp hi0 j
      (Finset.mem_univ j)
    have hlt := logMean_lt_arithMean_of_ne (ρ.p_pos i) (ρ.p_pos j) hne
    have hrec : 1 / arithMean (ρ.eigenvalues i) (ρ.eigenvalues j) < 1 / ρ.bkmWeight i j :=
      one_div_lt_one_div_of_lt (ρ.bkm_weight_pos i j) hlt
    have hdiff_pos : 0 < 1 / ρ.bkmWeight i j - 1 / arithMean (ρ.eigenvalues i) (ρ.eigenvalues j) :=
      sub_pos.mpr hrec
    have hfac :
        Complex.normSq (X i j) *
            (1 / ρ.bkmWeight i j - 1 / arithMean (ρ.eigenvalues i) (ρ.eigenvalues j)) = 0 := by
      dsimp [gap] at hij0
      linear_combination hij0
    have hnorm0 : Complex.normSq (X i j) = 0 := (mul_eq_zero.mp hfac).resolve_right hdiff_pos.ne'
    exact Complex.normSq_eq_zero.mp hnorm0
  · intro hzero
    have htot0 : ∑ i : n, ∑ j : n, gap i j = 0 := by
      refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
      by_cases heq : ρ.eigenvalues i = ρ.eigenvalues j
      · have hw1 : ρ.bkmWeight i j = ρ.eigenvalues i := by
          dsimp [FaithfulDensityState.bkmWeight]
          simp [heq]
        have hw2 : arithMean (ρ.eigenvalues i) (ρ.eigenvalues j) = ρ.eigenvalues i := by
          rw [heq]; exact arithMean_self _
        dsimp [gap]
        rw [hw1, hw2, sub_self]
      · simp [gap, hzero i j heq]
    exact (sub_eq_zero.mp (hsum_eq.trans htot0)).symm

/-- **Full Petz Collapse (`SLD = RLD ↔ [ρ, X] = 0`)**:
the minimal (`SLD`) and maximal (`RLD`) Petz monotone metrics coincide on `X` if and only if
`X` commutes with `ρ`. -/
theorem sld_eq_rld_iff_commutes (ρ : FaithfulDensityState n) (X : Matrix n n ℂ) :
    sldTangentMetric ρ X = rldTangentMetric ρ X ↔
      diagDensityMatrix ρ * X = X * diagDensityMatrix ρ := by
  have hchain := petz_monotone_metric_hierarchy ρ X
  constructor
  · intro hEq
    exact (sld_eq_bkm_iff_commutes ρ X).mp
      (le_antisymm hchain.1 (hEq ▸ le_trans hchain.2.1 hchain.2.2))
  · intro hcomm
    have hzero := (diagDensityMatrix_commutes_iff ρ X).mp hcomm
    unfold sldTangentMetric rldTangentMetric
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases heq : ρ.eigenvalues i = ρ.eigenvalues j
    · have ha : arithMean (ρ.eigenvalues i) (ρ.eigenvalues j) = ρ.eigenvalues i := by
        rw [heq]; exact arithMean_self _
      have hh : harmonicMean (ρ.eigenvalues i) (ρ.eigenvalues j) = ρ.eigenvalues i := by
        rw [heq]
        exact harmonicMean_self (ρ.p_pos j).ne'
      rw [ha, hh]
    · simp [hzero i j heq]

/-- On diagonal (commuting/classical) variations `X = diag(dx)`, all four Petz quantum Fisher
metrics collapse identically to the classical Chentsov–Fisher metric `∑ i, (dx i)^2 / p_i`. -/
theorem petz_metrics_diagonal_eq_classical_fisher
    (ρ : FaithfulDensityState n) (dx : n → ℝ) :
    let X : Matrix n n ℂ := Matrix.diagonal (fun i => (dx i : ℂ))
    sldTangentMetric ρ X = ∑ i : n, dx i ^ 2 / ρ.eigenvalues i ∧
      bkmTangentMetric ρ X = ∑ i : n, dx i ^ 2 / ρ.eigenvalues i ∧
      geomTangentMetric ρ X = ∑ i : n, dx i ^ 2 / ρ.eigenvalues i ∧
      rldTangentMetric ρ X = ∑ i : n, dx i ^ 2 / ρ.eigenvalues i := by
  intro X
  have hsld : sldTangentMetric ρ X = ∑ i : n, dx i ^ 2 / ρ.eigenvalues i := by
    unfold sldTangentMetric
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · dsimp [X, arithMean]
      simp [Complex.normSq_ofReal, sq]
    · intro j _ hji
      dsimp [X]
      simp [Matrix.diagonal_apply_ne _ hji.symm]
    · intro hm
      exact (hm (Finset.mem_univ i)).elim
  have hcomm : diagDensityMatrix ρ * X = X * diagDensityMatrix ρ := by
    ext i j
    by_cases hij : i = j <;> simp [diagDensityMatrix, X, hij, mul_comm]
  have hrld_eq := (sld_eq_rld_iff_commutes ρ X).mpr hcomm
  have hchain := petz_monotone_metric_hierarchy ρ X
  refine ⟨hsld, ?_, ?_, ?_⟩
  · exact (le_antisymm hchain.1 (hrld_eq ▸ le_trans hchain.2.1 hchain.2.2)).symm.trans hsld
  · exact (le_antisymm (le_trans hchain.1 hchain.2.1) (hrld_eq ▸ hchain.2.2)).symm.trans hsld
  · rw [← hrld_eq, hsld]

end PetzMonotoneMetrics

end InfoGeometry.OperatorAlgebra.GNSRepresentationAndPetzMonotoneMetrics

end section
