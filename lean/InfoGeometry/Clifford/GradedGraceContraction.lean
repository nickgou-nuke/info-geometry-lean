/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Riemannian.CartanMetric
import InfoGeometry.Algebra.FibonacciGrothendieckRing
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# InfoGeometry.Clifford.GradedGraceContraction

Constructive `ℕ`-grade projections, resolution of the identity, golden-ratio
(`φ`) grade-contraction ("Grace") operators, faithful `FibonacciGrothendieckRing`
realizations, Euclidean blade Hilbert inner products, exponential high-grade
Lyapunov decay, proximal Parsimonious Flow variational optimality, and Minkowski
`Cl(3,1)` Krein signature analysis for Clifford algebras.
-/

set_option autoImplicit false

namespace InfoGeometry.Clifford.GradedGraceContraction

open CliffordAlgebra
open InfoGeometry.Riemannian
open InfoGeometry.Algebra.FibonacciGrothendieckRing
open scoped goldenRatio
open scoped DirectSum

section ScalarHelpers

private theorem zpow_neg_succ_mul_exp (m k : ℕ) :
    -(k : ℤ) + -((m * k : ℕ) : ℤ) = -(((m + 1) * k : ℕ) : ℤ) := by
  push_cast
  ring

private theorem zpow_neg_double_exp (m c : ℕ) :
    (-((m * c : ℕ) : ℤ)) + (-((m * c : ℕ) : ℤ)) = -((2 * m * c : ℕ) : ℤ) := by
  push_cast
  ring

private theorem scalar_proximal_completion (x a w : ℝ) (hw : w ≠ 0) :
    ((1 / 2 : ℝ) * ((w - 1) * (x ^ 2)) + (1 / 2 : ℝ) * ((x - a) * (x - a))) -
        ((1 / 2 : ℝ) * ((w - 1) * ((w⁻¹ * a) ^ 2)) +
          (1 / 2 : ℝ) * ((w⁻¹ * a - a) * (w⁻¹ * a - a))) =
      (1 / 2 : ℝ) * ((x - w⁻¹ * a) * (w * (x - w⁻¹ * a))) := by
  field_simp [hw]
  ring

private theorem scalar_lower_bound_of_diff {p q r s : ℝ} (hid : p - q = r) (hle : s ≤ r) :
    q + s ≤ p := by
  linarith [hid, hle]

private theorem scalar_le_and_eq_zero {p q s : ℝ} (hlb : q + s ≤ p) (hnn : 0 ≤ s) :
    q ≤ p ∧ (p = q → s = 0) :=
  ⟨by linarith [hlb, hnn], fun h => by linarith [hlb, hnn, h]⟩

private theorem scalar_two_mul_sig_pair (s x y : ℝ) :
    s * ((x + y) * (x + y)) - s * (x * x) - s * (y * y) = 2 * (s * (x * y)) := by
  ring

private theorem scalar_one_sub_inv_phi_props (hinv : φ ^ (-(1 : ℤ)) = φ - 1)
    (hsq_inv : φ ^ (-(2 : ℤ)) = 2 - φ) :
    1 - φ ^ (-(1 : ℤ)) = 2 - φ ∧
      1 - φ ^ (-(1 : ℤ)) = φ ^ (-(2 : ℤ)) ∧
        0 < 1 - φ ^ (-(1 : ℤ)) ∧
          1 - φ ^ (-(1 : ℤ)) < 1 := by
  have hpos : 0 < φ ^ (-(1 : ℤ)) := zpow_pos Real.goldenRatio_pos _
  refine ⟨by linarith [hinv], by linarith [hinv, hsq_inv], by linarith [hinv, Real.goldenRatio_lt_two],
    by linarith [hpos]⟩

end ScalarHelpers

/-! ## Part A: Constructive ℕ-Grade Projections and Resolution of Identity -/

section GradeProjections

section ExteriorOnly

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- Canonical `R`-linear projection onto the grade-`k` component `⋀[R]^k M`
of `ExteriorAlgebra R M`. -/
noncomputable def exteriorGradeProj (k : ℕ) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  GradedAlgebra.proj (fun i : ℕ => ⋀[R]^i M) k

theorem exteriorGradeProj_mem (k : ℕ) (x : ExteriorAlgebra R M) :
    exteriorGradeProj R M k x ∈ ⋀[R]^k M := by
  simp only [exteriorGradeProj, GradedAlgebra.proj, LinearMap.comp_apply,
    Submodule.coe_subtype]
  exact SetLike.coe_mem _

variable {R M}

theorem exteriorGradeProj_of_mem {k : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^k M) :
    exteriorGradeProj R M k x = x := by
  simp only [exteriorGradeProj, GradedAlgebra.proj_apply]
  rw [DirectSum.decompose_of_mem (fun i : ℕ => ⋀[R]^i M) hx, DirectSum.of_eq_same]

theorem exteriorGradeProj_of_mem_ne {j k : ℕ} (hjk : j ≠ k) {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^j M) :
    exteriorGradeProj R M k x = 0 := by
  simp only [exteriorGradeProj, GradedAlgebra.proj_apply]
  rw [DirectSum.decompose_of_mem (fun i : ℕ => ⋀[R]^i M) hx,
    DirectSum.of_eq_of_ne j k _ hjk.symm]
  rfl

theorem exteriorGradeProj_idem (k : ℕ) (x : ExteriorAlgebra R M) :
    exteriorGradeProj R M k (exteriorGradeProj R M k x) = exteriorGradeProj R M k x :=
  exteriorGradeProj_of_mem (exteriorGradeProj_mem R M k x)

theorem exteriorGradeProj_orthog {j k : ℕ} (hjk : j ≠ k) (x : ExteriorAlgebra R M) :
    exteriorGradeProj R M j (exteriorGradeProj R M k x) = 0 :=
  exteriorGradeProj_of_mem_ne hjk.symm (exteriorGradeProj_mem R M k x)

theorem algebraMap_mem_exteriorPower_zero (r : R) :
    algebraMap R (ExteriorAlgebra R M) r ∈ ⋀[R]^0 M := by
  rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.one_eq_span, Submodule.mem_span_singleton]
  exact ⟨r, (Algebra.algebraMap_eq_smul_one r).symm⟩

theorem ι_mem_exteriorPower_one (m : M) :
    ExteriorAlgebra.ι R m ∈ ⋀[R]^1 M := by
  rw [ExteriorAlgebra.exteriorPower, pow_one]
  exact LinearMap.mem_range_self _ m

theorem exterior_algebraMapInv_of_mem_zero {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^0 M) :
    algebraMap R (ExteriorAlgebra R M) (ExteriorAlgebra.algebraMapInv x) = x := by
  rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.one_eq_span, Submodule.mem_span_singleton]
    at hx
  rcases hx with ⟨r, rfl⟩
  rw [Algebra.smul_def, mul_one]
  exact congrArg (algebraMap R (ExteriorAlgebra R M))
    (AlgHom.commutes (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R M →ₐ[R] R) r)

theorem exterior_algebraMapInv_of_mem_succ {k : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^(k + 1) M) :
    ExteriorAlgebra.algebraMapInv x = 0 := by
  rw [ExteriorAlgebra.exteriorPower, pow_succ] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a _ b hb
    rcases LinearMap.mem_range.mp hb with ⟨m, rfl⟩
    rw [map_mul, show (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R M →ₐ[R] R)
      (ExteriorAlgebra.ι R m) = 0 by simp [ExteriorAlgebra.algebraMapInv], mul_zero]
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

theorem exteriorGradeProj_zero_eq_algebraMap_algebraMapInv (x : ExteriorAlgebra R M) :
    exteriorGradeProj R M 0 x =
      algebraMap R (ExteriorAlgebra R M) (ExteriorAlgebra.algebraMapInv x) := by
  induction x using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[R]^i M) with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb]
  | homogeneous hm =>
    rename_i i
    rcases hm with ⟨a, ha⟩
    cases i with
    | zero =>
      rw [exteriorGradeProj_of_mem ha, exterior_algebraMapInv_of_mem_zero ha]
    | succ k =>
      rw [exteriorGradeProj_of_mem_ne (Nat.succ_ne_zero k) ha,
        exterior_algebraMapInv_of_mem_succ ha, map_zero]

end ExteriorOnly

section CliffordGradeProj

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- Constructive grade-`k` projection on `CliffordAlgebra Q`, transported across the
canonical module isomorphism `CliffordAlgebra.equivExterior Q`. -/
noncomputable def cliffordGradeProj (k : ℕ) : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  (CliffordAlgebra.equivExterior Q).symm.toLinearMap ∘ₗ
    exteriorGradeProj R M k ∘ₗ
      (CliffordAlgebra.equivExterior Q).toLinearMap

@[simp]
theorem cliffordGradeProj_idem (k : ℕ) (x : CliffordAlgebra Q) :
    cliffordGradeProj Q k (cliffordGradeProj Q k x) = cliffordGradeProj Q k x := by
  dsimp [cliffordGradeProj]
  rw [LinearEquiv.apply_symm_apply, exteriorGradeProj_idem]

theorem cliffordGradeProj_comp_idem (k : ℕ) :
    cliffordGradeProj Q k ∘ₗ cliffordGradeProj Q k = cliffordGradeProj Q k :=
  LinearMap.ext (cliffordGradeProj_idem Q k)

theorem cliffordGradeProj_orthog {j k : ℕ} (hjk : j ≠ k) (x : CliffordAlgebra Q) :
    cliffordGradeProj Q j (cliffordGradeProj Q k x) = 0 := by
  dsimp [cliffordGradeProj]
  rw [LinearEquiv.apply_symm_apply, exteriorGradeProj_orthog hjk, map_zero]

theorem cliffordGradeProj_comp_orthog {j k : ℕ} (hjk : j ≠ k) :
    cliffordGradeProj Q j ∘ₗ cliffordGradeProj Q k = 0 :=
  LinearMap.ext (cliffordGradeProj_orthog Q hjk)

theorem equivExterior_algebraMap (r : R) :
    CliffordAlgebra.equivExterior Q (algebraMap R (CliffordAlgebra Q) r) =
      algebraMap R (ExteriorAlgebra R M) r := by
  simp only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply,
    CliffordAlgebra.changeForm_algebraMap]

theorem equivExterior_ι (m : M) :
    CliffordAlgebra.equivExterior Q (CliffordAlgebra.ι Q m) = ExteriorAlgebra.ι R m := by
  simp only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply,
    CliffordAlgebra.changeForm_ι]

@[simp]
theorem cliffordGradeProj_zero_algebraMap (r : R) :
    cliffordGradeProj Q 0 (algebraMap R (CliffordAlgebra Q) r) =
      algebraMap R (CliffordAlgebra Q) r := by
  change (CliffordAlgebra.equivExterior Q).symm
    (exteriorGradeProj R M 0
      (CliffordAlgebra.equivExterior Q (algebraMap R (CliffordAlgebra Q) r))) = _
  rw [equivExterior_algebraMap,
    exteriorGradeProj_of_mem (algebraMap_mem_exteriorPower_zero (R := R) (M := M) r),
    ← equivExterior_algebraMap Q, LinearEquiv.symm_apply_apply]

@[simp]
theorem cliffordGradeProj_succ_algebraMap (k : ℕ) (r : R) :
    cliffordGradeProj Q (k + 1) (algebraMap R (CliffordAlgebra Q) r) = 0 := by
  change (CliffordAlgebra.equivExterior Q).symm
    (exteriorGradeProj R M (k + 1)
      (CliffordAlgebra.equivExterior Q (algebraMap R (CliffordAlgebra Q) r))) = _
  rw [equivExterior_algebraMap,
    exteriorGradeProj_of_mem_ne (Nat.zero_ne_add_one k)
      (algebraMap_mem_exteriorPower_zero (R := R) (M := M) r),
    map_zero]

theorem cliffordGradeProj_ne_zero_algebraMap {k : ℕ} (hk : k ≠ 0) (r : R) :
    cliffordGradeProj Q k (algebraMap R (CliffordAlgebra Q) r) = 0 := by
  cases k with
  | zero => exact (hk rfl).elim
  | succ k => exact cliffordGradeProj_succ_algebraMap Q k r

@[simp]
theorem cliffordGradeProj_one_ι (m : M) :
    cliffordGradeProj Q 1 (CliffordAlgebra.ι Q m) = CliffordAlgebra.ι Q m := by
  change (CliffordAlgebra.equivExterior Q).symm
    (exteriorGradeProj R M 1
      (CliffordAlgebra.equivExterior Q (CliffordAlgebra.ι Q m))) = _
  rw [equivExterior_ι,
    exteriorGradeProj_of_mem (ι_mem_exteriorPower_one (R := R) (M := M) m),
    ← equivExterior_ι Q, LinearEquiv.symm_apply_apply]

theorem cliffordGradeProj_ne_one_ι {k : ℕ} (hk : k ≠ 1) (m : M) :
    cliffordGradeProj Q k (CliffordAlgebra.ι Q m) = 0 := by
  change (CliffordAlgebra.equivExterior Q).symm
    (exteriorGradeProj R M k
      (CliffordAlgebra.equivExterior Q (CliffordAlgebra.ι Q m))) = _
  rw [equivExterior_ι,
    exteriorGradeProj_of_mem_ne hk.symm (ι_mem_exteriorPower_one (R := R) (M := M) m),
    map_zero]

theorem clifford_ι_leftInverse :
    Function.LeftInverse
      (ExteriorAlgebra.ιInv.comp (CliffordAlgebra.equivExterior Q).toLinearMap)
      (CliffordAlgebra.ι Q) := by
  intro m
  change ExteriorAlgebra.ιInv (CliffordAlgebra.equivExterior Q (CliffordAlgebra.ι Q m)) = m
  rw [equivExterior_ι]
  exact ExteriorAlgebra.ι_leftInverse m

theorem clifford_ι_injective : Function.Injective (CliffordAlgebra.ι Q) :=
  (clifford_ι_leftInverse Q).injective

/-! ### Alignment with `InfoGeometry.Riemannian.hTrace_cl` -/

/-- Grade-0 Clifford projection recovers the existing scalar trace `hTrace_cl`. -/
theorem cliffordGradeProj_zero_eq_algebraMap_hTrace (x : CliffordAlgebra Q) :
    cliffordGradeProj Q 0 x = algebraMap R (CliffordAlgebra Q) (hTrace_cl Q x) := by
  change (CliffordAlgebra.equivExterior Q).symm
    (exteriorGradeProj R M 0 (CliffordAlgebra.equivExterior Q x)) = _
  rw [exteriorGradeProj_zero_eq_algebraMap_algebraMapInv]
  have hcomm :
      algebraMap R (ExteriorAlgebra R M)
          (ExteriorAlgebra.algebraMapInv (CliffordAlgebra.equivExterior Q x)) =
        CliffordAlgebra.equivExterior Q
          (algebraMap R (CliffordAlgebra Q)
            (ExteriorAlgebra.algebraMapInv (CliffordAlgebra.equivExterior Q x))) :=
    (equivExterior_algebraMap Q _).symm
  rw [hcomm, LinearEquiv.symm_apply_apply]
  rfl

@[simp]
theorem hTrace_cliffordGradeProj_zero (x : CliffordAlgebra Q) :
    hTrace_cl Q (cliffordGradeProj Q 0 x) = hTrace_cl Q x := by
  rw [cliffordGradeProj_zero_eq_algebraMap_hTrace]
  simp [hTrace_cl]

theorem hTrace_cliffordGradeProj_succ (k : ℕ) (x : CliffordAlgebra Q) :
    hTrace_cl Q (cliffordGradeProj Q (k + 1) x) = 0 := by
  have hmem : exteriorGradeProj R M (k + 1) (CliffordAlgebra.equivExterior Q x) ∈ ⋀[R]^(k + 1) M :=
    exteriorGradeProj_mem R M (k + 1) _
  dsimp [hTrace_cl, cliffordGradeProj]
  rw [LinearEquiv.apply_symm_apply]
  exact exterior_algebraMapInv_of_mem_succ hmem

theorem hTrace_cliffordGradeProj_ne_zero {k : ℕ} (hk : k ≠ 0) (x : CliffordAlgebra Q) :
    hTrace_cl Q (cliffordGradeProj Q k x) = 0 := by
  cases k with
  | zero => exact (hk rfl).elim
  | succ k => exact hTrace_cliffordGradeProj_succ Q k x

end CliffordGradeProj

end GradeProjections

/-! ### Finite-Dimensional Cutoff and Resolution of the Identity over `ℝ` -/

section RealResolution

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [Module.Finite ℝ M]
variable (Q : QuadraticForm ℝ M)

/-- Exterior powers vanish strictly above the vector-space dimension `Module.finrank ℝ M`. -/
theorem exteriorPower_eq_bot_of_gt_finrank {k : ℕ} (hk : Module.finrank ℝ M < k) :
    (⋀[ℝ]^k M) = ⊥ := by
  rw [← Submodule.finrank_eq_zero]
  rw [exteriorPower.finrank_eq ℝ M, Nat.choose_eq_zero_of_lt hk]

/-- Clifford grade projections vanish identically for degrees strictly above
`Module.finrank ℝ M`. -/
theorem cliffordGradeProj_eq_zero_of_gt_finrank {k : ℕ} (hk : Module.finrank ℝ M < k) :
    cliffordGradeProj Q k = 0 := by
  refine LinearMap.ext fun x => ?_
  have hxbot :
      exteriorGradeProj ℝ M k (CliffordAlgebra.equivExterior Q x) ∈ (⊥ : Submodule ℝ _) := by
    rw [← exteriorPower_eq_bot_of_gt_finrank (M := M) hk]
    exact exteriorGradeProj_mem ℝ M k _
  rw [Submodule.mem_bot] at hxbot
  rw [LinearMap.zero_apply]
  change (CliffordAlgebra.equivExterior Q).symm
    (exteriorGradeProj ℝ M k (CliffordAlgebra.equivExterior Q x)) = 0
  rw [hxbot, map_zero]

theorem exteriorGradeProj_sum_range_eq_id :
    (∑ k ∈ Finset.range (Module.finrank ℝ M + 1), exteriorGradeProj ℝ M k) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sum_apply, LinearMap.id_apply]
  induction x using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[ℝ]^i M) with
  | zero => simp
  | add a b ha hb => simp [Finset.sum_add_distrib, ha, hb]
  | homogeneous hm =>
    rename_i i
    rcases hm with ⟨a, ha⟩
    by_cases hi : i < Module.finrank ℝ M + 1
    · rw [Finset.sum_eq_single i]
      · exact exteriorGradeProj_of_mem ha
      · intro k _ hki
        exact exteriorGradeProj_of_mem_ne hki.symm ha
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hi)).elim
    · have hgt : Module.finrank ℝ M < i := Nat.lt_of_not_ge fun hle => hi (Nat.lt_succ_of_le hle)
      have ha0 : a = 0 := by
        rw [← Submodule.mem_bot (R := ℝ), ← exteriorPower_eq_bot_of_gt_finrank (M := M) hgt]
        exact ha
      subst ha0
      simp

/-- **Resolution of the Identity**: the finite sum of Clifford grade projections up to
`Module.finrank ℝ M` equals the identity linear map on `CliffordAlgebra Q`. -/
theorem cliffordGradeProj_sum_range_eq_id :
    (∑ k ∈ Finset.range (Module.finrank ℝ M + 1), cliffordGradeProj Q k) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sum_apply, LinearMap.id_apply]
  have hsum := congrArg (fun f : ExteriorAlgebra ℝ M →ₗ[ℝ] ExteriorAlgebra ℝ M =>
      f (CliffordAlgebra.equivExterior Q x)) (exteriorGradeProj_sum_range_eq_id (M := M))
  rw [LinearMap.sum_apply, LinearMap.id_apply] at hsum
  have hsum' := congrArg (CliffordAlgebra.equivExterior Q).symm hsum
  rw [map_sum, LinearEquiv.symm_apply_apply] at hsum'
  dsimp [cliffordGradeProj]
  exact hsum'

theorem cliffordGradeProj_sum_range_apply (x : CliffordAlgebra Q) :
    (∑ k ∈ Finset.range (Module.finrank ℝ M + 1), cliffordGradeProj Q k x) = x := by
  simpa only [LinearMap.sum_apply, LinearMap.id_apply] using
    congrArg (fun f : CliffordAlgebra Q →ₗ[ℝ] CliffordAlgebra Q => f x)
      (cliffordGradeProj_sum_range_eq_id Q)

end RealResolution

/-! ## Part B: Golden-Ratio Realization of `FibonacciGrothendieckRing` -/

section GoldenFibonacciRealization

/-- Real realization of `FibonacciRingModel` sending `(a, b) = a·1 + b·τ` to `a + b·φ`. -/
noncomputable def evalGoldenModel (x : FibonacciRingModel) : ℝ :=
  FibonacciRingModel.eval φ x

@[simp]
theorem evalGoldenModel_one : evalGoldenModel FibonacciRingModel.one = 1 :=
  FibonacciRingModel.eval_one φ

@[simp]
theorem evalGoldenModel_tau : evalGoldenModel FibonacciRingModel.tau = φ :=
  FibonacciRingModel.eval_tau φ

theorem evalGoldenModel_add (x y : FibonacciRingModel) :
    evalGoldenModel (x + y) = evalGoldenModel x + evalGoldenModel y :=
  FibonacciRingModel.eval_add φ x y

theorem evalGoldenModel_neg (x : FibonacciRingModel) :
    evalGoldenModel (-x) = -evalGoldenModel x :=
  FibonacciRingModel.eval_neg φ x

theorem evalGoldenModel_sub (x y : FibonacciRingModel) :
    evalGoldenModel (x - y) = evalGoldenModel x - evalGoldenModel y := by
  rw [sub_eq_add_neg, evalGoldenModel_add, evalGoldenModel_neg, sub_eq_add_neg]

theorem evalGoldenModel_mul (x y : FibonacciRingModel) :
    evalGoldenModel (FibonacciRingModel.mul x y) = evalGoldenModel x * evalGoldenModel y :=
  FibonacciRingModel.eval_mul φ Real.goldenRatio_sq x y

/-- `{1, φ}` is linearly independent over `ℚ`, proven from `Real.goldenRatio_irrational`. -/
theorem rat_linear_independent_one_goldenRatio (q₁ q₂ : ℚ)
    (h : (q₁ : ℝ) + (q₂ : ℝ) * φ = 0) :
    q₁ = 0 ∧ q₂ = 0 := by
  have hq₂ : q₂ = 0 := by
    by_contra hne
    have hq₂r : (q₂ : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hne
    have hmul : φ * (q₂ : ℝ) = -((q₁ : ℝ)) := by
      rw [mul_comm]
      exact eq_neg_of_add_eq_zero_right h
    have hphi : (((-q₁ / q₂ : ℚ) : ℝ)) = φ := by
      rw [Rat.cast_div, Rat.cast_neg]
      exact ((eq_div_iff hq₂r).mpr hmul).symm
    exact Real.goldenRatio_irrational ⟨-q₁ / q₂, hphi⟩
  have hq₁r : (q₁ : ℝ) = 0 := by
    simpa [hq₂] using h
  exact ⟨Rat.cast_eq_zero.mp hq₁r, hq₂⟩

theorem evalGoldenModel_injective : Function.Injective evalGoldenModel := by
  intro x y hxy
  have hsub : evalGoldenModel (x - y) = 0 := by
    rw [evalGoldenModel_sub, hxy, sub_self]
  dsimp [evalGoldenModel, FibonacciRingModel.eval] at hsub
  have hrat :
      ((((x.1 - y.1 : ℤ) : ℚ) : ℝ)) + ((((x.2 - y.2 : ℤ) : ℚ) : ℝ)) * φ = 0 := by
    simpa [Int.cast_sub] using hsub
  obtain ⟨h1, h2⟩ := rat_linear_independent_one_goldenRatio _ _ hrat
  have h1z : x.1 = y.1 := sub_eq_zero.mp (Int.cast_injective (α := ℚ) h1)
  have h2z : x.2 = y.2 := sub_eq_zero.mp (Int.cast_injective (α := ℚ) h2)
  exact Prod.ext h1z h2z

/-- Additive realization of the Grothendieck completion `FibonacciK0` into `ℝ`,
compatible with the fusion multiplication `k0Mul`. -/
noncomputable def evalGoldenK0 : FibonacciK0 →+ ℝ where
  toFun x := evalGoldenModel (k0ToModel x)
  map_zero' := by
    rw [map_zero]
    simp [evalGoldenModel, FibonacciRingModel.eval]
  map_add' x y := by simp [map_add, evalGoldenModel_add]

theorem evalGoldenK0_injective : Function.Injective evalGoldenK0 :=
  evalGoldenModel_injective.comp k0ToModel_injective

@[simp]
theorem evalGoldenK0_one : evalGoldenK0 fibOneK0 = 1 := by
  have h : evalGoldenK0 fibOneK0 = evalGoldenModel (k0ToModel fibOneK0) := rfl
  rw [h]
  simp

theorem evalGoldenK0_k0Mul (x y : FibonacciK0) :
    evalGoldenK0 (k0Mul x y) = evalGoldenK0 x * evalGoldenK0 y := by
  simp only [evalGoldenK0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, k0ToModel_k0Mul,
    evalGoldenModel_mul]

/-- Exact integer Fibonacci coordinates in `FibonacciRingModel` representing `φ ^ (-k)`
via `φ⁻¹ = 1 - φ` and Cassini/Binet identities. -/
def graceFibCoord (k : ℕ) : FibonacciRingModel :=
  ((-1 : ℤ) ^ k * (Nat.fib (k + 1) : ℤ), (-1 : ℤ) ^ (k + 1) * (Nat.fib k : ℤ))

/-- Every Grace contraction weight `φ ^ (-k)` is an exact element of `ℤ[φ]`, namely
`(-1)^k * F_{k+1} + (-1)^(k+1) * F_k * φ`. -/
theorem evalGoldenModel_graceFibCoord (k : ℕ) :
    evalGoldenModel (graceFibCoord k) = φ ^ (-(k : ℤ)) := by
  dsimp [evalGoldenModel, FibonacciRingModel.eval, graceFibCoord]
  have hbinet := Real.fib_succ_sub_goldenRatio_mul_fib k
  rw [zpow_neg, zpow_natCast, ← inv_pow, Real.inv_goldenRatio, neg_eq_neg_one_mul ψ, mul_pow]
  rw [← hbinet]
  push_cast
  ring

/-- Every strictly positive-grade Grace weight `φ ^ (-k)` (`k ≥ 1`) is irrational. -/
theorem irrational_grace_weight {k : ℕ} (hk : 1 ≤ k) :
    Irrational (φ ^ (-(k : ℤ))) := by
  intro ⟨q, hq⟩
  have heq := (evalGoldenModel_graceFibCoord k).trans hq.symm
  dsimp [evalGoldenModel, FibonacciRingModel.eval, graceFibCoord] at heq
  have hzero :
      ((((-1 : ℤ) ^ k * (Nat.fib (k + 1) : ℤ) : ℚ) - q : ℚ) : ℝ) +
        (((((-1 : ℤ) ^ (k + 1) * (Nat.fib k : ℤ) : ℤ) : ℚ)) : ℝ) * φ = 0 := by
    push_cast at heq ⊢
    linarith [heq]
  obtain ⟨_, h2⟩ := rat_linear_independent_one_goldenRatio _ _ hzero
  have h2z : (-1 : ℤ) ^ (k + 1) * (Nat.fib k : ℤ) = 0 :=
    Int.cast_injective (α := ℚ) h2
  rcases mul_eq_zero.mp h2z with hsign | hfib
  · exact pow_ne_zero (k + 1) (by decide : (-1 : ℤ) ≠ 0) hsign
  · have hpos : 0 < Nat.fib k := Nat.fib_pos.mpr hk
    omega

/-- Golden spectral-gap self-similarity: `1 - φ⁻¹ = 2 - φ = φ⁻² ∈ (0, 1)`. -/
theorem golden_spectral_gap_self_similar :
    1 - φ ^ (-(1 : ℤ)) = 2 - φ ∧
      1 - φ ^ (-(1 : ℤ)) = φ ^ (-(2 : ℤ)) ∧
        0 < 1 - φ ^ (-(1 : ℤ)) ∧
          1 - φ ^ (-(1 : ℤ)) < 1 := by
  have h1 : φ ^ (-(1 : ℤ)) = φ - 1 := by
    rw [zpow_neg_one, Real.inv_goldenRatio, ← Real.one_sub_goldenConj]
    linarith [Real.goldenRatio_add_goldenConj]
  have h2 : φ ^ (-(2 : ℤ)) = 2 - φ := by
    rw [zpow_neg, zpow_two, ← sq, Real.goldenRatio_sq]
    have hmul : (φ + 1) * (2 - φ) = 1 := by
      nlinarith [Real.goldenRatio_sq]
    exact inv_eq_of_mul_eq_one_right hmul
  exact scalar_one_sub_inv_phi_props h1 h2

end GoldenFibonacciRealization

/-! ## Part C: Grace Grade-Contraction Operator, Explicit Inverse, Iterates, and Fixed Points -/

section GraceOperatorSection

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

/-- The Grace grade-contraction operator `G_Q = ∑_{k=0}^{finrank M} φ^{-k} Π_k`. -/
noncomputable def graceOperator : CliffordAlgebra Q →ₗ[ℝ] CliffordAlgebra Q :=
  ∑ k ∈ Finset.range (Module.finrank ℝ M + 1), (φ ^ (-(k : ℤ))) • cliffordGradeProj Q k

/-- The explicit inverse Grace operator `G_Q⁻¹ = ∑_{k=0}^{finrank M} φ^k Π_k`. -/
noncomputable def graceInverseOperator : CliffordAlgebra Q →ₗ[ℝ] CliffordAlgebra Q :=
  ∑ k ∈ Finset.range (Module.finrank ℝ M + 1), (φ ^ (k : ℤ)) • cliffordGradeProj Q k

theorem graceOperator_apply (x : CliffordAlgebra Q) :
    graceOperator Q x =
      ∑ k ∈ Finset.range (Module.finrank ℝ M + 1),
        (φ ^ (-(k : ℤ))) • cliffordGradeProj Q k x := by
  dsimp [graceOperator]
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun k _ => LinearMap.smul_apply _ _ x

theorem graceInverseOperator_apply (x : CliffordAlgebra Q) :
    graceInverseOperator Q x =
      ∑ k ∈ Finset.range (Module.finrank ℝ M + 1),
        (φ ^ (k : ℤ)) • cliffordGradeProj Q k x := by
  dsimp [graceInverseOperator]
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun k _ => LinearMap.smul_apply _ _ x

section FiniteRealGrace

variable [Module.Finite ℝ M]

theorem cliffordGradeProj_graceOperator (k : ℕ) (x : CliffordAlgebra Q) :
    cliffordGradeProj Q k (graceOperator Q x) =
      (φ ^ (-(k : ℤ))) • cliffordGradeProj Q k x := by
  rw [graceOperator_apply, map_sum]
  by_cases hk : k < Module.finrank ℝ M + 1
  · rw [Finset.sum_eq_single k]
    · rw [map_smul, cliffordGradeProj_idem]
    · intro j _ hjk
      rw [map_smul, cliffordGradeProj_orthog Q hjk.symm, smul_zero]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hk)).elim
  · have hgt : Module.finrank ℝ M < k := Nat.lt_of_not_ge fun hle => hk (Nat.lt_succ_of_le hle)
    have hzero : cliffordGradeProj Q k = 0 := cliffordGradeProj_eq_zero_of_gt_finrank Q hgt
    rw [hzero, LinearMap.zero_apply, smul_zero]
    exact Finset.sum_eq_zero fun j _ => by simp only [map_smul, LinearMap.zero_apply, smul_zero]

theorem cliffordGradeProj_graceInverseOperator (k : ℕ) (x : CliffordAlgebra Q) :
    cliffordGradeProj Q k (graceInverseOperator Q x) =
      (φ ^ (k : ℤ)) • cliffordGradeProj Q k x := by
  rw [graceInverseOperator_apply, map_sum]
  by_cases hk : k < Module.finrank ℝ M + 1
  · rw [Finset.sum_eq_single k]
    · rw [map_smul, cliffordGradeProj_idem]
    · intro j _ hjk
      rw [map_smul, cliffordGradeProj_orthog Q hjk.symm, smul_zero]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hk)).elim
  · have hgt : Module.finrank ℝ M < k := Nat.lt_of_not_ge fun hle => hk (Nat.lt_succ_of_le hle)
    have hzero : cliffordGradeProj Q k = 0 := cliffordGradeProj_eq_zero_of_gt_finrank Q hgt
    rw [hzero, LinearMap.zero_apply, smul_zero]
    exact Finset.sum_eq_zero fun j _ => by simp only [map_smul, LinearMap.zero_apply, smul_zero]

theorem graceInverseOperator_graceOperator (x : CliffordAlgebra Q) :
    graceInverseOperator Q (graceOperator Q x) = x := by
  rw [graceInverseOperator_apply]
  refine (Finset.sum_congr rfl fun k _ => ?_).trans (cliffordGradeProj_sum_range_apply Q x)
  rw [cliffordGradeProj_graceOperator, smul_smul, ← zpow_add₀ Real.goldenRatio_ne_zero,
    add_neg_cancel, zpow_zero, one_smul]

theorem graceOperator_graceInverseOperator (x : CliffordAlgebra Q) :
    graceOperator Q (graceInverseOperator Q x) = x := by
  rw [graceOperator_apply]
  refine (Finset.sum_congr rfl fun k _ => ?_).trans (cliffordGradeProj_sum_range_apply Q x)
  rw [cliffordGradeProj_graceInverseOperator, smul_smul, ← zpow_add₀ Real.goldenRatio_ne_zero,
    neg_add_cancel, zpow_zero, one_smul]

theorem graceInverse_comp_grace :
    graceInverseOperator Q ∘ₗ graceOperator Q = LinearMap.id :=
  LinearMap.ext (graceInverseOperator_graceOperator Q)

theorem grace_comp_graceInverse :
    graceOperator Q ∘ₗ graceInverseOperator Q = LinearMap.id :=
  LinearMap.ext (graceOperator_graceInverseOperator Q)

/-- The Grace operator packaged as an explicit `ℝ`-linear automorphism on `CliffordAlgebra Q`. -/
noncomputable def graceLinearEquiv : CliffordAlgebra Q ≃ₗ[ℝ] CliffordAlgebra Q :=
  LinearEquiv.ofLinearMap (graceOperator Q) (graceInverseOperator Q)
    (grace_comp_graceInverse Q) (graceInverse_comp_grace Q)

/-- Exact spectral power formula for `m`-fold iteration of the Grace operator. -/
theorem graceOperator_iterate (m : ℕ) (x : CliffordAlgebra Q) :
    (graceOperator Q)^[m] x =
      ∑ k ∈ Finset.range (Module.finrank ℝ M + 1),
        (φ ^ (-((m * k : ℕ) : ℤ))) • cliffordGradeProj Q k x := by
  induction m with
  | zero =>
    simpa [Function.iterate_zero, id_eq] using (cliffordGradeProj_sum_range_apply Q x).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', graceOperator_apply, ih]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [map_sum, Finset.sum_eq_single k]
    · rw [map_smul, cliffordGradeProj_idem, smul_smul, ← zpow_add₀ Real.goldenRatio_ne_zero,
        zpow_neg_succ_mul_exp]
    · intro j _ hjk
      rw [map_smul, cliffordGradeProj_orthog Q hjk.symm, smul_zero]
    · intro hnot
      exact (hnot hk).elim

theorem cliffordGradeProj_graceOperator_iterate (m k : ℕ) (x : CliffordAlgebra Q) :
    cliffordGradeProj Q k ((graceOperator Q)^[m] x) =
      (φ ^ (-((m * k : ℕ) : ℤ))) • cliffordGradeProj Q k x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', cliffordGradeProj_graceOperator, ih, smul_smul,
      ← zpow_add₀ Real.goldenRatio_ne_zero, zpow_neg_succ_mul_exp]

/-- The Grace operator preserves the canonical Clifford scalar trace `hTrace_cl`. -/
theorem hTrace_graceOperator (x : CliffordAlgebra Q) :
    hTrace_cl Q (graceOperator Q x) = hTrace_cl Q x := by
  rw [← hTrace_cliffordGradeProj_zero Q (graceOperator Q x),
    cliffordGradeProj_graceOperator, Nat.cast_zero, neg_zero, zpow_zero, one_smul,
    hTrace_cliffordGradeProj_zero]

/-- An element of `CliffordAlgebra Q` is fixed by the Grace operator if and only if
it is a pure scalar. -/
theorem graceOperator_fixed_iff_scalar (x : CliffordAlgebra Q) :
    graceOperator Q x = x ↔ x = algebraMap ℝ (CliffordAlgebra Q) (hTrace_cl Q x) := by
  constructor
  · intro hfix
    have hhi : ∀ k : ℕ, 1 ≤ k → cliffordGradeProj Q k x = 0 := by
      intro k hk
      have hproj := congrArg (cliffordGradeProj Q k) hfix
      rw [cliffordGradeProj_graceOperator] at hproj
      have hlt : φ ^ (-(k : ℤ)) < 1 := by
        rw [zpow_neg, zpow_natCast]
        have hgt : (1 : ℝ) < φ ^ k :=
          one_lt_pow₀ Real.one_lt_goldenRatio (Nat.ne_of_gt hk)
        exact inv_lt_one_of_one_lt₀ hgt
      have hsub : (φ ^ (-(k : ℤ)) - 1) • cliffordGradeProj Q k x = 0 := by
        rw [sub_smul, one_smul, hproj, sub_self]
      exact (smul_eq_zero.mp hsub).resolve_left (ne_of_lt (sub_neg.mpr hlt))
    have hsum := (cliffordGradeProj_sum_range_apply Q x).symm
    rw [Finset.sum_eq_single 0] at hsum
    · simpa [cliffordGradeProj_zero_eq_algebraMap_hTrace] using hsum
    · intro k _ hk0
      exact hhi k (Nat.pos_of_ne_zero hk0)
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.zero_lt_succ _))).elim
  · intro hx
    rw [hx, graceOperator_apply, Finset.sum_eq_single 0]
    · simp
    · intro k _ hk0
      rw [cliffordGradeProj_ne_zero_algebraMap Q hk0, smul_zero]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.zero_lt_succ _))).elim

end FiniteRealGrace

end GraceOperatorSection

/-! ## Part D: Blade Hilbert Space, Lyapunov Decay, and Proximal Variational Optimality -/

section BladeHilbertSpace

/-- Canonical exterior-algebra blade basis of `ExteriorAlgebra ℝ (Fin n → ℝ)`,
indexed by subsets `S : Finset (Fin n)`. -/
noncomputable def exteriorBladeBasis (n : ℕ) :
    Module.Basis (Finset (Fin n)) ℝ (ExteriorAlgebra ℝ (Fin n → ℝ)) :=
  ((DirectSum.Decomposition.isInternal (fun k : ℕ => ⋀[ℝ]^k (Fin n → ℝ))).collectedBasis
      fun k => (Pi.basisFun ℝ (Fin n)).exteriorPower k).reindex
    Set.powersetCard.prodEquiv

/-- Canonical blade basis of `CliffordAlgebra Q` over `Fin n → ℝ`,
indexed by `S : Finset (Fin n)`. -/
noncomputable def cliffordBladeBasis {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) :
    Module.Basis (Finset (Fin n)) ℝ (CliffordAlgebra Q) :=
  (exteriorBladeBasis n).map (CliffordAlgebra.equivExterior Q).symm

theorem exteriorBladeBasis_mem_grade (n : ℕ) (S : Finset (Fin n)) :
    exteriorBladeBasis n S ∈ ⋀[ℝ]^S.card (Fin n → ℝ) := by
  have hmem :=
    (DirectSum.Decomposition.isInternal (fun k : ℕ => ⋀[ℝ]^k (Fin n → ℝ))).collectedBasis_mem
      (fun k => (Pi.basisFun ℝ (Fin n)).exteriorPower k)
      (Set.powersetCard.prodEquiv.symm S)
  have hfst : (Set.powersetCard.prodEquiv.symm S).1 = S.card := by
    rw [Set.powersetCard.prodEquiv_symm_apply]
  rw [hfst] at hmem
  simpa only [exteriorBladeBasis, Module.Basis.reindex_apply] using hmem

@[simp]
theorem cliffordGradeProj_bladeBasis {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) (k : ℕ)
    (S : Finset (Fin n)) :
    cliffordGradeProj Q k (cliffordBladeBasis Q S) =
      if S.card = k then cliffordBladeBasis Q S else 0 := by
  dsimp [cliffordGradeProj, cliffordBladeBasis]
  rw [LinearEquiv.apply_symm_apply]
  split_ifs with hcard
  · rw [← hcard]
    exact congrArg (CliffordAlgebra.equivExterior Q).symm
      (exteriorGradeProj_of_mem (exteriorBladeBasis_mem_grade n S))
  · rw [exteriorGradeProj_of_mem_ne hcard (exteriorBladeBasis_mem_grade n S), map_zero]

/-- Blade-basis coordinate formula for Clifford grade projections. -/
@[simp]
theorem repr_cliffordGradeProj {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) (k : ℕ)
    (u : CliffordAlgebra Q) (S : Finset (Fin n)) :
    (cliffordBladeBasis Q).repr (cliffordGradeProj Q k u) S =
      if S.card = k then (cliffordBladeBasis Q).repr u S else 0 := by
  conv_lhs => rw [← (cliffordBladeBasis Q).sum_repr u]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cliffordGradeProj_bladeBasis]
  rw [Finset.sum_eq_single S]
  · split_ifs with hcard
    · simp only [Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]
    · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, mul_zero]
  · intro T _ hTS
    split_ifs with hT
    · simp only [Module.Basis.repr_self, Finsupp.single_eq_of_ne hTS.symm, mul_zero]
    · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ S)).elim

theorem card_finset_fin_le_finrank (n : ℕ) (S : Finset (Fin n)) :
    S.card ≤ Module.finrank ℝ (Fin n → ℝ) := by
  have hle : S.card ≤ Fintype.card (Fin n) := S.card_le_univ
  simpa [Module.finrank_pi, Fintype.card_fin] using hle

@[simp]
theorem repr_graceOperator {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u : CliffordAlgebra Q) (S : Finset (Fin n)) :
    (cliffordBladeBasis Q).repr (graceOperator Q u) S =
      φ ^ (-(S.card : ℤ)) * (cliffordBladeBasis Q).repr u S := by
  have hlt : S.card < Module.finrank ℝ (Fin n → ℝ) + 1 :=
    Nat.lt_succ_of_le (card_finset_fin_le_finrank n S)
  rw [graceOperator_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finset.sum_eq_single S.card]
  · simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, repr_cliffordGradeProj,
      ite_true]
  · intro k _ hkS
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, repr_cliffordGradeProj]
    split_ifs with hcard
    · exact (hkS.symm hcard).elim
    · rw [mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hlt)).elim

@[simp]
theorem repr_graceInverseOperator {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u : CliffordAlgebra Q) (S : Finset (Fin n)) :
    (cliffordBladeBasis Q).repr (graceInverseOperator Q u) S =
      φ ^ (S.card : ℤ) * (cliffordBladeBasis Q).repr u S := by
  have hlt : S.card < Module.finrank ℝ (Fin n → ℝ) + 1 :=
    Nat.lt_succ_of_le (card_finset_fin_le_finrank n S)
  rw [graceInverseOperator_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finset.sum_eq_single S.card]
  · simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, repr_cliffordGradeProj,
      ite_true]
  · intro k _ hkS
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, repr_cliffordGradeProj]
    split_ifs with hcard
    · exact (hkS.symm hcard).elim
    · rw [mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hlt)).elim

/-- Strictly positive-definite Euclidean blade Hilbert inner product on `CliffordAlgebra Q`. -/
noncomputable def cliffordBladeInner {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) :
    CliffordAlgebra Q →ₗ[ℝ] CliffordAlgebra Q →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v =>
        ∑ S : Finset (Fin n), (cliffordBladeBasis Q).repr u S * (cliffordBladeBasis Q).repr v S
      map_add' := fun v w => by
        simp only [map_add, Finsupp.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r v => by
        simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        exact mul_left_comm _ r _ }
  map_add' u₁ u₂ := by
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, Finsupp.coe_add,
      Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r u := by
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
      map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    exact mul_assoc r _ _

theorem cliffordBladeInner_symm {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u v : CliffordAlgebra Q) :
    cliffordBladeInner Q u v = cliffordBladeInner Q v u := by
  dsimp [cliffordBladeInner]
  refine Finset.sum_congr rfl fun S _ => ?_
  exact mul_comm _ _

theorem cliffordBladeInner_self_nonneg {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u : CliffordAlgebra Q) :
    0 ≤ cliffordBladeInner Q u u := by
  dsimp [cliffordBladeInner]
  exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem cliffordBladeInner_self_eq_zero {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u : CliffordAlgebra Q) :
    cliffordBladeInner Q u u = 0 ↔ u = 0 := by
  constructor
  · intro h
    dsimp [cliffordBladeInner] at h
    rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => mul_self_nonneg _] at h
    apply (cliffordBladeBasis Q).repr.injective
    ext S
    simpa [mul_self_eq_zero] using h S (Finset.mem_univ S)
  · rintro rfl
    simp

theorem cliffordBladeInner_self_pos_iff {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u : CliffordAlgebra Q) :
    0 < cliffordBladeInner Q u u ↔ u ≠ 0 := by
  rw [lt_iff_le_and_ne, ne_eq, eq_comm, cliffordBladeInner_self_eq_zero]
  exact and_iff_right (cliffordBladeInner_self_nonneg Q u)

/-- Canonical `InnerProductSpace.Core` instance induced by `cliffordBladeInner Q`. -/
@[instance_reducible]
noncomputable def cliffordBladeInnerCore {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) :
    InnerProductSpace.Core ℝ (CliffordAlgebra Q) where
  inner u v := cliffordBladeInner Q u v
  conj_inner_symm u v := by simp [cliffordBladeInner_symm]
  add_left u v w := by simp
  smul_left u v r := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_trivial]
  re_inner_nonneg u := cliffordBladeInner_self_nonneg Q u
  definite u h := (cliffordBladeInner_self_eq_zero Q u).mp h

noncomputable scoped instance instCliffordBladeCore {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) :
    InnerProductSpace.Core ℝ (CliffordAlgebra Q) :=
  cliffordBladeInnerCore Q

noncomputable scoped instance instCliffordBladeNormedAddCommGroup {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ)) :
    NormedAddCommGroup (CliffordAlgebra Q) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

noncomputable scoped instance instCliffordBladeInnerProductSpace {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ)) :
    InnerProductSpace ℝ (CliffordAlgebra Q) :=
  InnerProductSpace.ofCore _

theorem cliffordBladeInner_gradeProj_self_adj {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (k : ℕ) (u v : CliffordAlgebra Q) :
    cliffordBladeInner Q (cliffordGradeProj Q k u) v =
      cliffordBladeInner Q u (cliffordGradeProj Q k v) := by
  dsimp [cliffordBladeInner]
  simp only [repr_cliffordGradeProj]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hcard : S.card = k
  · simp [hcard]
  · simp [hcard]

theorem cliffordBladeInner_gradeProj_orthog {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    {j k : ℕ} (hjk : j ≠ k) (u v : CliffordAlgebra Q) :
    cliffordBladeInner Q (cliffordGradeProj Q j u) (cliffordGradeProj Q k v) = 0 := by
  rw [cliffordBladeInner_gradeProj_self_adj, cliffordGradeProj_orthog Q hjk, map_zero]

theorem cliffordBladeInner_grade_pythagorean {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u v : CliffordAlgebra Q) :
    cliffordBladeInner Q u v =
      ∑ k ∈ Finset.range (n + 1),
        cliffordBladeInner Q (cliffordGradeProj Q k u) (cliffordGradeProj Q k v) := by
  have hrhs :
      (∑ k ∈ Finset.range (n + 1),
          cliffordBladeInner Q (cliffordGradeProj Q k u) (cliffordGradeProj Q k v)) =
        ∑ S : Finset (Fin n),
          ((cliffordBladeBasis Q).repr u S * (cliffordBladeBasis Q).repr v S) := by
    have hswap :
        (∑ k ∈ Finset.range (n + 1),
            cliffordBladeInner Q (cliffordGradeProj Q k u) (cliffordGradeProj Q k v)) =
          ∑ S : Finset (Fin n),
            ∑ k ∈ Finset.range (n + 1),
              ((cliffordBladeBasis Q).repr (cliffordGradeProj Q k u) S *
                (cliffordBladeBasis Q).repr (cliffordGradeProj Q k v) S) := by
      dsimp [cliffordBladeInner]
      exact Finset.sum_comm
    rw [hswap]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hmem : S.card ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa using S.card_le_univ))
    rw [Finset.sum_eq_single S.card]
    · simp only [repr_cliffordGradeProj, ite_true]
    · intro k _ hkS
      simp only [repr_cliffordGradeProj]
      split_ifs with hcard
      · exact (hkS.symm hcard).elim
      · rw [zero_mul]
    · intro hnot
      exact (hnot hmem).elim
  exact hrhs.symm

theorem graceOperator_self_adj {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u v : CliffordAlgebra Q) :
    cliffordBladeInner Q (graceOperator Q u) v =
      cliffordBladeInner Q u (graceOperator Q v) := by
  dsimp [cliffordBladeInner]
  simp only [repr_graceOperator]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [mul_comm (φ ^ (-(S.card : ℤ))) ((cliffordBladeBasis Q).repr u S), mul_assoc]

theorem graceInverseOperator_self_adj {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u v : CliffordAlgebra Q) :
    cliffordBladeInner Q (graceInverseOperator Q u) v =
      cliffordBladeInner Q u (graceInverseOperator Q v) := by
  dsimp [cliffordBladeInner]
  simp only [repr_graceInverseOperator]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [mul_comm (φ ^ (S.card : ℤ)) ((cliffordBladeBasis Q).repr u S), mul_assoc]

/-- The Grace-weighted inner product `⟨u, G_Q v⟩` on `CliffordAlgebra Q`. -/
noncomputable def graceBladeInner {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) :
    CliffordAlgebra Q →ₗ[ℝ] CliffordAlgebra Q →ₗ[ℝ] ℝ where
  toFun u := (cliffordBladeInner Q u).comp (graceOperator Q)
  map_add' u₁ u₂ := by
    refine LinearMap.ext fun v => ?_
    change cliffordBladeInner Q (u₁ + u₂) (graceOperator Q v) =
      cliffordBladeInner Q u₁ (graceOperator Q v) +
      cliffordBladeInner Q u₂ (graceOperator Q v)
    rw [map_add, LinearMap.add_apply]
  map_smul' r u := by
    refine LinearMap.ext fun v => ?_
    change cliffordBladeInner Q (r • u) (graceOperator Q v) =
      r • cliffordBladeInner Q u (graceOperator Q v)
    simp only [map_smul, LinearMap.smul_apply]

theorem graceBladeInner_eq_repr_sum {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u v : CliffordAlgebra Q) :
    graceBladeInner Q u v =
      ∑ S : Finset (Fin n),
        φ ^ (-(S.card : ℤ)) *
          ((cliffordBladeBasis Q).repr u S * (cliffordBladeBasis Q).repr v S) := by
  change cliffordBladeInner Q u (graceOperator Q v) = _
  dsimp [cliffordBladeInner]
  simp only [repr_graceOperator]
  refine Finset.sum_congr rfl fun S _ => ?_
  exact mul_left_comm ((cliffordBladeBasis Q).repr u S) (φ ^ (-(S.card : ℤ))) _

theorem graceBladeInner_symm {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u v : CliffordAlgebra Q) :
    graceBladeInner Q u v = graceBladeInner Q v u := by
  change cliffordBladeInner Q u (graceOperator Q v) =
    cliffordBladeInner Q v (graceOperator Q u)
  rw [cliffordBladeInner_symm, graceOperator_self_adj]

theorem graceBladeInner_self_nonneg {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u : CliffordAlgebra Q) :
    0 ≤ graceBladeInner Q u u := by
  rw [graceBladeInner_eq_repr_sum]
  refine Finset.sum_nonneg fun S _ => ?_
  exact mul_nonneg (zpow_nonneg (le_of_lt Real.goldenRatio_pos) _) (mul_self_nonneg _)

theorem graceBladeInner_self_eq_zero {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u : CliffordAlgebra Q) :
    graceBladeInner Q u u = 0 ↔ u = 0 := by
  constructor
  · intro h
    rw [graceBladeInner_eq_repr_sum,
      Finset.sum_eq_zero_iff_of_nonneg fun S _ =>
        mul_nonneg (zpow_nonneg (le_of_lt Real.goldenRatio_pos) _) (mul_self_nonneg _)] at h
    apply (cliffordBladeBasis Q).repr.injective
    ext S
    have hS := mul_eq_zero.mp (h S (Finset.mem_univ S))
    rcases hS with hw | hsq
    · exact ((zpow_pos Real.goldenRatio_pos _).ne' hw).elim
    · simpa [mul_self_eq_zero] using hsq
  · rintro rfl
    simp

theorem graceBladeInner_self_pos_iff {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u : CliffordAlgebra Q) :
    0 < graceBladeInner Q u u ↔ u ≠ 0 := by
  rw [lt_iff_le_and_ne, ne_eq, eq_comm, graceBladeInner_self_eq_zero]
  exact and_iff_right (graceBladeInner_self_nonneg Q u)

/-- Sharp two-sided spectral coercivity bounds of the Grace-weighted inner product
relative to the Euclidean blade Hilbert norm. -/
theorem graceBladeInner_bounds {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u : CliffordAlgebra Q) :
    φ ^ (-(n : ℤ)) * cliffordBladeInner Q u u ≤ graceBladeInner Q u u ∧
      graceBladeInner Q u u ≤ cliffordBladeInner Q u u := by
  rw [graceBladeInner_eq_repr_sum]
  dsimp [cliffordBladeInner]
  rw [Finset.mul_sum]
  refine ⟨Finset.sum_le_sum fun S _ => ?_, Finset.sum_le_sum fun S _ => ?_⟩
  · have hle : φ ^ (-(n : ℤ)) ≤ φ ^ (-(S.card : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      refine inv_anti₀ (pow_pos Real.goldenRatio_pos _) ?_
      exact pow_right_mono₀ (le_of_lt Real.one_lt_goldenRatio) (by simpa using S.card_le_univ)
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hle (mul_self_nonneg _)
  · have hle : φ ^ (-(S.card : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt Real.one_lt_goldenRatio))
    simpa using mul_le_mul_of_nonneg_right hle (mul_self_nonneg _)

/-- **Exponential Lyapunov Decay** of all non-scalar multivector grades under iterated
Grace contraction: `‖G^m u - Π₀ u‖² ≤ φ^{-2m} ‖u - Π₀ u‖²`. -/
theorem graceOperator_iterate_nonscalar_decay {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (m : ℕ) (u : CliffordAlgebra Q) :
    cliffordBladeInner Q ((graceOperator Q)^[m] u - cliffordGradeProj Q 0 u)
        ((graceOperator Q)^[m] u - cliffordGradeProj Q 0 u) ≤
      φ ^ (-((2 * m : ℕ) : ℤ)) *
        cliffordBladeInner Q (u - cliffordGradeProj Q 0 u) (u - cliffordGradeProj Q 0 u) := by
  have hcoord : ∀ S : Finset (Fin n),
      (cliffordBladeBasis Q).repr ((graceOperator Q)^[m] u - cliffordGradeProj Q 0 u) S =
        φ ^ (-((m * S.card : ℕ) : ℤ)) *
          (cliffordBladeBasis Q).repr (u - cliffordGradeProj Q 0 u) S := by
    intro S
    rw [map_sub, map_sub, Finsupp.coe_sub, Finsupp.coe_sub, Pi.sub_apply, Pi.sub_apply]
    have hlt : S.card < Module.finrank ℝ (Fin n → ℝ) + 1 :=
      Nat.lt_succ_of_le (card_finset_fin_le_finrank n S)
    have hiter : (cliffordBladeBasis Q).repr ((graceOperator Q)^[m] u) S =
        φ ^ (-((m * S.card : ℕ) : ℤ)) * (cliffordBladeBasis Q).repr u S := by
      rw [graceOperator_iterate, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finset.sum_eq_single S.card]
      · simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, repr_cliffordGradeProj,
          ite_true]
      · intro k _ hkS
        simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, repr_cliffordGradeProj]
        split_ifs with hcard
        · exact (hkS.symm hcard).elim
        · rw [mul_zero]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hlt)).elim
    rw [hiter]
    simp only [repr_cliffordGradeProj]
    by_cases h0 : S.card = 0
    · simp [h0]
    · simp [h0]
  dsimp [cliffordBladeInner]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [hcoord S]
  by_cases h0 : S.card = 0
  · simp [map_sub, repr_cliffordGradeProj, h0]
  · have hpos : 1 ≤ S.card := Nat.pos_of_ne_zero h0
    have hpow :
        (φ ^ (-((m * S.card : ℕ) : ℤ))) * (φ ^ (-((m * S.card : ℕ) : ℤ))) ≤
          φ ^ (-((2 * m : ℕ) : ℤ)) := by
      rw [← zpow_add₀ Real.goldenRatio_ne_zero, zpow_neg_double_exp,
        zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      refine inv_anti₀ (pow_pos Real.goldenRatio_pos _) ?_
      refine pow_right_mono₀ (le_of_lt Real.one_lt_goldenRatio) ?_
      calc
        2 * m = (2 * m) * 1 := (mul_one _).symm
        _ ≤ (2 * m) * S.card := Nat.mul_le_mul_left _ hpos
    rw [mul_mul_mul_comm]
    exact mul_le_mul_of_nonneg_right hpow (mul_self_nonneg _)

/-! ### Proximal Parsimonious Flow Variational Principle (Exact JKO Step) -/

/-- Higher-grade penalty energy `E(u) = (1/2) ∑_k (φ^k - 1) ‖Π_k u‖²`. -/
noncomputable def gradePenaltyEnergy {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u : CliffordAlgebra Q) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ k ∈ Finset.range (n + 1),
      (φ ^ (k : ℤ) - 1) * cliffordBladeInner Q (cliffordGradeProj Q k u) (cliffordGradeProj Q k u)

theorem gradePenaltyEnergy_eq_repr_sum {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u : CliffordAlgebra Q) :
    gradePenaltyEnergy Q u =
      (1 / 2 : ℝ) *
        ∑ S : Finset (Fin n), (φ ^ (S.card : ℤ) - 1) * ((cliffordBladeBasis Q).repr u S) ^ 2 := by
  dsimp [gradePenaltyEnergy, cliffordBladeInner]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hmem : S.card ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa using S.card_le_univ))
  rw [Finset.sum_eq_single S.card]
  · simp only [repr_cliffordGradeProj, ite_true, pow_two]
  · intro k _ hkS
    simp only [repr_cliffordGradeProj]
    split_ifs with hcard
    · exact (hkS.symm hcard).elim
    · rw [zero_mul, mul_zero]
  · intro hnot
    exact (hnot hmem).elim

theorem gradePenaltyEnergy_nonneg {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u : CliffordAlgebra Q) :
    0 ≤ gradePenaltyEnergy Q u := by
  rw [gradePenaltyEnergy_eq_repr_sum]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun S _ => ?_)
  have hge : (1 : ℝ) ≤ φ ^ (S.card : ℤ) := by
    rw [zpow_natCast]
    exact one_le_pow₀ (le_of_lt Real.one_lt_goldenRatio)
  exact mul_nonneg (sub_nonneg.mpr hge) (sq_nonneg _)

/-- Proximal Parsimonious Flow objective around base state `u₀`:
`J_Q(u₀; u) = gradePenaltyEnergy Q u + (1/2) ‖u - u₀‖²`. -/
noncomputable def parsimoniousProximalObjective {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u₀ u : CliffordAlgebra Q) : ℝ :=
  gradePenaltyEnergy Q u + (1 / 2 : ℝ) * cliffordBladeInner Q (u - u₀) (u - u₀)

/-- **Exact Completion-of-the-Square Identity** for the proximal Parsimonious Flow functional:
the excess energy above `graceOperator Q u₀` equals `(1/2) ⟨u - G_Q u₀, G_Q⁻¹ (u - G_Q u₀)⟩`. -/
theorem parsimoniousProximalObjective_sub_grace {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u₀ u : CliffordAlgebra Q) :
    parsimoniousProximalObjective Q u₀ u -
        parsimoniousProximalObjective Q u₀ (graceOperator Q u₀) =
      (1 / 2 : ℝ) *
        cliffordBladeInner Q (u - graceOperator Q u₀)
          (graceInverseOperator Q (u - graceOperator Q u₀)) := by
  dsimp [parsimoniousProximalObjective, cliffordBladeInner]
  rw [gradePenaltyEnergy_eq_repr_sum, gradePenaltyEnergy_eq_repr_sum]
  simp only [repr_graceOperator, repr_graceInverseOperator, map_sub, Finsupp.coe_sub, Pi.sub_apply]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [zpow_neg φ (S.card : ℤ), ← mul_sub (φ ^ (S.card : ℤ))]
  exact scalar_proximal_completion ((cliffordBladeBasis Q).repr u S)
    ((cliffordBladeBasis Q).repr u₀ S) (φ ^ (S.card : ℤ))
    (zpow_ne_zero _ Real.goldenRatio_ne_zero)

theorem parsimoniousProximalObjective_lower_bound {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u₀ u : CliffordAlgebra Q) :
    parsimoniousProximalObjective Q u₀ (graceOperator Q u₀) +
        (1 / 2 : ℝ) * cliffordBladeInner Q (u - graceOperator Q u₀) (u - graceOperator Q u₀) ≤
      parsimoniousProximalObjective Q u₀ u := by
  have hid := parsimoniousProximalObjective_sub_grace Q u₀ u
  have hle :
      cliffordBladeInner Q (u - graceOperator Q u₀) (u - graceOperator Q u₀) ≤
        cliffordBladeInner Q (u - graceOperator Q u₀)
          (graceInverseOperator Q (u - graceOperator Q u₀)) := by
    dsimp [cliffordBladeInner]
    simp only [repr_graceInverseOperator]
    refine Finset.sum_le_sum fun S _ => ?_
    have hge : (1 : ℝ) ≤ φ ^ (S.card : ℤ) := by
      rw [zpow_natCast]
      exact one_le_pow₀ (le_of_lt Real.one_lt_goldenRatio)
    rw [mul_left_comm ((cliffordBladeBasis Q).repr (u - graceOperator Q u₀) S)
      (φ ^ (S.card : ℤ)) _]
    simpa using mul_le_mul_of_nonneg_right hge (mul_self_nonneg _)
  exact scalar_lower_bound_of_diff hid (mul_le_mul_of_nonneg_left hle (by positivity))

/-- **Unique Global Minimizer Theorem**: `graceOperator Q u₀` is the unique global
minimizer of the proximal Parsimonious Flow objective `parsimoniousProximalObjective Q u₀`. -/
theorem graceOperator_is_unique_proximal_minimizer {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (u₀ u : CliffordAlgebra Q) :
    parsimoniousProximalObjective Q u₀ (graceOperator Q u₀) ≤
        parsimoniousProximalObjective Q u₀ u ∧
      (parsimoniousProximalObjective Q u₀ u =
          parsimoniousProximalObjective Q u₀ (graceOperator Q u₀) ↔
        u = graceOperator Q u₀) := by
  have hlb := parsimoniousProximalObjective_lower_bound Q u₀ u
  have hnn : 0 ≤ cliffordBladeInner Q (u - graceOperator Q u₀) (u - graceOperator Q u₀) :=
    cliffordBladeInner_self_nonneg Q _
  obtain ⟨hle, himp⟩ := scalar_le_and_eq_zero hlb (mul_nonneg (by positivity) hnn)
  refine ⟨hle, ?_⟩
  constructor
  · intro heq
    have hzero : cliffordBladeInner Q (u - graceOperator Q u₀) (u - graceOperator Q u₀) = 0 :=
      (mul_eq_zero.mp (himp heq)).resolve_left (by norm_num)
    exact sub_eq_zero.mp ((cliffordBladeInner_self_eq_zero Q _).mp hzero)
  · rintro rfl
    rfl

end BladeHilbertSpace

/-! ## Part E: Minkowski `Cl(3,1)` Krein Signature Contrast and Krein Involution -/

section MinkowskiKrein

/-- The general reversal scalar pairing `hTrace_cl Q (reverse u * v)` on any `CliffordAlgebra Q`.
In indefinite signatures this is a Krein pairing rather than a positive-definite inner product. -/
noncomputable def cliffordKreinPairing {R : Type*} [CommRing R] [Invertible (2 : R)]
    {M : Type*} [AddCommGroup M] [Module R M] (Q : QuadraticForm R M)
    (u v : CliffordAlgebra Q) : R :=
  hTrace_cl Q (CliffordAlgebra.reverse u * v)

/-- Closed formula for `cliffordKreinPairing` on grade-1 vectors:
`cliffordKreinPairing Q (ι Q a) (ι Q b) = (QuadraticMap.associated (R := R) Q) a b`. -/
theorem cliffordKreinPairing_ι_ι {R : Type*} [CommRing R] [Invertible (2 : R)]
    {M : Type*} [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) (a b : M) :
    cliffordKreinPairing Q (CliffordAlgebra.ι Q a) (CliffordAlgebra.ι Q b) =
      QuadraticMap.associated (R := R) Q a b := by
  dsimp [cliffordKreinPairing, hTrace_cl]
  rw [CliffordAlgebra.reverse_ι]
  simp only [CliffordAlgebra.changeFormEquiv_apply, CliffordAlgebra.changeForm_ι_mul_ι]
  rw [map_sub]
  have hι :
      (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R M →ₐ[R] R)
          (ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R b) = 0 := by
    rw [map_mul]
    simp [ExteriorAlgebra.algebraMapInv]
  rw [hι, zero_sub, AlgHom.commutes]
  change -QuadraticMap.associatedHom R (-Q) a b = QuadraticMap.associatedHom R Q a b
  rw [map_neg, LinearMap.neg_apply, LinearMap.neg_apply, neg_neg]

/-- Minkowski `(+, +, +, -)` signature weights on `Fin 4`. -/
def signatureWeights31 : Fin 4 → ℝ := ![1, 1, 1, -1]

/-- Minkowski quadratic form on `ℝ⁴` with signature `(+, +, +, -)`. -/
noncomputable def Q31 : QuadraticForm ℝ (Fin 4 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ signatureWeights31

/-- Canonical 16-dimensional Minkowski Clifford algebra `Cl(3,1)`. -/
abbrev Cl31 : Type := CliffordAlgebra Q31

theorem Q31_basis_vector (i : Fin 4) : Q31 (Pi.single i (1 : ℝ)) = signatureWeights31 i := by
  simp only [Q31, QuadraticMap.weightedSumSquares_apply]
  fin_cases i <;>
    simp [signatureWeights31, Pi.single_apply]

/-- The timelike basis vector `γ₃` has `cliffordKreinPairing Q31 γ₃ γ₃ = -1`. -/
theorem cliffordKreinPairing_Q31_timelike :
    cliffordKreinPairing Q31 (CliffordAlgebra.ι Q31 (Pi.single 3 (1 : ℝ)))
      (CliffordAlgebra.ι Q31 (Pi.single 3 (1 : ℝ))) = -1 := by
  rw [cliffordKreinPairing_ι_ι, QuadraticMap.associated_eq_self_apply, Q31_basis_vector]
  rfl

/-- Explicit refutation of naïve Minkowski positivity: the Clifford reversal trace pairing on
`Cl(3,1)` is indefinite (it attains `-1 < 0` on the timelike generator). -/
theorem not_nonneg_cliffordKreinPairing_Q31 :
    ¬ ∀ u : Cl31, 0 ≤ cliffordKreinPairing Q31 u u := by
  intro h
  have hle := h (CliffordAlgebra.ι Q31 (Pi.single 3 (1 : ℝ)))
  rw [cliffordKreinPairing_Q31_timelike] at hle
  exact (by norm_num : ¬ (0 : ℝ) ≤ -1) hle

/-- Associated bilinear form of `Q31` evaluated directly in Minkowski coordinates. -/
theorem associated_Q31_apply (v w : Fin 4 → ℝ) :
    QuadraticMap.associated (R := ℝ) Q31 v w =
      ∑ i : Fin 4, signatureWeights31 i * (v i * w i) := by
  have h2 : (2 : ℝ) * QuadraticMap.associated (R := ℝ) Q31 v w = QuadraticMap.polar Q31 v w := by
    have hns := LinearMap.congr_fun
      (LinearMap.congr_fun (QuadraticMap.two_nsmul_associated (R := ℝ) ℝ Q31) v) w
    simp only [LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at hns
    exact hns
  have hpol :
      QuadraticMap.polar Q31 v w = 2 * ∑ i : Fin 4, signatureWeights31 i * (v i * w i) := by
    rw [QuadraticMap.polar, Q31]
    simp only [QuadraticMap.weightedSumSquares_apply, Pi.add_apply, smul_eq_mul]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact scalar_two_mul_sig_pair (signatureWeights31 i) (v i) (w i)
  exact mul_left_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0) (h2.trans hpol)

/-- Krein fundamental symmetry involution `J₃,₁` on `ℝ⁴`, flipping the timelike coordinate. -/
def kreinFlip31 : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v i := if i = 3 then -v i else v i
  map_add' v w := by
    ext i
    simp only [Pi.add_apply]
    split_ifs with h
    · exact neg_add (v i) (w i)
    · rfl
  map_smul' r v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs with h
    · exact (mul_neg r (v i)).symm
    · rfl

theorem kreinFlip31_involutive (v : Fin 4 → ℝ) : kreinFlip31 (kreinFlip31 v) = v := by
  ext i
  dsimp [kreinFlip31]
  split_ifs <;> simp

/-- Inserting the Krein fundamental symmetry `kreinFlip31` converts the Minkowski grade-1
Clifford pairing into the strictly positive-definite Euclidean inner product on `ℝ⁴`. -/
theorem cliffordKreinPairing_Q31_kreinFlip_vectors (v w : Fin 4 → ℝ) :
    cliffordKreinPairing Q31 (CliffordAlgebra.ι Q31 (kreinFlip31 v)) (CliffordAlgebra.ι Q31 w) =
      ∑ i : Fin 4, v i * w i := by
  rw [cliffordKreinPairing_ι_ι, associated_Q31_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  fin_cases i <;> simp [signatureWeights31, kreinFlip31]

theorem cliffordKreinPairing_Q31_kreinFlip_self_nonneg (v : Fin 4 → ℝ) :
    0 ≤ cliffordKreinPairing Q31 (CliffordAlgebra.ι Q31 (kreinFlip31 v))
      (CliffordAlgebra.ι Q31 v) := by
  rw [cliffordKreinPairing_Q31_kreinFlip_vectors]
  exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem cliffordKreinPairing_Q31_kreinFlip_self_eq_zero (v : Fin 4 → ℝ) :
    cliffordKreinPairing Q31 (CliffordAlgebra.ι Q31 (kreinFlip31 v))
        (CliffordAlgebra.ι Q31 v) = 0 ↔ v = 0 := by
  rw [cliffordKreinPairing_Q31_kreinFlip_vectors,
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ => mul_self_nonneg _]
  constructor
  · intro h
    ext i
    simpa [mul_self_eq_zero] using h i (Finset.mem_univ i)
  · rintro rfl _ _
    simp

end MinkowskiKrein

/-! ## Part F: Coordinate-Less Isometry Invariance -/

section IsometryInvariance

section GeneralRing

variable {R : Type*} [CommRing R]
variable {M M₁ M₂ : Type*} [AddCommGroup M] [Module R M]
variable [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

theorem Q_map_isometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (m : M₁) :
    Q₂ (f m) = Q₁ m :=
  f.map_app m

theorem ι_sq_of_isometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (m : M₁) :
    (CliffordAlgebra.ι Q₂ (f m)) ^ 2 = algebraMap R (CliffordAlgebra Q₂) (Q₁ m) := by
  rw [sq, CliffordAlgebra.ι_sq_scalar, f.map_app]

theorem ι_sq_equivOfIsometry {Q : QuadraticForm R M}
    (e : Q.IsometryEquiv Q) (m : M) :
    (CliffordAlgebra.ι Q (e m)) ^ 2 = (CliffordAlgebra.ι Q m) ^ 2 := by
  rw [sq, sq, CliffordAlgebra.ι_sq_scalar, CliffordAlgebra.ι_sq_scalar, e.map_app]

theorem involute_map {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.involute (CliffordAlgebra.map f x) =
      CliffordAlgebra.map f (CliffordAlgebra.involute x) := by
  have h :
      CliffordAlgebra.involute.comp (CliffordAlgebra.map f) =
        (CliffordAlgebra.map f).comp CliffordAlgebra.involute := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro m
    simp
  exact AlgHom.congr_fun h x

theorem involute_equivOfIsometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.involute (CliffordAlgebra.equivOfIsometry e x) =
      CliffordAlgebra.equivOfIsometry e (CliffordAlgebra.involute x) :=
  involute_map e.toIsometry x

theorem reverse_map {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.reverse (CliffordAlgebra.map f x) =
      CliffordAlgebra.map f (CliffordAlgebra.reverse x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [CliffordAlgebra.reverse.commutes]
  | ι m => simp
  | mul a b ha hb => simp [CliffordAlgebra.reverse.map_mul, ha, hb]
  | add a b ha hb => simp [map_add, ha, hb]

theorem reverse_equivOfIsometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.reverse (CliffordAlgebra.equivOfIsometry e x) =
      CliffordAlgebra.equivOfIsometry e (CliffordAlgebra.reverse x) :=
  reverse_map e.toIsometry x

theorem star_map {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (x : CliffordAlgebra Q₁) :
    star (CliffordAlgebra.map f x) = CliffordAlgebra.map f (star x) := by
  simp only [CliffordAlgebra.star_def, involute_map, reverse_map]

theorem star_equivOfIsometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) (x : CliffordAlgebra Q₁) :
    star (CliffordAlgebra.equivOfIsometry e x) = CliffordAlgebra.equivOfIsometry e (star x) :=
  star_map e.toIsometry x

private theorem submodule_pow_mono {A : Type*} [Ring A] [Algebra R A]
    {S T : Submodule R A} (hST : S ≤ T) (k : ℕ) : S ^ k ≤ T ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact Submodule.mul_le.mpr fun _ ha _ hb => Submodule.mul_mem_mul (ih ha) (hST hb)

theorem evenOdd_map_le {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (i : ZMod 2) :
    (CliffordAlgebra.evenOdd Q₁ i).map (CliffordAlgebra.map f).toLinearMap ≤
      CliffordAlgebra.evenOdd Q₂ i := by
  rw [CliffordAlgebra.evenOdd, Submodule.map_iSup]
  refine iSup_le fun j => ?_
  refine le_trans ?_ (le_iSup (fun k : { n : ℕ // (n : ZMod 2) = i } =>
    LinearMap.range (CliffordAlgebra.ι Q₂) ^ (k : ℕ)) j)
  rw [Submodule.map_pow, CliffordAlgebra.ι_range_map_map]
  refine submodule_pow_mono ?_ (j : ℕ)
  rintro _ ⟨m, _, rfl⟩
  exact ⟨m, rfl⟩

theorem evenOdd_map_equivOfIsometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) (i : ZMod 2) :
    (CliffordAlgebra.evenOdd Q₁ i).map (CliffordAlgebra.equivOfIsometry e).toLinearMap =
      CliffordAlgebra.evenOdd Q₂ i := by
  refine le_antisymm (evenOdd_map_le e.toIsometry i) ?_
  intro y hy
  have hy' : (CliffordAlgebra.equivOfIsometry e.symm) y ∈ CliffordAlgebra.evenOdd Q₁ i :=
    evenOdd_map_le e.symm.toIsometry i (Submodule.mem_map_of_mem hy)
  refine ⟨CliffordAlgebra.equivOfIsometry e.symm y, hy', ?_⟩
  change (CliffordAlgebra.equivOfIsometry e) ((CliffordAlgebra.equivOfIsometry e).symm y) = y
  exact (CliffordAlgebra.equivOfIsometry e).apply_symm_apply y

theorem equivOfIsometry_mem_evenOdd_iff {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) (i : ZMod 2) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.equivOfIsometry e x ∈ CliffordAlgebra.evenOdd Q₂ i ↔
      x ∈ CliffordAlgebra.evenOdd Q₁ i := by
  constructor
  · intro hx
    have hback := evenOdd_map_le e.symm.toIsometry i (Submodule.mem_map_of_mem hx)
    change CliffordAlgebra.equivOfIsometry e.symm (CliffordAlgebra.equivOfIsometry e x) ∈
      CliffordAlgebra.evenOdd Q₁ i at hback
    rw [← CliffordAlgebra.equivOfIsometry_symm,
      (CliffordAlgebra.equivOfIsometry e).symm_apply_apply] at hback
    exact hback
  · intro hx
    exact evenOdd_map_le e.toIsometry i (Submodule.mem_map_of_mem hx)

noncomputable def evenEquivOfIsometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) :
    CliffordAlgebra.even Q₁ ≃ₐ[R] CliffordAlgebra.even Q₂ :=
  AlgEquiv.ofAlgHom
    (((CliffordAlgebra.equivOfIsometry e).toAlgHom.comp (CliffordAlgebra.even Q₁).val).codRestrict
      (CliffordAlgebra.even Q₂) fun x =>
        (equivOfIsometry_mem_evenOdd_iff e 0 x.1).mpr x.2)
    (((CliffordAlgebra.equivOfIsometry e.symm).toAlgHom.comp
        (CliffordAlgebra.even Q₂).val).codRestrict
      (CliffordAlgebra.even Q₁) fun x =>
        (equivOfIsometry_mem_evenOdd_iff e.symm 0 x.1).mpr x.2)
    (by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      exact (CliffordAlgebra.equivOfIsometry e).apply_symm_apply x.1)
    (by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      change (CliffordAlgebra.equivOfIsometry e.symm)
        ((CliffordAlgebra.equivOfIsometry e) x.1) = x.1
      rw [← CliffordAlgebra.equivOfIsometry_symm,
        (CliffordAlgebra.equivOfIsometry e).symm_apply_apply])

theorem evenOdd_proj_equivOfIsometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) (i : ZMod 2) (x : CliffordAlgebra Q₁) :
    GradedAlgebra.proj (CliffordAlgebra.evenOdd Q₂) i (CliffordAlgebra.equivOfIsometry e x) =
      CliffordAlgebra.equivOfIsometry e (GradedAlgebra.proj (CliffordAlgebra.evenOdd Q₁) i x) := by
  induction x using DirectSum.Decomposition.inductionOn (CliffordAlgebra.evenOdd Q₁) with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | homogeneous hx =>
    rename_i j
    rcases hx with ⟨a, ha⟩
    have ha2 : CliffordAlgebra.equivOfIsometry e a ∈ CliffordAlgebra.evenOdd Q₂ j :=
      (equivOfIsometry_mem_evenOdd_iff e j a).mpr ha
    by_cases hij : j = i
    · subst hij
      simp only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem _ ha,
        DirectSum.decompose_of_mem _ ha2, DirectSum.of_eq_same]
    · simp only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem _ ha,
        DirectSum.decompose_of_mem _ ha2, DirectSum.of_eq_of_ne j i _ (Ne.symm hij),
        ZeroMemClass.coe_zero, map_zero]

theorem map_contractLeft {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (d : Module.Dual R M₂) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f.toLinearMap) x) =
      CliffordAlgebra.contractLeft d (CliffordAlgebra.map f x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul x_cl m hx =>
    simp only [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
      CliffordAlgebra.map_apply_ι, LinearMap.comp_apply, hx]
    rfl

theorem exteriorPower_map_le (g : M₁ →ₗ[R] M₂) (k : ℕ) :
    (⋀[R]^k M₁).map (ExteriorAlgebra.map g).toLinearMap ≤ ⋀[R]^k M₂ := by
  rw [ExteriorAlgebra.exteriorPower, ExteriorAlgebra.exteriorPower, Submodule.map_pow,
    ExteriorAlgebra.ι_range_map_map]
  refine submodule_pow_mono ?_ k
  rintro _ ⟨m, _, rfl⟩
  exact ⟨m, rfl⟩

theorem exteriorGradeProj_map (g : M₁ →ₗ[R] M₂) (k : ℕ) (y : ExteriorAlgebra R M₁) :
    ExteriorAlgebra.map g (exteriorGradeProj R M₁ k y) =
      exteriorGradeProj R M₂ k (ExteriorAlgebra.map g y) := by
  induction y using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[R]^i M₁) with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | homogeneous hy =>
    rename_i j
    rcases hy with ⟨a, ha⟩
    have ha2 : ExteriorAlgebra.map g a ∈ ⋀[R]^j M₂ :=
      exteriorPower_map_le g j (Submodule.mem_map_of_mem ha)
    by_cases hjk : j = k
    · subst hjk
      rw [exteriorGradeProj_of_mem ha, exteriorGradeProj_of_mem ha2]
    · rw [exteriorGradeProj_of_mem_ne hjk ha, exteriorGradeProj_of_mem_ne hjk ha2, map_zero]

theorem exterior_algebraMapInv_map (g : M₁ →ₗ[R] M₂) (y : ExteriorAlgebra R M₁) :
    ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.map g y) =
      ExteriorAlgebra.algebraMapInv y := by
  have h :
      (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R M₂ →ₐ[R] R).comp
          (ExteriorAlgebra.map g) =
        ExteriorAlgebra.algebraMapInv := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro m
    simp [ExteriorAlgebra.algebraMapInv]
  exact AlgHom.congr_fun h y

theorem exteriorGradeProj_involute (k : ℕ) (y : ExteriorAlgebra R M) :
    exteriorGradeProj R M k (CliffordAlgebra.involute y) =
      (-1 : R) ^ k • exteriorGradeProj R M k y := by
  have hpow : ∀ (j : ℕ) (a : ExteriorAlgebra R M), a ∈ ⋀[R]^j M →
      CliffordAlgebra.involute a = (-1 : R) ^ j • a := by
    intro j
    induction j with
    | zero =>
      intro a ha
      rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.one_eq_span,
        Submodule.mem_span_singleton] at ha
      rcases ha with ⟨r, rfl⟩
      rw [Algebra.smul_def, mul_one, AlgHom.commutes, pow_zero, one_smul]
    | succ j ih =>
      intro a ha
      rw [ExteriorAlgebra.exteriorPower, pow_succ] at ha
      refine Submodule.mul_induction_on ha ?_ ?_
      · intro u hu v hv
        rw [← ExteriorAlgebra.exteriorPower] at hu
        rcases LinearMap.mem_range.mp hv with ⟨m, rfl⟩
        rw [map_mul, ih u hu, show CliffordAlgebra.involute (ExteriorAlgebra.ι R m) =
          -ExteriorAlgebra.ι R m from CliffordAlgebra.involute_ι m,
          smul_mul_assoc, mul_neg, smul_neg, ← neg_smul, pow_succ, mul_neg_one]
      · intro u v hu hv
        rw [map_add, hu, hv, smul_add]
  induction y using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[R]^i M) with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]
  | homogeneous hy =>
    rename_i j
    rcases hy with ⟨a, ha⟩
    have hinv : CliffordAlgebra.involute a = (-1 : R) ^ j • a := hpow j a ha
    have ha_mem : CliffordAlgebra.involute a ∈ ⋀[R]^j M := by
      rw [hinv]
      exact Submodule.smul_mem _ _ ha
    by_cases hjk : j = k
    · subst hjk
      rw [exteriorGradeProj_of_mem ha_mem, exteriorGradeProj_of_mem ha, hinv]
    · rw [exteriorGradeProj_of_mem_ne hjk ha_mem, exteriorGradeProj_of_mem_ne hjk ha, smul_zero]

theorem involute_contractLeft (Q : QuadraticForm R M) (d : Module.Dual R M)
    (x : CliffordAlgebra Q) :
    CliffordAlgebra.involute (CliffordAlgebra.contractLeft d x) =
      -(CliffordAlgebra.contractLeft d (CliffordAlgebra.involute x)) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add a b ha hb => simp only [map_add, ha, hb, neg_add]
  | ι_mul x_cl m hx =>
    rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
      CliffordAlgebra.involute_ι, hx, neg_mul, mul_neg, neg_neg]
    rw [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg, neg_neg,
      CliffordAlgebra.contractLeft_ι_mul]

end GeneralRing

section InvertibleTwo

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M M₁ M₂ : Type*} [AddCommGroup M] [Module R M]
variable [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

private theorem associated_neg_comp_isometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (m : M₁) :
    ((QuadraticMap.associated (R := R) (-Q₂)) (f m)).comp f.toLinearMap =
      (QuadraticMap.associated (R := R) (-Q₁)) m := by
  ext y
  simp only [LinearMap.comp_apply, QuadraticMap.associated_apply, neg_apply]
  change ⅟2 • (-Q₂ (f m + f y) - -Q₂ (f m) - -Q₂ (f y)) = ⅟2 • (-Q₁ (m + y) - -Q₁ m - -Q₁ y)
  rw [← map_add f, f.map_app, f.map_app, f.map_app]

theorem equivExterior_map {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.equivExterior Q₂ (CliffordAlgebra.map f x) =
      ExteriorAlgebra.map f.toLinearMap (CliffordAlgebra.equivExterior Q₁ x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [AlgHom.commutes, equivExterior_algebraMap]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul x_cl m hx =>
    simp only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply] at hx ⊢
    rw [map_mul, CliffordAlgebra.map_apply_ι, CliffordAlgebra.changeForm_ι_mul, hx,
      CliffordAlgebra.changeForm_ι_mul, map_sub, map_mul, ExteriorAlgebra.map_apply_ι]
    congr 1
    have hzero :
        ExteriorAlgebra.map f.toLinearMap
            (CliffordAlgebra.contractLeft (QuadraticMap.associated (R := R) (-Q₁) m)
              (CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof x_cl)) =
          CliffordAlgebra.contractLeft (QuadraticMap.associated (R := R) (-Q₂) (f m))
            (ExteriorAlgebra.map f.toLinearMap
              (CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof
                x_cl)) := by
      have hmap := map_contractLeft
        (Q₁ := (0 : QuadraticForm R M₁)) (Q₂ := (0 : QuadraticForm R M₂))
        { f.toLinearMap with map_app' := fun _ => rfl }
        (QuadraticMap.associated (R := R) (-Q₂) (f m))
        (CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof x_cl)
      rw [associated_neg_comp_isometry f m] at hmap
      exact hmap
    exact hzero.symm

theorem equivExterior_equivOfIsometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.equivExterior Q₂ (CliffordAlgebra.equivOfIsometry e x) =
      ExteriorAlgebra.map (e : M₁ →ₗ[R] M₂) (CliffordAlgebra.equivExterior Q₁ x) :=
  equivExterior_map e.toIsometry x

theorem equivExterior_symm_equivOfIsometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) (y : ExteriorAlgebra R M₁) :
    CliffordAlgebra.equivOfIsometry e ((CliffordAlgebra.equivExterior Q₁).symm y) =
      (CliffordAlgebra.equivExterior Q₂).symm (ExteriorAlgebra.map (e : M₁ →ₗ[R] M₂) y) := by
  apply (CliffordAlgebra.equivExterior Q₂).injective
  rw [equivExterior_equivOfIsometry, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem cliffordGradeProj_map {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (k : ℕ) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.map f (cliffordGradeProj Q₁ k x) =
      cliffordGradeProj Q₂ k (CliffordAlgebra.map f x) := by
  apply (CliffordAlgebra.equivExterior Q₂).injective
  rw [equivExterior_map]
  change ExteriorAlgebra.map f.toLinearMap
      (CliffordAlgebra.equivExterior Q₁
        ((CliffordAlgebra.equivExterior Q₁).symm
          (exteriorGradeProj R M₁ k (CliffordAlgebra.equivExterior Q₁ x)))) =
    CliffordAlgebra.equivExterior Q₂
      ((CliffordAlgebra.equivExterior Q₂).symm
        (exteriorGradeProj R M₂ k (CliffordAlgebra.equivExterior Q₂ (CliffordAlgebra.map f x))))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, exteriorGradeProj_map,
    equivExterior_map]

theorem cliffordGradeProj_equivOfIsometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) (k : ℕ) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.equivOfIsometry e (cliffordGradeProj Q₁ k x) =
      cliffordGradeProj Q₂ k (CliffordAlgebra.equivOfIsometry e x) :=
  cliffordGradeProj_map e.toIsometry k x

/-- Grade-`k` Clifford submodule `LinearMap.range (cliffordGradeProj Q k)`. -/
noncomputable def cliffordGradeSubmodule (Q : QuadraticForm R M) (k : ℕ) :
    Submodule R (CliffordAlgebra Q) :=
  LinearMap.range (cliffordGradeProj Q k)

theorem mem_cliffordGradeSubmodule_iff {Q : QuadraticForm R M} (k : ℕ) (x : CliffordAlgebra Q) :
    x ∈ cliffordGradeSubmodule Q k ↔ cliffordGradeProj Q k x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact cliffordGradeProj_idem Q k y
  · intro hx
    exact ⟨x, hx⟩

theorem mem_cliffordGradeSubmodule_equivOfIsometry_iff
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) (k : ℕ) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.equivOfIsometry e x ∈ cliffordGradeSubmodule Q₂ k ↔
      x ∈ cliffordGradeSubmodule Q₁ k := by
  rw [mem_cliffordGradeSubmodule_iff, mem_cliffordGradeSubmodule_iff,
    ← cliffordGradeProj_equivOfIsometry e k x]
  exact (CliffordAlgebra.equivOfIsometry e).injective.eq_iff

theorem hTrace_cl_map {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (x : CliffordAlgebra Q₁) :
    hTrace_cl Q₂ (CliffordAlgebra.map f x) = hTrace_cl Q₁ x := by
  change ExteriorAlgebra.algebraMapInv (CliffordAlgebra.equivExterior Q₂ (CliffordAlgebra.map f x)) =
    ExteriorAlgebra.algebraMapInv (CliffordAlgebra.equivExterior Q₁ x)
  rw [equivExterior_map, exterior_algebraMapInv_map]

theorem hTrace_cl_equivOfIsometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) (x : CliffordAlgebra Q₁) :
    hTrace_cl Q₂ (CliffordAlgebra.equivOfIsometry e x) = hTrace_cl Q₁ x :=
  hTrace_cl_map e.toIsometry x

theorem cliffordKreinPairing_equivOfIsometry {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) (u v : CliffordAlgebra Q₁) :
    cliffordKreinPairing Q₂ (CliffordAlgebra.equivOfIsometry e u)
        (CliffordAlgebra.equivOfIsometry e v) =
      cliffordKreinPairing Q₁ u v := by
  dsimp [cliffordKreinPairing]
  rw [reverse_equivOfIsometry, ← map_mul, hTrace_cl_equivOfIsometry]

theorem equivExterior_involute (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    CliffordAlgebra.equivExterior Q (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute (CliffordAlgebra.equivExterior Q x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [AlgHom.commutes, equivExterior_algebraMap]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul x_cl m hx =>
    simp only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply] at hx ⊢
    rw [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg, CliffordAlgebra.changeForm_ι_mul,
      hx, CliffordAlgebra.changeForm_ι_mul, map_sub, map_mul, CliffordAlgebra.involute_ι,
      neg_mul]
    have hinvol :
        CliffordAlgebra.involute
            (CliffordAlgebra.contractLeft (QuadraticMap.associated (R := R) (-Q) m)
              (CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof
                x_cl)) =
          -(CliffordAlgebra.contractLeft (QuadraticMap.associated (R := R) (-Q) m)
            (CliffordAlgebra.involute
              (CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof
                x_cl))) :=
      involute_contractLeft (0 : QuadraticForm R M) _ _
    rw [hinvol]
    module

theorem cliffordGradeProj_involute (Q : QuadraticForm R M) (k : ℕ) (x : CliffordAlgebra Q) :
    cliffordGradeProj Q k (CliffordAlgebra.involute x) =
      (-1 : R) ^ k • cliffordGradeProj Q k x := by
  change (CliffordAlgebra.equivExterior Q).symm
      (exteriorGradeProj R M k (CliffordAlgebra.equivExterior Q (CliffordAlgebra.involute x))) =
    (-1 : R) ^ k •
      (CliffordAlgebra.equivExterior Q).symm
        (exteriorGradeProj R M k (CliffordAlgebra.equivExterior Q x))
  rw [equivExterior_involute, exteriorGradeProj_involute, map_smul]

end InvertibleTwo

section RealGraceInvariance

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℝ M₁]
variable [AddCommGroup M₂] [Module ℝ M₂]

theorem graceOperator_equivOfIsometry {Q₁ : QuadraticForm ℝ M₁} {Q₂ : QuadraticForm ℝ M₂}
    (e : Q₁.IsometryEquiv Q₂) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.equivOfIsometry e (graceOperator Q₁ x) =
      graceOperator Q₂ (CliffordAlgebra.equivOfIsometry e x) := by
  have hfin : Module.finrank ℝ M₁ = Module.finrank ℝ M₂ :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  rw [graceOperator_apply, graceOperator_apply, map_sum, hfin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, cliffordGradeProj_equivOfIsometry]

theorem graceInverseOperator_equivOfIsometry {Q₁ : QuadraticForm ℝ M₁} {Q₂ : QuadraticForm ℝ M₂}
    (e : Q₁.IsometryEquiv Q₂) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.equivOfIsometry e (graceInverseOperator Q₁ x) =
      graceInverseOperator Q₂ (CliffordAlgebra.equivOfIsometry e x) := by
  have hfin : Module.finrank ℝ M₁ = Module.finrank ℝ M₂ :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  rw [graceInverseOperator_apply, graceInverseOperator_apply, map_sum, hfin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, cliffordGradeProj_equivOfIsometry]

end RealGraceInvariance

end IsometryInvariance

end InfoGeometry.Clifford.GradedGraceContraction
