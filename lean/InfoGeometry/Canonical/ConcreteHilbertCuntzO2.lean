/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ConcreteHilbertCommutation
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.ErlangenNet
open InfoGeometry.Topology
open InfoGeometry.Canonical.ConcreteHilbertCommutation

/-!
# Completed Two-Branch Hilbert Cuntz $O_2$ Decomposition on `H_lp`

Constructs the right Cuntz branch operator `S_right_lp_clm` on the completed
Hilbert boundary carrier `H_lp E := lp (fun _ : BinaryCantorBoundary => DoubledSpace E) 2`
mirroring `S_left_lp_clm` from `ConcreteHilbertCommutation`, proves that it is
an isometry commuting with the fiber phase-axis operator `K_lp_clm`, and establishes
the Cuntz $O_2$ complementary orthogonal range decomposition alongside `S_left_lp_clm`.
-/

namespace InfoGeometry.Canonical.ConcreteHilbertCuntzO2

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Coefficient-function action of the right Cuntz branch (`δ_ω ↦ δ_{minus·ω}`). -/
def S_right_raw (ψ : BinaryCantorBoundary → DoubledSpace E) (x : BinaryCantorBoundary) :
    DoubledSpace E :=
  if headBoundary x = BinarySector.minus then ψ (tailBoundary x) else 0

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma S_right_raw_norm (ψ : BinaryCantorBoundary → DoubledSpace E) (x : BinaryCantorBoundary) :
    ‖S_right_raw ψ x‖ = if headBoundary x = BinarySector.minus then ‖ψ (tailBoundary x)‖ else 0 := by
  unfold S_right_raw
  split_ifs
  · rfl
  · rw [norm_zero]

/-- Explicit equivalence identifying the `minus`-headed boundary sector with the full Cantor boundary. -/
def minusEquiv : BinaryCantorBoundary ≃ { x : BinaryCantorBoundary // headBoundary x = BinarySector.minus } where
  toFun x := ⟨prefixBoundary BinarySector.minus x, rfl⟩
  invFun y := tailBoundary y.1
  left_inv x := by
    ext n
    rfl
  right_inv y := by
    ext n
    cases n
    · exact y.2.symm
    · rfl

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma summable_S_right_raw (ψ : BinaryCantorBoundary → DoubledSpace E)
    (h : Summable fun x => ‖ψ x‖ ^ (2 : ℝ)) :
    Summable fun x => ‖S_right_raw ψ x‖ ^ (2 : ℝ) := by
  have h_split := @summable_subtype_and_compl ℝ BinaryCantorBoundary _ _ _
    (fun x => ‖S_right_raw ψ x‖ ^ (2 : ℝ)) _ { x | headBoundary x = BinarySector.minus }
  rw [← h_split]
  constructor
  · have heq : (fun (y : { x // headBoundary x = BinarySector.minus }) => ‖S_right_raw ψ y.1‖ ^ (2 : ℝ)) =
        (fun x : BinaryCantorBoundary => ‖ψ x‖ ^ (2 : ℝ)) ∘ minusEquiv.symm := by
      ext y
      dsimp [minusEquiv]
      rw [S_right_raw_norm]
      have hy : headBoundary y.1 = BinarySector.minus := y.2
      simp only [hy, ite_true]
    change Summable (fun (y : { x // headBoundary x = BinarySector.minus }) => ‖S_right_raw ψ y.1‖ ^ (2 : ℝ))
    rw [heq]
    exact (Equiv.summable_iff minusEquiv.symm).mpr h
  · have heq_zero : (fun (y : { x // x ∉ { x | headBoundary x = BinarySector.minus } }) =>
        ‖S_right_raw ψ y.1‖ ^ (2 : ℝ)) = 0 := by
      ext y
      dsimp
      rw [S_right_raw_norm]
      have hy : headBoundary y.1 ≠ BinarySector.minus := y.2
      simp only [hy, ite_false]
      exact Real.zero_rpow two_ne_zero
    change Summable (fun (y : { x // x ∉ { x | headBoundary x = BinarySector.minus } }) =>
      ‖S_right_raw ψ y.1‖ ^ (2 : ℝ))
    rw [heq_zero]
    exact summable_zero

/-- The right Cuntz branch operator on the completed `lp` boundary carrier. -/
def S_right_lp (ψ : H_lp E) : H_lp E :=
  ⟨S_right_raw ψ, by
    apply memℓp_gen
    have h1 : (2 : ENNReal).toReal = 2 := rfl
    rw [h1]
    have h2 : Memℓp ψ.1 2 := ψ.prop
    have h3 := (memℓp_gen_iff zero_lt_two).mp h2
    rw [h1] at h3
    exact summable_S_right_raw ψ h3⟩

/-- The right `lp` Cuntz branch preserves the `L²` norm on the boundary carrier. -/
lemma S_right_lp_norm_eq (ψ : H_lp E) :
    ‖S_right_lp (E := E) ψ‖ = ‖ψ‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hψ : Summable (fun x : BinaryCantorBoundary => ‖ψ x‖ ^ (2 : ℝ)) :=
    (lp.memℓp ψ).summable hp
  have hf : Summable (fun x : BinaryCantorBoundary => ‖S_right_raw ψ x‖ ^ (2 : ℝ)) :=
    summable_S_right_raw ψ hψ
  have hsplit := hf.tsum_subtype_add_tsum_subtype_compl
    { x : BinaryCantorBoundary | headBoundary x = BinarySector.minus }
  have hminus : (∑' y : { x : BinaryCantorBoundary // headBoundary x = BinarySector.minus },
      ‖S_right_raw ψ y.1‖ ^ (2 : ℝ)) =
      ∑' x : BinaryCantorBoundary, ‖ψ x‖ ^ (2 : ℝ) := by
    have heq : (fun (y : { x : BinaryCantorBoundary // headBoundary x = BinarySector.minus }) =>
        ‖S_right_raw ψ y.1‖ ^ (2 : ℝ)) =
        (fun x : BinaryCantorBoundary => ‖ψ x‖ ^ (2 : ℝ)) ∘ minusEquiv.symm := by
      ext y
      dsimp [minusEquiv]
      rw [S_right_raw_norm]
      simp only [y.2, ite_true]
    rw [heq]
    exact (minusEquiv.symm).tsum_eq (fun x => ‖ψ x‖ ^ (2 : ℝ))
  have hplus : (∑' y : { x : BinaryCantorBoundary // x ∉ { x : BinaryCantorBoundary |
      headBoundary x = BinarySector.minus } }, ‖S_right_raw ψ y.1‖ ^ (2 : ℝ)) = 0 := by
    have heq_zero : (fun (y : { x : BinaryCantorBoundary // x ∉ { x : BinaryCantorBoundary |
        headBoundary x = BinarySector.minus } }) =>
        ‖S_right_raw ψ y.1‖ ^ (2 : ℝ)) = 0 := by
      ext y
      have hy : headBoundary y.1 ≠ BinarySector.minus := y.2
      simp [S_right_raw_norm, hy]
    rw [heq_zero]
    exact tsum_zero
  have htsum : (∑' x : BinaryCantorBoundary, ‖S_right_raw ψ x‖ ^ (2 : ℝ)) =
      ∑' x : BinaryCantorBoundary, ‖ψ x‖ ^ (2 : ℝ) := by
    calc
      (∑' x : BinaryCantorBoundary, ‖S_right_raw ψ x‖ ^ (2 : ℝ)) =
          (∑' x : { x : BinaryCantorBoundary // headBoundary x = BinarySector.minus },
            ‖S_right_raw ψ x.1‖ ^ (2 : ℝ)) +
          (∑' x : { x : BinaryCantorBoundary // x ∉ { x : BinaryCantorBoundary |
            headBoundary x = BinarySector.minus } }, ‖S_right_raw ψ x.1‖ ^ (2 : ℝ)) := hsplit.symm
      _ = ∑' x : BinaryCantorBoundary, ‖ψ x‖ ^ (2 : ℝ) := by rw [hminus, hplus, add_zero]
  have hpowS : ‖S_right_lp (E := E) ψ‖ ^ (2 : ℝ) =
      ∑' x : BinaryCantorBoundary, ‖S_right_lp (E := E) ψ x‖ ^ (2 : ℝ) := by
    simpa only [show (2 : ENNReal).toReal = (2 : ℝ) by rfl] using
      (lp.norm_rpow_eq_tsum hp (S_right_lp (E := E) ψ))
  have hpowψ : ‖ψ‖ ^ (2 : ℝ) =
      ∑' x : BinaryCantorBoundary, ‖ψ x‖ ^ (2 : ℝ) := by
    simpa only [show (2 : ENNReal).toReal = (2 : ℝ) by rfl] using
      (lp.norm_rpow_eq_tsum hp ψ)
  have hpow : ‖S_right_lp (E := E) ψ‖ ^ (2 : ℝ) = ‖ψ‖ ^ (2 : ℝ) := by
    rw [hpowS, hpowψ]
    exact htsum
  exact (Real.rpow_left_inj (lp.norm_nonneg' _) (lp.norm_nonneg' _) (by norm_num)).mp hpow

lemma S_right_lp_add (ψ φ : H_lp E) :
    S_right_lp (E := E) (ψ + φ) = S_right_lp ψ + S_right_lp φ := by
  apply Subtype.ext
  funext x
  change S_right_raw (↑(ψ + φ)) x = (S_right_raw (↑ψ) + S_right_raw (↑φ)) x
  rw [lp.coeFn_add]
  dsimp [S_right_raw]
  split_ifs <;> simp

lemma S_right_lp_smul (a : ℝ) (ψ : H_lp E) :
    S_right_lp (E := E) (a • ψ) = a • S_right_lp ψ := by
  apply Subtype.ext
  funext x
  change S_right_raw (↑(a • ψ)) x = (a • S_right_raw (↑ψ)) x
  rw [lp.coeFn_smul]
  dsimp [S_right_raw]
  split_ifs <;> simp

/-- Underlying ℝ-linear map for the right Cuntz branch. -/
def S_right_lp_linear : H_lp E →ₗ[ℝ] H_lp E where
  toFun := S_right_lp
  map_add' := S_right_lp_add
  map_smul' := S_right_lp_smul

/-- Continuous linear map for the right Cuntz branch on `H_lp E`. -/
def S_right_lp_clm : H_lp E →L[ℝ] H_lp E :=
  (S_right_lp_linear (E := E)).mkContinuous 1 (by
    intro ψ
    change ‖S_right_lp ψ‖ ≤ 1 * ‖ψ‖
    rw [S_right_lp_norm_eq]
    simp)

@[simp] theorem S_right_lp_clm_norm_le :
    ‖S_right_lp_clm (E := E)‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le (S_right_lp_linear (E := E)) (by norm_num) (by
    intro ψ
    change ‖S_right_lp ψ‖ ≤ 1 * ‖ψ‖
    rw [S_right_lp_norm_eq]
    simp)

/-- The right Cuntz branch is an isometry on `H_lp E`. -/
theorem S_right_lp_clm_isometry :
    Isometry (S_right_lp_clm (E := E)) := by
  intro ψ φ
  have hnorm := S_right_lp_norm_eq (E := E) (ψ - φ)
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact congrArg ENNReal.ofReal hnorm

/-- Pointwise commutation of `S_right_lp` with `K_lp` on `H_lp E`. -/
theorem S_right_commutes_K_lp (ψ : H_lp E) :
    S_right_lp (K_lp ψ) = K_lp (S_right_lp ψ) := by
  apply Subtype.ext
  funext x
  dsimp [S_right_lp, K_lp, S_right_raw, K_raw]
  split_ifs
  · rfl
  · exact (map_zero (clockAxis (E := E))).symm

/-- Global continuous-linear commutation between `S_right_lp_clm` and `K_lp_clm`. -/
theorem S_right_lp_clm_commutes_K_lp_clm :
    (S_right_lp_clm (E := E)).comp (K_lp_clm (E := E)) =
      (K_lp_clm (E := E)).comp (S_right_lp_clm (E := E)) := by
  apply ContinuousLinearMap.ext
  intro ψ
  exact S_right_commutes_K_lp (E := E) ψ

@[simp] theorem S_left_lp_clm_apply (ψ : H_lp E) (x : BinaryCantorBoundary) :
    S_left_lp_clm (E := E) ψ x =
      if headBoundary x = BinarySector.plus then ψ (tailBoundary x) else 0 :=
  rfl

@[simp] theorem S_right_lp_clm_apply (ψ : H_lp E) (x : BinaryCantorBoundary) :
    S_right_lp_clm (E := E) ψ x =
      if headBoundary x = BinarySector.minus then ψ (tailBoundary x) else 0 :=
  rfl

/-- Complementary orthogonal range disjointness for the two Cuntz branches `S_left` and `S_right`. -/
theorem S_left_right_lp_clm_disjoint (φ₁ φ₂ : H_lp E)
    (h : S_left_lp_clm (E := E) φ₁ = S_right_lp_clm (E := E) φ₂) :
    φ₁ = 0 ∧ φ₂ = 0 := by
  constructor
  · apply Subtype.ext
    funext x
    have hx := congrArg (fun (f : H_lp E) => f (prefixBoundary BinarySector.plus x)) h
    simpa [S_left_lp_clm_apply, S_right_lp_clm_apply] using hx
  · apply Subtype.ext
    funext x
    have hx := congrArg (fun (f : H_lp E) => f (prefixBoundary BinarySector.minus x)) h
    simpa [S_left_lp_clm_apply, S_right_lp_clm_apply] using hx.symm

lemma prefixBoundary_injective (s : BinarySector) :
    Function.Injective (prefixBoundary s) := by
  intro x y hxy
  have h := congrArg tailBoundary hxy
  simpa [tailBoundary_prefixBoundary] using h

/-- Pullback (adjoint coisometry) of a state onto sector `s : BinarySector` on `H_lp E`. -/
def branchPullback (s : BinarySector) (ψ : H_lp E) : H_lp E :=
  ⟨fun x => ψ (prefixBoundary s x), by
    apply memℓp_gen
    have h1 : (2 : ENNReal).toReal = 2 := rfl
    rw [h1]
    have hψ : Summable (fun x : BinaryCantorBoundary => ‖ψ x‖ ^ (2 : ℝ)) := by
      have h2 : Memℓp ψ.1 2 := ψ.prop
      have h3 := (memℓp_gen_iff zero_lt_two).mp h2
      simpa [h1] using h3
    exact hψ.comp_injective (prefixBoundary_injective s)⟩

@[simp] theorem branchPullback_apply (s : BinarySector) (ψ : H_lp E) (x : BinaryCantorBoundary) :
    branchPullback s ψ x = ψ (prefixBoundary s x) :=
  rfl

/-- Cuntz $O_2$ partition-of-unity / surjective range decomposition on `H_lp E`. -/
theorem cuntz_o2_lp_decomposition (ψ : H_lp E) :
    ∃ φ₁ φ₂ : H_lp E,
      ψ = S_left_lp_clm (E := E) φ₁ + S_right_lp_clm (E := E) φ₂ := by
  refine ⟨branchPullback BinarySector.plus ψ, branchPullback BinarySector.minus ψ, ?_⟩
  apply Subtype.ext
  funext x
  rw [lp.coeFn_add]
  cases hhead : headBoundary x
  · have hx : prefixBoundary BinarySector.plus (tailBoundary x) = x := by
      rw [← hhead, boundary_eta x]
    change ψ x =
      S_left_lp_clm (E := E) (branchPullback BinarySector.plus ψ) x +
      S_right_lp_clm (E := E) (branchPullback BinarySector.minus ψ) x
    simp [S_left_lp_clm_apply, S_right_lp_clm_apply, hhead, hx]
  · have hx : prefixBoundary BinarySector.minus (tailBoundary x) = x := by
      rw [← hhead, boundary_eta x]
    change ψ x =
      S_left_lp_clm (E := E) (branchPullback BinarySector.plus ψ) x +
      S_right_lp_clm (E := E) (branchPullback BinarySector.minus ψ) x
    simp [S_left_lp_clm_apply, S_right_lp_clm_apply, hhead, hx]

end InfoGeometry.Canonical.ConcreteHilbertCuntzO2
