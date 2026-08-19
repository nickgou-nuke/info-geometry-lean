import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.lpSpace
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.ErlangenNet
open InfoGeometry.Topology

/-!
# Concrete Cuntz left branch / phase-axis commutation

This module proves the tensor-factor separation identity on the concrete
Cantor-boundary function carrier:

* the left Cuntz branch acts on the boundary index by prefix/tail splitting;
* the phase axis acts only on the doubled fiber.

The theorem here is the branch-correct coefficient-function version of
`S_left (δ_ω ⊗ v) = δ_{0ω} ⊗ v`. On coefficients, this is

`(S_left ψ)(x) = if head x = plus then ψ (tail x) else 0`.

The analytic bounded-extension theorem for the actual `lp` subtype remains the
next closure target. This file proves the exact algebraic commutation on the
`PiLp` boundary carrier and removes the previous `True` placeholder.

#### BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully
checked by the kernel.]

* `tailBoundary_prefixBoundary`
* `boundary_eta`
* `S_left_op_apply_plus`
* `S_left_op_apply_minus`
* `K_op_apply`
* `S_left_commutes_K_apply`
* `S_left_commutes_K`
* `S_left_lp_injective`
* `S_left_lp_norm`
* `S_left_lp_continuousLinearMap`
* `S_left_lp_adjoint`
* `S_left_lp_adjoint_inner_left`
* `K_lp_norm`
* `K_lp_continuousLinearMap`
* `S_left_lp_continuousLinearMap_comp_K_lp_continuousLinearMap_eq_reverse`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported
verified premises.]

* None.

#### BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, interfaces, fields,
witnesses, certificates, or renamed placeholders.]

* None.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConcreteHilbertCommutation

open scoped TensorProduct

section AlgebraicTensorSeparation

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/--
Algebraic tensor-factor separation.

If `S` acts on the Cantor/base factor and `K` acts on the doubled fiber factor,
then the two extended endomorphisms commute on the algebraic tensor product.
Both composites are the tensor map `S ⊗ K`.
-/
@[rep_depth operator]
theorem tensorFactorSeparation_left_eq_tensorMap
    (S : V →ₗ[ℝ] V) (K : W →ₗ[ℝ] W) :
    (TensorProduct.map S (LinearMap.id : W →ₗ[ℝ] W)).comp
        (TensorProduct.map (LinearMap.id : V →ₗ[ℝ] V) K) =
      TensorProduct.map S K := by
  exact TensorProduct.ext' (fun v w => by simp [LinearMap.comp_apply])

/--
Right-then-left tensor-factor separation.  This is the same `S ⊗ K` map.
-/
@[rep_depth operator]
theorem tensorFactorSeparation_right_eq_tensorMap
    (S : V →ₗ[ℝ] V) (K : W →ₗ[ℝ] W) :
    (TensorProduct.map (LinearMap.id : V →ₗ[ℝ] V) K).comp
        (TensorProduct.map S (LinearMap.id : W →ₗ[ℝ] W)) =
      TensorProduct.map S K := by
  exact TensorProduct.ext' (fun v w => by simp [LinearMap.comp_apply])

/--
Tensor-factor separation identity:
`(S ⊗ id) (id ⊗ K) = (id ⊗ K) (S ⊗ id)`.
-/
@[rep_depth operator]
theorem tensorFactorSeparation
    (S : V →ₗ[ℝ] V) (K : W →ₗ[ℝ] W) :
    (TensorProduct.map S (LinearMap.id : W →ₗ[ℝ] W)).comp
        (TensorProduct.map (LinearMap.id : V →ₗ[ℝ] V) K) =
      (TensorProduct.map (LinearMap.id : V →ₗ[ℝ] V) K).comp
        (TensorProduct.map S (LinearMap.id : W →ₗ[ℝ] W)) := by
  rw [tensorFactorSeparation_left_eq_tensorMap, tensorFactorSeparation_right_eq_tensorMap]

end AlgebraicTensorSeparation

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The head sector of a binary Cantor boundary code. -/
@[rep_depth operator]
def headBoundary (x : (ℕ → BinarySector)) : BinarySector :=
  x 0

/-- The tail of a binary Cantor boundary code. -/
@[rep_depth operator]
def tailBoundary (x : (ℕ → BinarySector)) : (ℕ → BinarySector) :=
  fun n => x (n + 1)

@[simp, rep_depth operator]
theorem headBoundary_prefixBoundary (s : BinarySector) (x : (ℕ → BinarySector)) :
    headBoundary (prefixBoundary s x) = s :=
  rfl

@[simp, rep_depth operator]
theorem tailBoundary_prefixBoundary (s : BinarySector) (x : (ℕ → BinarySector)) :
    tailBoundary (prefixBoundary s x) = x := by
  funext n
  rfl

/-- Every boundary code is its head prepended to its tail. -/
@[rep_depth operator]
theorem boundary_eta (x : (ℕ → BinarySector)) :
    prefixBoundary (headBoundary x) (tailBoundary x) = x := by
  funext n
  cases n <;> rfl

/--
The concrete Hilbert-boundary carrier used for pointwise tensor-factor
separation.

`PiLp` is a topological `L^2`-normed function carrier over the boundary index.
The actual summability subtype `lp ... 2` is constructed below; the remaining
analytic debt is boundedness as a continuous linear operator and its adjoint.
-/
abbrev H (E : Type 0) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    Type _ :=
  PiLp 2 (fun _ : (ℕ → BinarySector) => DoubledSpace E)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp, rep_depth operator]
theorem doubled_zero_pair :
    (WithLp.toLp (2 : ENNReal) ((0 : E), (0 : E)) : DoubledSpace E) = 0 := by
  apply DoubledSpace.ext <;> rfl

/--
Left Cuntz branch on coefficient functions.

This is the coefficient-function form of `δ_ω ↦ δ_{plus·ω}`.
-/
@[rep_depth operator]
noncomputable def S_left_op (ψ : H E) : H E :=
  WithLp.toLp 2 fun x : (ℕ → BinarySector) =>
    match headBoundary x with
    | BinarySector.plus => ψ (tailBoundary x)
    | BinarySector.minus => 0

/-- The phase axis acts pointwise on the doubled fiber. -/
@[rep_depth operator]
noncomputable def K_op (ψ : H E) : H E :=
  WithLp.toLp 2 fun x : (ℕ → BinarySector) => clockAxis (E := E) (ψ x)

@[simp, rep_depth operator]
theorem S_left_op_apply_plus (ψ : H E) (x : (ℕ → BinarySector)) :
    S_left_op (E := E) ψ (prefixBoundary BinarySector.plus x) = ψ x := by
  simp [S_left_op]

@[simp, rep_depth operator]
theorem S_left_op_apply_minus (ψ : H E) (x : (ℕ → BinarySector)) :
    S_left_op (E := E) ψ (prefixBoundary BinarySector.minus x) = 0 := by
  simp [S_left_op]

@[simp, rep_depth operator]
theorem K_op_apply (ψ : H E) (x : (ℕ → BinarySector)) :
    K_op (E := E) ψ x = clockAxis (E := E) (ψ x) := by
  simp [K_op]

/--
Pointwise Cuntz/phase-axis commutation on every boundary code.
-/
@[rep_depth operator]
theorem S_left_commutes_K_apply (ψ : H E) (x : (ℕ → BinarySector)) :
    S_left_op (E := E) (K_op (E := E) ψ) x =
      K_op (E := E) (S_left_op (E := E) ψ) x := by
  cases h : headBoundary x <;> simp [S_left_op, K_op, h]

/--
Global Cuntz/phase-axis commutation on the `PiLp` boundary carrier.
-/
@[rep_depth operator]
theorem S_left_commutes_K (ψ : H E) :
    S_left_op (E := E) (K_op (E := E) ψ) =
      K_op (E := E) (S_left_op (E := E) ψ) := by
  apply PiLp.ext
  intro x
  exact S_left_commutes_K_apply (E := E) ψ x
/--
The analytic Hilbert completion carrier for the boundary function space.
-/
abbrev H_lp (E : Type 0) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  lp (fun _ : (ℕ → BinarySector) => DoubledSpace E) 2

def S_left_raw (ψ : (ℕ → BinarySector) → DoubledSpace E) (x : (ℕ → BinarySector)) : DoubledSpace E :=
  if headBoundary x = BinarySector.plus then ψ (tailBoundary x) else 0


omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma S_left_raw_norm (ψ : (ℕ → BinarySector) → DoubledSpace E) (x : (ℕ → BinarySector)) :
    ‖S_left_raw ψ x‖ = if headBoundary x = BinarySector.plus then ‖ψ (tailBoundary x)‖ else 0 := by
  unfold S_left_raw
  split_ifs
  · rfl
  · rw [norm_zero]

def plusEquiv : (ℕ → BinarySector) ≃ { x : (ℕ → BinarySector) // headBoundary x = BinarySector.plus } where
  toFun x := ⟨prefixBoundary BinarySector.plus x, rfl⟩
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
lemma summable_S_left_raw (ψ : (ℕ → BinarySector) → DoubledSpace E) (h : Summable fun x => ‖ψ x‖ ^ (2 : ℝ)) :
    Summable fun x => ‖S_left_raw ψ x‖ ^ (2 : ℝ) := by
  have h_split := @summable_subtype_and_compl ℝ (ℕ → BinarySector) _ _ _ (fun x => ‖S_left_raw ψ x‖ ^ (2 : ℝ)) _ {x | headBoundary x = BinarySector.plus}
  rw [← h_split]
  constructor
  · have heq : (fun (y : {x // headBoundary x = BinarySector.plus}) => ‖S_left_raw ψ y.1‖ ^ (2 : ℝ)) =
               (fun x : (ℕ → BinarySector) => ‖ψ x‖ ^ (2 : ℝ)) ∘ plusEquiv.symm := by
      ext y
      dsimp [plusEquiv]
      rw [S_left_raw_norm]
      have hy : headBoundary y.1 = BinarySector.plus := y.2
      rw [if_pos hy]
    change Summable (fun (y : {x // headBoundary x = BinarySector.plus}) => ‖S_left_raw ψ y.1‖ ^ (2 : ℝ))
    rw [heq]
    exact (Equiv.summable_iff plusEquiv.symm).mpr h
  · have heq_zero : (fun (y : {x // x ∉ {x | headBoundary x = BinarySector.plus}}) => ‖S_left_raw ψ y.1‖ ^ (2 : ℝ)) = 0 := by
      ext y
      dsimp
      rw [S_left_raw_norm]
      have hy : headBoundary y.1 ≠ BinarySector.plus := y.2
      rw [if_neg hy]
      exact Real.zero_rpow two_ne_zero
    change Summable (fun (y : {x // x ∉ {x | headBoundary x = BinarySector.plus}}) => ‖S_left_raw ψ y.1‖ ^ (2 : ℝ))
    rw [heq_zero]
    exact summable_zero

/--
The bounded continuous linear branch operator on the true Hilbert completion.
-/
def S_left_lp (ψ : H_lp E) : H_lp E :=
  ⟨S_left_raw ψ, by
    apply memℓp_gen
    have h1 : (2 : ENNReal).toReal = 2 := rfl
    rw [h1]
    have h2 : Memℓp ψ.1 2 := ψ.prop
    have h3 := (memℓp_gen_iff zero_lt_two).mp h2
    rw [h1] at h3
    exact summable_S_left_raw ψ h3⟩

@[simp]
theorem S_left_lp_zero :
    S_left_lp (E := E) 0 = 0 := by
  apply Subtype.ext
  funext x
  change S_left_raw (0 : H_lp E) x = (0 : H_lp E) x
  simp [S_left_raw]

theorem S_left_lp_add (ψ φ : H_lp E) :
    S_left_lp (E := E) (ψ + φ) =
      S_left_lp (E := E) ψ + S_left_lp (E := E) φ := by
  apply Subtype.ext
  funext x
  simp only [S_left_lp]
  change S_left_raw (ψ.1 + φ.1) x =
    (S_left_raw ψ.1 + S_left_raw φ.1) x
  by_cases h : headBoundary x = BinarySector.plus
  · simp [S_left_raw, h] <;> rfl
  · simp [S_left_raw, h]

theorem S_left_lp_smul (a : ℝ) (ψ : H_lp E) :
    S_left_lp (E := E) (a • ψ) =
      a • S_left_lp (E := E) ψ := by
  apply Subtype.ext
  funext x
  simp only [S_left_lp]
  change S_left_raw (a • ψ.1) x =
    (a • S_left_raw ψ.1) x
  by_cases h : headBoundary x = BinarySector.plus
  · simp [S_left_raw, h] <;> rfl
  · simp [S_left_raw, h]

def S_left_lp_linearMap : H_lp E →ₗ[ℝ] H_lp E where
  toFun := S_left_lp
  map_add' := S_left_lp_add
  map_smul' := S_left_lp_smul

theorem S_left_lp_norm (ψ : H_lp E) :
    ‖S_left_lp (E := E) ψ‖ = ‖ψ‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hnormS := lp.norm_rpow_eq_tsum hp (S_left_lp (E := E) ψ)
  have hnormψ := lp.norm_rpow_eq_tsum hp ψ
  let s : Set (ℕ → BinarySector) :=
    {x | headBoundary x = BinarySector.plus}
  have hsum :
      (∑' x : (ℕ → BinarySector),
        ‖S_left_raw ψ.1 x‖ ^ (2 : ℝ)) =
        ∑' x : (ℕ → BinarySector), ‖ψ.1 x‖ ^ (2 : ℝ) := by
    calc
      ∑' x : (ℕ → BinarySector),
          ‖S_left_raw ψ.1 x‖ ^ (2 : ℝ) =
          ∑' x : (ℕ → BinarySector),
            s.indicator
              (fun y => ‖S_left_raw ψ.1 y‖ ^ (2 : ℝ)) x := by
        apply tsum_congr
        intro x
        by_cases hx : x ∈ s
        · simp [Set.indicator_of_mem hx]
        · have hne : headBoundary x ≠ BinarySector.plus := by
            intro hhead
            exact hx hhead
          simp [Set.indicator, S_left_raw_norm, hne]
      _ = ∑' x : s, ‖S_left_raw ψ.1 x.1‖ ^ (2 : ℝ) := by
        exact (tsum_subtype s
          (fun y => ‖S_left_raw ψ.1 y‖ ^ (2 : ℝ))).symm
      _ = ∑' x : (ℕ → BinarySector),
          ‖S_left_raw ψ.1 (plusEquiv x).1‖ ^ (2 : ℝ) := by
        symm
        exact Equiv.tsum_eq plusEquiv
          (fun y : s => ‖S_left_raw ψ.1 y.1‖ ^ (2 : ℝ))
      _ = ∑' x : (ℕ → BinarySector), ‖ψ.1 x‖ ^ (2 : ℝ) := by
        apply tsum_congr
        intro x
        change
          ‖S_left_raw ψ.1 (prefixBoundary BinarySector.plus x)‖ ^ (2 : ℝ) =
            ‖ψ.1 x‖ ^ (2 : ℝ)
        rw [S_left_raw_norm]
        simp only [headBoundary_prefixBoundary, if_pos rfl]
        rw [tailBoundary_prefixBoundary]
        simp
  have hpow :
      ‖S_left_lp (E := E) ψ‖ ^ (2 : ℕ) = ‖ψ‖ ^ (2 : ℕ) := by
    calc
      ‖S_left_lp (E := E) ψ‖ ^ (2 : ℕ) =
          ∑' x : (ℕ → BinarySector),
            ‖S_left_raw ψ.1 x‖ ^ (2 : ℝ) := by
        convert hnormS using 1 <;> norm_num [Real.rpow_natCast]
      _ = ∑' x : (ℕ → BinarySector), ‖ψ.1 x‖ ^ (2 : ℝ) := hsum
      _ = ‖ψ‖ ^ (2 : ℕ) := by
        convert hnormψ.symm using 1 <;> norm_num [Real.rpow_natCast]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hpow

def S_left_lp_continuousLinearMap : H_lp E →L[ℝ] H_lp E :=
  (S_left_lp_linearMap (E := E)).mkContinuous 1 (by
    intro ψ
    change ‖S_left_lp (E := E) ψ‖ ≤ 1 * ‖ψ‖
    rw [S_left_lp_norm]
    simp)

/-- The Hilbert-space adjoint supplied by the native continuous-linear-map API. -/
def S_left_lp_adjoint : H_lp E →L[ℝ] H_lp E :=
  ContinuousLinearMap.adjoint (S_left_lp_continuousLinearMap (E := E))

@[simp]
theorem S_left_lp_adjoint_inner_left (ψ φ : H_lp E) :
    inner ℝ (S_left_lp_adjoint (E := E) ψ) φ =
      inner ℝ ψ (S_left_lp_continuousLinearMap (E := E) φ) := by
  exact ContinuousLinearMap.adjoint_inner_left
    (S_left_lp_continuousLinearMap (E := E)) φ ψ

theorem S_left_lp_injective :
    Function.Injective (S_left_lp (E := E)) := by
  intro ψ φ h
  apply Subtype.ext
  funext x
  have hx := congrFun (congrArg Subtype.val h)
    (prefixBoundary BinarySector.plus x)
  change S_left_raw ψ.1 (prefixBoundary BinarySector.plus x) =
    S_left_raw φ.1 (prefixBoundary BinarySector.plus x) at hx
  simpa [S_left_raw] using hx

def K_raw (ψ : (ℕ → BinarySector) → DoubledSpace E) (x : (ℕ → BinarySector)) : DoubledSpace E :=
  clockAxis (E := E) (ψ x)


lemma complex_i_norm (u : DoubledSpace E) :
    ‖complex_i (E := E) u‖ = ‖u‖ := by
  have hnn : ‖complex_i (E := E) u‖₊ = ‖u‖₊ := by
    have htop : (2 : ENNReal) ≠ ⊤ := by norm_num
    rw [WithLp.prod_nnnorm_eq_add (p := (2 : ENNReal)) htop]
    rw [WithLp.prod_nnnorm_eq_add (p := (2 : ENNReal)) htop]
    simp [complex_i_apply, add_comm]
  exact congrArg (fun x : NNReal => (x : ℝ)) hnn

lemma summable_K_raw (ψ : (ℕ → BinarySector) → DoubledSpace E) (h : Summable fun x => ‖ψ x‖ ^ (2 : ℝ)) :
    Summable fun x => ‖K_raw ψ x‖ ^ (2 : ℝ) := by
  have h_eq : (fun x => ‖K_raw ψ x‖ ^ (2 : ℝ)) = (fun x => ‖ψ x‖ ^ (2 : ℝ)) := by
    ext x
    dsimp [K_raw]
    rw [complex_i_norm]
  rw [h_eq]
  exact h

/--
The bounded continuous linear charge conjugation operator on the true Hilbert completion.
-/
def K_lp (ψ : H_lp E) : H_lp E :=
  ⟨K_raw ψ, by
    apply memℓp_gen
    have h1 : (2 : ENNReal).toReal = 2 := rfl
    rw [h1]
    have h2 : Memℓp ψ.1 2 := ψ.prop
    have h3 := (memℓp_gen_iff zero_lt_two).mp h2
    rw [h1] at h3
    exact summable_K_raw ψ h3⟩

@[simp]
theorem K_lp_zero :
    K_lp (E := E) 0 = 0 := by
  apply Subtype.ext
  funext x
  simp only [K_lp]
  change clockAxis (E := E) 0 = 0
  exact map_zero (clockAxis (E := E))

theorem K_lp_add (ψ φ : H_lp E) :
    K_lp (E := E) (ψ + φ) =
      K_lp (E := E) ψ + K_lp (E := E) φ := by
  apply Subtype.ext
  funext x
  simp only [K_lp]
  change clockAxis (E := E) (ψ.1 x + φ.1 x) =
    clockAxis (E := E) (ψ.1 x) + clockAxis (E := E) (φ.1 x)
  exact map_add (clockAxis (E := E)) _ _

theorem K_lp_smul (a : ℝ) (ψ : H_lp E) :
    K_lp (E := E) (a • ψ) =
      a • K_lp (E := E) ψ := by
  apply Subtype.ext
  funext x
  simp [K_lp, K_raw]

def K_lp_linearMap : H_lp E →ₗ[ℝ] H_lp E where
  toFun := K_lp
  map_add' := K_lp_add
  map_smul' := K_lp_smul

theorem K_lp_norm (ψ : H_lp E) :
    ‖K_lp (E := E) ψ‖ = ‖ψ‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hnormK := lp.norm_rpow_eq_tsum hp (K_lp (E := E) ψ)
  have hnormψ := lp.norm_rpow_eq_tsum hp ψ
  have hsum :
      (∑' x : (ℕ → BinarySector),
        ‖K_raw ψ.1 x‖ ^ (2 : ℝ)) =
        ∑' x : (ℕ → BinarySector), ‖ψ.1 x‖ ^ (2 : ℝ) := by
    apply tsum_congr
    intro x
    dsimp [K_raw]
    rw [complex_i_norm]
  have hpow :
      ‖K_lp (E := E) ψ‖ ^ (2 : ℕ) = ‖ψ‖ ^ (2 : ℕ) := by
    calc
      ‖K_lp (E := E) ψ‖ ^ (2 : ℕ) =
          ∑' x : (ℕ → BinarySector),
            ‖K_raw ψ.1 x‖ ^ (2 : ℝ) := by
        convert hnormK using 1 <;> norm_num [Real.rpow_natCast]
      _ = ∑' x : (ℕ → BinarySector), ‖ψ.1 x‖ ^ (2 : ℝ) := hsum
      _ = ‖ψ‖ ^ (2 : ℕ) := by
        convert hnormψ.symm using 1 <;> norm_num [Real.rpow_natCast]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hpow

def K_lp_continuousLinearMap : H_lp E →L[ℝ] H_lp E :=
  (K_lp_linearMap (E := E)).mkContinuous 1 (by
    intro ψ
    change ‖K_lp (E := E) ψ‖ ≤ 1 * ‖ψ‖
    rw [K_lp_norm]
    simp)

theorem K_lp_sq (ψ : H_lp E) :
    K_lp (E := E) (K_lp ψ) = -ψ := by
  apply Subtype.ext
  funext x
  simp only [K_lp]
  change clockAxis (E := E) (clockAxis (E := E) (ψ.1 x)) = -(ψ.1 x)
  calc
    clockAxis (E := E) (clockAxis (E := E) (ψ.1 x)) =
        ((clockAxis (E := E)).comp (clockAxis (E := E))) (ψ.1 x) := rfl
    _ = (-(ContinuousLinearMap.id ℝ (DoubledSpace E))) (ψ.1 x) := by
      rw [clockAxis_sq]
    _ = -(ψ.1 x) := by rfl

/--
Lift the pointwise commutation here from the `PiLp` carrier to equality of
continuous linear maps on the Hilbert completion.
-/
@[rep_depth operator]
theorem S_left_commutes_K_lp (ψ : H_lp E) :
    S_left_lp (K_lp ψ) = K_lp (S_left_lp ψ) := by
  apply Subtype.ext
  funext x
  dsimp [S_left_lp, K_lp, S_left_raw, K_raw]
  split_ifs
  · rfl
  · exact (map_zero (clockAxis (E := E))).symm

theorem S_left_lp_linearMap_comp_K_lp_linearMap_eq_reverse :
    (S_left_lp_linearMap (E := E)).comp (K_lp_linearMap (E := E)) =
      (K_lp_linearMap (E := E)).comp (S_left_lp_linearMap (E := E)) := by
  apply LinearMap.ext
  intro ψ
  exact S_left_commutes_K_lp (E := E) ψ

theorem S_left_lp_continuousLinearMap_comp_K_lp_continuousLinearMap_eq_reverse :
    (S_left_lp_continuousLinearMap (E := E)).comp
        (K_lp_continuousLinearMap (E := E)) =
      (K_lp_continuousLinearMap (E := E)).comp
        (S_left_lp_continuousLinearMap (E := E)) := by
  apply ContinuousLinearMap.ext
  intro ψ
  exact S_left_commutes_K_lp (E := E) ψ

end InfoGeometry.Canonical.ConcreteHilbertCommutation
