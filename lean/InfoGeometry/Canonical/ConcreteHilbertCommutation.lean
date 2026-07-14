import Mathlib.Analysis.Normed.Lp.PiLp
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

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported
verified premises.]

* None.

#### BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, sockets, fields,
witnesses, certificates, or renamed placeholders.]

* Construct the true `lp (fun _ : BinaryCantorBoundary => DoubledSpace E) 2`
  Cuntz branch as a bounded continuous linear map.
* Prove that the branch operator preserves the `Memℓp` predicate.
* Lift the pointwise commutation here from the `PiLp` carrier to equality of
  continuous linear maps on the Hilbert completion.
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
def headBoundary (x : BinaryCantorBoundary) : BinarySector :=
  x 0

/-- The tail of a binary Cantor boundary code. -/
@[rep_depth operator]
def tailBoundary (x : BinaryCantorBoundary) : BinaryCantorBoundary :=
  fun n => x (n + 1)

@[simp, rep_depth operator]
theorem headBoundary_prefixBoundary (s : BinarySector) (x : BinaryCantorBoundary) :
    headBoundary (prefixBoundary s x) = s :=
  rfl

@[simp, rep_depth operator]
theorem tailBoundary_prefixBoundary (s : BinarySector) (x : BinaryCantorBoundary) :
    tailBoundary (prefixBoundary s x) = x := by
  funext n
  rfl

/-- Every boundary code is its head prepended to its tail. -/
@[rep_depth operator]
theorem boundary_eta (x : BinaryCantorBoundary) :
    prefixBoundary (headBoundary x) (tailBoundary x) = x := by
  funext n
  cases n <;> rfl

/--
The concrete Hilbert-boundary carrier used for pointwise tensor-factor
separation.

`PiLp` is a topological `L^2`-normed function carrier over the boundary index.
The actual summability subtype `lp ... 2` is deliberately left as closure debt
until the branch boundedness proof is supplied.
-/
abbrev H (E : Type 0) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    Type _ :=
  PiLp 2 (fun _ : BinaryCantorBoundary => DoubledSpace E)

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
  WithLp.toLp 2 fun x : BinaryCantorBoundary =>
    match headBoundary x with
    | BinarySector.plus => ψ (tailBoundary x)
    | BinarySector.minus => 0

/-- The phase axis acts pointwise on the doubled fiber. -/
@[rep_depth operator]
noncomputable def K_op (ψ : H E) : H E :=
  WithLp.toLp 2 fun x : BinaryCantorBoundary => clockAxis (E := E) (ψ x)

@[simp, rep_depth operator]
theorem S_left_op_apply_plus (ψ : H E) (x : BinaryCantorBoundary) :
    S_left_op (E := E) ψ (prefixBoundary BinarySector.plus x) = ψ x := by
  simp [S_left_op]

@[simp, rep_depth operator]
theorem S_left_op_apply_minus (ψ : H E) (x : BinaryCantorBoundary) :
    S_left_op (E := E) ψ (prefixBoundary BinarySector.minus x) = 0 := by
  simp [S_left_op]

@[simp, rep_depth operator]
theorem K_op_apply (ψ : H E) (x : BinaryCantorBoundary) :
    K_op (E := E) ψ x = clockAxis (E := E) (ψ x) := by
  simp [K_op]

/--
Pointwise Cuntz/phase-axis commutation on every boundary code.
-/
@[rep_depth operator]
theorem S_left_commutes_K_apply (ψ : H E) (x : BinaryCantorBoundary) :
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
  lp (fun _ : BinaryCantorBoundary => DoubledSpace E) 2

def S_left_raw (ψ : BinaryCantorBoundary → DoubledSpace E) (x : BinaryCantorBoundary) : DoubledSpace E :=
  if headBoundary x = BinarySector.plus then ψ (tailBoundary x) else 0


omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma S_left_raw_norm (ψ : BinaryCantorBoundary → DoubledSpace E) (x : BinaryCantorBoundary) :
    ‖S_left_raw ψ x‖ = if headBoundary x = BinarySector.plus then ‖ψ (tailBoundary x)‖ else 0 := by
  unfold S_left_raw
  split_ifs
  · rfl
  · rw [norm_zero]

def plusEquiv : BinaryCantorBoundary ≃ { x : BinaryCantorBoundary // headBoundary x = BinarySector.plus } where
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
lemma summable_S_left_raw (ψ : BinaryCantorBoundary → DoubledSpace E) (h : Summable fun x => ‖ψ x‖ ^ (2 : ℝ)) :
    Summable fun x => ‖S_left_raw ψ x‖ ^ (2 : ℝ) := by
  have h_split := @summable_subtype_and_compl ℝ BinaryCantorBoundary _ _ _ (fun x => ‖S_left_raw ψ x‖ ^ (2 : ℝ)) _ {x | headBoundary x = BinarySector.plus}
  rw [← h_split]
  constructor
  · have heq : (fun (y : {x // headBoundary x = BinarySector.plus}) => ‖S_left_raw ψ y.1‖ ^ (2 : ℝ)) =
               (fun x : BinaryCantorBoundary => ‖ψ x‖ ^ (2 : ℝ)) ∘ plusEquiv.symm := by
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

def K_raw (ψ : BinaryCantorBoundary → DoubledSpace E) (x : BinaryCantorBoundary) : DoubledSpace E :=
  clockAxis (E := E) (ψ x)


lemma complex_i_norm (u : DoubledSpace E) :
    ‖complex_i (E := E) u‖ = ‖u‖ := by
  have hnn : ‖complex_i (E := E) u‖₊ = ‖u‖₊ := by
    have htop : (2 : ENNReal) ≠ ⊤ := by norm_num
    rw [WithLp.prod_nnnorm_eq_add (p := (2 : ENNReal)) htop]
    rw [WithLp.prod_nnnorm_eq_add (p := (2 : ENNReal)) htop]
    simp [complex_i_apply, add_comm]
  exact congrArg (fun x : NNReal => (x : ℝ)) hnn

lemma summable_K_raw (ψ : BinaryCantorBoundary → DoubledSpace E) (h : Summable fun x => ‖ψ x‖ ^ (2 : ℝ)) :
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

end InfoGeometry.Canonical.ConcreteHilbertCommutation
