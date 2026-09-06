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

end InfoGeometry.Canonical.ConcreteHilbertCommutation
