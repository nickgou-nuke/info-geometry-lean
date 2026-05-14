import InfoGeometry.Canonical.ChiralLightConeTensorTower
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.ChiralLightConeTensorTower

/-!
# Cantor/Clifford function model

Intermediate carrier for functions on the symbolic chiral Cantor boundary.

This file deliberately stays below the Cuntz and spectral-triple layers.  It
only packages:

* boundary functions `ChiralBoundary -> Value`;
* finite prefix/cylinder predicates from `CausalWord n`;
* prefixing and cylinder readouts;
* optional local head action data.

It does not assert a Cantor homeomorphism, Cuntz relations, a Hilbert-space
representation, or a spectral triple.
-/

/-- Function space on the symbolic chiral Cantor boundary. -/
@[rep_depth krein]
structure BoundaryFunctionSpace (Value : Type*) where
  function : ChiralBoundary → Value

namespace BoundaryFunctionSpace

variable {Value : Type*}
variable (F : BoundaryFunctionSpace Value)

/-- Evaluate a boundary function at an infinite chiral boundary code. -/
@[rep_depth krein]
def eval (x : ChiralBoundary) : Value :=
  F.function x

@[rep_depth krein]
theorem eval_apply (x : ChiralBoundary) :
    F.eval x = F.function x :=
  rfl

end BoundaryFunctionSpace

/-- Prefix a chiral arrow to an infinite boundary code. -/
@[rep_depth krein]
def prefixBoundary (a : CausalArrow) (x : ChiralBoundary) : ChiralBoundary
    | 0 => a
    | n + 1 => x n

@[simp, rep_depth krein]
theorem prefixBoundary_zero (a : CausalArrow) (x : ChiralBoundary) :
    prefixBoundary a x 0 = a :=
  rfl

@[simp, rep_depth krein]
theorem prefixBoundary_succ (a : CausalArrow) (x : ChiralBoundary) (n : ℕ) :
    prefixBoundary a x (n + 1) = x n :=
  rfl

/-- Prefix action on boundary functions by precomposition with a boundary prefix. -/
@[rep_depth krein]
def prefixReadout
    {Value : Type*}
    (a : CausalArrow)
    (F : BoundaryFunctionSpace Value) : BoundaryFunctionSpace Value where
  function := fun x => F.function (prefixBoundary a x)

@[simp, rep_depth krein]
theorem prefixReadout_apply
    {Value : Type*}
    (a : CausalArrow)
    (F : BoundaryFunctionSpace Value)
    (x : ChiralBoundary) :
    (prefixReadout a F).function x = F.function (prefixBoundary a x) :=
  rfl

/-- A boundary code has finite causal prefix `w`. -/
@[rep_depth krein]
def HasPrefix {n : ℕ} (w : CausalWord n) (x : ChiralBoundary) : Prop :=
  ∀ k : Fin n, x k = w k

/-- Cylinder readout: restrict a boundary function to a finite prefix predicate. -/
@[rep_depth krein]
def cylinderReadout
    {Value : Type*} {n : ℕ}
    (w : CausalWord n)
    (F : BoundaryFunctionSpace Value) :
    {x : ChiralBoundary // HasPrefix w x} → Value :=
  fun x => F.function x.1

@[rep_depth krein]
theorem cylinderReadout_apply
    {Value : Type*} {n : ℕ}
    (w : CausalWord n)
    (F : BoundaryFunctionSpace Value)
    (x : {x : ChiralBoundary // HasPrefix w x}) :
    cylinderReadout w F x = F.function x.1 :=
  rfl

/-- The boundary obtained from a finite word and tail has the original word as prefix. -/
@[rep_depth krein]
theorem toBoundary_hasPrefix
    {n : ℕ}
    (w : CausalWord n)
    (tail : CausalArrow) :
    HasPrefix w (CausalWord.toBoundary w tail) := by
  intro k
  exact CausalWord.toBoundary_of_lt w tail k.2

/-- Cylinder sample obtained by extending a finite word with a constant tail. -/
@[rep_depth krein]
def cylinderSample
    {Value : Type*} {n : ℕ}
    (w : CausalWord n)
    (tail : CausalArrow)
    (F : BoundaryFunctionSpace Value) : Value :=
  F.function (CausalWord.toBoundary w tail)

@[rep_depth krein]
theorem cylinderSample_eq_cylinderReadout
    {Value : Type*} {n : ℕ}
    (w : CausalWord n)
    (tail : CausalArrow)
    (F : BoundaryFunctionSpace Value) :
    cylinderSample w tail F =
      cylinderReadout w F ⟨CausalWord.toBoundary w tail, toBoundary_hasPrefix w tail⟩ :=
  rfl

/-- Pointwise arrow flip on a boundary code. -/
@[rep_depth krein]
def flipBoundary (x : ChiralBoundary) : ChiralBoundary :=
  fun n => ChiralArrow.flip (x n)

@[simp, rep_depth krein]
theorem flipBoundary_flip (x : ChiralBoundary) :
    flipBoundary (flipBoundary x) = x := by
  funext n
  simp [flipBoundary]

/-- Flip action on boundary functions by precomposition with boundary flip. -/
@[rep_depth krein]
def flipReadout
    {Value : Type*}
    (F : BoundaryFunctionSpace Value) : BoundaryFunctionSpace Value where
  function := fun x => F.function (flipBoundary x)

@[simp, rep_depth krein]
theorem flipReadout_flip
    {Value : Type*}
    (F : BoundaryFunctionSpace Value) :
    flipReadout (flipReadout F) = F := by
  cases F with
  | mk f =>
      simp [flipReadout]

/-- Symbolic local Clifford-head action on a value type. -/
@[rep_depth krein]
structure LocalHeadAction (Value : Type*) where
  act : ChiralSymbol → Value → Value

/-- Apply a finite chiral word head to a boundary-function value read at `x`. -/
@[rep_depth krein]
def finiteHeadReadout
    {Value : Type*} {n : ℕ}
    (A : LocalHeadAction Value)
    (w : ChiralWord n)
    (F : BoundaryFunctionSpace Value)
    (x : ChiralBoundary) : Fin n → Value :=
  fun k => A.act (w k) (F.function x)

@[rep_depth krein]
theorem finiteHeadReadout_apply
    {Value : Type*} {n : ℕ}
    (A : LocalHeadAction Value)
    (w : ChiralWord n)
    (F : BoundaryFunctionSpace Value)
    (x : ChiralBoundary)
    (k : Fin n) :
    finiteHeadReadout A w F x k = A.act (w k) (F.function x) :=
  rfl

/-- Package for boundary functions with a symbolic Clifford-head action. -/
@[rep_depth krein]
structure CantorCliffordFunctionModel (Value : Type*) where
  functions : BoundaryFunctionSpace Value
  localHeadAction : LocalHeadAction Value

namespace CantorCliffordFunctionModel

variable {Value : Type*}
variable (M : CantorCliffordFunctionModel Value)

/-- Evaluate the model's function on the chiral boundary. -/
@[rep_depth krein]
def eval (x : ChiralBoundary) : Value :=
  M.functions.function x

/-- Prefix readout of the model's boundary function. -/
@[rep_depth krein]
def prefixed (a : CausalArrow) : BoundaryFunctionSpace Value :=
  prefixReadout a M.functions

/-- Cylinder sample of the model's boundary function. -/
@[rep_depth krein]
def cylinder {n : ℕ} (w : CausalWord n) (tail : CausalArrow) : Value :=
  cylinderSample w tail M.functions

@[rep_depth krein]
theorem eval_apply (x : ChiralBoundary) :
    M.eval x = M.functions.function x :=
  rfl

@[rep_depth krein]
theorem prefix_apply (a : CausalArrow) (x : ChiralBoundary) :
    (M.prefixed a).function x = M.functions.function (prefixBoundary a x) :=
  rfl

@[rep_depth krein]
theorem cylinder_eq_sample {n : ℕ} (w : CausalWord n) (tail : CausalArrow) :
    M.cylinder w tail = M.functions.function (CausalWord.toBoundary w tail) :=
  rfl

end CantorCliffordFunctionModel

end InfoGeometry.Canonical
