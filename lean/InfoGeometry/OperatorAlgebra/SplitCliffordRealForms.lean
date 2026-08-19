/-
InfoGeometry/OperatorAlgebra/SplitCliffordRealForms.lean

Finite constructive skeleton for split Clifford real forms.

Raw property source:

  Galina-Kaplan-Saal,
  "Split Clifford Modules over a Hilbert Space",
  arXiv:math/0204117v3.

The paper classifies real forms of Garding-Wightman Clifford/CAR modules by
the complement involution `x |-> 1 - x` on the occupation space `{0,1}^N`,
together with measure-equivalence, multiplicity symmetry, and a measurable
anti-linear cocycle.

This file does not formalize the full direct-integral analytic theorem.
It extracts the constructive finite algebraic skeleton:

* finite occupation states `Fin m -> Bool`;
* complement `x |-> 1 - x`;
* bit toggle `x |-> x + delta_k`;
* complement/toggle compatibility;
* the induced closure involution on functions;
* fixed and anti-fixed sectors as the finite real-form shadow.

The analytic Garding-Wightman splitting criterion remains property-gated.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ClosureInvolution

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SplitCliffordRealForms

open InfoGeometry.OperatorAlgebra.ClosureInvolution

/-! ## 1. Finite occupation space -/

/--
Finite occupation space: `m` fermionic occupation bits.
-/
abbrev Occupation
    (m : Nat) : Type :=
  Fin m -> Bool

namespace Occupation

variable {m : Nat}

/--
Complement occupation state: `x |-> 1 - x`.
-/
def complement
    (x : Occupation m) : Occupation m :=
  fun i => ! x i

/--
Toggle the `k`-th occupation bit.
-/
def toggle
    (k : Fin m)
    (x : Occupation m) : Occupation m :=
  fun i => if i = k then ! x i else x i

/--
Complement is involutive.
-/
theorem complement_involutive
    (x : Occupation m) :
    complement (complement x) = x := by
  funext i
  simp [complement]

/-- The occupation complement as a native `Equiv`.

Packaging the involution as an equivalence lets downstream closure and
spectral constructions use Mathlib's inverse/equivalence API instead of
repeating pointwise double-complement rewrites. -/
def complementEquiv (m : Nat) : Occupation m ≃ Occupation m where
  toFun := complement
  invFun := complement
  left_inv := complement_involutive
  right_inv := complement_involutive

@[simp] theorem complementEquiv_apply (m : Nat) (x : Occupation m) :
    complementEquiv m x = complement x := rfl

@[simp] theorem complementEquiv_symm_apply (m : Nat) (x : Occupation m) :
    (complementEquiv m).symm x = complement x := rfl

@[simp] theorem complementEquiv_symm :
    (complementEquiv m).symm = complementEquiv m := by
  ext x
  rfl

@[simp] theorem complementEquiv_involutive
    (m : Nat) (x : Occupation m) :
    complementEquiv m (complementEquiv m x) = x := by
  simpa only [complementEquiv_symm] using
    (complementEquiv m).symm_apply_apply x

/--
Toggling a bit is involutive.
-/
theorem toggle_involutive
    (k : Fin m)
    (x : Occupation m) :
    toggle k (toggle k x) = x := by
  funext i
  by_cases h : i = k
  · simp [toggle, h]
  · simp [toggle, h]

/--
Complement commutes with finite bit-toggle.

This is the finite constructive form of

`1 - (x + delta_k) = (1 - x) + delta_k`.
-/
theorem complement_toggle
    (k : Fin m)
    (x : Occupation m) :
    complement (toggle k x) =
      toggle k (complement x) := by
  funext i
  by_cases h : i = k
  · simp [complement, toggle, h]
  · simp [complement, toggle, h]

/--
Toggle commutes with complement.
-/
theorem toggle_complement
    (k : Fin m)
    (x : Occupation m) :
    toggle k (complement x) =
      complement (toggle k x) :=
  (complement_toggle k x).symm

end Occupation

/-! ## 2. Complement closure on finite occupation functions -/

/--
Real-valued functions on finite occupation space.

This is the finite discrete shadow of the direct integral `L2(X)`.
-/
abbrev OccupationFunction
    (m : Nat) : Type :=
  Occupation m -> Real

/--
Closure involution on finite occupation functions induced by complement:

`theta f x = f(1 - x)`.
-/
def occupationComplementClosure
    (m : Nat) :
    LinearClosureInvolution (OccupationFunction m) := by
  let θ : OccupationFunction m →ₗ[ℝ] OccupationFunction m :=
    { toFun := fun f => fun x => f (Occupation.complementEquiv m x)
      map_add' := by
        intro f g
        funext x
        simp
      map_smul' := by
        intro a f
        funext x
        simp }
  refine { theta := θ, theta_involutive := ?_ }
  dsimp [θ]
  intro f
  funext x
  change f (Occupation.complementEquiv m
    (Occupation.complementEquiv m x)) = f x
  have hcomp := Occupation.complementEquiv_involutive m x
  rw [hcomp]

@[simp] theorem occupationComplementClosure_theta_apply
    (m : Nat) (f : OccupationFunction m) (x : Occupation m) :
    (occupationComplementClosure m).theta f x =
      f (Occupation.complementEquiv m x) := rfl

namespace occupationComplementClosure

variable {m : Nat}

/--
Membership in the fixed sector is exactly complement invariance:

`f(1-x) = f(x)`.
-/
theorem mem_fixed_iff
    (f : OccupationFunction m) :
    f ∈ (occupationComplementClosure m).Fixed ↔
      forall x : Occupation m,
        f (Occupation.complement x) = f x := by
  constructor
  · intro hf x
    have htheta :
        (occupationComplementClosure m).theta f = f :=
      ((occupationComplementClosure m).mem_fixed_iff f).mp hf
    exact congrFun htheta x
  · intro h
    exact
      ((occupationComplementClosure m).mem_fixed_iff f).mpr
        (funext h)

/--
Membership in the anti-fixed sector is exactly complement sign-reversal:

`f(1-x) = -f(x)`.
-/
theorem mem_antiFixed_iff
    (f : OccupationFunction m) :
    f ∈ (occupationComplementClosure m).AntiFixed ↔
      forall x : Occupation m,
        f (Occupation.complement x) = -f x := by
  constructor
  · intro hf x
    have htheta :
        (occupationComplementClosure m).theta f = -f :=
      ((occupationComplementClosure m).mem_antiFixed_iff f).mp hf
    exact congrFun htheta x
  · intro h
    exact
      ((occupationComplementClosure m).mem_antiFixed_iff f).mpr
        (funext h)

/--
The finite real-form shadow is the fixed sector of complement.
-/
def RealForm
    (m : Nat) : Submodule Real (OccupationFunction m) :=
  (occupationComplementClosure m).Fixed

/--
The finite chiral-imbalance shadow is the anti-fixed sector of complement.
-/
def ChiralImbalance
    (m : Nat) : Submodule Real (OccupationFunction m) :=
  (occupationComplementClosure m).AntiFixed

/--
A function in the finite real form satisfies `f(1-x)=f(x)`.
-/
theorem realForm_apply_complement
    {f : OccupationFunction m}
    (hf : f ∈ RealForm m)
    (x : Occupation m) :
    f (Occupation.complement x) = f x :=
  (mem_fixed_iff f).mp hf x

/--
A function in the finite chiral-imbalance sector satisfies `f(1-x)=-f(x)`.
-/
theorem chiralImbalance_apply_complement
    {f : OccupationFunction m}
    (hf : f ∈ ChiralImbalance m)
    (x : Occupation m) :
    f (Occupation.complement x) = -f x :=
  (mem_antiFixed_iff f).mp hf x

/--
Every occupation function decomposes into fixed and anti-fixed parts.
-/
theorem fixed_add_anti_decomposition
    (f : OccupationFunction m) :
    (occupationComplementClosure m).fixedPart f +
      (occupationComplementClosure m).antiPart f =
        f :=
  (occupationComplementClosure m).fixed_add_anti_decomposition f

/--
The complement image is fixed part minus anti-fixed part.
-/
theorem fixed_sub_anti_decomposition
    (f : OccupationFunction m) :
    (occupationComplementClosure m).fixedPart f -
      (occupationComplementClosure m).antiPart f =
        (occupationComplementClosure m).theta f :=
  (occupationComplementClosure m).fixed_sub_anti_decomposition f

end occupationComplementClosure

/-! ## 3. Support obstruction skeleton -/

/--
A support is stable under occupation complement if membership is preserved by
`x |-> 1-x`.
-/
def SupportStableUnderComplement
    {m : Nat}
    (S : Set (Occupation m)) : Prop :=
  forall x : Occupation m,
    x ∈ S ↔ Occupation.complement x ∈ S

/--
If a nonempty support is disjoint from its complement image, then it cannot be
stable under complement.

This is the finite set-theoretic shadow of the Fermi-Fock obstruction:
a support concentrated on one complement-disjoint orbit cannot carry a real
form whose closure maps support to `1-support`.
-/
theorem not_supportStable_of_complement_disjoint
    {m : Nat}
    {S : Set (Occupation m)}
    (hNonempty : exists x : Occupation m, x ∈ S)
    (hDisjoint :
      forall x : Occupation m,
        x ∈ S -> Occupation.complement x ∉ S) :
    ¬ SupportStableUnderComplement S := by
  intro hStable
  rcases hNonempty with ⟨x, hx⟩
  have hxComp : Occupation.complement x ∈ S :=
    (hStable x).mp hx
  exact hDisjoint x hx hxComp

end InfoGeometry.OperatorAlgebra.SplitCliffordRealForms
