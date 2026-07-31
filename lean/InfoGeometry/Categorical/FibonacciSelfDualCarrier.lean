import InfoGeometry.Categorical.FibonacciBraidDirectLimit
import InfoGeometry.Convex.SelfDualCone
import InfoGeometry.OperatorAlgebra.ProperCarrierSelfDualConeExtension

/-!
# InfoGeometry.Categorical.FibonacciSelfDualCarrier

Carrier socket for Fibonacci braid/direct-limit actions on a Hilbert
self-dual cone.

The purpose of this file is deliberately modest:

* package a Hilbert carrier with a `Convex.SelfDualCone`;
* record cone preservation for finite braid words and direct-limit matrix
  observables as explicit fields;
* delegate finite-stage self-dual cone extension to the existing
  `OperatorAlgebra.ProperCarrierSelfDualConeExtension` owner.

No theorem here constructs the Tomita natural cone, a Type III standard form,
or a full Fibonacci `BraidedCategory`.
-/

noncomputable section

set_option autoImplicit false

namespace InfoGeometry.Categorical.FibonacciSelfDualCarrier

open InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
open InfoGeometry.Categorical.FibonacciBraidDirectLimit
open InfoGeometry.Convex

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Hilbert carrier for Fibonacci braid data with an installed self-dual positive
cone.

`braidAction` is the finite braid-word action.  `limitObservableAction` is the
action of algebraic direct-limit matrix observables on the same carrier.  Both
cone-preservation laws are explicit fields until a concrete Majorana/O(5,5) or
operator-algebra realization proves them.
-/
structure ActionModel (A : Type*) [Semiring A] where
  /-- Hilbert self-dual positive cone. -/
  positiveCone : SelfDualCone E
  /-- Finite Fibonacci braid-word action on the carrier. -/
  braidAction : FibonacciBraidWord → E → E
  /-- Algebraic direct-limit matrix-observable action on the carrier. -/
  limitObservableAction : Matrix (Fin 2) (Fin 2) A → E → E
  /-- Finite braid words preserve the positive cone. -/
  braidAction_preserves_positiveCone :
    ∀ w : FibonacciBraidWord,
      Set.MapsTo (braidAction w) (positiveCone.cone : Set E) positiveCone.cone
  /-- Direct-limit matrix observables preserve the positive cone. -/
  limitObservableAction_preserves_positiveCone :
    ∀ M : Matrix (Fin 2) (Fin 2) A,
      Set.MapsTo (limitObservableAction M) (positiveCone.cone : Set E) positiveCone.cone

namespace ActionModel

variable {A : Type*} [Semiring A]
variable (C : ActionModel (E := E) A)

/-- The carrier cone is equal to its Hilbert inner dual. -/
theorem positiveCone_innerDual_eq :
    ProperCone.innerDual (C.positiveCone.cone : Set E) = C.positiveCone.cone :=
  SelfDualCone.innerDual_eq C.positiveCone

/-- Projection theorem: finite Fibonacci braid actions preserve the carrier cone. -/
theorem braidAction_maps_positiveCone
    (w : FibonacciBraidWord) :
    Set.MapsTo (C.braidAction w) (C.positiveCone.cone : Set E) C.positiveCone.cone :=
  C.braidAction_preserves_positiveCone w

/-- Pointwise form of finite braid cone preservation. -/
theorem braidAction_mem_positiveCone
    (w : FibonacciBraidWord) {x : E}
    (hx : x ∈ (C.positiveCone.cone : Set E)) :
    C.braidAction w x ∈ (C.positiveCone.cone : Set E) :=
  C.braidAction_preserves_positiveCone w hx

/-- Projection theorem: direct-limit matrix observables preserve the carrier cone. -/
theorem limitObservableAction_maps_positiveCone
    (M : Matrix (Fin 2) (Fin 2) A) :
    Set.MapsTo (C.limitObservableAction M) (C.positiveCone.cone : Set E) C.positiveCone.cone :=
  C.limitObservableAction_preserves_positiveCone M

/-- Pointwise form of direct-limit observable cone preservation. -/
theorem limitObservableAction_mem_positiveCone
    (M : Matrix (Fin 2) (Fin 2) A) {x : E}
    (hx : x ∈ (C.positiveCone.cone : Set E)) :
    C.limitObservableAction M x ∈ (C.positiveCone.cone : Set E) :=
  C.limitObservableAction_preserves_positiveCone M hx

/-- Direct-limit `R` matrices preserve the carrier cone through the installed observable action. -/
theorem limitRMatrix_mem_positiveCone
    {Stage : Nat → Type*} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (D : ActionModel (E := E) (BraidLimit (Stage := Stage) bond))
    (n : Nat) (q qInv : Stage n) {x : E}
    (hx : x ∈ (D.positiveCone.cone : Set E)) :
    D.limitObservableAction (limitRMatrix bond n q qInv) x ∈ (D.positiveCone.cone : Set E) :=
  D.limitObservableAction_mem_positiveCone (limitRMatrix bond n q qInv) hx

/-- Direct-limit `B = F R F` matrices preserve the carrier cone through the installed action. -/
theorem limitBMatrix_mem_positiveCone
    {Stage : Nat → Type*} [∀ n : Nat, CommRing (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (D : Carrier (E := E) (BraidLimit (Stage := Stage) bond))
    (n : Nat) (q qInv τ sqrtτ : Stage n) {x : E}
    (hx : x ∈ (D.positiveCone.cone : Set E)) :
    D.limitObservableAction (limitBMatrix bond n q qInv τ sqrtτ) x ∈
      (D.positiveCone.cone : Set E) :=
  D.limitObservableAction_mem_positiveCone (limitBMatrix bond n q qInv τ sqrtτ) hx

end Carrier

/-! ## Proper-carrier staged self-dual extension -/

/--
The staged proper-carrier self-dual extension theorem, re-exported in the
Fibonacci carrier namespace.  This is the correct owner-backed route for
turning finite self-dual carrier stages into a colimit carrier: monotonicity,
stagewise self-duality, and a detector are explicit hypotheses.
-/
theorem staged_selfDualCone_extends_to_colimit
    {X : Type*}
    (pairing : X → X → ℝ)
    (K : ℕ → Set X)
    (hmono : Monotone K)
    (hself :
      ∀ n : ℕ,
        InfoGeometry.OperatorAlgebra.SelfDualConeColimit.IsSelfDualCone pairing (K n))
    (hdetect :
      ∀ x, (∀ y, y ∈ Set.iUnion K → 0 ≤ pairing x y) → ∃ n : ℕ, x ∈ K n) :
    InfoGeometry.OperatorAlgebra.SelfDualConeColimit.IsSelfDualCone
      pairing (Set.iUnion K) :=
  InfoGeometry.OperatorAlgebra.ProperCarrierSelfDualConeExtension.properCarrier_selfDualCone_extends_to_algebra
    pairing K hmono hself hdetect

end InfoGeometry.Categorical.FibonacciSelfDualCarrier
