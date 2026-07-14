import Mathlib
import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
import InfoGeometry.Clifford.BottPeriodicity

/-!
# InfoGeometry.OperatorAlgebra.ErlangenConformalInvariant

Operator-algebraic Erlangen packet for the conformal corridor.

This file rewrites the Klein/Erlangen slogan in the language actually used by
the repository's operator and symmetry lanes.

## Core principle

Geometry is encoded by a symmetry representation and its invariant observables,
not merely by coordinates. Given a group action on an algebra `A`, the
geometric observables are the fixed points of that action:

* `A^G = {x | ∀ g, α_g x = x}`

When the action is implemented by representation operators `U_g`, this is the
commutant/fixed-point viewpoint:

* `Ad(U_g)(A) = U_g A U_g⁻¹`
* invariant observables satisfy `Ad(U_g)(A) = A`
* equivalently: `A^G = A ∩ U(G)'`

This file only formalizes the fixed-point subalgebra and its functorial
transport along equivariant maps. It does not formalize the full commutant of
an operator representation.

## Repo specialization

For the conformal/operator corridor, the intended architectural reading is:

* `O(5,5)`   — ambient split-orthogonal symmetry;
* `Pin(5,5)` — full Clifford double cover including reflections;
* `Spin(5,5)` — even orientation-preserving subgroup;
* `P, D, K` — infinitesimal chart readout of the conformal lane;
* Möbius / null-boundary / modular readouts — downstream surfaces of the same
  symmetry corridor.

## Direct-limit tower: what is proved here

If a finite-stage tower is `G`-equivariant, then each equivariant stage map
sends invariant elements to invariant elements. This is the safe stagewise
statement behind a canonical map

* `colim(X_n^G) → (colim X_n)^G`

when an actual direct limit is constructed elsewhere.

## Explicit non-claims

This file does not prove:

* construction of an algebraic direct limit;
* equality `(colim X_n)^G = colim(X_n^G)`;
* any compact-group averaging or conditional expectation;
* any C*-, W*-, or von Neumann completion theorem;
* any global fixed-point exactness result for noncompact `O(5,5)` / `Pin(5,5)`.

Those require separate owner interfaces and, in the noncompact case, additional
regularization/continuity/completion data.
-/

noncomputable section

namespace ErlangenConformalInvariant

/--
An action of a group G on an algebra A by algebra automorphisms.
-/
structure GroupAction (G : Type*) [Group G] (A : Type*) [Ring A] [Algebra ℝ A] where
  toFun : G → (A ≃ₐ[ℝ] A)
  map_one' : toFun 1 = AlgEquiv.refl
  map_mul' : ∀ g1 g2 : G, toFun (g1 * g2) = (toFun g1).trans (toFun g2)

namespace GroupAction

variable {G : Type*} [Group G] {A : Type*} [Ring A] [Algebra ℝ A]
variable (act : GroupAction G A)

instance : CoeFun (GroupAction G A) (fun _ => G → (A ≃ₐ[ℝ] A)) where
  coe := toFun

/--
The invariant subalgebra (fixed-point subalgebra) of A under the group action.
-/
def fixedSubalgebra : Subalgebra ℝ A where
  carrier := {x | ∀ g : G, act g x = x}
  mul_mem' := by
    intro x y hx hy g
    simp [hx g, hy g]
  one_mem' := by
    intro g
    simp
  add_mem' := by
    intro x y hx hy g
    simp [hx g, hy g]
  zero_mem' := by
    intro g
    simp
  algebraMap_mem' := by
    intro r g
    simp

end GroupAction

/--
Equivariance of an algebra homomorphism between two group actions.
-/
structure EquivariantHom {G : Type*} [Group G] {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]
    (actA : GroupAction G A) (actB : GroupAction G B) (φ : A →ₐ[ℝ] B) : Prop where
  equivariance : ∀ (g : G) (x : A), φ (actA g x) = actB g (φ x)

namespace EquivariantHom

variable {G : Type*} [Group G] {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]
variable {actA : GroupAction G A} {actB : GroupAction G B} {φ : A →ₐ[ℝ] B}

/--
An equivariant homomorphism maps invariant elements to invariant elements.
This is the pullback step of the fixed-point algebra along finite direct-limit stages.
-/
theorem fixedSubalgebra_pullback (h : EquivariantHom actA actB φ) (x : A) (hx : x ∈ actA.fixedSubalgebra) :
    φ x ∈ actB.fixedSubalgebra := by
  intro g
  rw [← h.equivariance, hx g]

/--
An equivariant homomorphism induces a canonical algebra homomorphism between the
fixed-point subalgebras.

This is the finite-stage invariant transport map used in the operator-algebraic
Erlangen reading of an equivariant tower. It is the safe algebraic precursor to
any stronger direct-limit statement.
-/
def fixedSubalgebraHom (h : EquivariantHom actA actB φ) :
    actA.fixedSubalgebra →ₐ[ℝ] actB.fixedSubalgebra where
  toFun x := ⟨φ x, fixedSubalgebra_pullback h x x.property⟩
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp
  map_zero' := by
    ext
    simp
  map_add' x y := by
    ext
    simp
  commutes' r := by
    ext
    simp

end EquivariantHom

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
[fixedSubalgebra_pullback compiles and proves equivariant fixed-point transport cleanly.]
[fixedSubalgebraHom compiles and packages the canonical finite-stage invariant map.]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[The GroupAction and EquivariantHom structures define the Erlangen Program mappings.]
[If an actual direct-limit tower is constructed elsewhere and its bonding maps are equivariant,
 this file supplies the stagewise fixed-point transport needed for a canonical
 `colim(X_n^G) → (colim X_n)^G` map.]

#### BUCKET 3: OPEN CLOSURE DEBT
[This file does not prove global fixed-point exactness across an algebraic or analytic limit.]
[For noncompact `O(5,5)` / `Pin(5,5)` symmetry, any stronger global invariant theorem needs a
 separate regularization/continuity/completion owner lane.]
-/

end ErlangenConformalInvariant
