import InfoGeometry.Prequantum.AlgebraicGNSState

/-!
# InfoGeometry.Prequantum.GNSBridge

The theorem-safe GNS corridor.

This file keeps the state representation abstract:

* a state is a positive normalized real linear functional;
* the GNS null set is the zero quadratic locus;
* finite compatible state nets can be rewrapped as abstract states stagewise.

No Hilbert-space completion or von Neumann closure is constructed here.
-/

set_option autoImplicit false

namespace GNSBridge

open InfoGeometry.Prequantum.AlgebraicGNSState

/-- Abstract GNS state wrapper around the repository's algebraic state. -/
structure AbstractGNSState
    (A : Type*) [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A] where
  /-- Positive normalized real state. -/
  state : RealAlgebraicState A

namespace AbstractGNSState

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]

/-- Evaluation of the abstract GNS state. -/
def eval (S : AbstractGNSState A) (x : A) : ℝ :=
  S.state.eval x

/-- The GNS null set. -/
def gnsNullSet (S : AbstractGNSState A) : Set A :=
  S.state.gnsNullSet

@[simp] theorem eval_one (S : AbstractGNSState A) :
    S.eval 1 = 1 := by
  simp [AbstractGNSState.eval]

/-- Algebraic vacuum normalization for the wrapped GNS state. -/
theorem gns_vacuum_norm_eq_one (S : AbstractGNSState A) :
    S.state.eval (star (1 : A) * 1) = 1 :=
  S.state.gns_vacuum_norm_eq_one

@[simp] theorem mem_gnsNullSet_iff (S : AbstractGNSState A) (x : A) :
    x ∈ S.gnsNullSet ↔ S.state.eval (star x * x) = 0 :=
  Iff.rfl

/-- The zero element lies in the GNS null set. -/
theorem zero_mem_gnsNullSet (S : AbstractGNSState A) :
    (0 : A) ∈ S.gnsNullSet := by
  have h0 : (star (0 : A) * (0 : A)) = 0 := by simp
  rw [mem_gnsNullSet_iff, h0]
  exact S.state.toLinearMap.map_zero

/-- Quadratic positivity is inherited from the underlying state. -/
theorem state_quadratic_nonneg
    (S : AbstractGNSState A) (x y : A) (t : ℝ) :
    0 ≤ S.state.eval (star x * x) + 2 * t * S.state.eval (star y * x) +
      t ^ 2 * S.state.eval (star y * y) := by
  simpa using S.state.state_quadratic_nonneg x y t

/-- Cauchy--Schwarz for the abstract GNS state. -/
theorem algebraic_cauchy_schwarz
    (S : AbstractGNSState A) (x y : A)
    (hy : 0 < S.state.eval (star y * y)) :
    (S.state.eval (star y * x)) ^ 2 ≤
      S.state.eval (star x * x) * S.state.eval (star y * y) := by
  simpa using S.state.algebraic_cauchy_schwarz x y hy

/-- A real linear expression bounded below for all `t` has zero slope. -/
theorem linear_nonneg_imp_zero (B C : ℝ)
    (h_linear : ∀ t : ℝ, 0 ≤ C + 2 * t * B) :
    B = 0 :=
  RealAlgebraicState.linear_nonneg_imp_zero B C h_linear

/-- If `y` is GNS-null, then it annihilates every partner in the state pairing. -/
theorem state_null_product_zero
    (S : AbstractGNSState A) (x y : A)
    (hy : y ∈ S.gnsNullSet) :
    S.state.eval (star y * x) = 0 :=
  S.state.state_null_product_zero x y hy

/-- The GNS null set is closed under addition. -/
theorem gns_null_addition_closed
    (S : AbstractGNSState A) (u v : A)
    (hu : u ∈ S.gnsNullSet) (hv : v ∈ S.gnsNullSet) :
    u + v ∈ S.gnsNullSet :=
  S.state.add_mem_gnsNullSet hu hv

/-- GNS equivalence: difference lies in the null set. -/
def gnsEquiv (S : AbstractGNSState A) (x y : A) : Prop :=
  S.state.gnsEquiv x y

/-- Reflexivity of the algebraic GNS equivalence. -/
theorem gns_refl (S : AbstractGNSState A) (x : A) :
    gnsEquiv S x x :=
  S.state.gnsEquiv_refl x

/-- Symmetry of the algebraic GNS equivalence. -/
theorem gns_symm (S : AbstractGNSState A) {x y : A} (h : gnsEquiv S x y) :
    gnsEquiv S y x :=
  S.state.gnsEquiv_symm h

/-- Transitivity of the algebraic GNS equivalence. -/
theorem gns_trans (S : AbstractGNSState A) {x y z : A}
    (h1 : gnsEquiv S x y) (h2 : gnsEquiv S y z) :
    gnsEquiv S x z :=
  S.state.gnsEquiv_trans h1 h2

/-- Setoid of GNS-equivalent elements. -/
def gnsSetoid (S : AbstractGNSState A) : Setoid A :=
  S.state.gnsSetoid

/-- The algebraic GNS quotient carrier.  This is not a completed Hilbert space. -/
abbrev gnsQuotient (S : AbstractGNSState A) : Type _ :=
  Quotient (gnsSetoid S)

@[simp] theorem gnsQuotient_mk (S : AbstractGNSState A) (x : A) :
    Quotient.mk (gnsSetoid S) x = (Quotient.mk (gnsSetoid S) x : gnsQuotient S) := rfl

end AbstractGNSState

section CompatibleFiniteNet

open InfoGeometry.Meta.MarkovJonesInduction

variable {A : Nat → Type*}
variable [∀ n : Nat, Ring (A n)] [∀ n : Nat, Algebra ℝ (A n)]
variable [∀ n : Nat, StarRing (A n)] [∀ n : Nat, StarModule ℝ (A n)]

/-- Rewrap a compatible finite-state net as an abstract GNS state at a stage. -/
def atStage
    {Net : InductiveAlgebraNet (𝕜 := ℝ) (A := A)}
    (S : CompatibleAlgebraicStateNet Net) (n : Nat)
    (hsymm : ∀ x y : A n, S.state n (star y * x) = S.state n (star x * y)) :
    AbstractGNSState (A n) where
  state := S.atStage n hsymm

@[simp] theorem atStage_eval_one
    {Net : InductiveAlgebraNet (𝕜 := ℝ) (A := A)}
    (S : CompatibleAlgebraicStateNet Net) (n : Nat)
    (hsymm : ∀ x y : A n, S.state n (star y * x) = S.state n (star x * y)) :
    (atStage (S := S) n hsymm).eval 1 = 1 := by
  simp [atStage]

end CompatibleFiniteNet

end GNSBridge
