import InfoGeometry.Spectral.Algebra.ExactCouple
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Spectral.Algebra.SpectralSequence
import InfoGeometry.Spectral.Cohomology.Basic
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Native homotopy groups and algebraic spectral pages

The former port assigned `PUnit` to stable homotopy groups and used
eventual-`True` fields as convergence claims.  Those declarations did not
formalize Adams, Adams--Novikov, EHP, or Whitehead theory.

This module now uses Mathlib's genuine homotopy groups, defined as homotopy
classes of iterated loops, for the topological owner layer.  Adams and
Adams--Novikov pages remain consequences of explicit exact-couple inputs.
Constructing the sphere exact couples, filtrations, and abutments is separate
from defining the homotopy groups they are intended to compute.
-/

namespace InfoGeometry.Spectral.HigherGroups

open InfoGeometry.Spectral.Algebra
open InfoGeometry.Spectral.Cohomology.Basic
open scoped Topology

universe u

/-! ## Native topological homotopy groups -/

/--
The genuine `n`th homotopy group of a pointed topological space.

This is Mathlib's quotient of `n`-fold generalized loops by pointed homotopy,
not a placeholder carrier.
-/
abbrev NativeHomotopyGroup
    (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :=
  HomotopyGroup.Pi n X x

/-- The native fundamental-group comparison for the first homotopy group. -/
def nativePiOneEquivFundamentalGroup
    (X : Type u) [TopologicalSpace X] (x : X) :
    NativeHomotopyGroup 1 X x ≃ FundamentalGroup X x :=
  HomotopyGroup.pi1EquivFundamentalGroup

/--
For at least two loop coordinates, the Eckmann--Hilton argument gives the
canonical commutativity law on the native homotopy group.
-/
theorem nativeHomotopyGroup_mul_comm
    (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X)
    [Nontrivial (Fin n)]
    (a b : NativeHomotopyGroup n X x) :
    a * b = b * a :=
  mul_comm a b

/-! ## Exact-couple spectral pages -/

variable {R : Type u} [Ring R]
variable {D E : Z2 → Type u}
variable [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E pq)]
variable [∀ pq, Module R (D pq)] [∀ pq, Module R (E pq)]

/-- An Adams page at the currently formalized exact-couple level. -/
abbrev AdamsPage
    (R : Type u) [Ring R]
    (E : Z2 → Type u)
    [∀ pq, AddCommGroup (E pq)] [∀ pq, Module R (E pq)] :=
  SpectralSequencePage R E shiftK

/-- Construct the square-zero Adams page supplied by explicit exact-couple data. -/
def adamsPageOfExactCouple (C : ExactCouple R D E) : AdamsPage R E :=
  C.toPage

@[simp]
theorem adamsPageOfExactCouple_d
    (C : ExactCouple R D E) (pq : Z2) :
    (adamsPageOfExactCouple C).d pq = C.differential pq :=
  rfl

/-- The exactness law at `E` proves the Adams-page differential squares to zero. -/
theorem adamsPageOfExactCouple_differential_sq_zero
    (C : ExactCouple R D E) (pq : Z2) :
    ((adamsPageOfExactCouple C).d (shiftK pq)).comp
        ((adamsPageOfExactCouple C).d pq) = 0 :=
  C.toPage_differential_sq_zero pq

/--
At this algebraic level an Adams--Novikov page has the same square-zero page
type.  Its distinction from an Adams page lies in the separately constructed
exact couple and coefficient theory, not in an additional proof packet.
-/
abbrev AdamsNovikovPage
    (R : Type u) [Ring R]
    (E : Z2 → Type u)
    [∀ pq, AddCommGroup (E pq)] [∀ pq, Module R (E pq)] :=
  SpectralSequencePage R E shiftK

/-- Construct an Adams--Novikov page from its explicit exact couple. -/
def adamsNovikovPageOfExactCouple
    (C : ExactCouple R D E) : AdamsNovikovPage R E :=
  C.toPage

/-- The induced Adams--Novikov page has a square-zero differential. -/
theorem adamsNovikovPageOfExactCouple_differential_sq_zero
    (C : ExactCouple R D E) (pq : Z2) :
    ((adamsNovikovPageOfExactCouple C).d (shiftK pq)).comp
        ((adamsNovikovPageOfExactCouple C).d pq) = 0 :=
  C.toPage_differential_sq_zero pq

/--
A three-term EHP fragment is an exact sequence of additive groups.  This is the
native algebraic interface required before a sphere-level EHP construction can
be claimed.
-/
abbrev EHPFragment
    (A B C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] :=
  ExactSequence A B C

/-- In every EHP fragment, the consecutive maps compose to zero. -/
theorem EHPFragment.comp_eq_zero
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (S : EHPFragment A B C) (a : A) :
    S.g (S.f a) = 0 :=
  S.f_exact a

/-- Exactness identifies every element in the kernel of `g` with an image under `f`. -/
theorem EHPFragment.mem_range_of_mem_kernel
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (S : EHPFragment A B C) {b : B} (hb : S.g b = 0) :
    ∃ a : A, S.f a = b :=
  S.exactness b hb

end InfoGeometry.Spectral.HigherGroups
