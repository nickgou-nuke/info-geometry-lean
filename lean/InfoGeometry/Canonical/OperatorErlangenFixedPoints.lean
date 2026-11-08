import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SupergradedBracket

/-!
# Operator Erlangen fixed points

This owner formalizes the symmetry-reduction axis independently of the
supergraded product split.  It proves only the universal fixed-point and
orbit facts; no arbitrary operator-algebra Galois anti-equivalence is claimed.
-/

namespace InfoGeometry.Canonical.OperatorErlangenFixedPoints

variable {G A : Type*} [Group G] [Semiring A] [MulSemiringAction G A]

/-- Elements fixed by every element of a subgroup. -/
def fixedPointSet (H : Subgroup G) : Set A :=
  {a | ∀ h : H, (h : G) • a = a}

/-- The fixed points form a native subsemiring. -/
def fixedPointSubsemiring (H : Subgroup G) : Subsemiring A where
  carrier := fixedPointSet H
  zero_mem' := by
    intro h
    simp
  add_mem' := by
    intro x y hx hy h
    rw [smul_add, hx h, hy h]
  one_mem' := by
    intro h
    simp
  mul_mem' := by
    intro x y hx hy h
    calc
      (h : G) • (x * y) = ((h : G) • x) * ((h : G) • y) :=
        MulSemiringAction.smul_mul (M := G) (R := A) (h : G) x y
      _ = x * y := by rw [hx h, hy h]

theorem mem_fixedPointSubsemiring_iff (H : Subgroup G) (a : A) :
    a ∈ fixedPointSubsemiring H ↔ ∀ h : H, (h : G) • a = a :=
  Iff.rfl

/-- More symmetry gives fewer invariant elements. -/
theorem fixedPointSet_antitone {H K : Subgroup G} (h : H ≤ K) :
    fixedPointSet (A := A) K ⊆ fixedPointSet (A := A) H := by
  intro a ha g
  exact ha ⟨g, h g.property⟩

theorem fixedPointSubsemiring_antitone {H K : Subgroup G} (h : H ≤ K) :
    fixedPointSubsemiring (A := A) K ≤ fixedPointSubsemiring (A := A) H := by
  intro a ha
  exact fixedPointSet_antitone (A := A) h ha

section SupergradedCompatibility

variable {R B : Type*} [Field R] [Ring B] [Algebra R B]
  [DistribMulAction G B]

def ringFixedPointSet (H : Subgroup G) : Set B :=
  {b | ∀ h : H, (h : G) • b = b}

theorem smul_superBracket
    (hmul : ∀ (g : G) (x y : B), g • (x * y) = (g • x) * (g • y))
    (g : G) (p q : Bool) (x y : B) :
    g • InfoGeometry.Algebra.SupergradedBracket.superBracket p q x y =
      InfoGeometry.Algebra.SupergradedBracket.superBracket p q (g • x) (g • y) := by
  have hxy : g • (x * y) = (g • x) * (g • y) :=
    hmul g x y
  have hyx : g • (y * x) = (g • y) * (g • x) :=
    hmul g y x
  cases p <;> cases q <;>
      simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
        InfoGeometry.Algebra.SupergradedBracket.commutator,
        InfoGeometry.Algebra.SupergradedBracket.anticommutator,
        InfoGeometry.Algebra.InvariantTransport.commutator,
        InfoGeometry.Algebra.InvariantTransport.anticommutator,
        smul_sub, smul_add, hxy, hyx]

theorem fixedPointSet_superBracket_mem
    (hmul : ∀ (g : G) (x y : B), g • (x * y) = (g • x) * (g • y))
    (H : Subgroup G) (p q : Bool) {x y : B}
    (hx : x ∈ ringFixedPointSet (G := G) H)
    (hy : y ∈ ringFixedPointSet (G := G) H) :
    InfoGeometry.Algebra.SupergradedBracket.superBracket p q x y ∈
      ringFixedPointSet (G := G) H := by
  intro h
  calc
    (h : G) • InfoGeometry.Algebra.SupergradedBracket.superBracket p q x y =
        InfoGeometry.Algebra.SupergradedBracket.superBracket p q
          ((h : G) • x) ((h : G) • y) :=
      smul_superBracket hmul (g := (h : G)) p q x y
    _ = InfoGeometry.Algebra.SupergradedBracket.superBracket p q x y := by
      rw [hx h, hy h]

end SupergradedCompatibility

section Orbits

variable {X : Type*} [MulAction G X]

/-- The orbit of an observable under the group action. -/
def orbit (a : X) : Set X := MulAction.orbit G a

/-- The stabilizer of an observable under the group action. -/
def stabilizer (a : X) : Subgroup G := MulAction.stabilizer G a

theorem orbit_eq_range (a : X) :
    orbit (G := G) (X := X) a = Set.range (fun g : G => g • a) := by
  rfl

/-- The standard orbit--quotient-by-stabilizer equivalence. -/
noncomputable def orbit_quotient_stabilizer_equiv (a : X) :
    ↥(orbit (G := G) (X := X) a) ≃ G ⧸ stabilizer (G := G) (X := X) a :=
  MulAction.orbitEquivQuotientStabilizer G a

end Orbits

end InfoGeometry.Canonical.OperatorErlangenFixedPoints
