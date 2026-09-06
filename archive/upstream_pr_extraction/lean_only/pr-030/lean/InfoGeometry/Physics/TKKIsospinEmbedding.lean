import Mathlib.Tactic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Lie.Basic
import InfoGeometry.NuclearHamiltonian
import InfoGeometry.Canonical.ZornSpinor

namespace InfoGeometry.Physics

open InfoGeometry.Canonical

/-- Generic TKK algebra interface used by the abstract nuclear-isospin files.
The concrete Zorn model below supplies explicit witnesses separately; this class
only records the linear triality operator needed by generic transport lemmas. -/
class TKKAlgebra (R L : Type*) [CommRing R] [AddCommGroup L] [Module R L]
    [LieRing L] [LieAlgebra R L] where
  trialityProjector : L →ₗ[R] L

/-- The triality projector carried by a `TKKAlgebra` instance. -/
def TrialityProjector {R L : Type*} [CommRing R] [AddCommGroup L] [Module R L]
    [LieRing L] [LieAlgebra R L] [TKKAlgebra R L] : L →ₗ[R] L :=
  TKKAlgebra.trialityProjector (R := R) (L := L)

/-- Concrete Zorn matrix type. -/
abbrev ConcreteZorn := InfoGeometry.Canonical.ZornMatrix ℚ

/-- Concrete triality witness on the canonical Zorn carrier: swap diagonal and spinor slots. -/
def concreteTrialityProjector : ConcreteZorn →ₗ[ℚ] ConcreteZorn where
  toFun Z := { a := Z.b, b := Z.a, x := Z.y, y := Z.x }
  map_add' := by
    intro X Y
    ext <;> rfl
  map_smul' := by
    intro c X
    ext <;> rfl

/-- Positive-grade basis witness in the concrete Zorn lane. -/
def ePlus : ConcreteZorn := { a := 1, b := 0, x := 0, y := 0 }

/-- A concrete `g₁` spinor witness (up₀ = [0, e₁; 0, 0]). -/
def up0 : ConcreteZorn := { a := 0, b := 0, x := ![1, 0, 0], y := 0 }

/-- Commutator in the concrete Zorn algebra. -/
def zornCommutator (X Y : ConcreteZorn) : ConcreteZorn := X * Y - Y * X

/-- Concrete isospin-breaking witness: the triality projector does not commute
with the Zorn commutator on explicit generators. -/
theorem triality_isospin_breaking :
    ∃ x y : ConcreteZorn,
      concreteTrialityProjector (zornCommutator x y) ≠
        zornCommutator x (concreteTrialityProjector y) := by
  use ePlus, up0
  intro h
  have h₁ := congrArg (fun Z : ConcreteZorn => Z.x 0) h
  have h₂ := congrArg (fun Z : ConcreteZorn => Z.y 0) h
  simp [concreteTrialityProjector, zornCommutator, ePlus, up0,
    InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross] at h₁ h₂
  <;> norm_num [Fin.val_zero, Fin.val_succ, ConcreteZorn] at h₁ h₂

/-- Concrete SU(2) action on g₁: purely diagonal elements in g₀ preserve g₁.
In the Zorn model:
- g₀ = {X | X.a = X.b, X.x = 0, X.y = 0} (purely diagonal)
- g₁ = {X | X.a = 0 ∧ X.b = 0 ∧ X.y = 0} (pure upper spinors)
For g₀ with g₀.a = g₀.b, g₀.x = 0, g₀.y = 0 and u with u.a = 0, u.b = 0, u.y = 0:
[g₀, u] has a = 0 and b = 0, so it stays in g₁.

Direct computation using the Zorn multiplication formula:
For X * Y: a = X.a * Y.a + X.x ⬝ Y.y
For X * Y: b = X.b * Y.b + X.y ⬝ Y.x

When X = g₀ (with g₀.a = g₀.b = α, g₀.x = 0, g₀.y = 0) and Y = u (with u.a = 0, u.b = 0, u.y = 0):
- (g₀ * u).a = α * 0 + 0 ⬝ 0 = 0
- (u * g₀).a = 0 * α + u.x ⬝ 0 = 0
- (g₀ * u - u * g₀).a = 0

- (g₀ * u).b = α * 0 * 0 + 0 ⬝ u.x = 0
- (u * g₀).b = 0 * α + u.y ⬝ g₀.x = 0 ⬝ 0 = 0
- (g₀ * u - u * g₀).b = 0

Thus [g₀, u] ∈ g₁. -/
theorem concrete_su2_action_g1 :
    ∀ (g₀ u : ConcreteZorn),
    g₀.a = g₀.b → g₀.x = 0 → g₀.y = 0 → u.a = 0 → u.b = 0 → u.y = 0 →
    (zornCommutator g₀ u).a = 0 ∧ (zornCommutator g₀ u).b = 0 := by
  intro g₀ u hg₀_ab hg₀_x hg₀_y hu_a hu_b hu_y
  simp only [zornCommutator, ConcreteZorn, Prod.ext_iff]
  constructor
  · -- Prove (g₀ * u - u * g₀).a = 0
    simp [InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      sub_mul, mul_sub]
    <;>
    (try simp_all [ConcreteZorn, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ])
  · -- Prove (g₀ * u - u * g₀).b = 0
    simp [InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      sub_mul, mul_sub]
    <;>
    (try simp_all [ConcreteZorn, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ])

end InfoGeometry.Physics
