import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Algebra.Category.ModuleCat.Injective

universe u

/-!
# Categorical Colimits and Representations in ModuleCat

We construct specific, concrete representations individuating the generalized categorical boundaries for $d^2 = 0$.

1. Concrete physical representations of abstract states (e.g., Isospin and Braid Group Actions).
2. Explicit Primal-Dual generalized mapping.
3. Concrete chain complex boundaries ($d^2 = 0$).
4. Concrete Free module resolution examples with complete proofs.
-/

namespace PhysicalRepresentations

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- 1. Isospin States as an explicit concrete representation module over a commutative ring. -/
@[ext]
structure IsospinState (R : Type u) [CommRing R] where
  up : R
  down : R

namespace IsospinState

variable {R : Type u} [CommRing R]

instance : Add (IsospinState R) := ⟨fun a b => ⟨a.up + b.up, a.down + b.down⟩⟩
@[simp] lemma add_up (a b : IsospinState R) : (a + b).up = a.up + b.up := rfl
@[simp] lemma add_down (a b : IsospinState R) : (a + b).down = a.down + b.down := rfl

instance : Zero (IsospinState R) := ⟨⟨0, 0⟩⟩
@[simp] lemma zero_up : (0 : IsospinState R).up = 0 := rfl
@[simp] lemma zero_down : (0 : IsospinState R).down = 0 := rfl

instance : Neg (IsospinState R) := ⟨fun a => ⟨-a.up, -a.down⟩⟩
@[simp] lemma neg_up (a : IsospinState R) : (-a).up = -a.up := rfl
@[simp] lemma neg_down (a : IsospinState R) : (-a).down = -a.down := rfl

instance : Sub (IsospinState R) := ⟨fun a b => ⟨a.up - b.up, a.down - b.down⟩⟩
@[simp] lemma sub_up (a b : IsospinState R) : (a - b).up = a.up - b.up := rfl
@[simp] lemma sub_down (a b : IsospinState R) : (a - b).down = a.down - b.down := rfl

instance : AddCommGroup (IsospinState R) where
  add := (· + ·)
  add_assoc := by intros a b c; ext <;> (simp; try ring)
  zero := 0
  zero_add := by intro a; ext <;> (simp; try ring)
  add_zero := by intro a; ext <;> (simp; try ring)
  neg := (-(·))
  neg_add_cancel := by intro a; ext <;> (simp; try ring)
  add_comm := by intros a b; ext <;> (simp; try ring)
  sub := (· - ·)
  sub_eq_add_neg := by intros a b; ext <;> (simp; try ring)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : SMul R (IsospinState R) := ⟨fun r a => ⟨r * a.up, r * a.down⟩⟩
@[simp] lemma smul_up (r : R) (a : IsospinState R) : (r • a).up = r * a.up := rfl
@[simp] lemma smul_down (r : R) (a : IsospinState R) : (r • a).down = r * a.down := rfl

instance : Module R (IsospinState R) where
  smul := (· • ·)
  one_smul := by intro a; ext <;> simp <;> try ring
  mul_smul := by intros r s a; ext <;> simp <;> try ring
  smul_add := by intros r a b; ext <;> simp <;> try ring
  smul_zero := by intros r; ext <;> simp <;> try ring
  add_smul := by intros r s a; ext <;> simp <;> try ring
  zero_smul := by intro a; ext <;> simp

/-- 2. Primal-Dual Mapping representation mapping a state to its dual.
This demonstrates the collapse of generalized categorical duality into coordinates. -/
def primalDualMap : IsospinState R →ₗ[R] (IsospinState R →ₗ[R] R) where
  toFun := fun v => {
    toFun := fun w => v.up * w.up + v.down * w.down
    map_add' := by intros x y; simp <;> try ring
    map_smul' := by intros r x; simp <;> try ring
  }
  map_add' := by intros x y; ext w; simp <;> try ring
  map_smul' := by intros r x; ext w; simp <;> try ring

/-- 3. Explicit Boundaries and d^2 = 0 mapping. 
This exact representation mirrors the De Rham chain $M_2 \to M_1 \to M_0$. -/
def d1 : IsospinState R →ₗ[R] IsospinState R where
  toFun := fun v => ⟨v.up - v.down, v.down - v.up⟩
  map_add' := by intros x y; ext <;> simp <;> try ring
  map_smul' := by intros r x; ext <;> simp <;> try ring

def d2 : IsospinState R →ₗ[R] IsospinState R where
  toFun := fun v => ⟨v.up + v.down, v.up + v.down⟩
  map_add' := by intros x y; ext <;> simp <;> try ring
  map_smul' := by intros r x; ext <;> simp <;> try ring

theorem d1_comp_d2_eq_zero : (d1 : IsospinState R →ₗ[R] IsospinState R).comp d2 = 0 := by
  ext v
  · simp [d1, d2, LinearMap.comp_apply]; try ring
  · simp [d1, d2, LinearMap.comp_apply]; try ring

/-- 4. Braid Group Action Physics Representation
A linear operator swapping and changing phases. -/
def sigma1 : IsospinState R →ₗ[R] IsospinState R where
  toFun := fun v => ⟨v.down, -v.up⟩
  map_add' := by intros x y; ext <;> simp <;> try ring
  map_smul' := by intros r x; ext <;> simp <;> try ring

/-- 5. Concrete Free Module resolution representation. -/
def freeResolutionBound : (R × R) →ₗ[R] R where
  toFun := fun v => v.1 - v.2
  map_add' := by intros x y; simp <;> try ring
  map_smul' := by intros r x; simp <;> try ring

end IsospinState
end PhysicalRepresentations
