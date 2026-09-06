import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

set_option linter.unusedSectionVars false

universe u

-- 1. Define the inverse system of finite abelian groups K_0(O_n) ≅ ℤ/(n-1)ℤ
variable (n : ℕ) [Fact (n ≥ 2)]

def K0_On := ZMod (n - 1)

instance : AddCommGroup (K0_On n) := inferInstanceAs (AddCommGroup (ZMod (n - 1)))

-- We define an inverse system over the constant group K0_On n.
def InvSys (G : Type u) [AddCommGroup G] := ℕ → (G →+ G)

-- The transition map from index i+k to index i
def transition_map {G : Type u} [AddCommGroup G] (sys : InvSys G) : ℕ → ℕ → (G →+ G)
| _, 0 => AddMonoidHom.id G
| i, k + 1 => (sys i).comp (transition_map sys (i + 1) k)

-- 2. Formally assert the Mittag-Leffler condition
-- The sequence of images stabilizes
def MittagLeffler {G : Type u} [AddCommGroup G] (sys : InvSys G) : Prop :=
  ∀ i, ∃ K, ∀ k ≥ K, AddMonoidHom.range (transition_map sys i k) = AddMonoidHom.range (transition_map sys i K)

-- For a constant system where all transition maps are the identity,
-- the Mittag-Leffler condition is trivially satisfied.
def constant_sys : InvSys (K0_On n) := fun _ => AddMonoidHom.id _

lemma transition_constant_sys (i k : ℕ) : transition_map (constant_sys n) i k = AddMonoidHom.id (K0_On n) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    change (constant_sys n i).comp (transition_map (constant_sys n) (i + 1) k) = _
    rw [ih (i + 1), constant_sys, AddMonoidHom.id_comp]

theorem mittag_leffler_constant_sys : MittagLeffler (constant_sys n) := by
  intro i
  use 0
  intro k hk
  rw [transition_constant_sys, transition_constant_sys]

-- 3. Prove that the first derived functor (the Milnor topological defect) vanishes
def shift_map {G : Type u} [AddCommGroup G] (sys : InvSys G) : (ℕ → G) →+ (ℕ → G) where
  toFun x := fun i => x i - sys i (x (i + 1))
  map_zero' := by ext i; simp
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, AddMonoidHom.map_add]
    abel

-- A helper to sum the sequence
def partial_sum {G : Type u} [AddCommGroup G] (y : ℕ → G) : ℕ → G
| 0 => 0
| i + 1 => partial_sum y i + y i

lemma partial_sum_diff {G : Type u} [AddCommGroup G] (y : ℕ → G) (i : ℕ) :
  partial_sum y (i + 1) - partial_sum y i = y i := by
  change partial_sum y i + y i - partial_sum y i = y i
  abel

theorem milnor_defect_vanishes_constant : Function.Surjective (shift_map (constant_sys n)) := by
  intro y
  use fun i => - partial_sum y i
  ext i
  simp [shift_map, constant_sys]
  have h := partial_sum_diff y i
  rw [← h]
  abel
