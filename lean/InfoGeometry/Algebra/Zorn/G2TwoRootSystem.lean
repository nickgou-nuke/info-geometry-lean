import InfoGeometry.Algebra.Zorn.G2CyclotomicWeylBridge
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2

namespace InfoGeometry.Algebra.Zorn.G2TwoRootSystem

open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2

/-- Positive roots predicate on the 12 cyclotomic roots (Bool × ZMod 6). -/
def isPosRoot : Root → Bool
  | (false, 0) => true  -- alpha (short simple)
  | (false, 1) => true  -- 2*alpha + beta
  | (false, 2) => true  -- alpha + beta
  | (false, 3) => false -- -alpha
  | (false, 4) => false -- -(2*alpha + beta)
  | (false, 5) => false -- -(alpha + beta)
  | (true, 0) => true   -- beta (long simple)
  | (true, 1) => false  -- -(3*alpha + beta)
  | (true, 2) => false  -- -(3*alpha + 2*beta)
  | (true, 3) => false  -- -beta
  | (true, 4) => true   -- 3*alpha + beta
  | (true, 5) => true   -- 3*alpha + 2*beta

/-- The root negation map sending r to -r. -/
def negRoot (r : Root) : Root :=
  (r.1, r.2 + 3)

theorem negRoot_involutive (r : Root) : negRoot (negRoot r) = r := by
  rcases r with ⟨b, k⟩
  dsimp [negRoot]
  ext
  · rfl
  · fin_cases k <;> rfl

/-- A root is positive if and only if its negation is negative. -/
theorem isPosRoot_neg (r : Root) : isPosRoot (negRoot r) = !isPosRoot r := by
  rcases r with ⟨b, k⟩
  cases b <;> fin_cases k <;> rfl

/-- There are exactly 6 positive roots. -/
theorem posRoots_card :
    (Finset.univ.filter (fun (r : Root) => isPosRoot r = true)).card = 6 := by
  decide

/-- The Weyl action of W(G₂) = ZMod 6 × Bool on the 12 roots. -/
def weylActRoot : (ZMod 6 × Bool) → Root → Root
  | (k, false), (b, x) => (b, x + k)
  | (k, true), (false, x) => (false, 3 - k - x)
  | (k, true), (true, x) => (true, 4 - k - x)

/-- Inversion set of a Weyl element w: the positive roots sent negative by w. -/
def invRoots (w : ZMod 6 × Bool) : Finset Root :=
  Finset.univ.filter (fun r => isPosRoot r = true && isPosRoot (weylActRoot w r) = false)

/-- The Coxeter length of a Weyl element is the cardinality of its inversion set. -/
def coxeterLength (w : ZMod 6 × Bool) : ℕ :=
  (invRoots w).card

/-- Length of identity is 0. -/
theorem coxeterLength_id : coxeterLength (0, false) = 0 := by decide

/-- Length of simple short reflection s is 1. -/
theorem coxeterLength_s : coxeterLength (0, true) = 1 := by decide

/-- Length of simple long reflection t is 1. -/
theorem coxeterLength_t : coxeterLength (1, true) = 1 := by decide

/-- Length of Coxeter element c is 2. -/
theorem coxeterLength_c : coxeterLength (1, false) = 2 := by decide

/-- Length of inverse Coxeter element c⁻¹ is 2. -/
theorem coxeterLength_c_inv : coxeterLength (5, false) = 2 := by decide

/-- Length of longest element w₀ is 6. -/
theorem coxeterLength_w0 : coxeterLength (3, false) = 6 := by decide

/-- THEOREM: The list of lengths of all 12 Weyl elements. -/
theorem weyl_all_lengths :
    ([ (0, false), (0, true), (1, true), (1, false), (5, false),
       (2, true), (5, true), (2, false), (4, false), (3, true),
       (4, true), (3, false) ].map coxeterLength) =
    [0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6] := by decide

/-- THEOREM: The sum of 2^(coxeterLength w) over all 12 Weyl elements is 189. -/
theorem weyl_poincare_sum_at_two :
    ([ (0, false), (0, true), (1, true), (1, false), (5, false),
       (2, true), (5, true), (2, false), (4, false), (3, true),
       (4, true), (3, false) ].map (fun w => 2 ^ coxeterLength w)).sum = 189 := by decide

end InfoGeometry.Algebra.Zorn.G2TwoRootSystem
