import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
import Mathlib.Tactic

set_option maxHeartbeats 2000000

namespace InfoGeometry.Algebra.Zorn.G2TwoOuterGenerators

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer

def g2Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.b ^^ X.x2 ^^ X.y0,
    X.a ^^ X.x2 ^^ X.y0,
    X.a ^^ X.b ^^ X.x1 ^^ X.x2 ^^ X.y2,
    X.x2 ^^ X.y1,
    X.y0,
    X.x2,
    X.x1 ^^ X.y0,
    X.a ^^ X.b ^^ X.x0 ^^ X.x2 ^^ X.y0 ^^ X.y1⟩

def g4Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.x2,
    X.b ^^ X.x2,
    X.x0 ^^ X.y1,
    X.x1 ^^ X.y0,
    X.x2,
    X.y0,
    X.y1,
    X.a ^^ X.b ^^ X.x2 ^^ X.y2⟩

theorem g2Fun_add (X Y : SplitOctF2) :
    g2Fun (add X Y) = add (g2Fun X) (g2Fun Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  ext <;> dsimp [g2Fun, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g4Fun_add (X Y : SplitOctF2) :
    g4Fun (add X Y) = add (g4Fun X) (g4Fun Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  ext <;> dsimp [g4Fun, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g2Fun_one : g2Fun one = one := by
  dsimp [g2Fun, one]
  rfl

theorem g4Fun_one : g4Fun one = one := by
  dsimp [g4Fun, one]
  rfl

theorem g2Fun_involutive (X : SplitOctF2) : g2Fun (g2Fun X) = X := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [g2Fun, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g4Fun_involutive (X : SplitOctF2) : g4Fun (g4Fun X) = X := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [g4Fun, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

lemma F2_mul_two (x : F2) : x * 2 = 0 := by
  fin_cases x <;> rfl

lemma F2_mul_three (x : F2) : x * 3 = x := by
  fin_cases x <;> rfl

lemma F2_mul_four (x : F2) : x * 4 = 0 := by
  fin_cases x <;> rfl

lemma F2_bit_sq (x : Bool) :
    bitToF2 x * bitToF2 x = bitToF2 x := by
  cases x <;> simp [bitToF2]

theorem g2Fun_mul (X Y : SplitOctF2) :
    g2Fun (mul X Y) = mul (g2Fun X) (g2Fun Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  revert a b x0 x1 x2 y0 y1 y2 a' b' x0' x1' x2' y0' y1' y2'
  native_decide

theorem g4Fun_mul (X Y : SplitOctF2) :
    g4Fun (mul X Y) = mul (g4Fun X) (g4Fun Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  revert a b x0 x1 x2 y0 y1 y2 a' b' x0' x1' x2' y0' y1' y2'
  native_decide

def g2Equiv : SplitOctF2 ≃ SplitOctF2 where
  toFun := g2Fun
  invFun := g2Fun
  left_inv := g2Fun_involutive
  right_inv := g2Fun_involutive

def g4Equiv : SplitOctF2 ≃ SplitOctF2 where
  toFun := g4Fun
  invFun := g4Fun
  left_inv := g4Fun_involutive
  right_inv := g4Fun_involutive

def g2Aut : SplitOctF2Aut :=
  ⟨g2Equiv, g2Fun_one, g2Fun_add, g2Fun_mul⟩

def g4Aut : SplitOctF2Aut :=
  ⟨g4Equiv, g4Fun_one, g4Fun_add, g4Fun_mul⟩

theorem g2Aut_sq : g2Aut * g2Aut = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  exact g2Fun_involutive

theorem g4Aut_sq : g4Aut * g4Aut = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  exact g4Fun_involutive

theorem g2Fun_ne_id : g2Fun ≠ id := by
  intro h
  have hx := congrFun h up0
  have hy := congrArg SplitOctF2.y2 hx
  simp [g2Fun, up0] at hy

theorem g4Fun_ne_id : g4Fun ≠ id := by
  intro h
  have hx := congrFun h up2
  have ha := congrArg SplitOctF2.a hx
  simp [g4Fun, up2] at ha

theorem g2Aut_ne_one : g2Aut ≠ (1 : SplitOctF2Aut) := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => f.1) h
  change g2Equiv = Equiv.refl SplitOctF2 at he
  apply g2Fun_ne_id
  funext X
  exact congrArg (fun e : SplitOctF2 ≃ SplitOctF2 => e X) he

theorem g4Aut_ne_one : g4Aut ≠ (1 : SplitOctF2Aut) := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => f.1) h
  change g4Equiv = Equiv.refl SplitOctF2 at he
  apply g4Fun_ne_id
  funext X
  exact congrArg (fun e : SplitOctF2 ≃ SplitOctF2 => e X) he

noncomputable def outerRootSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure {g2Aut, g4Aut}

theorem g2Aut_mem_outerRootSubgroup : g2Aut ∈ outerRootSubgroup := by
  exact Subgroup.subset_closure (by simp)

theorem g4Aut_mem_outerRootSubgroup : g4Aut ∈ outerRootSubgroup := by
  exact Subgroup.subset_closure (by simp)

end InfoGeometry.Algebra.Zorn.G2TwoOuterGenerators
