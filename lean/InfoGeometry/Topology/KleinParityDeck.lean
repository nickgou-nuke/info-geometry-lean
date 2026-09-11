import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A parity-indexed affine Klein deck carrier

The reflection sign is indexed by `ZMod 2`, not reconstructed from an
integer absolute value.  This is the finite algebraic core of the Klein deck
action and is independent of quotient-topology claims.
-/

namespace InfoGeometry.Topology.KleinParityDeck

abbrev Point := ℝ × ZMod 2

def sign (p : ZMod 2) : ℤ := if p = 0 then 1 else -1
def signR (p : ZMod 2) : ℝ := (sign p : ℝ)

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]

theorem sign_add (p q : ZMod 2) : sign (p + q) = sign p * sign q := by
  fin_cases p <;> fin_cases q <;> norm_num [sign] <;> decide

theorem signR_add (p q : ZMod 2) : signR (p + q) = signR p * signR q := by
  unfold signR
  rw [sign_add]
  norm_num

structure Deck where
  translation : ℤ
  parity : ZMod 2

def Deck.mul (g h : Deck) : Deck :=
  ⟨g.translation + sign g.parity * h.translation, g.parity + h.parity⟩

def Deck.one : Deck := ⟨0, 0⟩

theorem Deck.mul_assoc (g h k : Deck) :
    Deck.mul (Deck.mul g h) k = Deck.mul g (Deck.mul h k) := by
  cases g; cases h; cases k
  simp only [Deck.mul]
  rw [sign_add]
  congr 1 <;> ring

theorem Deck.one_mul (g : Deck) : Deck.mul Deck.one g = g := by
  cases g
  simp [Deck.mul, Deck.one, sign]

theorem Deck.mul_one (g : Deck) : Deck.mul g Deck.one = g := by
  cases g
  simp [Deck.mul, Deck.one, sign]

def act (g : Deck) (p : Point) : Point :=
  (signR g.parity * p.1 + g.translation, p.2 + g.parity)

def generatorA : Deck := ⟨1, 0⟩
def generatorB : Deck := ⟨0, 1⟩

theorem generatorA_act (p : Point) : act generatorA p = (p.1 + 1, p.2) := by
  simp [act, generatorA, signR, sign]

theorem generatorB_act (p : Point) : act generatorB p = (-p.1, p.2 + 1) := by
  simp [act, generatorB, signR, sign]

end InfoGeometry.Topology.KleinParityDeck
