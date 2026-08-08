import InfoGeometry.Canonical.FiniteFibonacciComputationalSpace

/-!
# InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks

Finite four-Fibonacci-anyon conformal-block interface.

The analytic paper derives two four-point Fibonacci conformal blocks and shows
that the neighboring exchanges `b₁` and `b₃` are diagonal in that basis, with
channel phases `q⁻⁴` and `q³`.  This file formalizes only that finite algebraic
interface:

* two four-anyon channels, matching the one-qubit computational basis;
* symbolic `R` phases `q⁻⁴` and `q³` for the two channels;
* diagonal `b₁`/`b₃` actions preserve the channel label;
* an abstract middle generator `b₂` can be plugged in, with Artin-rewrite
  invariance stated only from explicit pointwise hypotheses.

No hypergeometric functions.
No analytic continuation theorem.
No CFT correlator construction.
No concrete non-diagonal `B` matrix.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks

open FiniteFibonacciComputationalSpace

/-- The two fusion/conformal-block channels for four Fibonacci anyons. -/
inductive FourAnyonChannel where
  /-- Vacuum channel, corresponding to the computational vector `|0⟩`. -/
  | vacuum
  /-- Fibonacci channel, corresponding to the computational vector `|1⟩`. -/
  | fib
  deriving DecidableEq, Repr, Fintype

namespace FourAnyonChannel

/-- Convert a Boolean qubit bit to the corresponding four-anyon channel. -/
def ofBool : Bool → FourAnyonChannel
  | false => vacuum
  | true => fib

/-- Convert a four-anyon channel to the corresponding Boolean qubit bit. -/
def toBool : FourAnyonChannel → Bool
  | vacuum => false
  | fib => true

@[simp]
theorem toBool_ofBool (b : Bool) :
    toBool (ofBool b) = b := by
  cases b <;> rfl

@[simp]
theorem ofBool_toBool (c : FourAnyonChannel) :
    ofBool (toBool c) = c := by
  cases c <;> rfl

end FourAnyonChannel

/-- The four-anyon channel basis is equivalent to the one-qubit computational basis. -/
def oneQubitEquivFourAnyonChannel : ComputationalVector 1 ≃ FourAnyonChannel where
  toFun α := FourAnyonChannel.ofBool (α 0)
  invFun c := fun _ => FourAnyonChannel.toBool c
  left_inv α := by
    funext i
    fin_cases i
    simp
  right_inv c := by
    simp

/-- There are exactly two four-anyon channels. -/
theorem card_fourAnyonChannel :
    Fintype.card FourAnyonChannel = 2 := by
  rw [← Fintype.card_congr oneQubitEquivFourAnyonChannel]
  norm_num [ComputationalVector]

/-- The diagonal `R`-matrix exponent in the four-anyon channel basis. -/
def rExponent : FourAnyonChannel → ℤ
  | FourAnyonChannel.vacuum => -4
  | FourAnyonChannel.fib => 3

@[simp]
theorem rExponent_vacuum :
    rExponent FourAnyonChannel.vacuum = -4 :=
  rfl

@[simp]
theorem rExponent_fib :
    rExponent FourAnyonChannel.fib = 3 :=
  rfl

/-- The symbolic diagonal `R` phase, parameterized by a primitive phase `q`. -/
def rPhase (q : Units ℂ) (c : FourAnyonChannel) : Units ℂ :=
  q ^ rExponent c

@[simp]
theorem rPhase_vacuum (q : Units ℂ) :
    rPhase q FourAnyonChannel.vacuum = q ^ (-4 : ℤ) :=
  rfl

@[simp]
theorem rPhase_fib (q : Units ℂ) :
    rPhase q FourAnyonChannel.fib = q ^ (3 : ℤ) :=
  rfl

/-- A phased four-anyon basis vector: scalar phase together with a channel label. -/
abbrev PhasedFourAnyonBlock := Units ℂ × FourAnyonChannel

/-- Diagonal action of `b₁` or `b₃` in the four-anyon channel basis. -/
def diagonalRAction (q : Units ℂ) : PhasedFourAnyonBlock → PhasedFourAnyonBlock :=
  fun v => (rPhase q v.2 * v.1, v.2)

/-- The diagonal `R` action preserves the four-anyon channel label. -/
theorem diagonalRAction_channel (q : Units ℂ) (v : PhasedFourAnyonBlock) :
    (diagonalRAction q v).2 = v.2 :=
  rfl

/-- On the vacuum channel the diagonal action multiplies by `q⁻⁴`. -/
theorem diagonalRAction_vacuum (q phase : Units ℂ) :
    diagonalRAction q (phase, FourAnyonChannel.vacuum) =
      (q ^ (-4 : ℤ) * phase, FourAnyonChannel.vacuum) :=
  rfl

/-- On the Fibonacci channel the diagonal action multiplies by `q³`. -/
theorem diagonalRAction_fib (q phase : Units ℂ) :
    diagonalRAction q (phase, FourAnyonChannel.fib) =
      (q ^ (3 : ℤ) * phase, FourAnyonChannel.fib) :=
  rfl

/-- A finite four-anyon braid generator readout with abstract middle generator `b₂`. -/
def fourAnyonGeneratorAction (q : Units ℂ)
    (middle : PhasedFourAnyonBlock → PhasedFourAnyonBlock) :
    Fin 3 → PhasedFourAnyonBlock → PhasedFourAnyonBlock
  | ⟨0, _⟩ => diagonalRAction q
  | ⟨1, _⟩ => middle
  | ⟨2, _⟩ => diagonalRAction q

/-- The first and third neighboring generators have the same diagonal channel action. -/
theorem fourAnyonGeneratorAction_first_eq_last (q : Units ℂ)
    (middle : PhasedFourAnyonBlock → PhasedFourAnyonBlock) :
    fourAnyonGeneratorAction q middle ⟨0, by norm_num⟩ =
      fourAnyonGeneratorAction q middle ⟨2, by norm_num⟩ :=
  rfl

/-- The first generator preserves channel labels. -/
theorem fourAnyonGeneratorAction_first_channel (q : Units ℂ)
    (middle : PhasedFourAnyonBlock → PhasedFourAnyonBlock)
    (v : PhasedFourAnyonBlock) :
    (fourAnyonGeneratorAction q middle ⟨0, by norm_num⟩ v).2 = v.2 :=
  rfl

/-- The third generator preserves channel labels. -/
theorem fourAnyonGeneratorAction_last_channel (q : Units ℂ)
    (middle : PhasedFourAnyonBlock → PhasedFourAnyonBlock)
    (v : PhasedFourAnyonBlock) :
    (fourAnyonGeneratorAction q middle ⟨2, by norm_num⟩ v).2 = v.2 :=
  rfl

/--
Finite `B₄` adjacent Artin relation for `b₁ b₂ b₁ = b₂ b₁ b₂`, under the
explicit pointwise property for the supplied middle action.
-/
theorem fourAnyon_first_middle_first_rewrite (q : Units ℂ)
    (middle : PhasedFourAnyonBlock → PhasedFourAnyonBlock)
    (h : ∀ v,
      diagonalRAction q (middle (diagonalRAction q v)) =
        middle (diagonalRAction q (middle v)))
    (v : PhasedFourAnyonBlock) :
    diagonalRAction q (middle (diagonalRAction q v)) =
      middle (diagonalRAction q (middle v)) :=
  h v

/--
Finite `B₄` adjacent Artin relation for `b₂ b₃ b₂ = b₃ b₂ b₃`, under the
explicit pointwise property for the supplied middle action.
-/
theorem fourAnyon_middle_last_middle_rewrite (q : Units ℂ)
    (middle : PhasedFourAnyonBlock → PhasedFourAnyonBlock)
    (h : ∀ v,
      middle (diagonalRAction q (middle v)) =
        diagonalRAction q (middle (diagonalRAction q v)))
    (v : PhasedFourAnyonBlock) :
    middle (diagonalRAction q (middle v)) =
      diagonalRAction q (middle (diagonalRAction q v)) :=
  h v

end InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks
