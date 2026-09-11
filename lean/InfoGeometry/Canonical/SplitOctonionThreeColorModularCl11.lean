import InfoGeometry.Canonical.ZornVectorMatrixIsomorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

namespace InfoGeometry.Canonical

/-!
# Three coloured modular `Cl(1,1)` atoms in the split octonions

The standard split-octonion coordinate carrier contains one common hyperbolic
axis `⟨1, ℓ⟩` and three coloured pairs `⟨u, ℓu⟩`, for `u = i,j,k`.  This file
proves the concrete multiplication identities for the modular dictionary

```text
ε = ℓ,   Jᵤ = -(ℓu),   Kᵤ = u.
```

The proofs use the executable rational Cayley--Dickson product.  The file
does not install an associative algebra structure on the ambient octonions,
and does not claim that the union of the three slices is associative.
-/

noncomputable section

inductive SplitOctonionColour
  | red | green | blue
deriving DecidableEq, Fintype

open SplitOctonionColour

def colourUnit : SplitOctonionColour → StandardRationalSplitOctonion
  | red => rationalBasis .i
  | green => rationalBasis .j
  | blue => rationalBasis .k

def colourLUnit : SplitOctonionColour → StandardRationalSplitOctonion
  | red => rationalBasis .il
  | green => rationalBasis .jl
  | blue => rationalBasis .kl

def fundamentalSymmetry : StandardRationalSplitOctonion := rationalBasis .l

def modularJ (c : SplitOctonionColour) : StandardRationalSplitOctonion :=
  -(splitOctonionMulQ fundamentalSymmetry (colourUnit c))

def phaseAxis (c : SplitOctonionColour) : StandardRationalSplitOctonion :=
  colourUnit c

def colourPlane (c : SplitOctonionColour) : Set StandardRationalSplitOctonion :=
  {x | ∃ a b : ℚ,
    x = a • colourUnit c + b • colourLUnit c}

def colourSplitQuaternionCore (c : SplitOctonionColour) : Set StandardRationalSplitOctonion :=
  {x | ∃ a b d e : ℚ,
    x = a • rationalBasis .one + b • fundamentalSymmetry +
      d • colourUnit c + e • colourLUnit c}

theorem modularJ_eq_colourLUnit (c : SplitOctonionColour) :
    modularJ c = colourLUnit c := by
  cases c <;> native_decide

@[simp] theorem fundamentalSymmetry_sq :
    splitOctonionMulQ fundamentalSymmetry fundamentalSymmetry =
      rationalBasis .one := by
  native_decide

@[simp] theorem colourUnit_sq (c : SplitOctonionColour) :
    splitOctonionMulQ (colourUnit c) (colourUnit c) =
      -(rationalBasis .one) := by
  cases c <;> native_decide

@[simp] theorem colourLUnit_sq (c : SplitOctonionColour) :
    splitOctonionMulQ (colourLUnit c) (colourLUnit c) =
      rationalBasis .one := by
  cases c <;> native_decide

@[simp] theorem modularJ_sq (c : SplitOctonionColour) :
    splitOctonionMulQ (modularJ c) (modularJ c) =
      rationalBasis .one := by
  cases c <;> native_decide

@[simp] theorem phaseAxis_sq (c : SplitOctonionColour) :
    splitOctonionMulQ (phaseAxis c) (phaseAxis c) =
      -(rationalBasis .one) := by
  exact colourUnit_sq c

theorem modularJ_mul_fundamentalSymmetry (c : SplitOctonionColour) :
    splitOctonionMulQ (modularJ c) fundamentalSymmetry = phaseAxis c := by
  cases c <;> native_decide

theorem fundamentalSymmetry_mul_modularJ (c : SplitOctonionColour) :
    splitOctonionMulQ fundamentalSymmetry (modularJ c) = -(phaseAxis c) := by
  cases c <;> native_decide

theorem modularJ_anticommutes_fundamentalSymmetry
    (c : SplitOctonionColour) :
    splitOctonionMulQ (modularJ c) fundamentalSymmetry =
      -splitOctonionMulQ fundamentalSymmetry (modularJ c) := by
  rw [modularJ_mul_fundamentalSymmetry, fundamentalSymmetry_mul_modularJ]
  simp

theorem phaseAxis_eq_modularJ_mul_fundamentalSymmetry
    (c : SplitOctonionColour) :
    phaseAxis c = splitOctonionMulQ (modularJ c) fundamentalSymmetry := by
  exact (modularJ_mul_fundamentalSymmetry c).symm

theorem colourPlane_eq_span (c : SplitOctonionColour) :
    colourPlane c =
      {x | ∃ a b : ℚ,
        x = a • colourUnit c + b • colourLUnit c} := rfl

theorem colourSplitQuaternionCore_eq_span (c : SplitOctonionColour) :
    colourSplitQuaternionCore c =
      {x | ∃ a b d e : ℚ,
        x = a • rationalBasis .one + b • fundamentalSymmetry +
          d • colourUnit c + e • colourLUnit c} := rfl

theorem colourSplitQuaternionCore_contains_common_axis
    (c : SplitOctonionColour) :
    rationalBasis .one ∈ colourSplitQuaternionCore c ∧
      fundamentalSymmetry ∈ colourSplitQuaternionCore c := by
  constructor
  · exact ⟨1, 0, 0, 0, by simp⟩
  · exact ⟨0, 1, 0, 0, by simp⟩

theorem colourSplitQuaternionCore_contains_colour_plane
    (c : SplitOctonionColour) :
    colourPlane c ⊆ colourSplitQuaternionCore c := by
  intro x hx
  rcases hx with ⟨a, b, rfl⟩
  exact ⟨0, 0, a, b, by simp [add_assoc, add_left_comm, add_comm]⟩

end

end InfoGeometry.Canonical
