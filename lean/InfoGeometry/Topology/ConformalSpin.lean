import Mathlib.Data.Rat.Defs
import Mathlib.Data.Complex.Basic

namespace InfoGeometry.Topology.CFT

/--
In 2D Conformal Field Theory, the conformal spin `S` of a primary field
is defined as the difference between its conformal weights: `S = h - \bar{h}`.
It governs the phase acquired under rotations (single-valuedness condition).
We represent `S` as a rational number to classify fields into
bosons, fermions, and parafermions.
-/
abbrev ConformalSpin := ℚ

namespace ConformalSpin

/-- Compatibility accessor for the native rational carrier. -/
abbrev S (spin : ConformalSpin) : ℚ := spin

end ConformalSpin

/--
A field is bosonic if its conformal spin is an integer.
This implies it is single-valued under a $2\pi$ rotation.
-/
def IsBosonicField (spin : ConformalSpin) : Prop :=
  spin.S.den = 1

/--
A field is fermionic if its conformal spin is a half-integer (e.g., 1/2, 3/2, -1/2).
This implies it acquires a minus sign under a $2\pi$ rotation.
In terms of a rational number `S`, it means `S = n + 1/2` for some integer `n`,
which is equivalent to its denominator in reduced form being exactly 2.
-/
def IsFermionicField (spin : ConformalSpin) : Prop :=
  spin.S.den = 2

/--
A field is parafermionic if its conformal spin is a rational number
that is neither an integer nor a half-integer.
-/
def IsParafermionicField (spin : ConformalSpin) : Prop :=
  spin.S.den > 2

/--
The structure constants $C_{ij}^k$ of the Operator Product Expansion (OPE).
They satisfy properties derived from the single-valuedness condition
(mutual locality). If we have three fields with conformal spins $S_i, S_j, S_k$,
the structure constant $C_{ij}^k$ can only be non-zero if the combination
of their spins allows for single-valuedness of the OPE correlation functions.

For mutually local fields, we require $S_i + S_j - S_k \in \mathbb{Z}$.
-/
structure OPEStructureConstants (I : Type) (spin : I → ConformalSpin) where
  /-- The structure constants $C_{ij}^k \in \mathbb{C}$ -/
  C : I → I → I → ℂ
  /--
  The single-valuedness condition implies that if the structure constant
  is non-zero, the difference in spins must be an integer.
  $C_{ij}^k \neq 0 \implies S_i + S_j - S_k \in \mathbb{Z}$.
  -/
  single_valuedness : ∀ i j k, C i j k ≠ 0 → ((spin i).S + (spin j).S - (spin k).S).den = 1

end InfoGeometry.Topology.CFT
