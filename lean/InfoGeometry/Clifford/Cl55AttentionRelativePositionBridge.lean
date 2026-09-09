import Mathlib
import InfoGeometry.Clifford.Cl55RoPESplitTorusBridge

/-!
# Relative-position bilinear for native `Cl(5,5)` RoPE rotors

This owner proves the exact algebraic mechanism used by rotary relative-position
readouts on one native Clifford plane.  It does not claim that every Transformer
attention implementation is represented by this carrier.
-/

namespace InfoGeometry.Clifford.Clifford55

open Matrix
open InfoGeometry.Clifford.Cl55RoPESplitTorusBridge

noncomputable section

/-- Unnormalized trace readout through the faithful native spinor matrix model. -/
def scalarTrace55 (x : Cl55) : ℝ :=
  Matrix.trace (cl55SpinorAlgEquiv x)

/-- Cyclicity of the trace transported through the native algebra equivalence. -/
theorem scalarTrace55_mul_comm (x y : Cl55) :
    scalarTrace55 (x * y) = scalarTrace55 (y * x) := by
  simp only [scalarTrace55, map_mul]
  exact Matrix.trace_mul_comm _ _

/-- Bilinear readout of two Clifford states. -/
def cliffordAttentionBilinear (q k : Cl55) : ℝ :=
  scalarTrace55 (q * k)

/-- Position-rotated query state on one elliptic Clifford plane. -/
def rotatedQuery55 (i : Fin 5) (theta m : ℝ) (q : Cl55) : Cl55 :=
  ropeRotor55 i (m * theta) * q

/-- Position-rotated key state using the inverse rotor on the right.

Trace cyclicity combines these outer rotors into the relative angle `m - n`.
The untraced product does not in general have this simplification. -/
def rotatedKey55 (i : Fin 5) (theta n : ℝ) (k : Cl55) : Cl55 :=
  k * ropeRotor55 i (-(n * theta))

/-- Exact relative-rotor product inside the native Clifford algebra. -/
theorem relative_rotor55
    (i : Fin 5) (theta m n : ℝ) :
    ropeRotor55 i (-(m * theta)) * ropeRotor55 i (n * theta) =
      ropeRotor55 i ((n - m) * theta) := by
  rw [ropeRotor55_add]
  congr
  ring

/-- The defined left-query/right-key actions depend only on the position
difference after taking the trace; the order of `q * k` is preserved. -/
theorem rotatedAttention_relative_position
    (i : Fin 5) (theta m n : ℝ) (q k : Cl55) :
    cliffordAttentionBilinear (rotatedQuery55 i theta m q)
        (rotatedKey55 i theta n k) =
      scalarTrace55 (ropeRotor55 i ((m - n) * theta) * (q * k)) := by
  unfold cliffordAttentionBilinear rotatedQuery55 rotatedKey55
  rw [← mul_assoc, scalarTrace55_mul_comm
    (ropeRotor55 i (m * theta) * q * k) (ropeRotor55 i (-(n * theta)))]
  simp only [mul_assoc]
  rw [← mul_assoc (ropeRotor55 i (-(n * theta)))
    (ropeRotor55 i (m * theta)), relative_rotor55]

/-- Relative-position form for a left/right transported product.

The only structural hypothesis is the explicit insertion of the inverse rotor
between the unrotated query and key channels. -/
theorem clifford_relative_position_product
    (i : Fin 5) (theta m n : ℝ) (q k : Cl55) :
    (q * ropeRotor55 i (-(m * theta))) *
        (ropeRotor55 i (n * theta) * k) =
      q * ropeRotor55 i ((n - m) * theta) * k := by
  calc
    (q * ropeRotor55 i (-(m * theta))) *
        (ropeRotor55 i (n * theta) * k) =
      q * (ropeRotor55 i (-(m * theta)) *
        ropeRotor55 i (n * theta)) * k := by
      simp only [mul_assoc]
    _ = q * ropeRotor55 i ((n - m) * theta) * k := by
      rw [relative_rotor55]

/-- Scalar bilinear readout depends on the relative rotor once the query/key
channels are transported by the native inverse/forward RoPE actions. -/
theorem cliffordAttention_relative_position
    (i : Fin 5) (theta m n : ℝ) (q k : Cl55) :
    cliffordAttentionBilinear
        (q * ropeRotor55 i (-(m * theta)))
        (ropeRotor55 i (n * theta) * k) =
      scalarTrace55 (q * ropeRotor55 i ((n - m) * theta) * k) := by
  unfold cliffordAttentionBilinear
  rw [clifford_relative_position_product]

end

end InfoGeometry.Clifford.Clifford55
