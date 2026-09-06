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

/-- Scalar part readout through the faithful native spinor matrix model. -/
def scalarTrace55 (x : Cl55) : ℝ :=
  Matrix.trace (cl55SpinorAlgEquiv x)

/-- Bilinear readout of two Clifford states. -/
def cliffordAttentionBilinear (q k : Cl55) : ℝ :=
  scalarTrace55 (q * k)

/-- Position-rotated query state on one elliptic Clifford plane. -/
def rotatedQuery55 (i : Fin 5) (theta m : ℝ) (q : Cl55) : Cl55 :=
  ropeRotor55 i (m * theta) * q

/-- Position-rotated key state using the inverse rotor on the right.

This convention is chosen so that the bilinear product isolates the relative
rotor between the two positions. -/
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

/-- A typed query/key embedding packet.  No neural-network semantics are
assumed beyond the supplied linear maps into the native Clifford carrier. -/
structure AttentionEmbeddingDatum (X : Type*) [AddCommGroup X] [Module ℝ X] where
  WQ : X →ₗ[ℝ] Cl55
  WK : X →ₗ[ℝ] Cl55

/-- Relative-position attention readout after arbitrary supplied linear query
and key embeddings. -/
theorem embeddedAttention_relative_position
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (D : AttentionEmbeddingDatum X)
    (i : Fin 5) (theta m n : ℝ) (xm xn : X) :
    cliffordAttentionBilinear
        (D.WQ xm * ropeRotor55 i (-(m * theta)))
        (ropeRotor55 i (n * theta) * D.WK xn) =
      scalarTrace55
        (D.WQ xm * ropeRotor55 i ((n - m) * theta) * D.WK xn) := by
  exact cliffordAttention_relative_position i theta m n (D.WQ xm) (D.WK xn)

end

end InfoGeometry.Clifford.Clifford55
