import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.AsanoRuelle.TopologicalEndpoint

Exact open target and first algebraic sublemmas for the nondegenerate
Asano-Ruelle topological endpoint step.

No wrappers. No fake closures.
-/

namespace InfoGeometry.AsanoRuelle

/--
Exact open mathematical target for the nondegenerate topological endpoint.
-/
def asanoRuelleTopologicalEndpointClaim
    (K1 K2 : Set ℂ)
    (hK1_closed : IsClosed K1)
    (hK2_closed : IsClosed K2)
    (hK2_bdd : Bornology.IsBounded K2)
    (A B C D z : ℂ)
    (hPhi_zerofree : ∀ z1 z2, z1 ∉ K1 → z2 ∉ K2 → A + B * z1 + C * z2 + D * z1 * z2 ≠ 0)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hQ : A + D * z = 0) : Prop :=
  (C ≠ 0 ∧ (-C / D) ∈ K1) ∨ (B ≠ 0 ∧ (-B / D) ∈ K2)

/--
Algebraic isolation of `z₂` from `Φ = 0`, off the left pole.
-/
theorem asano_isolate_z2
    {K : Type*} [Field K]
    {A B C D z1 z2 : K}
    (hPhi : A + B * z1 + C * z2 + D * z1 * z2 = 0)
    (hPole : C + D * z1 ≠ 0) :
    z2 = - (A + B * z1) / (C + D * z1) := by
  have h1 : (C + D * z1) * z2 = - (A + B * z1) := by
    calc
      (C + D * z1) * z2 = C * z2 + D * z1 * z2 := by ring
      _ = (A + B * z1 + C * z2 + D * z1 * z2) - (A + B * z1) := by ring
      _ = 0 - (A + B * z1) := by rw [hPhi]
      _ = - (A + B * z1) := by ring
  rw [← h1]
  exact (mul_div_cancel_left₀ z2 hPole).symm

/--
Pole-image exclusion: in the nondegenerate branch, the numerator does not
vanish at the left pole.
-/
theorem asano_numerator_ne_zero_at_pole
    {K : Type*} [Field K]
    {A B C D z1 : K}
    (hNondeg : A * D - B * C ≠ 0)
    (hPole : C + D * z1 = 0) :
    A + B * z1 ≠ 0 := by
  intro hNum
  have h_det : A * D - B * C = D * (A + B * z1) - B * (C + D * z1) := by ring
  rw [hNum, hPole, mul_zero, mul_zero, sub_zero] at h_det
  exact hNondeg h_det

/--
Nondegenerate pole exclusion on the zero locus.

If `AD - BC ≠ 0`, a root of
`A + B z₁ + C z₂ + D z₁ z₂ = 0`
cannot occur at the left Möbius pole `C + D z₁ = 0`.
-/
theorem asano_no_root_at_left_pole_of_nondegenerate
    {K : Type*} [Field K]
    {A B C D z1 z2 : K}
    (hNondeg : A * D - B * C ≠ 0)
    (hPole : C + D * z1 = 0)
    (hRoot : A + B * z1 + C * z2 + D * z1 * z2 = 0) :
    False := by
  have hNumNe : A + B * z1 ≠ 0 :=
    asano_numerator_ne_zero_at_pole (A := A) (B := B) (C := C) (D := D) hNondeg hPole
  have hNumEq : A + B * z1 = 0 := by
    have hLin :
        (C + D * z1) * z2 = - (A + B * z1) := by
      calc
        (C + D * z1) * z2 = C * z2 + D * z1 * z2 := by ring
        _ = (A + B * z1 + C * z2 + D * z1 * z2) - (A + B * z1) := by ring
        _ = 0 - (A + B * z1) := by rw [hRoot]
        _ = - (A + B * z1) := by ring
    rw [hPole, zero_mul] at hLin
    have hNeg : -(A + B * z1) = 0 := by simpa using hLin.symm
    exact neg_eq_zero.mp hNeg
  exact hNumNe hNumEq

end InfoGeometry.AsanoRuelle
