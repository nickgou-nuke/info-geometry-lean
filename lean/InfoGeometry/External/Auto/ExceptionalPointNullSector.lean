import Mathlib.Tactic

noncomputable section

open Complex

namespace InfoGeometry.GrandUnification.ExceptionalPoints

/-- Non-Hermitian operator in a complex Hilbert space. -/
structure NonHermitianOperator
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  T : H →L[ℂ] H
  is_non_hermitian : T ≠ T.adjoint

/-- Shifted operator at spectral point `z`: `T - zI`. -/
def shiftAt (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) : H →ₗ[ℂ] H :=
  (op.T - z • ContinuousLinearMap.id ℂ H).toLinearMap

/-- Local exceptional-point criterion via generalized kernels of powers of the shifted map. -/
def IsExceptionalPoint
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) : Prop :=
  ∃ k : ℕ, 1 < k ∧
    LinearMap.ker (shiftAt H op z ^ k) ≠ LinearMap.ker (shiftAt H op z) ∧
    LinearMap.ker (shiftAt H op z ^ k) = LinearMap.ker (shiftAt H op z ^ (k + 1))

/-- At an exceptional point, the first generalized kernel strictly differs from the ordinary kernel:
there exists a generalized defect vector killed by `(T-zI)^k` but not by `T-zI`. -/
lemma exceptional_has_generalized_defect_vector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (hep : IsExceptionalPoint H op z) :
    ∃ k : ℕ, 1 < k ∧
      ∃ v : H,
        (shiftAt H op z ^ k) v = 0 ∧ (shiftAt H op z) v ≠ 0 := by
  rcases hep with ⟨k, hk, hneq, _hstabilize⟩
  have hmono : LinearMap.ker (shiftAt H op z) ≤ LinearMap.ker (shiftAt H op z ^ k) := by
    have hk0 : (0 : ℕ) < k := lt_trans (show (0 : ℕ) < 1 by decide) hk
    have hmono0 :
        LinearMap.iterateKer (shiftAt H op z) 1 ≤ LinearMap.iterateKer (shiftAt H op z) k :=
      OrderHom.monotone (LinearMap.iterateKer (shiftAt H op z)) (Nat.succ_le_of_lt hk0)
    simpa [LinearMap.iterateKer, pow_one] using hmono0
  have hlt : LinearMap.ker (shiftAt H op z) < LinearMap.ker (shiftAt H op z ^ k) :=
    lt_of_le_of_ne hmono hneq.symm
  rcases SetLike.exists_of_lt hlt with ⟨v, hvk, hv1⟩
  refine ⟨k, hk, v, ?_, ?_⟩
  · exact LinearMap.mem_ker.mp hvk
  · intro hv
    exact hv1 (by simpa [LinearMap.mem_ker] using hv)

/-- Abstract bridge: if the exceptional generalized-kernel sector is exactly the range of `P_zero`
(and every vector in the shifted image lies in this sector), then all shifted vectors are
`P_zero`-localized. -/
theorem exceptional_points_in_null_sector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (_hep : IsExceptionalPoint H op z)
    (P_zero : H →L[ℂ] H) (_hproj : P_zero * P_zero = P_zero)
    (hk : ∃ k : ℕ, 1 < k ∧
      LinearMap.range (shiftAt H op z) ≤ LinearMap.ker (shiftAt H op z ^ k) ∧
      LinearMap.ker (shiftAt H op z ^ k) = LinearMap.range (P_zero.toLinearMap)) :
    LinearMap.range (shiftAt H op z) ≤ LinearMap.range (P_zero.toLinearMap) := by
  rcases hk with ⟨k, _hk, hrange, hkerEq⟩
  intro y hy
  exact hkerEq ▸ hrange hy

/-- The projector equation implies `P_zero` fixes points in its range. -/
theorem exceptional_projection_identity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P_zero : H →L[ℂ] H) (hproj : P_zero * P_zero = P_zero) :
    ∀ x : H, x ∈ LinearMap.range (P_zero.toLinearMap) → P_zero x = x := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  change P_zero (P_zero y) = P_zero y
  simpa [ContinuousLinearMap.mul_apply] using congrArg (fun f : H →L[ℂ] H => f y) hproj

/-- Repackaged conclusion for the next EP step. -/
theorem exceptional_shift_image_stays_in_null_projector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (op : NonHermitianOperator H) (z : ℂ) (hep : IsExceptionalPoint H op z)
    (P_zero : H →L[ℂ] H) (hproj : P_zero * P_zero = P_zero)
    (hNull : ∃ k : ℕ, 1 < k ∧
      LinearMap.range (shiftAt H op z) ≤ LinearMap.ker (shiftAt H op z ^ k) ∧
      LinearMap.ker (shiftAt H op z ^ k) = LinearMap.range (P_zero.toLinearMap)) :
    LinearMap.range (shiftAt H op z) ≤ LinearMap.range (P_zero.toLinearMap) := by
  exact exceptional_points_in_null_sector (H := H) (op := op) (z := z) (_hep := hep)
    (P_zero := P_zero) (_hproj := hproj) (hk := hNull)

end InfoGeometry.GrandUnification.ExceptionalPoints
