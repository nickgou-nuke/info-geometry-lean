import InfoGeometry.MassSpectrometry.FiniteFragmentAbsorption
import InfoGeometry.SignedNetwork.RankedDAGResolvent

/-!
# Finite Green response of a terminating fragmentation model

Reuses `SignedNetwork.RankedDAGResolvent.finiteGreen` and its two inverse laws.
No duplicate inverse predicate, infinite series, or analytic hitting-time
expectation is introduced. The row potential is a finite algebraic quantity.
-/

noncomputable section
namespace InfoGeometry.MassSpectrometry
open scoped BigOperators Matrix
open InfoGeometry.SignedNetwork.RankedDAGResolvent

namespace FiniteGreenResponse
variable {A : Type*} [Ring A]

/-- Different valid truncation horizons give the same inverse. -/
theorem horizon_independent (K : A) (N M : ℕ) (hN : K ^ N = 0) (hM : K ^ M = 0) :
    finiteGreen K N = finiteGreen K M := by
  calc
    finiteGreen K N = finiteGreen K N * ((1 - K) * finiteGreen K M) := by
      rw [finiteGreen_left_inverse K M hM, mul_one]
    _ = (finiteGreen K N * (1 - K)) * finiteGreen K M := (mul_assoc _ _ _).symm
    _ = finiteGreen K M := by rw [finiteGreen_right_inverse K N hN, one_mul]

/-- Finite resolvent identity; no commutation between K and L is assumed. -/
theorem resolvent_identity (K L : A) (N M : ℕ) (hK : K ^ N = 0) (hL : L ^ M = 0) :
    finiteGreen K N - finiteGreen L M =
      finiteGreen K N * (K - L) * finiteGreen L M := by
  have hd : K - L = (1 - L) - (1 - K) := by abel
  rw [hd, mul_sub, sub_mul, mul_assoc, finiteGreen_left_inverse L M hL,
    mul_one, finiteGreen_right_inverse K N hK, one_mul]

/-- The inverse is realized as a native unit, not merely an invertibility field. -/
def oneSubUnit (K : A) (N : ℕ) (hK : K ^ N = 0) : Aˣ where
  val := 1 - K
  inv := finiteGreen K N
  val_inv := finiteGreen_left_inverse K N hK
  inv_val := finiteGreen_right_inverse K N hK

/-- A left-recursive form of the same finite sum. -/
theorem finiteGreen_succ_left (K : A) (N : ℕ) :
    finiteGreen K (N + 1) = 1 + K * finiteGreen K N := by
  induction N with
  | zero => simp [finiteGreen]
  | succ N ih =>
      rw [finiteGreen_succ, ih, finiteGreen_succ, mul_add, ← pow_succ']
      abel

end FiniteGreenResponse

namespace StochasticGrammar
variable {n : ℕ} {D : FragmentationDAG n}

/-- Exact finite fundamental matrix at the explicit rank horizon. -/
def fundamentalMatrix (G : StochasticGrammar D) : Matrix (Fin n) (Fin n) ℝ :=
  finiteGreen G.transientMatrix (InfoGeometry.Algebra.RankedMatrixPowers.rankHorizon D.rank)

theorem fundamentalMatrix_left_inverse (G : StochasticGrammar D) :
    (1 - G.transientMatrix) * G.fundamentalMatrix = 1 :=
  finiteGreen_left_inverse _ _ G.transient_pow_rankHorizon_eq_zero

theorem fundamentalMatrix_right_inverse (G : StochasticGrammar D) :
    G.fundamentalMatrix * (1 - G.transientMatrix) = 1 :=
  finiteGreen_right_inverse _ _ G.transient_pow_rankHorizon_eq_zero

/-- The transient equation has exactly this solution for every reward/readout. -/
theorem response_unique (G : StochasticGrammar D) (g x : Fin n → ℝ) :
    (1 - G.transientMatrix) *ᵥ x = g ↔ x = G.fundamentalMatrix *ᵥ g := by
  constructor
  · intro hx
    calc
      x = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x := (Matrix.one_mulVec x).symm
      _ = (G.fundamentalMatrix * (1 - G.transientMatrix)) *ᵥ x := by
        rw [G.fundamentalMatrix_right_inverse]
      _ = G.fundamentalMatrix *ᵥ ((1 - G.transientMatrix) *ᵥ x) :=
        (Matrix.mulVec_mulVec x _ _).symm
      _ = G.fundamentalMatrix *ᵥ g := by rw [hx]
  · intro hx
    rw [hx, Matrix.mulVec_mulVec, G.fundamentalMatrix_left_inverse, Matrix.one_mulVec]

theorem response_fixedPoint (G : StochasticGrammar D) (g : Fin n → ℝ) :
    G.fundamentalMatrix *ᵥ g = g + G.transientMatrix *ᵥ (G.fundamentalMatrix *ᵥ g) := by
  have h := (G.response_unique g (G.fundamentalMatrix *ᵥ g)).mpr rfl
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h
  exact sub_eq_iff_eq_add.mp h

theorem transient_pow_nonneg (G : StochasticGrammar D) (k : ℕ) :
    ∀ u v, 0 ≤ (G.transientMatrix ^ k) u v := by
  induction k with
  | zero => intro u v; simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
      intro u v
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun w _ => mul_nonneg (ih u w) (G.weight_nonneg w v))

theorem transient_pow_row_sum_le_one (G : StochasticGrammar D) (k : ℕ) :
    ∀ u, ∑ v, (G.transientMatrix ^ k) u v ≤ 1 := by
  induction k with
  | zero => intro u; simp [Matrix.one_apply]
  | succ k ih =>
      intro u
      calc
        ∑ v, (G.transientMatrix ^ (k + 1)) u v =
            ∑ w, (G.transientMatrix ^ k) u w * (∑ v, G.weight w v) := by
          simp only [pow_succ, Matrix.mul_apply]
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum, transientMatrix]
        _ ≤ ∑ w, (G.transientMatrix ^ k) u w * 1 := by
          exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left
            (G.row_sum_le_one w) (G.transient_pow_nonneg k u w))
        _ ≤ 1 := by simpa using ih u

theorem finiteGreen_nonneg (G : StochasticGrammar D) (N : ℕ) (u v : Fin n) :
    0 ≤ finiteGreen G.transientMatrix N u v := by
  simp only [finiteGreen, Finset.sum_apply]
  exact Finset.sum_nonneg (fun k _ => G.transient_pow_nonneg k u v)

theorem finiteGreen_row_sum_le (G : StochasticGrammar D) (N : ℕ) (u : Fin n) :
    ∑ v, finiteGreen G.transientMatrix N u v ≤ (N : ℝ) := by
  calc
    ∑ v, finiteGreen G.transientMatrix N u v =
        ∑ k ∈ Finset.range N, ∑ v, (G.transientMatrix ^ k) u v := by
      simp only [finiteGreen, Finset.sum_apply]
      exact Finset.sum_comm
    _ ≤ ∑ _k ∈ Finset.range N, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun k _ => G.transient_pow_row_sum_le_one k u)
    _ = (N : ℝ) := by simp

/-- Finite occupancy potential; a probabilistic expectation needs a path-law model. -/
def occupancyPotential (G : StochasticGrammar D) : Fin n → ℝ :=
  G.fundamentalMatrix *ᵥ (fun _ => 1)

theorem occupancyPotential_equation (G : StochasticGrammar D) :
    G.occupancyPotential = (fun _ => 1) + G.transientMatrix *ᵥ G.occupancyPotential :=
  G.response_fixedPoint _

end StochasticGrammar
end InfoGeometry.MassSpectrometry
