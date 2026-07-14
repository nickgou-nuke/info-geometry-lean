import InfoGeometry.Canonical.FiniteInvariantTransport

/-!
# InfoGeometry.Canonical.FiniteDeterminantTower

Finite determinant-scaling lemmas for tensor-doubling towers.

These lemmas formalize only the finite algebraic engine behind determinant
renormalization:

* if a stage embedding squares a determinant-like multiplicative readout, then
  after `k` steps the readout is raised to `2 ^ k`;
* if a log-determinant-like additive readout doubles at each embedding, then
  after `k` steps it is multiplied by `2 ^ k`;
* consequently the volume-normalized additive readout `L / 2 ^ n` is preserved
  along finite tensor-doubling stages.

No operator-algebraic completion or infinite-dimensional determinant theorem is
asserted here.
-/

namespace FiniteDeterminantTower

open InfoGeometry.Canonical.FiniteInvariantTransport

/--
If each finite bonding map squares a determinant-like readout, then after `k`
tensor-doubling steps the readout is raised to the power `2 ^ k`.
-/
theorem determinant_square_along_chain
    {A M : Type*} [Monoid M]
    (next : Nat → A → A) (D : A → M)
    (hD : ∀ n x, D (next n x) = D x * D x)
    (n k : Nat) (x : A) :
    D (chainApply next n k x) = D x ^ (2 ^ k) := by
  induction k with
  | zero =>
      simp [chainApply]
  | succ k ih =>
      calc
        D (chainApply next n (k + 1) x)
            = D (next (n + k) (chainApply next n k x)) := by
                rfl
        _ = D (chainApply next n k x) * D (chainApply next n k x) := by
                rw [hD]
        _ = D x ^ (2 ^ k) * D x ^ (2 ^ k) := by
                rw [ih]
        _ = D x ^ (2 ^ (k + 1)) := by
                rw [← pow_add]
                congr 1
                omega

/--
If each finite bonding map doubles a log-determinant-like additive readout, then
after `k` tensor-doubling steps the readout is multiplied by `2 ^ k`.
-/
theorem logDet_double_along_chain
    {A : Type*}
    (next : Nat → A → A) (L : A → ℝ)
    (hL : ∀ n x, L (next n x) = 2 * L x)
    (n k : Nat) (x : A) :
    L (chainApply next n k x) = (2 ^ k : ℝ) * L x := by
  induction k with
  | zero =>
      simp [chainApply]
  | succ k ih =>
      calc
        L (chainApply next n (k + 1) x)
            = L (next (n + k) (chainApply next n k x)) := by
                rfl
        _ = 2 * L (chainApply next n k x) := by
                rw [hL]
        _ = 2 * ((2 ^ k : ℝ) * L x) := by
                rw [ih]
        _ = (2 ^ (k + 1) : ℝ) * L x := by
                norm_num [pow_succ]
                ring

/--
The volume-normalized additive readout `L / 2 ^ n` is invariant under finite
stage-doubling embeddings when the unnormalized readout doubles at each step.
-/
theorem normalized_logDet_invariant_along_chain
    {A : Type*}
    (next : Nat → A → A) (L : A → ℝ)
    (hL : ∀ n x, L (next n x) = 2 * L x)
    (n k : Nat) (x : A) :
    L (chainApply next n k x) / (2 ^ (n + k) : ℝ) = L x / (2 ^ n : ℝ) := by
  rw [logDet_double_along_chain next L hL n k x]
  have hpow_ne : (2 ^ n : ℝ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpowk_ne : (2 ^ k : ℝ) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [pow_add]
  field_simp [hpow_ne, hpowk_ne]

end FiniteDeterminantTower
