import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Meta.Architecture

noncomputable section

/-!
# InfoGeometry.Clifford.CliffordBott

Direct-limit bridge for the repo-native split Clifford tower.

This file does not construct analytic CAR completions, Type III factors, or the
K-theory Bott periodicity theorem.  It records the kernel-checked algebraic
part already available from the repository's canonical split `Cl(n,n)` tower:

* `Cl_infty` is the Mathlib direct limit of the split Clifford tower;
* the finite head null generator `gammaHeadNullMinus 0` lifts to a square-zero
  element of that direct limit;
* every later representative, including the `8`-step Bott clock subsequence,
  remains square-zero and represents the same limit element;
* the parabolic power law `(1 + rε)^n = 1 + nrε` holds inside the direct limit.
-/

namespace InfoGeometry.Clifford.CliffordBott

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNN

/-- Repo-native infinite split Clifford algebra: the direct limit of `Cl(n,n)`. -/
@[rep_depth krein]
abbrev ClInfty : Type :=
  SplitCliffordInfinity

/-- Compatibility alias for the usual `Cl_∞` notation. -/
@[rep_depth krein]
abbrev Cl_infty : Type :=
  ClInfty

/-- Canonical map from a finite split Clifford stage into the direct limit. -/
@[rep_depth krein]
def ofStage (n : ℕ) : SplitClNNAlg n →+* Cl_infty :=
  DirectLimit.Ring.of SplitClNNAlg (fun m n h => splitCliffordMap m n h) n

@[simp, rep_depth krein]
theorem ofStage_map (m n : ℕ) (h : m ≤ n) (x : SplitClNNAlg m) :
    ofStage n (splitCliffordMap m n h x) = ofStage m x := by
  exact DirectLimit.Ring.of_f (G := SplitClNNAlg)
    (f := fun m n h => splitCliffordMap m n h) h x

@[simp, rep_depth krein]
theorem ofStage_zero (n : ℕ) :
    ofStage n (0 : SplitClNNAlg n) = 0 := by
  exact map_zero (ofStage n)

@[simp, rep_depth krein]
theorem ofStage_one (n : ℕ) :
    ofStage n (1 : SplitClNNAlg n) = 1 := by
  exact map_one (ofStage n)

@[simp, rep_depth krein]
theorem ofStage_mul (n : ℕ) (x y : SplitClNNAlg n) :
    ofStage n (x * y) = ofStage n x * ofStage n y := by
  exact map_mul (ofStage n) x y

@[simp, rep_depth krein]
theorem ofStage_add (n : ℕ) (x y : SplitClNNAlg n) :
    ofStage n (x + y) = ofStage n x + ofStage n y := by
  exact map_add (ofStage n) x y

@[simp, rep_depth krein]
theorem ofStage_smul (n : ℕ) (r : ℝ) (x : SplitClNNAlg n) :
    ofStage n (r • x) = r • ofStage n x := by
  exact (DirectLimit.smul_def (G := SplitClNNAlg)
    (f := fun m n h => splitCliffordMap m n h) n x r).symm

@[simp, rep_depth krein]
theorem ofStage_pow (n k : ℕ) (x : SplitClNNAlg n) :
    ofStage n (x ^ k) = ofStage n x ^ k := by
  exact map_pow (ofStage n) x k

/-- Any finite square-zero element remains square-zero after entering `Cl_infty`. -/
@[rep_depth krein]
theorem ofStage_square_zero {n : ℕ} {x : SplitClNNAlg n} (hx : x * x = 0) :
    ofStage n x * ofStage n x = 0 := by
  rw [← ofStage_mul n x x, hx, ofStage_zero]

/-- The concrete split `Cl(1,1)` head null mode used as the finite nilpotent seed. -/
@[rep_depth krein]
def finiteNilpotentShield : SplitClNNAlg 1 :=
  gammaHeadNullMinus 0

@[simp, rep_depth krein]
theorem finiteNilpotentShield_sq :
    finiteNilpotentShield * finiteNilpotentShield = 0 := by
  simpa [finiteNilpotentShield] using gammaHeadNullMinus_sq 0

/-- The lifted square-zero element of the direct-limit split Clifford algebra. -/
@[rep_depth krein]
def clInfinityNilpotentShield : Cl_infty :=
  ofStage 1 finiteNilpotentShield

@[simp, rep_depth krein]
theorem clInfinityNilpotentShield_sq :
    clInfinityNilpotentShield * clInfinityNilpotentShield = 0 := by
  exact ofStage_square_zero finiteNilpotentShield_sq

/-- Existence form of the lifted nilpotent shield in `Cl_infty`. -/
@[rep_depth krein]
theorem cl_infty_has_nilpotent_lift :
    ∃ ε : Cl_infty, ε * ε = 0 :=
  ⟨clInfinityNilpotentShield, clInfinityNilpotentShield_sq⟩

/--
The seed transported to stage `1 + k`.  This is an algebraic representative in
the finite tower, not a completion-level tensor-product construction.
-/
@[rep_depth krein]
def stableNilpotentShieldStage (k : ℕ) : SplitClNNAlg (1 + k) :=
  splitCliffordMap 1 (1 + k) (Nat.le_add_right 1 k) finiteNilpotentShield

@[simp, rep_depth krein]
theorem stableNilpotentShieldStage_sq (k : ℕ) :
    stableNilpotentShieldStage k * stableNilpotentShieldStage k = 0 := by
  rw [stableNilpotentShieldStage, ← map_mul, finiteNilpotentShield_sq, map_zero]

@[simp, rep_depth krein]
theorem stableNilpotentShieldStage_lifts (k : ℕ) :
    ofStage (1 + k) (stableNilpotentShieldStage k) = clInfinityNilpotentShield := by
  exact ofStage_map 1 (1 + k) (Nat.le_add_right 1 k) finiteNilpotentShield

/-- The same lift sampled along the `8`-step Bott clock subsequence. -/
@[rep_depth krein]
def bottClockNilpotentStage (k : ℕ) : SplitClNNAlg (1 + 8 * k) :=
  splitCliffordMap 1 (1 + 8 * k) (Nat.le_add_right 1 (8 * k)) finiteNilpotentShield

@[simp, rep_depth krein]
theorem bottClockNilpotentStage_sq (k : ℕ) :
    bottClockNilpotentStage k * bottClockNilpotentStage k = 0 := by
  rw [bottClockNilpotentStage, ← map_mul, finiteNilpotentShield_sq, map_zero]

@[simp, rep_depth krein]
theorem bottClockNilpotentStage_lifts (k : ℕ) :
    ofStage (1 + 8 * k) (bottClockNilpotentStage k) = clInfinityNilpotentShield := by
  exact ofStage_map 1 (1 + 8 * k) (Nat.le_add_right 1 (8 * k)) finiteNilpotentShield

@[rep_depth krein]
theorem finiteNilpotentShield_one_add_smul_mul (a b : ℝ) :
    (1 + a • finiteNilpotentShield) * (1 + b • finiteNilpotentShield)
      = 1 + (a + b) • finiteNilpotentShield := by
  rw [mul_add, add_mul, add_mul, one_mul, mul_one]
  rw [smul_mul_smul, finiteNilpotentShield_sq, smul_zero]
  simp [add_smul, add_assoc]

@[rep_depth krein]
theorem finiteNilpotentShield_parabolic_pow (r : ℝ) (n : ℕ) :
    (1 + r • finiteNilpotentShield) ^ n
      = 1 + ((n : ℝ) * r) • finiteNilpotentShield := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih, finiteNilpotentShield_one_add_smul_mul]
      congr 1
      norm_num [Nat.cast_succ]
      ring_nf

/--
The parabolic arithmetic progression now holds inside the direct-limit split
Clifford algebra itself.
-/
@[rep_depth krein]
theorem clInfinity_parabolic_pow (r : ℝ) (n : ℕ) :
    (1 + r • clInfinityNilpotentShield) ^ n
      = 1 + ((n : ℝ) * r) • clInfinityNilpotentShield := by
  have hrepr :
      1 + r • clInfinityNilpotentShield = ofStage 1 (1 + r • finiteNilpotentShield) := by
    have hsmul :
        r • clInfinityNilpotentShield = ofStage 1 (r • finiteNilpotentShield) := by
      simpa [clInfinityNilpotentShield] using
        (ofStage_smul 1 r finiteNilpotentShield).symm
    rw [ofStage_add, ofStage_one, hsmul]
  rw [hrepr, ← ofStage_pow, finiteNilpotentShield_parabolic_pow]
  rw [ofStage_add, ofStage_one, ofStage_smul]
  rfl

end InfoGeometry.Clifford.CliffordBott
