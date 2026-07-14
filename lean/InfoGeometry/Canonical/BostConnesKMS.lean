import Mathlib
import InfoGeometry.Arithmetic.BostConnesSystem

/-!
# Bost--Connes KMS Projection Evaluation

This module gives a theorem-owned projection-evaluation corridor for
the Bost--Connes KMS state.

The partition sum is identified with `Re ζ(β)` in the convergence domain
`1 < β`.  A full C*-algebraic KMS state is not constructed here.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `S_hom_one`, `S_hom_mul`, `S_one`, `S_mul`, and `S_isometry` re-export the
  proof-carrying multiplicative isometry indexing owner.
* `S_list_prod`, `S_prime_power`, and `S_prime_power_list_prod` expose
  factorization-compatible readbacks for arbitrary multiplicative words and
  explicit prime-power decompositions.
* `kmsProjectionWeight_eq` unfolds the normalized Boltzmann weight
  `n^{-β}/ζβ`.
* `bostConnesPartition_eq_riemannZeta_re` proves the zeta identification.
* `tsum_normalizedBostConnesWeight` proves total normalized mass one.
* `kms_evaluation_on_projections` proves the range-matrix formula
  `φ(S_n S_m^*) = δ_{n,m} n^{-β}/ζβ`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

* `KMSProjectionState` is a projection-state readout whose normalization
  parameter `ζβ` must be supplied by an analytic owner.

#### BUCKET 3: OPEN CLOSURE DEBT

* Lift this projection readout from the algebraic Cuntz-indexed projection
  basis to a genuine C*-KMS state on the completed Bost--Connes algebra.
-/

open scoped BigOperators

noncomputable section

namespace InfoGeometry.Canonical.BostConnesKMS

open InfoGeometry.Arithmetic.BostConnesSystem

/-! ## 1. Proof-carrying multiplicative Cuntz representation -/

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- The proof-carrying Cuntz-indexed Bost--Connes representation. -/
abbrev BostConnesCuntzSystem (Op : Type*) [Ring Op] [StarRing Op] :=
  CuntzMultiplicativeIndexing Op

/--
The positive-integer monoid homomorphism behind the Bost--Connes generators.

This is the formal substrate behind the algebraic rigor claim: because this is
typed as `ℕ+ →* Op`, Lean gets `S 1 = 1` and `S (n * m) = S n * S m` from the
monoid-hom API.
-/
def S_hom (C : BostConnesCuntzSystem Op) : ℕ+ →* Op :=
  C.S

/-- Physical notation for the positive-integer indexed generator `S_n`. -/
def S (C : BostConnesCuntzSystem Op) (n : ℕ+) : Op :=
  S_hom C n

@[simp]
theorem S_hom_one (C : BostConnesCuntzSystem Op) :
    S_hom C 1 = 1 :=
  (S_hom C).map_one

@[simp]
theorem S_hom_mul (C : BostConnesCuntzSystem Op) (n m : ℕ+) :
    S_hom C (n * m) = S_hom C n * S_hom C m :=
  (S_hom C).map_mul n m

/-- Prime generator notation for the Cuntz-indexed Bost--Connes system. -/
def S_prime (C : BostConnesCuntzSystem Op) (p : ℕ) [Fact p.Prime] : Op :=
  S C (MultiplicativeIndexing.primePNat p (Fact.out : p.Prime))

@[simp]
theorem S_one (C : BostConnesCuntzSystem Op) :
    S C 1 = 1 := by
  simp [S]

@[simp]
theorem S_mul (C : BostConnesCuntzSystem Op) (n m : ℕ+) :
    S C (n * m) = S C n * S C m := by
  simp [S]

/-- Each multiplicatively indexed generator is an isometry. -/
theorem S_isometry (C : BostConnesCuntzSystem Op) (n : ℕ+) :
    star (S C n) * S C n = 1 := by
  simpa [S] using C.generator_isometry n

/-- Prime generators are isometries. -/
theorem S_prime_isometry (C : BostConnesCuntzSystem Op)
    (p : ℕ) [Fact p.Prime] :
    star (S_prime C p) * S_prime C p = 1 := by
  simpa [S_prime] using
    S_isometry C (MultiplicativeIndexing.primePNat p (Fact.out : p.Prime))

/--
Ordered multiplicative word readback.

If a positive integer index has been decomposed as a list of factors, its
generator is the ordered product of the corresponding generators.
-/
theorem S_list_prod (C : BostConnesCuntzSystem Op) (l : List ℕ+) :
    S C l.prod = (l.map (S C)).prod := by
  simpa [S, S_hom, CuntzMultiplicativeIndexing.generator] using
    C.toMultiplicativeIndexing.generator_list_prod l

/--
Prime-power readback for a factorization component.

This is the local step used after Mathlib factorization reduces an integer to
prime powers.
-/
theorem S_prime_power (C : BostConnesCuntzSystem Op)
    (p k : ℕ) (hp : Nat.Prime p) :
    S C ((MultiplicativeIndexing.primePNat p hp) ^ k) =
      S C (MultiplicativeIndexing.primePNat p hp) ^ k := by
  simp [S, S_hom]

/-- A single prime-power factor `p^k`, with primality carried explicitly. -/
structure PrimePowerIndex where
  p : ℕ
  hp : Nat.Prime p
  k : ℕ

namespace PrimePowerIndex

/-- The positive integer represented by a prime-power factor. -/
def toPNat (a : PrimePowerIndex) : ℕ+ :=
  (MultiplicativeIndexing.primePNat a.p a.hp) ^ a.k

/-- The generator attached to the underlying prime. -/
def primeGenerator (C : BostConnesCuntzSystem Op) (a : PrimePowerIndex) : Op :=
  S C (MultiplicativeIndexing.primePNat a.p a.hp)

end PrimePowerIndex

/--
Prime-power word readback:

`S_(p₁^k₁ ... pₘ^kₘ) = S_p₁^k₁ ... S_pₘ^kₘ`.

This is the formal Lean blueprint for passing from a prime factorization to the
monoid-hom representation of the Bost--Connes generators.
-/
theorem S_prime_power_list_prod (C : BostConnesCuntzSystem Op)
    (factors : List PrimePowerIndex) :
    S C (factors.map PrimePowerIndex.toPNat).prod =
      (factors.map fun a => (PrimePowerIndex.primeGenerator C a) ^ a.k).prod := by
  induction factors with
  | nil =>
      simp [PrimePowerIndex.primeGenerator]
  | cons a rest ih =>
      simp [PrimePowerIndex.toPNat, PrimePowerIndex.primeGenerator, S_mul,
        S_prime_power, ih]

/-! ## 2. Normalized KMS projection readout -/

/--
The normalized Bost--Connes Boltzmann weight attached to the projection
`S_n S_n^*`.

The parameter `ζβ` is the normalizing partition value.  Analytically, the
intended specialization is `ζβ = ζ(β)`.
-/
def kmsProjectionWeight (β ζβ : ℝ) (n : ℕ+) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-β) / ζβ

@[simp]
theorem kmsProjectionWeight_eq (β ζβ : ℝ) (n : ℕ+) :
    kmsProjectionWeight β ζβ n = ((n : ℕ) : ℝ) ^ (-β) / ζβ :=
  rfl

/-- The convergent Bost--Connes partition sum over positive integers. -/
def bostConnesPartition (β : ℝ) : ℝ :=
  ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ (-β)

/-- The Bost--Connes Boltzmann summand is summable when `1 < β`. -/
theorem summable_bostConnesWeight (β : ℝ) (hβ : 1 < β) :
    Summable (fun n : ℕ+ => ((n : ℕ) : ℝ) ^ (-β)) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-β)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsucc : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-β)) :=
    (summable_nat_add_iff 1).mpr hbase
  rw [← summable_pnat_iff_summable_succ
    (f := fun n : ℕ => (n : ℝ) ^ (-β))] at hsucc
  exact hsucc

/-- In the convergence domain, the real partition sum is `Re ζ(β)`. -/
theorem bostConnesPartition_eq_riemannZeta_re (β : ℝ) (hβ : 1 < β) :
    bostConnesPartition β = (riemannZeta (β : ℂ)).re := by
  have hs : 1 < (β : ℂ).re := by simpa using hβ
  have hsumC : Summable (fun n : ℕ => 1 / (n + 1 : ℂ) ^ (β : ℂ)) := by
    have hbase : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (β : ℂ)) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hbase
  rw [bostConnesPartition]
  change (∑' n : ℕ+, ((n : ℕ) : ℝ) ^ (-β)) = _
  rw [tsum_pnat_eq_tsum_succ
    (f := fun n : ℕ => (n : ℝ) ^ (-β))]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, Complex.re_tsum hsumC]
  apply tsum_congr
  intro n
  have hcast : (n : ℂ) + 1 = (((n + 1 : ℕ) : ℝ) : ℂ) := by norm_num
  rw [hcast, ← Complex.ofReal_cpow
    (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ)) β]
  norm_cast
  rw [one_div, ← Real.rpow_neg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]

/-- The partition function is strictly positive for `1 < β`. -/
theorem bostConnesPartition_pos (β : ℝ) (hβ : 1 < β) :
    0 < bostConnesPartition β := by
  rw [bostConnesPartition_eq_riemannZeta_re β hβ]
  exact riemannZeta_re_pos_of_one_lt hβ

/-- The canonically normalized positive-integer Boltzmann weight. -/
def normalizedBostConnesWeight (β : ℝ) (n : ℕ+) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-β) / bostConnesPartition β

/-- The normalized Boltzmann weights have total mass one for `1 < β`. -/
theorem tsum_normalizedBostConnesWeight (β : ℝ) (hβ : 1 < β) :
    ∑' n : ℕ+, normalizedBostConnesWeight β n = 1 := by
  rw [show (∑' n : ℕ+, normalizedBostConnesWeight β n) =
      (∑' n : ℕ+, ((n : ℕ) : ℝ) ^ (-β)) / bostConnesPartition β by
        simp only [normalizedBostConnesWeight, tsum_div_const]]
  change bostConnesPartition β / bostConnesPartition β = 1
  exact div_self (ne_of_gt (bostConnesPartition_pos β hβ))

/-- Every normalized Bost--Connes weight is strictly positive for `1 < β`. -/
theorem normalizedBostConnesWeight_pos (β : ℝ) (hβ : 1 < β) (n : ℕ+) :
    0 < normalizedBostConnesWeight β n := by
  exact div_pos
    (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) (-β))
    (bostConnesPartition_pos β hβ)

/-- Every normalized Bost--Connes weight is at most one. -/
theorem normalizedBostConnesWeight_le_one (β : ℝ) (hβ : 1 < β) (n : ℕ+) :
    normalizedBostConnesWeight β n ≤ 1 := by
  apply (div_le_one (bostConnesPartition_pos β hβ)).2
  rw [bostConnesPartition]
  exact (summable_bostConnesWeight β hβ).le_tsum n fun m _ =>
    Real.rpow_nonneg (Nat.cast_nonneg m) (-β)

/--
Projection-level KMS readout.

This is not packaged as a global state on all of `Op`; it is the closed
range-matrix formula for `φ(S_n S_m^*)`.
-/
def kmsProjectionReadout (β ζβ : ℝ) (n m : ℕ+) : ℝ :=
  if n = m then kmsProjectionWeight β ζβ n else 0

/-- Diagonal projection readout. -/
@[simp]
theorem kmsProjectionReadout_self (β ζβ : ℝ) (n : ℕ+) :
    kmsProjectionReadout β ζβ n n = ((n : ℕ) : ℝ) ^ (-β) / ζβ := by
  simp [kmsProjectionReadout, kmsProjectionWeight]

/-- Off-diagonal projection readout vanishes. -/
theorem kmsProjectionReadout_ne {β ζβ : ℝ} {n m : ℕ+} (h : n ≠ m) :
    kmsProjectionReadout β ζβ n m = 0 := by
  simp [kmsProjectionReadout, h]

/--
Proof-carrying KMS projection state over a Cuntz-indexed Bost--Connes system.

The field `eval_projection` is the only required data: it states that the
chosen scalar readout evaluates the projection matrix coefficients by the
normalized Boltzmann weight.
-/
structure KMSProjectionState (C : BostConnesCuntzSystem Op) where
  β : ℝ
  ζβ : ℝ
  φ : Op → ℝ
  eval_projection :
    ∀ n m : ℕ+, φ (S C n * star (S C m)) = kmsProjectionReadout β ζβ n m

namespace KMSProjectionState

variable {C : BostConnesCuntzSystem Op}

/--
The documented Bost--Connes KMS projection evaluation:

`φ(S_n S_m^*) = δ_{n,m} · n^{-β} / ζβ`.
-/
theorem kms_evaluation_on_projections
    (Φ : KMSProjectionState C) (n m : ℕ+) :
    Φ.φ (S C n * star (S C m)) =
      if n = m then ((n : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ else 0 := by
  rw [Φ.eval_projection n m]
  by_cases h : n = m
  · simp [kmsProjectionReadout, kmsProjectionWeight, h]
  · simp [kmsProjectionReadout, h]

/-- Diagonal version of `kms_evaluation_on_projections`. -/
theorem kms_evaluation_on_diagonal_projection
    (Φ : KMSProjectionState C) (n : ℕ+) :
    Φ.φ (S C n * star (S C n)) = ((n : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ := by
  simpa using Φ.kms_evaluation_on_projections n n

/-- Off-diagonal version of `kms_evaluation_on_projections`. -/
theorem kms_evaluation_on_off_diagonal_projection
    (Φ : KMSProjectionState C) {n m : ℕ+} (h : n ≠ m) :
    Φ.φ (S C n * star (S C m)) = 0 := by
  simpa [h] using Φ.kms_evaluation_on_projections n m

/--
KMS evaluation after reducing arbitrary indexed words to their multiplicative
positive-integer products.

Callers may first rewrite `S C ns.prod` and `S C ms.prod` using `S_list_prod`;
this theorem then evaluates the resulting matrix coefficient by the same
Kronecker/normalized-Boltzmann formula.
-/
theorem kms_evaluation_on_word_products
    (Φ : KMSProjectionState C) (ns ms : List ℕ+) :
    Φ.φ (S C ns.prod * star (S C ms.prod)) =
      if ns.prod = ms.prod then
        (((ns.prod : ℕ+) : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ
      else 0 := by
  exact Φ.kms_evaluation_on_projections ns.prod ms.prod

end KMSProjectionState

end InfoGeometry.Canonical.BostConnesKMS
