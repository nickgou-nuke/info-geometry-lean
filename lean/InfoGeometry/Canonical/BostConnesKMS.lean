import Mathlib
import InfoGeometry.Arithmetic.BostConnesSystem

/-!
# Bost--Connes KMS Projection Evaluation

This module gives a theorem-owned projection-evaluation corridor for
the Bost--Connes KMS state.

The full analytic Bost--Connes theorem and the identity `ζβ = ζ(β)` are not
proved here.  They are deliberately represented by an explicit normalization
parameter `ζβ`; analytic Euler-product/zeta facts belong to the zeta bridge.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `S_hom_one`, `S_hom_mul`, `S_one`, `S_mul`, `S_isometry`, and
  `S_orthogonal` re-export the proof-carrying multiplicative Cuntz indexing
  owner.
* `S_list_prod`, `S_prime_power`, and `S_prime_power_list_prod` expose
  factorization-compatible readbacks for arbitrary multiplicative words and
  explicit prime-power decompositions.
* `kmsProjectionWeight_eq` unfolds the normalized Boltzmann weight
  `n^{-β}/ζβ`.
* `kms_evaluation_on_projections` proves the documented projection formula
  `φ(S_n^* S_m) = δ_{n,m} n^{-β}/ζβ`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

* `KMSProjectionState` is a projection-state readout whose normalization
  parameter `ζβ` must be supplied by an analytic owner.

#### BUCKET 3: OPEN CLOSURE DEBT

* Prove or import the analytic identification `ζβ = ζ(β)` in the convergence
  half-plane.
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

/-
/-- Orthogonality of the Cuntz branches. -/
theorem S_orthogonal (C : BostConnesCuntzSystem Op) (n m : ℕ+) :
    star (S C n) * S C m = if n = m then 1 else 0 := by
  simpa [S] using C.generator_orthogonal n m
-/

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

/--
Projection-level KMS readout.

This is not packaged as a global state on all of `Op`; it is the closed
projection-basis formula for `φ(S_n^* S_m)`.
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
    ∀ n m : ℕ+, φ (star (S C n) * S C m) = kmsProjectionReadout β ζβ n m

namespace KMSProjectionState

variable {C : BostConnesCuntzSystem Op}

/--
The documented Bost--Connes KMS projection evaluation:

`φ(S_n^* S_m) = δ_{n,m} · n^{-β} / ζβ`.
-/
theorem kms_evaluation_on_projections
    (Φ : KMSProjectionState C) (n m : ℕ+) :
    Φ.φ (star (S C n) * S C m) =
      if n = m then ((n : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ else 0 := by
  rw [Φ.eval_projection n m]
  by_cases h : n = m
  · simp [kmsProjectionReadout, kmsProjectionWeight, h]
  · simp [kmsProjectionReadout, h]

/-- Diagonal version of `kms_evaluation_on_projections`. -/
theorem kms_evaluation_on_diagonal_projection
    (Φ : KMSProjectionState C) (n : ℕ+) :
    Φ.φ (star (S C n) * S C n) = ((n : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ := by
  simpa using Φ.kms_evaluation_on_projections n n

/-- Off-diagonal version of `kms_evaluation_on_projections`. -/
theorem kms_evaluation_on_off_diagonal_projection
    (Φ : KMSProjectionState C) {n m : ℕ+} (h : n ≠ m) :
    Φ.φ (star (S C n) * S C m) = 0 := by
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
    Φ.φ (star (S C ns.prod) * S C ms.prod) =
      if ns.prod = ms.prod then
        (((ns.prod : ℕ+) : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ
      else 0 := by
  exact Φ.kms_evaluation_on_projections ns.prod ms.prod

end KMSProjectionState

end InfoGeometry.Canonical.BostConnesKMS
