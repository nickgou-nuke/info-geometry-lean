import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.QCCRProved
import InfoGeometry.Canonical.InductiveColimitBridge

/-!
# Kuzmin Colimit Connections

This file is a theorem-level user of `InductiveColimitBridge` for the
Kuzmin/q-CCR/Cuntz--Toeplitz lane.

#### BUCKET 1: CLOSED FINITE THEOREMS

The existing finite `n = 2` q-Gram positivity and `q = 0`
Cuntz--Toeplitz readouts are re-exported from `QCCRProved`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES

The colimit readouts require explicit stage systems, bonding maps, cone maps,
finite equivalence compatibility, finite relation preservation, and limit
readout predicates.

#### BUCKET 3: OPEN CLOSURE DEBT

This file does not construct a C*-completion, an infinite-generator
Cuntz--Toeplitz algebra, or Kuzmin's analytic classification theorem.
-/

namespace InfoGeometry.Canonical.KuzminColimit

open InductiveColimitBridge

universe u v

/-- A finite comparison has the supplied equivalence readout in the limit. -/
theorem finite_equiv_to_colimit
    (T : CompatibleFiniteEquivalenceTower)
    (n : ℕ) (x : T.Left.Stage n) (y : T.Right.Stage n)
    (hxy : T.equivAt n x y) :
    T.limitEquiv (T.Left.toLimit n x) (T.Right.toLimit n y) :=
  T.finite_equiv_to_colimit n x y hxy

/-- A finite comparison remains compatible after any finite number of inclusions. -/
theorem finite_equiv_transports
    (T : CompatibleFiniteEquivalenceTower)
    (n m : ℕ) (x : T.Left.Stage n) (y : T.Right.Stage n)
    (hxy : T.equivAt n x y) :
    T.equivAt (n + m)
      (T.Left.bondSeq n m x)
      (T.Right.bondSeq n m y) :=
  T.finite_equiv_transports n m x y hxy

/-- Transporting the finite comparison first gives a valid limit comparison. -/
theorem transported_equiv_to_same_colimit
    (T : CompatibleFiniteEquivalenceTower)
    (n m : ℕ) (x : T.Left.Stage n) (y : T.Right.Stage n)
    (hxy : T.equivAt n x y) :
    T.limitEquiv
      (T.Left.toLimit (n + m) (T.Left.bondSeq n m x))
      (T.Right.toLimit (n + m) (T.Right.bondSeq n m y)) :=
  T.transported_equiv_to_same_colimit n m x y hxy

/-- The finite q-CCR relation survives on the q-CCR limit side. -/
theorem qCCR_relation_survives_colimit
    (T : CompatibleFiniteEquivalenceTower)
    (qCCRRel : ∀ n : ℕ, T.Left.Stage n → Prop)
    (qCCRLimitRel : T.Left.Limit → Prop)
    (qCCRLimitReadout : T.Left.LimitReadout qCCRRel qCCRLimitRel)
    (n : ℕ) (x : T.Left.Stage n) (hx : qCCRRel n x) :
    qCCRLimitRel (T.Left.toLimit n x) :=
  qCCRLimitReadout n x hx

/-- The finite Cuntz--Toeplitz relation survives on the Toeplitz limit side. -/
theorem toeplitz_relation_survives_colimit
    (T : CompatibleFiniteEquivalenceTower)
    (toeplitzRel : ∀ n : ℕ, T.Right.Stage n → Prop)
    (toeplitzLimitRel : T.Right.Limit → Prop)
    (toeplitzLimitReadout : T.Right.LimitReadout toeplitzRel toeplitzLimitRel)
    (n : ℕ) (y : T.Right.Stage n) (hy : toeplitzRel n y) :
    toeplitzLimitRel (T.Right.toLimit n y) :=
  toeplitzLimitReadout n y hy

/--
A finite Kuzmin comparison supplies both limit relation readouts and the limit
comparison readout, under explicit relation-preservation premises.
-/
theorem finite_kuzmin_relations_to_colimit
    (T : CompatibleFiniteEquivalenceTower)
    (qCCRRel : ∀ n : ℕ, T.Left.Stage n → Prop)
    (toeplitzRel : ∀ n : ℕ, T.Right.Stage n → Prop)
    (qCCRLimitRel : T.Left.Limit → Prop)
    (toeplitzLimitRel : T.Right.Limit → Prop)
    (qCCRLimitReadout : T.Left.LimitReadout qCCRRel qCCRLimitRel)
    (toeplitzLimitReadout : T.Right.LimitReadout toeplitzRel toeplitzLimitRel)
    (finiteEquivRespectsRelations :
      ∀ (n : ℕ) (x : T.Left.Stage n) (y : T.Right.Stage n),
        T.equivAt n x y → qCCRRel n x ∧ toeplitzRel n y)
    (n : ℕ) (x : T.Left.Stage n) (y : T.Right.Stage n)
    (hxy : T.equivAt n x y) :
    qCCRLimitRel (T.Left.toLimit n x) ∧
      toeplitzLimitRel (T.Right.toLimit n y) ∧
      T.limitEquiv (T.Left.toLimit n x) (T.Right.toLimit n y) := by
  rcases finiteEquivRespectsRelations n x y hxy with ⟨hx, hy⟩
  exact ⟨qCCRLimitReadout n x hx,
    toeplitzLimitReadout n y hy,
    T.finite_equiv_to_colimit n x y hxy⟩

/--
The same finite relation package may be transported to any later finite stage
before reading it in the limit.
-/
theorem transported_kuzmin_relations_to_colimit
    (T : CompatibleFiniteEquivalenceTower)
    (qCCRRel : ∀ n : ℕ, T.Left.Stage n → Prop)
    (toeplitzRel : ∀ n : ℕ, T.Right.Stage n → Prop)
    (qCCRLimitRel : T.Left.Limit → Prop)
    (toeplitzLimitRel : T.Right.Limit → Prop)
    (qCCRLimitReadout : T.Left.LimitReadout qCCRRel qCCRLimitRel)
    (toeplitzLimitReadout : T.Right.LimitReadout toeplitzRel toeplitzLimitRel)
    (finiteEquivRespectsRelations :
      ∀ (n : ℕ) (x : T.Left.Stage n) (y : T.Right.Stage n),
        T.equivAt n x y → qCCRRel n x ∧ toeplitzRel n y)
    (n m : ℕ) (x : T.Left.Stage n) (y : T.Right.Stage n)
    (hxy : T.equivAt n x y) :
    qCCRLimitRel (T.Left.toLimit (n + m) (T.Left.bondSeq n m x)) ∧
      toeplitzLimitRel (T.Right.toLimit (n + m) (T.Right.bondSeq n m y)) ∧
      T.limitEquiv
        (T.Left.toLimit (n + m) (T.Left.bondSeq n m x))
        (T.Right.toLimit (n + m) (T.Right.bondSeq n m y)) := by
  have hxy_m := T.finite_equiv_transports n m x y hxy
  rcases finiteEquivRespectsRelations (n + m)
      (T.Left.bondSeq n m x) (T.Right.bondSeq n m y) hxy_m with ⟨hx, hy⟩
  exact ⟨qCCRLimitReadout (n + m) (T.Left.bondSeq n m x) hx,
    toeplitzLimitReadout (n + m) (T.Right.bondSeq n m y) hy,
    T.transported_equiv_to_same_colimit n m x y hxy⟩

/-- Transported q-CCR representatives have the same limit point as their source. -/
theorem qCCR_transport_same_limit_point
    (T : CompatibleFiniteEquivalenceTower)
    (n m : ℕ) (x : T.Left.Stage n) :
    T.Left.toLimit (n + m) (T.Left.bondSeq n m x) =
      T.Left.toLimit n x :=
  T.Left.toLimit_bondSeq n m x

/-- Transported Toeplitz representatives have the same limit point as their source. -/
theorem toeplitz_transport_same_limit_point
    (T : CompatibleFiniteEquivalenceTower)
    (n m : ℕ) (y : T.Right.Stage n) :
    T.Right.toLimit (n + m) (T.Right.bondSeq n m y) =
      T.Right.toLimit n y :=
  T.Right.toLimit_bondSeq n m y

/-! ## Concrete finite q-CCR readback from the existing `QCCRProved` owner -/

/-- The existing finite `n=2` q-Gram positivity theorem, exposed as a stage theorem. -/
theorem qccr_n2_gram_positive_stage
    (q : ℝ) (hq : |q| < 1) (x : Fin 4 → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ ((InfoGeometry.Algebra.QCCR.Proved.gram_matrix_k2_n2 q).mulVec x) :=
  InfoGeometry.Algebra.QCCR.Proved.gram_positive_definite q hq x hx

/-- The finite `q=0` Cuntz--Toeplitz readout from the existing q-CCR owner. -/
theorem finite_cuntz_toeplitz_q_zero_readout
    {R : Type*} [CommRing R] [StarRing R]
    (a astar : Fin 2 → R) (hstar : ∀ i, star (a i) = astar i)
    (hrel : ∀ i j, astar i * a j = (if i = j then 1 else 0) + (0 : R) * (a j * astar i))
    (i j : Fin 2) :
    astar i * a j = (if i = j then 1 else 0) :=
  InfoGeometry.Algebra.QCCR.Proved.cuntz_toeplitz_limit a astar hstar hrel i j

end InfoGeometry.Canonical.KuzminColimit
