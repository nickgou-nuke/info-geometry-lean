import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Meta.Architecture

namespace InfoGeometry.Canonical.MoorePenrose

open InfoGeometry.Canonical.Drazin

/-!
# Moore-Penrose Inverse

Formalization of the Moore-Penrose pseudoinverse in a StarRing.
The Moore-Penrose inverse `b` of an element `a` satisfies:
1. `a * b * a = a`
2. `b * a * b = b`
3. `(a * b)* = a * b`  (Right projector is self-adjoint)
4. `(b * a)* = b * a`  (Left projector is self-adjoint)
-/

/-- Predicate encoding the Moore-Penrose inverse laws. -/
@[rep_depth operator]
def IsMoorePenroseInverse {R : Type*} [Ring R] [StarRing R] (a b : R) : Prop :=
  a * b * a = a ∧
  b * a * b = b ∧
  star (a * b) = a * b ∧
  star (b * a) = b * a

namespace IsMoorePenroseInverse

variable {R : Type*} [Ring R] [StarRing R] {a b : R}

/-- Constructor for the Moore-Penrose laws predicate. -/
@[rep_depth operator]
theorem mk
    (haba : a * b * a = a)
    (hbab : b * a * b = b)
    (habstar : star (a * b) = a * b)
    (hbastar : star (b * a) = b * a) :
    IsMoorePenroseInverse a b :=
  ⟨haba, hbab, habstar, hbastar⟩

/-- Penrose relation `a b a = a`. -/
@[rep_depth operator]
theorem aba_eq_a (h : IsMoorePenroseInverse a b) : a * b * a = a := h.1

/-- Penrose relation `b a b = b`. -/
@[rep_depth operator]
theorem bab_eq_b (h : IsMoorePenroseInverse a b) : b * a * b = b := h.2.1

/-- Self-adjointness of `a*b`. -/
@[rep_depth operator]
theorem ab_star (h : IsMoorePenroseInverse a b) : star (a * b) = a * b := h.2.2.1

/-- Self-adjointness of `b*a`. -/
@[rep_depth operator]
theorem ba_star (h : IsMoorePenroseInverse a b) : star (b * a) = b * a := h.2.2.2

/-- The geometric projection onto the range of `a`. -/
@[rep_depth operator]
def rightProjector (a b : R) : R := a * b

/-- The geometric projection onto the co-range of `a`. -/
@[rep_depth operator]
def leftProjector (a b : R) : R := b * a

/-- Theorem: The range projection is idempotent (P² = P). -/
@[rep_depth operator]
theorem rightProjector_idempotent :
    (h : IsMoorePenroseInverse a b) →
    (rightProjector a b) * (rightProjector a b) = rightProjector a b := by
  intro h
  unfold rightProjector
  calc
    (a * b) * (a * b) = (a * b * a) * b := by simp [mul_assoc]
    _ = a * b := by rw [h.aba_eq_a]

/-- Theorem: The range projection is self-adjoint (P* = P). -/
@[rep_depth operator]
theorem rightProjector_star (h : IsMoorePenroseInverse a b) :
    star (rightProjector a b) = rightProjector a b :=
  h.ab_star

/-- Theorem: The co-range projection is idempotent (P² = P). -/
@[rep_depth operator]
theorem leftProjector_idempotent :
    (h : IsMoorePenroseInverse a b) →
    (leftProjector a b) * (leftProjector a b) = leftProjector a b := by
  intro h
  unfold leftProjector
  calc
    (b * a) * (b * a) = (b * a * b) * a := by simp [mul_assoc]
    _ = b * a := by rw [h.bab_eq_b]

/-- Theorem: The co-range projection is self-adjoint (P* = P). -/
@[rep_depth operator]
theorem leftProjector_star (h : IsMoorePenroseInverse a b) :
    star (leftProjector a b) = leftProjector a b :=
  h.ba_star

end IsMoorePenroseInverse

/-! ### Chiral Anomaly and Scale Generation -/

/-- Spectral projector from Drazin data. -/
@[rep_depth operator]
def spectralProjector {R : Type*} [Ring R] (a a_d : R) : R :=
  IsDrazinInverse.projection a a_d

/-- Metric projector from Moore-Penrose data. -/
@[rep_depth operator]
def metricProjector {R : Type*} [Ring R] [StarRing R] (a a_mp : R) : R :=
  IsMoorePenroseInverse.leftProjector a a_mp

/--
Projector mismatch `Δ = P_D - P_MP` between spectral and metric sectors.
-/
@[rep_depth operator]
def projectorMismatch {R : Type*} [Ring R] [StarRing R] (a a_d a_mp : R) : R :=
  spectralProjector a a_d - metricProjector a a_mp

/--
The Chiral Anomaly Operator (χ).
Defined as the commutator between the spectral projector (Drazin) 
and the geometric left projector (Moore-Penrose).
χ = [P_D, P_L].
-/
@[rep_depth operator]
def chiralAnomaly {R : Type*} [Ring R] [StarRing R] (a a_d a_mp : R) : R :=
  let P_D := IsDrazinInverse.projection a a_d
  let P_L := IsMoorePenroseInverse.leftProjector a a_mp
  P_D * P_L - P_L * P_D

/--
Algebraic identity: the anomaly commutator is the mismatch commutator with the
metric projector.
-/
@[rep_depth operator]
theorem chiralAnomaly_eq_mismatch_commutator_metric
    {R : Type*} [Ring R] [StarRing R] (a a_d a_mp : R) :
    chiralAnomaly a a_d a_mp =
      projectorMismatch a a_d a_mp * metricProjector a a_mp
        - metricProjector a a_mp * projectorMismatch a a_d a_mp := by
  unfold chiralAnomaly projectorMismatch spectralProjector metricProjector
  unfold IsDrazinInverse.projection IsMoorePenroseInverse.leftProjector
  noncomm_ring

/--
If the spectral-metric mismatch vanishes, the anomaly vanishes.
-/
@[rep_depth operator]
theorem chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero
    {R : Type*} [Ring R] [StarRing R] {a a_d a_mp : R}
    (hΔ : projectorMismatch a a_d a_mp = 0) :
    chiralAnomaly a a_d a_mp = 0 := by
  rw [chiralAnomaly_eq_mismatch_commutator_metric]
  simp [hΔ]

/-- Vanishing mismatch is equivalent to projector equality. -/
@[rep_depth operator]
theorem projectorMismatch_eq_zero_iff
    {R : Type*} [Ring R] [StarRing R] {a a_d a_mp : R} :
    projectorMismatch a a_d a_mp = 0 ↔
      spectralProjector a a_d = metricProjector a a_mp := by
  unfold projectorMismatch
  exact sub_eq_zero

/--
The Emergent Scale ε.
Generated by the divergence between geometry and spectrum.
ε = || [P_D, P_L] ||.
-/
@[rep_depth operator]
noncomputable def epsilon {R : Type*} [NormedRing R] [StarRing R] (a a_d a_mp : R) : ℝ :=
  nnnorm (chiralAnomaly a a_d a_mp)

/-- Backward-compatible alias for the emergent anomaly scale ε. -/
@[rep_depth operator]
noncomputable def chiralScale {R : Type*} [NormedRing R] [StarRing R] (a a_d a_mp : R) : ℝ :=
  epsilon a a_d a_mp

end InfoGeometry.Canonical.MoorePenrose
