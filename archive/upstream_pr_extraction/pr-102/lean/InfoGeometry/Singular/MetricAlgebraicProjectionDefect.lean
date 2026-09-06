import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Singular.Drazin

/-!
# Metric/algebraic projection defect

This file records the elementary compatibility defect between the
Moore--Penrose range projector and the Drazin spectral projector.  It is
deliberately only an algebraic commutator: no Fredholm index, associator, or
physical anomaly is identified with it here.
-/

namespace InfoGeometry.Singular.MetricAlgebraicProjectionDefect

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.Drazin

variable {R : Type*} [Ring R] [StarRing R]

/-- The metric (Moore--Penrose) projection `A * B`. -/
def metricProjection (A B : R) (hMP : IsMoorePenroseInverse A B) : R :=
  MP_Projector A B hMP

/-- The algebraic (Drazin) projection `A * D`. -/
def algebraicProjection (A D : R) (k : ℕ)
    (hD : IsDrazinInverse A D k) : R :=
  Drazin_Projector A D k hD

/-- Commutator defect of two idempotent candidates (or, more generally, two
elements of a ring). -/
def commutatorDefect (P Q : R) : R := P * Q - Q * P

omit [StarRing R] in
theorem commutatorDefect_eq_zero_iff_commutes (P Q : R) :
    commutatorDefect P Q = 0 ↔ P * Q = Q * P := by
  unfold commutatorDefect
  exact sub_eq_zero

omit [StarRing R] in
theorem commutatorDefect_swap (P Q : R) :
    commutatorDefect Q P = -(commutatorDefect P Q) := by
  unfold commutatorDefect
  rw [neg_sub]

omit [StarRing R] in
theorem commutatorDefect_add_swap (P Q : R) :
    commutatorDefect P Q + commutatorDefect Q P = 0 := by
  rw [commutatorDefect_swap]
  simp

/-- The commutator measuring incompatibility of the two projections. -/
def projectionDefect (A B D : R) (k : ℕ)
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k) : R :=
  commutatorDefect (metricProjection A B hMP) (algebraicProjection A D k hD)

@[simp] theorem projectionDefect_eq_chiralAnomaly
    {A B D : R} {k : ℕ}
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k) :
    projectionDefect A B D k hMP hD = ChiralAnomaly A B D k hMP hD := by
  rfl

theorem metricProjection_idempotent
    {A B : R} (hMP : IsMoorePenroseInverse A B) :
    metricProjection A B hMP * metricProjection A B hMP =
      metricProjection A B hMP := by
  exact MP_Projector_idempotent hMP

omit [StarRing R] in
theorem algebraicProjection_idempotent
    {A D : R} {k : ℕ} (hD : IsDrazinInverse A D k) :
    algebraicProjection A D k hD * algebraicProjection A D k hD =
      algebraicProjection A D k hD := by
  exact Drazin_Projector_idempotent hD

theorem projectionDefect_eq_zero_iff_commutes
    {A B D : R} {k : ℕ}
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k) :
    projectionDefect A B D k hMP hD = 0 ↔
      metricProjection A B hMP * algebraicProjection A D k hD =
        algebraicProjection A D k hD * metricProjection A B hMP := by
  unfold projectionDefect
  exact commutatorDefect_eq_zero_iff_commutes _ _

theorem projectionDefect_eq_zero_of_equal
    {A B D : R} {k : ℕ}
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k)
    (hEq : metricProjection A B hMP = algebraicProjection A D k hD) :
    projectionDefect A B D k hMP hD = 0 := by
  apply (projectionDefect_eq_zero_iff_commutes hMP hD).2
  rw [hEq]

end InfoGeometry.Singular.MetricAlgebraicProjectionDefect
