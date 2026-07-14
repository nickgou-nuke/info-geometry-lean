import InfoGeometry.Canonical.ConformalFiveGradeInversion
import InfoGeometry.Canonical.FibonacciParafermionAtoms

/-!
# InfoGeometry.Canonical.FibonacciFiveGradeBridge

Theorem-safe bridge between the five-grade conformal carrier and finite
Fibonacci fusion/parafermion atoms, stated directly with explicit functions,
sets, and hypotheses.  This file avoids bridge-packet structures and readback
projections.

No claim is made that a specific `Cl(5,5)` model has been constructed here.
-/

noncomputable section

namespace FibonacciFiveGradeBridge

open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Canonical.FibonacciParafermionAtoms

variable {L : Type*}

/-- The finite Fibonacci matrix from explicit coefficients is involutive. -/
theorem fusionMatrix_sq (a b : ℝ) (h : IsFibonacciRelation a b) :
    F_matrix a b * F_matrix a b = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact F_matrix_sq a b h

/-- A supplied grade-preserving braid action preserves grade. -/
theorem braid_preserves_grade (grade : L → ConformalGrade) (braid : L → L)
    (h_grade : ∀ x : L, grade (braid x) = grade x) (x : L) :
    grade (braid x) = grade x :=
  h_grade x

/-- A supplied grade-preserving braid action preserves the modular center. -/
theorem braid_preserves_center (grade : L → ConformalGrade) (braid : L → L)
    (h_grade : ∀ x : L, grade (braid x) = grade x) {x : L}
    (hx : grade x = ConformalGrade.zero) :
    grade (braid x) = ConformalGrade.zero := by
  rw [h_grade x]
  exact hx

/-- A supplied grade-preserving braid action preserves the `+2` source sector. -/
theorem braid_preserves_source (grade : L → ConformalGrade) (braid : L → L)
    (h_grade : ∀ x : L, grade (braid x) = grade x) {x : L}
    (hx : grade x = ConformalGrade.posTwo) :
    grade (braid x) = ConformalGrade.posTwo := by
  rw [h_grade x]
  exact hx

/-- A supplied grade-preserving braid action preserves the `-2` sink sector. -/
theorem braid_preserves_sink (grade : L → ConformalGrade) (braid : L → L)
    (h_grade : ∀ x : L, grade (braid x) = grade x) {x : L}
    (hx : grade x = ConformalGrade.negTwo) :
    grade (braid x) = ConformalGrade.negTwo := by
  rw [h_grade x]
  exact hx

/-- A supplied grade-preserving braid action preserves the outgoing sector. -/
theorem braid_preserves_outgoing (grade : L → ConformalGrade) (braid : L → L)
    (h_grade : ∀ x : L, grade (braid x) = grade x) {x : L}
    (hx : grade x = ConformalGrade.posOne) :
    grade (braid x) = ConformalGrade.posOne := by
  rw [h_grade x]
  exact hx

/-- A supplied grade-preserving braid action preserves the incoming sector. -/
theorem braid_preserves_incoming (grade : L → ConformalGrade) (braid : L → L)
    (h_grade : ∀ x : L, grade (braid x) = grade x) {x : L}
    (hx : grade x = ConformalGrade.negOne) :
    grade (braid x) = ConformalGrade.negOne := by
  rw [h_grade x]
  exact hx

/-- Braid transport never sends a computational element into leakage under explicit hypotheses. -/
theorem braid_not_leakage_of_computational
    (computationalSet leakageSet : Set L) (braid : L → L)
    (h_comp : ∀ x : L, x ∈ computationalSet → braid x ∈ computationalSet)
    (h_disjoint : ∀ x : L, x ∈ computationalSet → x ∈ leakageSet → False)
    {x : L} (hx : x ∈ computationalSet) :
    ¬ braid x ∈ leakageSet := by
  intro hLeak
  exact h_disjoint (braid x) (h_comp x hx) hLeak

/-- A supplied braid action preserves leakage under an explicit preservation hypothesis. -/
theorem braid_preserves_leakage
    (leakageSet : Set L) (braid : L → L)
    (h_leak : ∀ x : L, x ∈ leakageSet → braid x ∈ leakageSet)
    {x : L} (hx : x ∈ leakageSet) :
    braid x ∈ leakageSet :=
  h_leak x hx

end FibonacciFiveGradeBridge
