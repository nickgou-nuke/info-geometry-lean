import InfoGeometry.Canonical.ConformalFiveGradeInversion
import InfoGeometry.Canonical.FibonacciParafermionAtoms

/-!
# InfoGeometry.Canonical.FibonacciFiveGradeBridge

Theorem-safe bridge between the five-grade conformal carrier and the finite
Fibonacci fusion/parafermion atoms.

This file does **not** identify the two theories.  It only packages the
explicit compatibility data one would need to read Fibonacci fusion through a
chosen five-grade carrier:

* a five-grade inversion carrier,
* a declared computational/leakage split,
* a grade-preserving braid action,
* and a finite Fibonacci `F`-matrix readout.

No claim is made that a specific `Cl(5,5)` model has been constructed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.FibonacciFiveGradeBridge

open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Canonical.ConformalFiveGradeInversion.FiveGradedConformalInversion
open InfoGeometry.Canonical.FibonacciParafermionAtoms

/--
Bridge packet for the five-grade carrier and the finite Fibonacci readout.

The packet is intentionally abstract: the braid action and the computational /
leakage sets are supplied as explicit data, not inferred.
-/
structure FiveGradeFibonacciBridge (L : Type*) where
  inversion : FiveGradedConformalInversion L
  computationalSet : Set L
  leakageSet : Set L
  braid : L → L
  braid_grade_preserving : ∀ x : L, inversion.grade (braid x) = inversion.grade x
  braid_computational_preserving : ∀ x : L, x ∈ computationalSet → braid x ∈ computationalSet
  braid_leakage_preserving : ∀ x : L, x ∈ leakageSet → braid x ∈ leakageSet
  computational_leakage_disjoint : ∀ x : L, x ∈ computationalSet → x ∈ leakageSet → False
  a : ℝ
  b : ℝ
  fibonacci_relation : IsFibonacciRelation a b

namespace FiveGradeFibonacciBridge

variable {L : Type*}

/-- The finite Fibonacci fusion matrix attached to the bridge packet. -/
noncomputable def fusionMatrix (B : FiveGradeFibonacciBridge L) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  F_matrix B.a B.b

/-- The bridge packet's Fibonacci matrix is involutive. -/
theorem fusionMatrix_sq (B : FiveGradeFibonacciBridge L) :
    B.fusionMatrix * B.fusionMatrix = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  simpa [fusionMatrix] using (F_matrix_sq B.a B.b B.fibonacci_relation)

/-- The braid action preserves the grade of every element. -/
theorem braid_preserves_grade (B : FiveGradeFibonacciBridge L) (x : L) :
    B.inversion.grade (B.braid x) = B.inversion.grade x :=
  B.braid_grade_preserving x

/-- The braid action preserves the modular center. -/
theorem braid_preserves_center (B : FiveGradeFibonacciBridge L) {x : L}
    (hx : x ∈ B.inversion.centerSet) :
    B.braid x ∈ B.inversion.centerSet := by
  change B.inversion.grade (B.braid x) = ConformalGrade.zero
  rw [B.braid_grade_preserving x]
  exact hx

/-- The braid action preserves the `+2` source sector. -/
theorem braid_preserves_source (B : FiveGradeFibonacciBridge L) {x : L}
    (hx : x ∈ B.inversion.sourceSet) :
    B.braid x ∈ B.inversion.sourceSet := by
  change B.inversion.grade (B.braid x) = ConformalGrade.posTwo
  rw [B.braid_grade_preserving x]
  exact hx

/-- The braid action preserves the `-2` sink sector. -/
theorem braid_preserves_sink (B : FiveGradeFibonacciBridge L) {x : L}
    (hx : x ∈ B.inversion.sinkSet) :
    B.braid x ∈ B.inversion.sinkSet := by
  change B.inversion.grade (B.braid x) = ConformalGrade.negTwo
  rw [B.braid_grade_preserving x]
  exact hx

/-- The braid action preserves the outgoing boundary sector. -/
theorem braid_preserves_outgoing (B : FiveGradeFibonacciBridge L) {x : L}
    (hx : x ∈ B.inversion.outgoingSet) :
    B.braid x ∈ B.inversion.outgoingSet := by
  change B.inversion.grade (B.braid x) = ConformalGrade.posOne
  rw [B.braid_grade_preserving x]
  exact hx

/-- The braid action preserves the incoming boundary sector. -/
theorem braid_preserves_incoming (B : FiveGradeFibonacciBridge L) {x : L}
    (hx : x ∈ B.inversion.incomingSet) :
    B.braid x ∈ B.inversion.incomingSet := by
  change B.inversion.grade (B.braid x) = ConformalGrade.negOne
  rw [B.braid_grade_preserving x]
  exact hx

/-- Braid transport never sends a computational element into the leakage set. -/
theorem braid_not_leakage_of_computational (B : FiveGradeFibonacciBridge L)
    {x : L} (hx : x ∈ B.computationalSet) :
    ¬ B.braid x ∈ B.leakageSet := by
  intro hLeak
  exact B.computational_leakage_disjoint (B.braid x)
    (B.braid_computational_preserving x hx) hLeak

/-- The bridge packet's braid action preserves the leakage set itself. -/
theorem braid_preserves_leakage (B : FiveGradeFibonacciBridge L) {x : L}
    (hx : x ∈ B.leakageSet) :
    B.braid x ∈ B.leakageSet :=
  B.braid_leakage_preserving x hx

end FiveGradeFibonacciBridge

end InfoGeometry.Canonical.FibonacciFiveGradeBridge
