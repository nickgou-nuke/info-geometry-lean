import InfoGeometry.Clifford.Grading

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.SpinStatistics

open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The Graded Commutator (Supercommutator) evaluates the algebraic signature of the particles.
For Bosons (even grade), this recovers the Lie Commutator (clmComm).
For Fermions (odd grade), this recovers the Jordan Anticommutator (jordanProd * 2).
-/
noncomputable def superCommutator (A B : DoubledSpace E →L[ℝ] DoubledSpace E) (A_is_odd B_is_odd : Bool) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  if A_is_odd && B_is_odd then
    A.comp B + B.comp A
  else
    A.comp B - B.comp A

/--
Theorem (Bosonic Statistics):
If both operators are bosonic (even-graded, corresponding to integer spin),
the graded supercommutator collapses exactly to the Lie bracket (standard commutation).
-/
theorem bosonic_statistics_commute (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    superCommutator A B false false = clmComm A B := by
  dsimp [superCommutator]
  rfl

/--
Theorem (Fermionic Statistics):
If both operators are fermionic (odd-graded, corresponding to half-integer spin),
the graded supercommutator collapses exactly to the Jordan anticommutator.
This is the algebraic root of the Pauli Exclusion Principle.
-/
theorem fermionic_statistics_anticommute (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    superCommutator A B true true = (2 : ℝ) • jordanProd A B := by
  dsimp [superCommutator, jordanProd]
  have h_smul : (2 : ℝ) • ((2 : ℝ)⁻¹ • (A.comp B + B.comp A)) = A.comp B + B.comp A := by
    rw [← smul_assoc]
    change ((2 : ℝ) * (2 : ℝ)⁻¹) • (A.comp B + B.comp A) = _
    have h2 : (2 : ℝ) * (2 : ℝ)⁻¹ = 1 := by norm_num
    rw [h2, one_smul]
  exact h_smul.symm

/--
Theorem (Mixed Statistics):
If one operator is bosonic and the other is fermionic, the supercommutator
is still the standard Lie commutator.
-/
theorem mixed_statistics_commute (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    superCommutator A B true false = clmComm A B ∧
    superCommutator A B false true = clmComm A B := by
  dsimp [superCommutator]
  exact ⟨rfl, rfl⟩

end InfoGeometry.Canonical.SpinStatistics
