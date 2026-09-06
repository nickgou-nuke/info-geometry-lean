import Mathlib
import Mathlib.LinearAlgebra.Dimension.Constructions
import proofs.ChiralConeAlgebraFinality
import proofs.TKKJordanPairData
import proofs.Clifford55AnomalyOSP

/-!
# Grothendieck motive: finite-dimensional colimit enforcement

This module records the motive at the **finite-dimensional** level,
using only genuinely proven identities.
-/

noncomputable section

namespace GrothendieckMotiveFindimColimit

open ChiralConeAlgebraFinality
open ChiralCausalCone
open TKKJordanPairData
open TKKJordanPairData.TKKGrade
open Clifford55AnomalyOSP

/-- The `2×2` chiral seed is genuinely finite-dimensional: its `ℂ`-finrank is 4. -/
lemma chiral_bit_finrank : Module.finrank ℂ ChiralConeAlgebraFinality.M2C = 4 := by
  simp [ChiralConeAlgebraFinality.M2C, Module.finrank_matrix]

/-- The finite chiral core is the collection of proved `M₂(ℂ)` identities. -/
theorem chiral_finite_core_identities :
  sPlus * sPlus = 0 ∧
  sMinus * sMinus = 0 ∧
  NPlus + NMinus = (1 : ChiralConeAlgebraFinality.M2C) ∧
  s3 = NPlus - NMinus ∧
  s3 * s3 = (1 : ChiralConeAlgebraFinality.M2C) := by
  constructor
  · exact sPlus_sq_zero
  constructor
  · exact sMinus_sq_zero
  constructor
  · exact chiral_projector_completeness
  constructor
  · exact chiral_parity_from_projectors
  · exact chiral_parity_sq

/-- The finite 5-grading is the standard TKK grade window closure. -/
theorem tkk_five_grade_finite_window :
  gradeAdd TKKGrade.z0 TKKGrade.p1 = some TKKGrade.p1 ∧
  gradeAdd TKKGrade.m1 TKKGrade.p1 = some TKKGrade.z0 ∧
  gradeAdd TKKGrade.p2 TKKGrade.p1 = none := by
  constructor
  · exact gradeAdd_z0_right TKKGrade.p1
  constructor
  · exact gradeAdd_m1_p1
  · exact gradeAdd_p2_p1_none

/-- The finite anomaly cancellation is the checked `Cl(5,5)`/OSP shadow. -/
theorem anomaly_index_five_five_eq_zero : anomalyIndex 5 5 = 0 := by
  simpa using anomalyIndex_55_zero

end GrothendieckMotiveFindimColimit

end noncomputable section
