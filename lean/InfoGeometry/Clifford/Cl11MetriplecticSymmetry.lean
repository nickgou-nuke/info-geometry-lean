/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11MetriplecticPencil
import InfoGeometry.Clifford.SplitQ11CausalCone
import InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation

/-!
# Projector defect and conjugation of the two real `Cl(1,1)` pencils

Prepared as a follow-up to the five-owner native baseline. Acceptance is
recorded per source revision by `verification/nambu-metriplectic/check.py`.

The difference between `gen (σ, γ)` and `scalarPencil σ γ` is supported on
the existing negative Krein projector. The equality criterion remains the
owner theorem `gen_eq_scalarPencil_iff`.

The conjugation formulas use the existing generators and native Klein four
action. In particular, `Eminus` has inverse `-Eminus`. The scalar coordinate
of `scalarPencil` is fixed by every conjugation, whereas the first coordinate
of `gen` changes sign under conjugation by `J1` or `Eminus`.
-/

noncomputable section

open Matrix
open scoped Matrix BigOperators

namespace InfoGeometry.Clifford.Cl11Matrix

/-- The exact defect is the negative Krein projector in the same matrix family. -/
theorem gen_sub_scalarPencil (σ γ : ℝ) :
    gen (σ, γ) - scalarPencil σ γ =
      (-2 * σ) • SplitQ11CausalCone.matrixKreinMinusProjector := by
  rw [SplitQ11CausalCone.matrix_krein_projectors_explicit.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gen, scalarPencil, Eplus, Eminus] <;> ring

/-- The positive generator reverses the second coordinate of the Clifford pencil. -/
theorem gen_Eplus_conjugate (σ γ : ℝ) :
    Eplus * gen (σ, γ) * Eplus = gen (σ, -γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gen, Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Coordinate form of the owner's mirror-conjugation theorem. -/
theorem gen_J1_conjugate (σ γ : ℝ) :
    J1 * gen (σ, γ) * J1 = gen (-σ, -γ) := by
  rw [gen_mirror_conjugate]
  change -gen (σ, γ) = gen (-(σ, γ))
  exact (gen.map_neg (σ, γ)).symm

/-- The negative generator reverses the first coordinate; its inverse is `-Eminus`. -/
theorem gen_Eminus_conjugate (σ γ : ℝ) :
    (-Eminus) * gen (σ, γ) * Eminus = gen (-σ, γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gen, Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## The scalar pencil has a different coordinate action -/

theorem scalarPencil_Eplus_conjugate (σ γ : ℝ) :
    Eplus * scalarPencil σ γ * Eplus = scalarPencil σ (-γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarPencil, Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

theorem scalarPencil_J1_conjugate (σ γ : ℝ) :
    J1 * scalarPencil σ γ * J1 = scalarPencil σ (-γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarPencil, Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two]

theorem scalarPencil_Eminus_conjugate (σ γ : ℝ) :
    (-Eminus) * scalarPencil σ γ * Eminus = scalarPencil σ γ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarPencil, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Readouts of the existing native algebra automorphisms -/

open InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
  (adjointAlgEquiv gammaUnit bivectorUnit causalUnit localCl11Map)

theorem adjointAlgEquiv_gammaUnit_gen (σ γ : ℝ) :
    adjointAlgEquiv gammaUnit (gen (σ, γ)) = gen (σ, -γ) := by
  change Eplus * gen (σ, γ) * Eplus = _
  exact gen_Eplus_conjugate σ γ

theorem adjointAlgEquiv_bivectorUnit_gen (σ γ : ℝ) :
    adjointAlgEquiv bivectorUnit (gen (σ, γ)) = gen (-σ, -γ) := by
  change J1 * gen (σ, γ) * J1 = _
  exact gen_J1_conjugate σ γ

theorem adjointAlgEquiv_causalUnit_gen (σ γ : ℝ) :
    adjointAlgEquiv causalUnit (gen (σ, γ)) = gen (-σ, γ) := by
  change Eminus * gen (σ, γ) * (-Eminus) = _
  simpa only [neg_mul, mul_neg] using gen_Eminus_conjugate σ γ

/-- The existing `P` tag is conjugation by `Eplus`. -/
theorem localCl11Map_P_gen (σ γ : ℝ) :
    localCl11Map (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P)
        (gen (σ, γ)) = gen (σ, -γ) := by
  change adjointAlgEquiv gammaUnit (gen (σ, γ)) = _
  exact adjointAlgEquiv_gammaUnit_gen σ γ

/-- The existing `T` tag is conjugation by `J1`. -/
theorem localCl11Map_T_gen (σ γ : ℝ) :
    localCl11Map (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
        (gen (σ, γ)) = gen (-σ, -γ) := by
  change adjointAlgEquiv bivectorUnit (gen (σ, γ)) = _
  exact adjointAlgEquiv_bivectorUnit_gen σ γ

/-- The existing `PT` tag is conjugation by `Eminus`. -/
theorem localCl11Map_PT_gen (σ γ : ℝ) :
    localCl11Map (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT)
        (gen (σ, γ)) = gen (-σ, γ) := by
  change adjointAlgEquiv causalUnit (gen (σ, γ)) = _
  exact adjointAlgEquiv_causalUnit_gen σ γ

end InfoGeometry.Clifford.Cl11Matrix
