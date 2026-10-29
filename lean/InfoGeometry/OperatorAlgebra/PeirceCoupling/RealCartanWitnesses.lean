/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedCartan
import InfoGeometry.OperatorAlgebra.PeirceCoupling.RealReflectionGeometry

/-!
# Dense noncommuting real witnesses

The forward and reverse matrices below have no zero entries, form a
nontrivial reflexive square-zero pair, and generate a native Cartan triple.
Their Gram sum nevertheless has a nonzero common-kernel vector. This tests
nonvacuity and distinguishes positivity from positive definiteness without
replacing the ambient full matrix algebra by a diagonal model.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCoupling.RealCartanWitnesses

open Matrix InfoGeometry.Core.DualSeedPeirce
open RealReflectionGeometry

noncomputable section

/-- A dense real rank-one square-zero operator. -/
def denseSeed : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2 / 9, 1 / 9, -2 / 9; 4 / 9, 2 / 9, -4 / 9; 4 / 9, 2 / 9, -4 / 9]

/-- A nonzero vector annihilated by both adjoint partners. -/
def harmonicVector : Fin 3 → ℝ := ![-2, 2, -1]

theorem denseSeed_sq : denseSeed * denseSeed = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [denseSeed, Matrix.mul_apply, Fin.sum_univ_succ]

theorem denseSeed_adjoint_sq : denseSeedᴴ * denseSeedᴴ = 0 := by
  rw [← Matrix.conjTranspose_mul, denseSeed_sq, Matrix.conjTranspose_zero]

theorem denseSeed_reflexive : denseSeed * denseSeedᴴ * denseSeed = denseSeed := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [denseSeed, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem denseSeed_adjoint_reflexive :
    denseSeedᴴ * denseSeed * denseSeedᴴ = denseSeedᴴ := by
  have h := congrArg Matrix.conjTranspose denseSeed_reflexive
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using h

theorem denseSeed_pair : IsDualSeedPair denseSeed denseSeedᴴ :=
  ⟨denseSeed_sq, denseSeed_adjoint_sq, denseSeed_reflexive, denseSeed_adjoint_reflexive⟩

theorem denseSeed_ne_zero : denseSeed ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
  norm_num [denseSeed] at h00

theorem denseSeed_not_commute : ¬ Commute denseSeed denseSeedᴴ :=
  denseSeed_pair.seeds_not_commute denseSeed_ne_zero

theorem denseSeed_cartan :
    IsSl2Triple (phasePolarization denseSeed denseSeedᴴ) denseSeed denseSeedᴴ :=
  denseSeed_pair.isSl2Triple denseSeed_ne_zero

theorem harmonicVector_ne_zero : harmonicVector ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [harmonicVector] at h0

theorem denseSeed_harmonic : denseSeed *ᵥ harmonicVector = 0 := by
  ext i
  fin_cases i <;>
    norm_num [denseSeed, harmonicVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem denseSeed_adjoint_harmonic : denseSeedᴴ *ᵥ harmonicVector = 0 := by
  ext i
  fin_cases i <;>
    norm_num [denseSeed, harmonicVector, Matrix.mulVec, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem denseGram_posSemidef :
    (denseSeed * denseSeedᴴ + denseSeedᴴ * denseSeed).PosSemidef :=
  gram_posSemidef denseSeed

theorem denseGram_not_posDef :
    ¬ (denseSeed * denseSeedᴴ + denseSeedᴴ * denseSeed).PosDef := by
  intro h
  exact harmonicVector_ne_zero ((gram_posDef_iff denseSeed).mp h harmonicVector
    ⟨denseSeed_harmonic, denseSeed_adjoint_harmonic⟩)

theorem denseGram_nonzero_idempotent :
    carrierSupport denseSeed denseSeedᴴ ≠ 0 ∧
      IsIdempotentElem (carrierSupport denseSeed denseSeedᴴ) :=
  ⟨denseSeed_pair.support_ne_zero denseSeed_ne_zero, denseSeed_pair.support_idempotent⟩

end
end InfoGeometry.OperatorAlgebra.PeirceCoupling.RealCartanWitnesses
