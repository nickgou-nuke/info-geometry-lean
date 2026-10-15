import InfoGeometry.Clifford.Cl55CARSpinAutomorphism
import InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
import InfoGeometry.Clifford.Cl55FockMatrixIntertwiner

/-!
# Transport of the `Cl(5,5)` CAR generators to the exterior Fock model

This bridge composes the existing neutral-space Clifford equivalence with
Mathlib's exterior Fock representation.  It records exactly how the
repository's recursive CAR generators act after transport.  The resulting
formula is expressed using the owner's neutral action; identifying the
coordinate vacuum rank-one projection with the scalar exterior monomial is a
separate basis-index comparison and is deliberately not asserted here.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55CARExteriorCalibration

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
open InfoGeometry.Clifford.Cl55FockMatrixIntertwiner

/-- The inverse neutral-coordinate map sends the positive null CAR vector to
the pure vector direction. -/
theorem nPair_eq_basisPair (i : Fin 5) :
    n_pair i = (basisVector i, basisVector i) := by
  apply Prod.ext <;> funext j <;>
    simp [n_pair, e_pos, f_neg, basisVector, Pi.single_apply]

/-- The negative null CAR vector is the vector/covector difference pair. -/
theorem nbarPair_eq_basisPair (i : Fin 5) :
    nbar_pair i = (basisVector i, -basisVector i) := by
  apply Prod.ext <;> funext j <;>
    simp [nbar_pair, e_pos, f_neg, basisVector, Pi.single_apply]

theorem dualToV5_dualBasisVector (i : Fin 5) :
    dualToV5 (dualBasisVector i) = basisVector i := by
  ext j
  rw [dualToV5_apply_coord]
  change dualBasisVector i (basisVector j) = basisVector i j
  rw [dualBasisVector_apply]
  simp [basisVector, Pi.single_apply, eq_comm]

theorem neutralToV55_symm_nPair (i : Fin 5) :
    neutralToV55.symm (n_pair i) =
      (2 • basisVector i,
        (0 : Module.Dual ℝ SplitClifford55ExteriorSpinor.V5)) := by
  rw [nPair_eq_basisPair, neutralToV55_symm_apply]
  apply Prod.ext
  · funext j
    simp
    ring
  · simp

/-- The inverse neutral-coordinate map sends the negative null CAR vector
to the covector direction. -/
theorem neutralToV55_symm_nbarPair (i : Fin 5) :
    neutralToV55.symm (nbar_pair i) =
      ((0 : SplitClifford55ExteriorSpinor.V5), 2 • dualBasisVector i) := by
  rw [nbarPair_eq_basisPair, neutralToV55_symm_apply]
  apply Prod.ext
  · simp
  · have hdual := dualToV5_dualBasisVector i
    have hinv : dualToV5.symm (basisVector i) = dualBasisVector i := by
      rw [← hdual]
      simp
    change dualToV5.symm (basisVector i - -basisVector i) = _
    rw [show basisVector i - -basisVector i =
      basisVector i + basisVector i by abel, map_add, hinv]
    simp [two_smul]

/-- The transported recursive annihilation generator is the neutral-action
operator associated with the inverse image of its null vector, including the
normalization used in the CAR definition. -/
theorem annihilation55_fock (i : Fin 5) :
    neutralCliffordFockAlgEquiv
        (neutralCliffordAlgEquiv.symm (annihilation55 i)) =
      (1 / 2 : ℝ) •
        (spinorCoordinateEquiv.conjAlgEquiv ℝ
          (neutralAction (neutralToV55.symm (n_pair i)))) := by
  simp [annihilation55, map_smul,
    neutralToV55_symm_nPair, neutralCliffordAlgEquiv_symm_ι55,
    neutralCliffordFockAlgEquiv_ι]

/-- The transported recursive creation generator is the neutral-action
operator associated with the inverse image of its null vector. -/
theorem creation55_fock (i : Fin 5) :
    neutralCliffordFockAlgEquiv
        (neutralCliffordAlgEquiv.symm (creation55 i)) =
      (1 / 2 : ℝ) •
        (spinorCoordinateEquiv.conjAlgEquiv ℝ
          (neutralAction (neutralToV55.symm (nbar_pair i)))) := by
  simp [creation55, map_smul,
    neutralToV55_symm_nbarPair, neutralCliffordAlgEquiv_symm_ι55,
    neutralCliffordFockAlgEquiv_ι]

end InfoGeometry.Clifford.Cl55CARExteriorCalibration
