import InfoGeometry.Canonical.CelikCantorSheetColourWeyl

/-!
# Orientation-reversing sheet/colour Weyl action

The commuting packet is complemented here by the concrete reflection of the
three colour labels `0,1,2 ↦ 0,2,1`.  Its permutation matrix reverses both the
clock and the shift, giving the genuine dihedral (`S₃`) extension.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikCantorSheetColourWeyl

open InfoGeometry.Quantum.QutritBraidIncidenceBridge
open InfoGeometry.Canonical.CelikCantorClifford
open InfoGeometry.Physics.MD014TriSpinZ3Projectors
open InfoGeometry.Topology.ArtinBraidS3Quotient
open scoped Kronecker

abbrev colourReflection : ColourMatrix :=
  qutritPermutationMatrix sigma2

@[simp] theorem colourReflection_sq :
    colourReflection * colourReflection = (1 : ColourMatrix) := by
  simpa [colourReflection] using qutritPermutationMatrix_sigma2_sq

theorem colourReflection_conj_shift :
    colourReflection * colourShift * colourReflection =
      colourShift * colourShift := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colourReflection, colourShift, qutritPermutationMatrix,
      Equiv.Perm.permMatrix, sigma2, qutritShiftMatrix,
      qutritGeneralizedPauliX, Matrix.mul_apply, Fin.sum_univ_three,
      Equiv.swap_apply_def]

theorem colourReflection_conj_clock :
    colourReflection * colourClock * colourReflection =
      colourClock * colourClock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colourReflection, colourClock, qutritPermutationMatrix,
      Equiv.Perm.permMatrix, sigma2, qutritPrimitiveClock,
      qutritGeneralizedPauliZ, sectorPhase, sectorProjector0,
      sectorProjector1, sectorProjector2, Matrix.mul_apply,
      Fin.sum_univ_three, Equiv.swap_apply_def, pow_two]
  · calc
      Topology.Parafermion.omega =
          Topology.Parafermion.omega *
            (Topology.Parafermion.omega ^ 3) := by
              rw [Topology.Parafermion.omega_cube_eq_one]
              simp
      _ = Topology.Parafermion.omega * Topology.Parafermion.omega *
          (Topology.Parafermion.omega * Topology.Parafermion.omega) := by ring

abbrev orientationReversingSheetFlip : SheetColourMatrix :=
  tensor sheetFlip colourReflection

theorem orientationReversingSheetFlip_sq :
    orientationReversingSheetFlip * orientationReversingSheetFlip =
      (1 : SheetColourMatrix) := by
  rw [orientationReversingSheetFlip, tensor_mul]
  simp [sheetFlip_sq, colourReflection_sq]

theorem orientationReversingSheetFlip_conj_shift :
    orientationReversingSheetFlip * liftedColourShift *
        orientationReversingSheetFlip =
      liftedColourShift * liftedColourShift := by
  change (sheetFlip ⊗ₖ colourReflection) *
      ((1 : SheetMatrix) ⊗ₖ colourShift) *
      (sheetFlip ⊗ₖ colourReflection) =
      ((1 : SheetMatrix) ⊗ₖ colourShift) *
        ((1 : SheetMatrix) ⊗ₖ colourShift)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp [colourReflection_conj_shift]

theorem orientationReversingSheetFlip_conj_clock :
    orientationReversingSheetFlip * liftedColourClock *
        orientationReversingSheetFlip =
      liftedColourClock * liftedColourClock := by
  change (sheetFlip ⊗ₖ colourReflection) *
      ((1 : SheetMatrix) ⊗ₖ colourClock) *
      (sheetFlip ⊗ₖ colourReflection) =
      ((1 : SheetMatrix) ⊗ₖ colourClock) *
        ((1 : SheetMatrix) ⊗ₖ colourClock)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp [colourReflection_conj_clock]

theorem orientation_reversing_S3_relations :
    orientationReversingSheetFlip * orientationReversingSheetFlip = 1 ∧
      orientationReversingSheetFlip * liftedColourShift *
          orientationReversingSheetFlip =
        liftedColourShift * liftedColourShift ∧
      orientationReversingSheetFlip * liftedColourClock *
          orientationReversingSheetFlip =
        liftedColourClock * liftedColourClock := by
  exact ⟨orientationReversingSheetFlip_sq,
    orientationReversingSheetFlip_conj_shift,
    orientationReversingSheetFlip_conj_clock⟩

end InfoGeometry.Canonical.CelikCantorSheetColourWeyl
