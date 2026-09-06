import InfoGeometry.Lie.SplitOctonionImaginaryAction

/-!
# Seven-coordinate split-imaginary carrier

This owner uses the native trace-zero split-Zorn carrier and its existing
linear equivalence with `Fin 7 → ℝ`.  The definite Euclidean Fano chart is not
identified with this split carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionImaginaryFanoBridge

open InfoGeometry.Lie.SplitOctonionImaginaryAction

abbrev SplitFanoCoordinates := Fin 7 → ℝ

noncomputable def imaginaryToSplitFano :
    Imaginary ≃ₗ[ℝ] SplitFanoCoordinates :=
  imaginaryCoordLinearEquiv.trans imaginaryCoords_seven

@[simp] theorem imaginaryToSplitFano_apply (X : Imaginary) :
    imaginaryToSplitFano X =
      imaginaryCoords_seven (imaginaryCoordLinearEquiv X) := rfl

noncomputable def splitFanoBasis : Fin 7 → Imaginary :=
  fun i => imaginaryToSplitFano.symm (Pi.single i 1)

theorem imaginaryToSplitFano_basis (i : Fin 7) :
    imaginaryToSplitFano (splitFanoBasis i) = Pi.single i 1 := by
  simp [splitFanoBasis]

@[simp] theorem imaginaryToSplitFano_symm_apply
    (v : SplitFanoCoordinates) :
    imaginaryToSplitFano (imaginaryToSplitFano.symm v) = v := by
  simp

theorem splitFanoBasis_injective : Function.Injective splitFanoBasis := by
  intro i j h
  have h' := congrArg imaginaryToSplitFano h
  rw [imaginaryToSplitFano_basis, imaginaryToSplitFano_basis] at h'
  have hi := congrFun h' i
  by_contra hij
  simp [Pi.single_apply, hij] at hi

/-- Every trace-zero split-octonion element is recovered from its seven native
    coordinates in the split Fano basis. -/
theorem splitFanoBasis_expansion (X : Imaginary) :
    X = ∑ i : Fin 7,
      (imaginaryToSplitFano X i) • splitFanoBasis i := by
  apply imaginaryToSplitFano.injective
  funext j
  simp [splitFanoBasis, Finset.sum_apply, Pi.single_apply]

end InfoGeometry.Canonical.SplitOctonionImaginaryFanoBridge
