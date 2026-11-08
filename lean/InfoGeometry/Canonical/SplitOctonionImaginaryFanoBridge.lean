import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Seven-coordinate split-imaginary carrier

This owner uses the native trace-zero split-Zorn carrier and its existing
linear equivalence with `Fin 7 → ℝ`.  The definite Euclidean Fano chart is not
identified with this split carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionImaginaryFanoBridge

open InfoGeometry.Lie.SplitOctonionImaginaryAction

abbrev SplitFanoCoordinates := InfoGeometry.Algebra.FiniteSpin.Vec7R

noncomputable instance : FiniteDimensional ℝ Imaginary :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_imaginary]; norm_num)

noncomputable def imaginaryBasis : Module.Basis (Fin 7) ℝ Imaginary := by
  let b := Module.Basis.ofVectorSpace ℝ Imaginary
  have hcard : Fintype.card (Module.Basis.ofVectorSpaceIndex ℝ Imaginary) = 7 := by
    have h := Module.finrank_eq_card_basis b
    rw [finrank_imaginary] at h
    exact h.symm
  exact b.reindex (Fintype.equivFinOfCardEq hcard)

noncomputable def imaginaryToSplitFano :
    Imaginary ≃ₗ[ℝ] SplitFanoCoordinates :=
  imaginaryBasis.equivFun

@[simp] theorem imaginaryToSplitFano_apply (X : Imaginary) :
    imaginaryToSplitFano X =
      imaginaryBasis.equivFun X := rfl

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
  symm
  simpa [splitFanoBasis, imaginaryToSplitFano] using
    (imaginaryBasis.sum_repr X)

end InfoGeometry.Canonical.SplitOctonionImaginaryFanoBridge
