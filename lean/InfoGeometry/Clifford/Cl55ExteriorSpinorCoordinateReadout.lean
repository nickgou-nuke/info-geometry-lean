import Mathlib.Algebra.Algebra.Equiv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitClifford55ExteriorFiniteGraded

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

noncomputable def exteriorIndexEquivFin :
    (Σ k : ℕ, Set.powersetCard (Fin 5) k) ≃ Fin 32 := by
  letI : Fintype (Σ k : ℕ, Set.powersetCard (Fin 5) k) :=
    Fintype.ofEquiv (Finset (Fin 5))
      InfoGeometry.Clifford.SplitClifford55ExteriorDegrees.gradedIndexFinsetNat.symm
  apply Fintype.equivFinOfCardEq
  rw [Fintype.card_congr
    InfoGeometry.Clifford.SplitClifford55ExteriorDegrees.gradedIndexFinsetNat]
  simp [Fintype.card_finset]

theorem spinor_finrank : Module.finrank ℝ Spinor = 32 := by
  letI : Fintype (Σ k : ℕ, Set.powersetCard (Fin 5) k) :=
    Fintype.ofEquiv (Finset (Fin 5))
      InfoGeometry.Clifford.SplitClifford55ExteriorDegrees.gradedIndexFinsetNat.symm
  rw [Module.finrank_eq_card_basis
    InfoGeometry.Clifford.SplitClifford55ExteriorDegrees.exteriorAlgebraBasisSigma]
  rw [Fintype.card_congr
    InfoGeometry.Clifford.SplitClifford55ExteriorDegrees.gradedIndexFinsetNat]
  simp [Fintype.card_finset]

theorem spinor_finiteDimensional : FiniteDimensional ℝ Spinor := by
  letI : Fintype (Σ k : ℕ, Set.powersetCard (Fin 5) k) :=
    Fintype.ofEquiv (Finset (Fin 5))
      InfoGeometry.Clifford.SplitClifford55ExteriorDegrees.gradedIndexFinsetNat.symm
  exact Module.Basis.finiteDimensional_of_finite
    InfoGeometry.Clifford.SplitClifford55ExteriorDegrees.exteriorAlgebraBasisSigma

noncomputable def spinorCoordinateEquiv :
    Spinor ≃ₗ[ℝ] (Fin 32 → ℝ) :=
  (Module.Basis.reindex
    InfoGeometry.Clifford.SplitClifford55ExteriorDegrees.exteriorAlgebraBasisSigma
    exteriorIndexEquivFin).equivFun

noncomputable def neutralCliffordRepCoordinate :
    CliffordAlgebra
        (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
          (E := V5)) →ₐ[ℝ] Module.End ℝ (Fin 32 → ℝ) :=
  (spinorCoordinateEquiv.conjAlgEquiv ℝ).toAlgHom.comp neutralCliffordRep

/-! The final coordinate readout uses Mathlib's basis-level algebra
    equivalence, so multiplication is transported by the kernel-owned
    `LinearMap.toMatrixAlgEquiv` rather than reproved entrywise. -/

noncomputable def neutralCliffordCoordinateMatrixRep :
    CliffordAlgebra
        (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
          (E := V5)) →ₐ[ℝ] Matrix (Fin 32) (Fin 32) ℝ :=
  (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32))).toAlgHom.comp
    neutralCliffordRepCoordinate

@[simp] theorem neutralCliffordRepCoordinate_ι (w : NeutralSpace) :
    neutralCliffordRepCoordinate
        (CliffordAlgebra.ι
          (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
            (E := V5)) w) =
      spinorCoordinateEquiv.conjAlgEquiv ℝ (neutralAction w) := by
  change (spinorCoordinateEquiv.conjAlgEquiv ℝ)
      (neutralCliffordRep
        (CliffordAlgebra.ι
          (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
            (E := V5)) w)) = _
  rw [neutralCliffordRep_ι]

@[simp] theorem neutralCliffordCoordinateMatrixRep_ι (w : NeutralSpace) :
    neutralCliffordCoordinateMatrixRep
        (CliffordAlgebra.ι
          (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
            (E := V5)) w) =
      (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32)))
        (spinorCoordinateEquiv.conjAlgEquiv ℝ (neutralAction w)) := by
  change (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32)))
      (neutralCliffordRepCoordinate
        (CliffordAlgebra.ι
          (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
            (E := V5)) w)) = _
  rw [neutralCliffordRepCoordinate_ι]

end InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
