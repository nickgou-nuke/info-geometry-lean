import InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge

abbrev PaperZorn :=
  InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.PaperZorn
abbrev CanonicalZorn :=
  InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn
abbrev Der := InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations

open InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge

local instance paperZornAdd : Add PaperZorn :=
  InfoGeometry.Algebra.ZornMatrix.instAddCommGroup.toAdd

@[simp] theorem paperCanonicalLinearEquiv_zero :
    paperCanonicalLinearEquiv (0 : PaperZorn) = (0 : CanonicalZorn) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

noncomputable def paperDerivation (D : Der) : Module.End ℝ PaperZorn :=
  (paperCanonicalLinearEquiv.symm.toLinearMap.comp D.1).comp
    paperCanonicalLinearEquiv.toLinearMap

noncomputable def paperDerivationLinear :
    Der →ₗ[ℝ] Module.End ℝ PaperZorn where
  toFun := paperDerivation
  map_add' D E := by
    apply LinearMap.ext
    intro X
    apply paperCanonicalLinearEquiv.injective
    simp [paperDerivation, LinearMap.comp_apply]
  map_smul' r D := by
    apply LinearMap.ext
    intro X
    apply paperCanonicalLinearEquiv.injective
    simp [paperDerivation, LinearMap.comp_apply]

@[simp] theorem paperDerivation_apply (D : Der) (X : PaperZorn) :
    paperDerivation D X =
      paperCanonicalLinearEquiv.symm (D.1 (paperCanonicalLinearEquiv X)) := rfl

@[simp] theorem paperDerivation_map_one (D : Der) :
    paperDerivation D (InfoGeometry.Algebra.ZornMatrix.I : PaperZorn) = 0 := by
  apply paperCanonicalLinearEquiv.injective
  rw [paperDerivation_apply]
  rw [paperCanonicalLinearEquiv.apply_symm_apply, paperCanonicalLinearEquiv_zero]
  have hI :
      paperCanonicalLinearEquiv (InfoGeometry.Algebra.ZornMatrix.I : PaperZorn) =
        (1 : CanonicalZorn) := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  rw [hI]
  change D.1 (1 : CanonicalZorn) = 0
  apply InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.injective
  change InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv
      (D.1 (1 : CanonicalZorn)) =
    InfoGeometry.Algebra.ZornVectorMatrix.zero
  simpa [InfoGeometry.Lie.CanonicalZornDerivation.canonicalToVectorDerivation_apply] using
    (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.map_one
      (InfoGeometry.Lie.CanonicalZornDerivation.canonicalToVectorDerivation D))

theorem canonicalDerivation_conj_norm_identity_left
    (D : Der) (X : CanonicalZorn) :
    D.1 X *
          InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj X +
        X * D.1 (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj X) =
      0 := by
  apply InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.injective
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_add,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_canonicalConj,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_zero]
  have h :=
    InfoGeometry.Algebra.ZornVectorMatrix.Derivation.derivation_conj_norm_identity_left
      (InfoGeometry.Lie.CanonicalZornDerivation.canonicalToVectorDerivation D)
      (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv X)
  simpa [InfoGeometry.Lie.CanonicalZornDerivation.canonicalToVectorDerivation_apply] using h

theorem canonicalDerivation_conj_norm_identity_right
    (D : Der) (X : CanonicalZorn) :
    D.1 (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj X) * X +
          InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj X * D.1 X =
      0 := by
  apply InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.injective
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_add,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_canonicalConj,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_zero]
  have h :=
    InfoGeometry.Algebra.ZornVectorMatrix.Derivation.derivation_conj_norm_identity_right
      (InfoGeometry.Lie.CanonicalZornDerivation.canonicalToVectorDerivation D)
      (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv X)
  simpa [InfoGeometry.Lie.CanonicalZornDerivation.canonicalToVectorDerivation_apply] using h

def paperConj (X : PaperZorn) : PaperZorn where
  a := X.b
  v := -X.v
  w := -X.w
  b := X.a

theorem paperCanonicalLinearEquiv_paperConj (X : PaperZorn) :
    paperCanonicalLinearEquiv (paperConj X) =
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj
        (paperCanonicalLinearEquiv X) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    rfl
  · funext i
    rfl

theorem paperDerivation_isDerivation (D : Der) :
    ∀ X Y : PaperZorn,
      paperDerivation D (X * Y) =
        paperDerivation D X * Y + X * paperDerivation D Y := by
  intro X Y
  apply paperCanonicalLinearEquiv.injective
  calc
    paperCanonicalLinearEquiv (paperDerivation D (X * Y)) =
        D.1 (paperCanonicalLinearEquiv X * paperCanonicalLinearEquiv Y) := by
      rw [paperDerivation_apply,
        paperCanonicalLinearEquiv.apply_symm_apply,
        paperCanonicalLinearEquiv_mul]
    _ = D.1 (paperCanonicalLinearEquiv X) * paperCanonicalLinearEquiv Y +
          paperCanonicalLinearEquiv X * D.1 (paperCanonicalLinearEquiv Y) :=
      D.property _ _
    _ = paperCanonicalLinearEquiv
          (paperDerivation D X * Y + X * paperDerivation D Y) := by
      symm
      calc
        paperCanonicalLinearEquiv
              (paperDerivation D X * Y + X * paperDerivation D Y) =
            paperCanonicalLinearEquiv (paperDerivation D X * Y) +
              paperCanonicalLinearEquiv (X * paperDerivation D Y) :=
          paperCanonicalLinearEquiv.map_add _ _
        _ = D.1 (paperCanonicalLinearEquiv X) * paperCanonicalLinearEquiv Y +
              paperCanonicalLinearEquiv X * D.1 (paperCanonicalLinearEquiv Y) := by
          rw [paperCanonicalLinearEquiv_mul, paperCanonicalLinearEquiv_mul,
            paperDerivation_apply, paperDerivation_apply,
            paperCanonicalLinearEquiv.apply_symm_apply,
            paperCanonicalLinearEquiv.apply_symm_apply]

theorem paperDerivation_conj_norm_identity_left
    (D : Der) (X : PaperZorn) :
    paperDerivation D X * paperConj X + X * paperDerivation D (paperConj X) =
      0 := by
  apply paperCanonicalLinearEquiv.injective
  rw [paperCanonicalLinearEquiv.map_add,
    paperCanonicalLinearEquiv_mul,
    paperCanonicalLinearEquiv_mul,
    paperCanonicalLinearEquiv_paperConj]
  rw [paperDerivation_apply, paperDerivation_apply,
    paperCanonicalLinearEquiv.apply_symm_apply,
    paperCanonicalLinearEquiv.apply_symm_apply,
    paperCanonicalLinearEquiv_paperConj]
  rw [paperCanonicalLinearEquiv_zero]
  exact canonicalDerivation_conj_norm_identity_left D (paperCanonicalLinearEquiv X)

theorem paperDerivation_conj_norm_identity_right
    (D : Der) (X : PaperZorn) :
    paperDerivation D (paperConj X) * X + paperConj X * paperDerivation D X =
      0 := by
  apply paperCanonicalLinearEquiv.injective
  rw [paperCanonicalLinearEquiv.map_add,
    paperCanonicalLinearEquiv_mul,
    paperCanonicalLinearEquiv_mul,
    paperCanonicalLinearEquiv_paperConj]
  rw [paperDerivation_apply, paperDerivation_apply,
    paperCanonicalLinearEquiv.apply_symm_apply,
    paperCanonicalLinearEquiv.apply_symm_apply,
    paperCanonicalLinearEquiv_paperConj]
  rw [paperCanonicalLinearEquiv_zero]
  exact canonicalDerivation_conj_norm_identity_right D (paperCanonicalLinearEquiv X)

theorem paperDerivation_map_conj (D : Der) (X : PaperZorn) :
    paperDerivation D (paperConj X) = -paperDerivation D X := by
  have hcanonical (Y : CanonicalZorn) :
      D.1 (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj Y) =
        -D.1 Y := by
    apply InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.injective
    change InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv
        (D.1 (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj Y)) =
      InfoGeometry.Algebra.ZornVectorMatrix.neg
        (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv (D.1 Y))
    have h :=
      InfoGeometry.Algebra.ZornVectorMatrix.Derivation.map_conj_eq_neg
        (InfoGeometry.Lie.CanonicalZornDerivation.canonicalToVectorDerivation D)
        (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv Y)
    rw [← InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_canonicalConj]
      at h
    exact h
  apply paperCanonicalLinearEquiv.injective
  calc
    paperCanonicalLinearEquiv (paperDerivation D (paperConj X)) =
        D.1 (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj
          (paperCanonicalLinearEquiv X)) := by
      rw [paperDerivation_apply, paperCanonicalLinearEquiv_paperConj,
        paperCanonicalLinearEquiv.apply_symm_apply]
    _ = -D.1 (paperCanonicalLinearEquiv X) := by
      exact hcanonical (paperCanonicalLinearEquiv X)
    _ = paperCanonicalLinearEquiv (-paperDerivation D X) := by
      simp only [map_neg, paperDerivation_apply,
        paperCanonicalLinearEquiv.apply_symm_apply]

theorem paperDerivation_lie (D E : Der) :
    paperDerivation ⁅D, E⁆ = ⁅paperDerivation D, paperDerivation E⁆ := by
  apply LinearMap.ext
  intro X
  apply paperCanonicalLinearEquiv.injective
  simp [paperDerivation, LinearMap.comp_apply,
    LieRing.of_associative_ring_bracket,
    paperCanonicalLinearEquiv.apply_symm_apply]

noncomputable def paperDerivationLieHom :
    Der →ₗ⁅ℝ⁆ Module.End ℝ PaperZorn :=
  { paperDerivationLinear with
    map_lie' := by
      intro D E
      exact paperDerivation_lie D E }

abbrev PaperDer := (paperDerivationLieHom).range

theorem paperDerivationLieHom_injective :
    Function.Injective paperDerivationLieHom := by
  intro D E h
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  have hX := LinearMap.congr_fun h (paperCanonicalLinearEquiv.symm X)
  have hX' := congrArg paperCanonicalLinearEquiv hX
  simpa [paperDerivationLieHom, paperDerivationLinear, paperDerivation,
    LinearMap.comp_apply, paperCanonicalLinearEquiv.apply_symm_apply] using hX'

noncomputable def paperDerivationLieEquiv :
    Der ≃ₗ⁅ℝ⁆ (paperDerivationLieHom).range :=
  LieEquiv.ofInjective paperDerivationLieHom paperDerivationLieHom_injective

noncomputable def paperDerivationBasis :
    Module.Basis (Fin 14) ℝ (paperDerivationLieHom).range :=
  InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis.map
    paperDerivationLieEquiv.toLinearEquiv

theorem paperDerivationBasis_apply (j : Fin 14) :
    paperDerivationBasis j =
      paperDerivationLieEquiv
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j) := by
  rw [paperDerivationBasis, Module.Basis.map_apply]
  rfl

noncomputable def paperAdCartan (k : InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.TracelessWeight) :
    Module.End ℝ PaperDer where
  toFun X :=
    paperDerivationLieEquiv
      (InfoGeometry.Lie.CanonicalZornCartanAdjointAction.adCartan k
        (paperDerivationLieEquiv.symm X))
  map_add' X Y := by
    simp [InfoGeometry.Lie.CanonicalZornCartanAdjointAction.adCartan,
      map_add]
  map_smul' r X := by
    simp [InfoGeometry.Lie.CanonicalZornCartanAdjointAction.adCartan,
      map_smul]

/-! The transported Cartan action is literally the Lie bracket with the
    transported Cartan derivation. -/
theorem paperAdCartan_eq_lie
    (k : InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.TracelessWeight)
    (X : PaperDer) :
    paperAdCartan k X =
      ⁅paperDerivationLieEquiv
          (InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieEquiv k), X⁆ := by
  change paperDerivationLieEquiv
      (InfoGeometry.Lie.CanonicalZornCartanAdjointAction.adCartan k
        (paperDerivationLieEquiv.symm X)) = _
  have hX : X = paperDerivationLieEquiv (paperDerivationLieEquiv.symm X) :=
    (paperDerivationLieEquiv.apply_symm_apply X).symm
  conv_rhs => rw [hX]
  rw [← paperDerivationLieEquiv.map_lie]
  simp

theorem paperAdCartan_paperDerivationBasis
    (k : InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.TracelessWeight)
    (j : Fin 14) :
    paperAdCartan k (paperDerivationBasis j) =
      ((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootWeight j k : ℝ) •
        paperDerivationBasis j : PaperDer) := by
  change paperDerivationLieEquiv
      (InfoGeometry.Lie.CanonicalZornCartanAdjointAction.adCartan k
        (paperDerivationLieEquiv.symm (paperDerivationBasis j))) = _
  rw [paperDerivationBasis_apply j, paperDerivationLieEquiv.symm_apply_apply]
  calc
    _ = paperDerivationLieEquiv
        (((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootWeight j k : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis j)) :=
      congrArg paperDerivationLieEquiv
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis_is_simultaneous_eigenbasis j k)
    _ = _ := map_smul _ _ _

theorem paperCartanBracket_paperDerivationBasis
    (k : InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.TracelessWeight)
    (j : Fin 14) :
    ⁅paperDerivationLieEquiv
        (InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieEquiv k),
      paperDerivationBasis j⁆ =
      ((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootWeight j k : ℝ) •
        paperDerivationBasis j : PaperDer) := by
  rw [← paperAdCartan_eq_lie]
  exact paperAdCartan_paperDerivationBasis k j

theorem finrank_paperDerivationRange :
    Module.finrank ℝ (paperDerivationLieHom).range = 14 := by
  rw [← paperDerivationLieEquiv.toLinearEquiv.finrank_eq]
  exact InfoGeometry.Lie.CanonicalZornDerivationDimension.finrank_canonicalZornDerivations

end InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge
