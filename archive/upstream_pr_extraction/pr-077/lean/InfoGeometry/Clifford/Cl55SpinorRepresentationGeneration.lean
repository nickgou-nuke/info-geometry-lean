import InfoGeometry.Clifford.Cl55Q55NativeSplitBridge

open scoped BigOperators

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Clifford
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.GammaMatrices
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.ClNN

def localGammaSubalgebra :
    Subalgebra ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  Algebra.adjoin ℝ (Set.range (fun x : ℝ × ℝ =>
    x.1 • gammaPlusAtom + x.2 • gammaMinusAtom))

theorem localGammaSubalgebra_top : localGammaSubalgebra = ⊤ := by
  apply top_unique
  intro M _
  have hp : gammaPlusAtom ∈ localGammaSubalgebra := by
    apply Algebra.subset_adjoin
    exact ⟨(1, 0), by simp⟩
  have hm : gammaMinusAtom ∈ localGammaSubalgebra := by
    apply Algebra.subset_adjoin
    exact ⟨(0, 1), by simp⟩
  have h12 : gradingAtom ∈ localGammaSubalgebra := by
    change InfoGeometry.Clifford.GammaMatrices.gamma12 ∈ localGammaSubalgebra
    rw [InfoGeometry.Clifford.GammaMatrices.gamma12_eq]
    exact localGammaSubalgebra.mul_mem hp hm
  rw [Cl11Matrix.mat2_decompose M]
  exact localGammaSubalgebra.add_mem
    (localGammaSubalgebra.add_mem
      (localGammaSubalgebra.add_mem
        (localGammaSubalgebra.smul_mem localGammaSubalgebra.one_mem _)
        (localGammaSubalgebra.smul_mem hp _))
      (localGammaSubalgebra.smul_mem hm _))
    (localGammaSubalgebra.smul_mem h12 _)

def gammaTensorSubalgebra (n : ℕ) :
    Subalgebra ℝ (SplitGammaMatrix n) :=
  Algebra.adjoin ℝ (Set.range (recursiveGammaTensor n))

noncomputable def appendRightAlgHom (n : ℕ) :
    SplitGammaMatrix n →ₐ[ℝ] SplitGammaMatrix (n + 1) :=
  (Matrix.kroneckerAlgEquiv (TensorIndex n) (Fin 2) ℝ).toAlgHom.comp
    (Algebra.TensorProduct.includeLeft)

noncomputable def appendLeftAlgHom (n : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ] SplitGammaMatrix (n + 1) :=
  (Matrix.kroneckerAlgEquiv (TensorIndex n) (Fin 2) ℝ).toAlgHom.comp
    (Algebra.TensorProduct.includeRight)

@[simp] theorem appendRightAlgHom_apply (n : ℕ) (A : SplitGammaMatrix n) :
    appendRightAlgHom n A = appendAtom A (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  change (Matrix.kroneckerAlgEquiv (TensorIndex n) (Fin 2) ℝ)
      ((Algebra.TensorProduct.includeLeft :
        SplitGammaMatrix n →ₐ[ℝ]
          TensorProduct ℝ (SplitGammaMatrix n)
            (Matrix (Fin 2) (Fin 2) ℝ)) A) = _
  rw [Algebra.TensorProduct.includeLeft_apply]
  rfl

@[simp] theorem appendLeftAlgHom_apply (n : ℕ)
    (B : Matrix (Fin 2) (Fin 2) ℝ) :
    appendLeftAlgHom n B = appendAtom (1 : SplitGammaMatrix n) B := by
  change (Matrix.kroneckerAlgEquiv (TensorIndex n) (Fin 2) ℝ)
      ((Algebra.TensorProduct.includeRight :
        Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ]
          TensorProduct ℝ (SplitGammaMatrix n)
            (Matrix (Fin 2) (Fin 2) ℝ)) B) = _
  rw [Algebra.TensorProduct.includeRight_apply]
  rfl

theorem gammaTensorSubalgebra_top :
    ∀ n : ℕ, gammaTensorSubalgebra n = ⊤ := by
  intro n
  induction n with
  | zero =>
      apply top_unique
      intro M _
      have hscalar : M = (M () ()) • (1 : SplitGammaMatrix 0) := by
        ext i j
        cases i
        cases j
        simp
      rw [hscalar]
      exact (gammaTensorSubalgebra 0).smul_mem
        (gammaTensorSubalgebra 0).one_mem _
  | succ n ih =>
      let S : Subalgebra ℝ (SplitGammaMatrix (n + 1)) :=
        gammaTensorSubalgebra (n + 1)
      have hlocal_le : localGammaSubalgebra ≤ S.comap (appendLeftAlgHom n) := by
        apply Algebra.adjoin_le
        intro B hB
        rcases hB with ⟨⟨x₁, x₂⟩, rfl⟩
        change appendLeftAlgHom n
            (x₁ • gammaPlusAtom + x₂ • gammaMinusAtom) ∈ S
        rw [appendLeftAlgHom_apply]
        have hg : recursiveGammaTensor (n + 1)
              (headPair n ((x₁, x₂))) ∈ S :=
          Algebra.subset_adjoin ⟨headPair n ((x₁, x₂)), rfl⟩
        rw [recursiveGammaTensor_headPair] at hg
        simpa [headPair] using hg
      have htail_le : gammaTensorSubalgebra n ≤
          S.comap (appendRightAlgHom n) := by
        apply Algebra.adjoin_le
        intro A hA
        rcases hA with ⟨v, rfl⟩
        have hg : recursiveGammaTensor (n + 1) (splitTailLift v) ∈ S :=
          Algebra.subset_adjoin ⟨splitTailLift v, rfl⟩
        change recursiveGammaTensor (n + 1) ((0, 0), v) ∈ S at hg
        rw [recursiveGammaTensor_splitTailLift] at hg
        have hgrad : appendLeftAlgHom n gradingAtom ∈ S := by
          apply hlocal_le
          change InfoGeometry.Clifford.GammaMatrices.gamma12 ∈
            localGammaSubalgebra
          rw [InfoGeometry.Clifford.GammaMatrices.gamma12_eq]
          exact localGammaSubalgebra.mul_mem
            (by exact Algebra.subset_adjoin ⟨(1, 0), by simp⟩)
            (by exact Algebra.subset_adjoin ⟨(0, 1), by simp⟩)
        have hm := S.mul_mem hg hgrad
        simpa [appendRightAlgHom_apply, appendLeftAlgHom_apply,
          appendAtom_mul, gradingAtom_sq] using hm
      apply top_unique
      intro M _
      let e := Matrix.kroneckerAlgEquiv (TensorIndex n) (Fin 2) ℝ
      have hAll : ∀ z : TensorProduct ℝ (SplitGammaMatrix n)
          (Matrix (Fin 2) (Fin 2) ℝ), e z ∈ S := by
        intro z
        refine TensorProduct.induction_on z ?_ ?_ ?_
        · simpa using S.zero_mem
        · intro A B
          have hA : appendRightAlgHom n A ∈ S := by
            apply htail_le
            rw [ih]
            trivial
          have hB : appendLeftAlgHom n B ∈ S := by
            apply hlocal_le
            rw [localGammaSubalgebra_top]
            trivial
          rw [Matrix.kroneckerAlgEquiv_apply]
          change appendAtom A B ∈ S
          simpa [appendRightAlgHom_apply, appendLeftAlgHom_apply,
            appendAtom_mul] using S.mul_mem hA hB
        · intro x y hx hy
          simpa [e, map_add] using S.add_mem hx hy
      simpa [e] using hAll (e.symm M)

theorem splitSpinorRepresentation_surjective_of_gammaTensor (n : ℕ) :
    Function.Surjective
      (InfoGeometry.Clifford.SpinorRep.spinorRepresentation n) := by
  rw [InfoGeometry.Clifford.SpinorRep.spinorRepresentation_surjective_iff_gamma_generate]
  let e := InfoGeometry.Clifford.SpinorRep.tensorMatrixEquivFinPowTwo n
  let S : Subalgebra ℝ (InfoGeometry.Clifford.SpinorRep.SpinorMatrix n) :=
    Algebra.adjoin ℝ (Set.range
      (InfoGeometry.Clifford.SpinorRep.recursiveGamma n))
  have hgen : ∀ A : SplitGammaMatrix n,
      A ∈ gammaTensorSubalgebra n → e A ∈ S := by
    intro A hA
    refine Algebra.adjoin_induction (p := fun C _ => e C ∈ S)
      (mem := ?_) (algebraMap := ?_) (add := ?_) (mul := ?_) hA
    · intro x hx
      rcases hx with ⟨v, rfl⟩
      apply Algebra.subset_adjoin
      exact ⟨v, by rfl⟩
    · intro r
      simpa [e] using S.algebraMap_mem r
    · intro C D hC hD hCp hDp
      simpa using S.add_mem hCp hDp
    · intro C D hC hD hCp hDp
      simpa using S.mul_mem hCp hDp
  apply top_unique
  intro M _
  have hA : e.symm M ∈ gammaTensorSubalgebra n := by
    rw [gammaTensorSubalgebra_top n]
    trivial
  have hm := hgen (e.symm M) hA
  simpa [S, e] using hm

theorem splitSpinorRepresentation_surjective :
    Function.Surjective
      (InfoGeometry.Clifford.SpinorRep.spinorRepresentation 5) :=
  splitSpinorRepresentation_surjective_of_gammaTensor 5

theorem cl55SpinorRepresentation_surjective :
    Function.Surjective cl55SpinorRepresentation := by
  intro M
  obtain ⟨x, hx⟩ := splitSpinorRepresentation_surjective M
  obtain ⟨z, hz⟩ := cl55ToSplitCl55.surjective x
  refine ⟨z, ?_⟩
  exact (congrArg
    (fun a => InfoGeometry.Clifford.SpinorRep.spinorRepresentation 5 a)
    hz).trans hx

end InfoGeometry.Clifford.Clifford55
