import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ChiralStokesPauliBasis
import InfoGeometry.Canonical.QutritWeylOperatorBasis

/-!
# The thirty-six Stokes–qutrit operator channels

`ChiralStokesPauliBasis` owns the four sheet Stokes channels and the sheet
tensor construction; `QutritWeylOperatorBasis` owns the nine discrete colour
channels `X^a Z^b`.  Separately they only give a *dimension count*.

This owner builds the actual product family and proves it is a basis of the
six-state operator algebra.  The `4 × 9 = 36` statement of the Stokes/qutrit
factorization therefore becomes a theorem about a concrete basis rather than an
equality of dimensions.

The proof route is Hilbert–Schmidt orthogonality: the sheet channels pair to
`2`, the colour words pair to `3`, and the sheet tensor multiplies traces, so
the thirty-six products pair to `6`.
-/

noncomputable section

namespace InfoGeometry.Canonical.StokesQutritChannelBasis

open Matrix
open scoped Kronecker
open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.TwoSheetStokesCoordinates
open InfoGeometry.Canonical.ChiralStokesPauliBasis
open InfoGeometry.Canonical.QutritWeylOperatorBasis

/-- The sheet tensor of `ChiralStokesPauliBasis` is the Kronecker product. -/
theorem sheetTensor_eq_kronecker (P : SheetMatrix) (A : M3C) :
    sheetTensor P A = P ⊗ₖ A := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  rfl

theorem sheetTensor_mul (P Q : SheetMatrix) (A B : M3C) :
    sheetTensor P A * sheetTensor Q B = sheetTensor (P * Q) (A * B) := by
  simp only [sheetTensor_eq_kronecker]
  exact (Matrix.mul_kronecker_mul P Q A B).symm

theorem sheetTensor_conjTranspose (P : SheetMatrix) (A : M3C) :
    (sheetTensor P A)ᴴ = sheetTensor Pᴴ Aᴴ := by
  simp only [sheetTensor_eq_kronecker]
  exact Matrix.conjTranspose_kronecker P A

theorem sheetTensor_trace (P : SheetMatrix) (A : M3C) :
    Matrix.trace (sheetTensor P A) = Matrix.trace P * Matrix.trace A := by
  simp only [sheetTensor_eq_kronecker]
  exact Matrix.trace_kronecker P A

/-- The four sheet Stokes channels in the order `I, Γ, J, Σ₂`. -/
def sheetChannel : Fin 4 → SheetMatrix :=
  ![sheetIdentity, sheetParity, sheetFlip, sheetPhase]

theorem sheetChannel_conjTranspose (μ : Fin 4) :
    (sheetChannel μ)ᴴ = sheetChannel μ := by
  fin_cases μ <;>
    · ext s t
      fin_cases s <;> fin_cases t <;>
        simp [sheetChannel, sheetIdentity, sheetParity, sheetFlip, sheetPhase,
          Matrix.conjTranspose]

/-- The four sheet channels are Hilbert–Schmidt orthogonal with uniform weight
`2`.  This is the sheet half of the thirty-six-channel Gram computation. -/
theorem sheetChannel_hs_orthogonal (μ ν : Fin 4) :
    Matrix.trace ((sheetChannel μ)ᴴ * sheetChannel ν) = if μ = ν then 2 else 0 := by
  rw [sheetChannel_conjTranspose]
  fin_cases μ <;> fin_cases ν <;>
    simp [sheetChannel, sheetIdentity, sheetParity, sheetFlip, sheetPhase,
      Matrix.trace, Fin.sum_univ_two] <;>
    ring_nf

/-- The thirty-six operator channels of the six-state carrier: a sheet Stokes
channel tensored with a discrete colour word. -/
def stokesWeylChannel (μ : Fin 4) (p : Fin 3 × Fin 3) : M6C :=
  sheetTensor (sheetChannel μ) (weylWord p.1 p.2)

theorem stokesWeylChannel_conjTranspose (μ : Fin 4) (p : Fin 3 × Fin 3) :
    (stokesWeylChannel μ p)ᴴ =
      sheetTensor (sheetChannel μ) ((weylWord p.1 p.2)ᴴ) := by
  rw [stokesWeylChannel, sheetTensor_conjTranspose, sheetChannel_conjTranspose]

/-- The full Gram computation: the thirty-six channels are Hilbert–Schmidt
orthogonal with uniform weight `2 * 3 = 6`. -/
theorem stokesWeylChannel_hs_orthogonal
    (μ ν : Fin 4) (p q : Fin 3 × Fin 3) :
    Matrix.trace ((stokesWeylChannel μ p)ᴴ * stokesWeylChannel ν q) =
      if μ = ν ∧ p = q then 6 else 0 := by
  rw [stokesWeylChannel_conjTranspose, stokesWeylChannel, sheetTensor_mul,
    sheetTensor_trace]
  rw [show (sheetChannel μ) * (sheetChannel ν) =
      (sheetChannel μ)ᴴ * sheetChannel ν by rw [sheetChannel_conjTranspose]]
  rw [sheetChannel_hs_orthogonal, weylWord_hs_orthogonal]
  by_cases hμ : μ = ν
  · by_cases hp : p.1 = q.1 ∧ p.2 = q.2
    · have hpq : p = q := Prod.ext hp.1 hp.2
      simp [hμ, hpq]
      norm_num
    · have hpq : p ≠ q := by
        intro hEq
        exact hp ⟨congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩
      rw [if_neg hp, if_neg (fun hcond : μ = ν ∧ p = q => hpq hcond.2), mul_zero]
  · simp [hμ]

theorem stokesWeylChannel_linearIndependent :
    LinearIndependent ℂ
      (fun x : Fin 4 × (Fin 3 × Fin 3) => stokesWeylChannel x.1 x.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c h x
  have hx := congrArg
    (fun M : M6C => Matrix.trace ((stokesWeylChannel x.1 x.2)ᴴ * M)) h
  change Matrix.trace
      ((stokesWeylChannel x.1 x.2)ᴴ *
        (∑ y : Fin 4 × (Fin 3 × Fin 3), c y • stokesWeylChannel y.1 y.2)) =
      Matrix.trace ((stokesWeylChannel x.1 x.2)ᴴ * 0) at hx
  rw [Matrix.mul_sum, Matrix.trace_sum] at hx
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_zero,
    Matrix.trace_zero] at hx
  simp_rw [stokesWeylChannel_hs_orthogonal] at hx
  have hcollapse :
      (∑ y : Fin 4 × (Fin 3 × Fin 3),
        c y * if x.1 = y.1 ∧ x.2 = y.2 then 6 else 0) = c x * 6 := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hne
      have hcond : ¬ (x.1 = y.1 ∧ x.2 = y.2) := by
        intro hcond
        exact hne (Prod.ext hcond.1.symm hcond.2.symm)
      simp [hcond]
    · simp
  rw [hcollapse] at hx
  exact (mul_eq_zero.mp hx).resolve_right (by norm_num)

/-- The Stokes/qutrit channel count: four sheet channels times nine colour
channels is exactly the complex dimension of the six-state operator algebra. -/
theorem stokesWeyl_channel_count :
    Fintype.card (Fin 4 × (Fin 3 × Fin 3)) = 4 * 9 ∧
      Fintype.card (Fin 4 × (Fin 3 × Fin 3)) = Module.finrank ℂ M6C := by
  refine ⟨by simp, ?_⟩
  simp [Module.finrank_matrix]

theorem stokesWeylChannel_span_eq_top :
    Submodule.span ℂ
        (Set.range (fun x : Fin 4 × (Fin 3 × Fin 3) =>
          stokesWeylChannel x.1 x.2)) = ⊤ := by
  apply stokesWeylChannel_linearIndependent.span_eq_top_of_card_eq_finrank
  simp [Module.finrank_matrix]

/-- The thirty-six Stokes–qutrit channels form a basis of the six-state
operator algebra. -/
def stokesWeylBasis :
    Module.Basis (Fin 4 × (Fin 3 × Fin 3)) ℂ M6C :=
  basisOfLinearIndependentOfCardEqFinrank stokesWeylChannel_linearIndependent (by
    simp [Module.finrank_matrix])

@[simp] theorem stokesWeylBasis_apply (x : Fin 4 × (Fin 3 × Fin 3)) :
    stokesWeylBasis x = stokesWeylChannel x.1 x.2 := by
  simp [stokesWeylBasis]

def stokesWeylCoefficient (A : M6C) (x : Fin 4 × (Fin 3 × Fin 3)) : ℂ :=
  (stokesWeylBasis.repr A) x

theorem stokesWeyl_expansion (A : M6C) :
    ∑ x : Fin 4 × (Fin 3 × Fin 3),
        stokesWeylCoefficient A x • stokesWeylChannel x.1 x.2 = A := by
  simpa [stokesWeylCoefficient] using Module.Basis.sum_repr stokesWeylBasis A

theorem stokesWeyl_expansion_unique (A : M6C)
    (c : Fin 4 × (Fin 3 × Fin 3) → ℂ)
    (h : ∑ x : Fin 4 × (Fin 3 × Fin 3), c x • stokesWeylChannel x.1 x.2 = A) :
    ∀ x, c x = stokesWeylCoefficient A x := by
  have hzero :
      ∑ x : Fin 4 × (Fin 3 × Fin 3),
          (c x - stokesWeylCoefficient A x) • stokesWeylChannel x.1 x.2 = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, h, stokesWeyl_expansion]
    simp
  have hcoeff :=
    (Fintype.linearIndependent_iff.mp stokesWeylChannel_linearIndependent)
      (fun x => c x - stokesWeylCoefficient A x) hzero
  intro x
  exact sub_eq_zero.mp (hcoeff x)

theorem stokesWeyl_trace_readout (A : M6C) (x : Fin 4 × (Fin 3 × Fin 3)) :
    Matrix.trace ((stokesWeylChannel x.1 x.2)ᴴ * A) =
      6 * stokesWeylCoefficient A x := by
  classical
  have h := congrArg
    (fun M : M6C => Matrix.trace ((stokesWeylChannel x.1 x.2)ᴴ * M))
    (stokesWeyl_expansion A)
  change Matrix.trace
      ((stokesWeylChannel x.1 x.2)ᴴ *
        (∑ y : Fin 4 × (Fin 3 × Fin 3),
          stokesWeylCoefficient A y • stokesWeylChannel y.1 y.2)) =
      Matrix.trace ((stokesWeylChannel x.1 x.2)ᴴ * A) at h
  rw [Matrix.mul_sum, Matrix.trace_sum] at h
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at h
  simp_rw [stokesWeylChannel_hs_orthogonal] at h
  have hcollapse :
      (∑ y : Fin 4 × (Fin 3 × Fin 3),
        stokesWeylCoefficient A y *
          if x.1 = y.1 ∧ x.2 = y.2 then 6 else 0) =
        6 * stokesWeylCoefficient A x := by
    rw [Finset.sum_eq_single x]
    · simp [mul_comm]
    · intro y _ hne
      have hcond : ¬ (x.1 = y.1 ∧ x.2 = y.2) := by
        intro hcond
        exact hne (Prod.ext hcond.1.symm hcond.2.symm)
      simp [hcond]
    · simp
  rw [hcollapse] at h
  exact h.symm

theorem stokesWeylCoefficient_eq_trace (A : M6C)
    (x : Fin 4 × (Fin 3 × Fin 3)) :
    stokesWeylCoefficient A x =
      (6 : ℂ)⁻¹ * Matrix.trace ((stokesWeylChannel x.1 x.2)ᴴ * A) := by
  rw [stokesWeyl_trace_readout]
  field_simp

/-! ## Compatibility with the owned Stokes coordinates -/

/-- The four Stokes coefficient matrices in the channel order `I, Γ, J, Σ₂`. -/
def stokesComponent (q : StokesQuad) : Fin 4 → M3C :=
  ![q.1, q.2.2.2, q.2.1, q.2.2.1]

/-- The Pauli expansion owned by `ChiralStokesPauliBasis` is exactly the sum
over the four sheet channels used here. -/
theorem pauliExpansion_eq_channel_sum (q : StokesQuad) :
    pauliExpansion q =
      ∑ μ : Fin 4, sheetTensor (sheetChannel μ) (stokesComponent q μ) := by
  rw [Fin.sum_univ_four]
  simp [pauliExpansion, sheetChannel, stokesComponent]

/-- Reassembling the Stokes coordinates of an operator returns the operator. -/
theorem assembleStokes_operatorStokes (A : M6C) :
    assembleStokes (operatorStokesLinearEquiv A) = A := by
  have hcoord : operatorStokesLinearEquiv A = blocksToStokes (blockLinearMap A) :=
    rfl
  rw [assembleStokes, hcoord, stokesToBlocks_blocksToStokes,
    blockLinearMapInv_blockLinearMap]

/-- Every six-state operator is the sum over its four sheet Stokes channels of
a sheet channel tensored with a colour coefficient matrix.  Together with the
nine-word colour expansion this is the `4 × 9 = 36` factorization. -/
theorem exists_channel_decomposition (A : M6C) :
    ∃ B : Fin 4 → M3C,
      A = ∑ μ : Fin 4, sheetTensor (sheetChannel μ) (B μ) := by
  refine ⟨stokesComponent (operatorStokesLinearEquiv A), ?_⟩
  rw [← pauliExpansion_eq_channel_sum, ← assembleStokes_eq_pauli_expansion,
    assembleStokes_operatorStokes]

end InfoGeometry.Canonical.StokesQutritChannelBasis

end noncomputable section
