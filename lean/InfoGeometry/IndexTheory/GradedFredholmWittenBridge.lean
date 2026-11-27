/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.IndexTheory.AtiyahSingerDirac
import InfoGeometry.NCG.NonCommutativeFredholmIndex
import InfoGeometry.Algebra.FiniteSUSYBlocks
import InfoGeometry.Quantum.SUSYHilbertWittenIndex

/-!
# 2-Term Graded Fredholm Complexes and the Witten Index Bridge

Formalization of Kudinoor (2023), *Supersymmetry and the Witten Index*, §2:

1. **2-term graded Fredholm complex** (`GradedFredholmComplex H_pos H_neg`): bounded operator
   `D_+ : H_pos →L[ℂ] H_neg` between complex Hilbert spaces with adjoint `D_- = D_+†` and
   finite-dimensional kernels `ker D_+` and `ker D_-`.
2. **Laplacian index equals Fredholm index** (`laplacianIndex_eq_fredholmIndex`): using
   `ContinuousLinearMap.ker_adjoint_comp_self` and `ContinuousLinearMap.ker_self_comp_adjoint`,
   `dim ker (D_- ∘L D_+) - dim ker (D_+ ∘L D_-) = dim ker D_+ - dim ker D_-`, and in finite
   dimensions `fredholmIndex_eq_finrank_sub` establishes `ind(D_+) = dim H_pos - dim H_neg`.
3. **SUSY Hilbert realization** (`toSUSYQuantumSystem`): on `WithLp 2 (H_pos × H_neg)`,
   `K = blockDiag 1 (-1)`, `Q_0 = blockOffDiag D_+ D_-`, and
   `H = Q_0 ∘L Q_0 = blockDiag (D_- ∘L D_+) (D_+ ∘L D_-)` form an `N = 1` supersymmetric
   quantum system whose Witten index equals `C.fredholmIndex`
   (`toSUSYQuantumSystem_wittenIndex_eq_fredholmIndex`). Notice the consistent normalization
   `H = Q_0 ∘L Q_0` matching `{Q_0, Q_0} = 2 H`.
4. **Repository bridges**: connects to `InfoGeometry.Canonical.AtiyahSingerDirac` (`dirac_sq_grading_commutes`
   and `mckean_singer_algebraic_cancellation`), `InfoGeometry.Algebra.FiniteSUSY` (matrix blocks
   and partner intertwining), and `InfoGeometry.NCG.NonCommutativeFredholmIndex`
   (`connes_chern_index_pairing_formula` instantiated on `Fin 2 ⊕ Fin 2` with index `1`).
5. **Scope boundary for smooth spin-manifold `Â(M)`**: Kudinoor §2.1–2.2 also discusses the
   analytic Atiyah–Singer formula `index(D) = ∫_M ch(E) Â(M)` and `index(Q) = Â(M)` for the
   `N = 1` nonlinear sigma model on smooth compact even-dimensional spin manifolds. Smooth
   spinor bundles, characteristic forms `ch(E)` and `Â(M)`, and heat-kernel PDE asymptotics
   remain a long-term Mathlib differential-geometry frontier outside the Hilbert-space and
   finite-matrix theorems established here.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate Matrix
open Complex
open InfoGeometry.Quantum.SUSYHilbertWittenIndex

namespace InfoGeometry.IndexTheory.GradedFredholmWittenBridge

section FredholmComplex

variable {H_pos H_neg : Type*}
  [NormedAddCommGroup H_pos] [InnerProductSpace ℂ H_pos] [CompleteSpace H_pos]
  [NormedAddCommGroup H_neg] [InnerProductSpace ℂ H_neg] [CompleteSpace H_neg]

/-- A 2-term graded Hilbert-space Fredholm complex `D_+ : H_pos →L[ℂ] H_neg` with adjoint
`D_- = D_+†` and finite-dimensional kernels `ker D_+` and `ker D_-`. -/
structure GradedFredholmComplex (H_pos H_neg : Type*)
    [NormedAddCommGroup H_pos] [InnerProductSpace ℂ H_pos] [CompleteSpace H_pos]
    [NormedAddCommGroup H_neg] [InnerProductSpace ℂ H_neg] [CompleteSpace H_neg] where
  D_pos : H_pos →L[ℂ] H_neg
  finDim_ker_pos : FiniteDimensional ℂ D_pos.ker
  finDim_ker_neg : FiniteDimensional ℂ (ContinuousLinearMap.adjoint D_pos).ker

namespace GradedFredholmComplex

variable (C : GradedFredholmComplex H_pos H_neg)

/-- Adjoint operator `D_- = D_+† : H_neg →L[ℂ] H_pos`. -/
abbrev D_neg : H_neg →L[ℂ] H_pos :=
  ContinuousLinearMap.adjoint C.D_pos

/-- Positive-chirality Laplacian `D_- ∘L D_+ : H_pos →L[ℂ] H_pos`. -/
def laplacianPos : H_pos →L[ℂ] H_pos :=
  C.D_neg ∘L C.D_pos

/-- Negative-chirality Laplacian `D_+ ∘L D_- : H_neg →L[ℂ] H_neg`. -/
def laplacianNeg : H_neg →L[ℂ] H_neg :=
  C.D_pos ∘L C.D_neg

theorem ker_laplacianPos_eq : C.laplacianPos.ker = C.D_pos.ker :=
  ContinuousLinearMap.ker_adjoint_comp_self C.D_pos

theorem ker_laplacianNeg_eq : C.laplacianNeg.ker = C.D_neg.ker :=
  ContinuousLinearMap.ker_self_comp_adjoint C.D_pos

/-- Partner intertwining of the chiral Laplacians: `D_+ ∘L (D_- ∘L D_+) = (D_+ ∘L D_-) ∘L D_+`. -/
theorem partner_intertwining :
    C.D_pos ∘L C.laplacianPos = C.laplacianNeg ∘L C.D_pos := by
  simp only [laplacianPos, laplacianNeg, ContinuousLinearMap.comp_assoc]

/-- Analytic Fredholm index `ind(D_+) = dim ker D_+ - dim ker D_-`. -/
def fredholmIndex : ℤ :=
  (Module.finrank ℂ C.D_pos.ker : ℤ) - (Module.finrank ℂ C.D_neg.ker : ℤ)

/-- Laplacian supertrace index equals Fredholm index in arbitrary Hilbert spaces:
`dim ker (D_- ∘L D_+) - dim ker (D_+ ∘L D_-) = dim ker D_+ - dim ker D_-`. -/
theorem laplacianIndex_eq_fredholmIndex :
    (Module.finrank ℂ C.laplacianPos.ker : ℤ) - (Module.finrank ℂ C.laplacianNeg.ker : ℤ) =
      C.fredholmIndex := by
  rw [C.ker_laplacianPos_eq, C.ker_laplacianNeg_eq]
  rfl

/-- Finite-dimensional rank-nullity form (Kudinoor Prop. 1.4):
`ind(D_+) = dim H_pos - dim H_neg`. -/
theorem fredholmIndex_eq_finrank_sub
    [FiniteDimensional ℂ H_pos] [FiniteDimensional ℂ H_neg] :
    C.fredholmIndex = (Module.finrank ℂ H_pos : ℤ) - (Module.finrank ℂ H_neg : ℤ) := by
  have h_pos := LinearMap.finrank_range_add_finrank_ker (C.D_pos : H_pos →ₗ[ℂ] H_neg)
  have h_neg := LinearMap.finrank_range_add_finrank_ker (C.D_neg : H_neg →ₗ[ℂ] H_pos)
  have h_adj_range :
      Module.finrank ℂ (LinearMap.range (C.D_neg : H_neg →ₗ[ℂ] H_pos)) =
        Module.finrank ℂ (LinearMap.range (C.D_pos : H_pos →ₗ[ℂ] H_neg)) := by
    have h_coe : (C.D_neg : H_neg →ₗ[ℂ] H_pos) =
        LinearMap.adjoint (C.D_pos : H_pos →ₗ[ℂ] H_neg) := by
      ext y
      refine ext_inner_left ℂ fun x => ?_
      change ⟪x, C.D_neg y⟫_ℂ = ⟪x, LinearMap.adjoint (C.D_pos : H_pos →ₗ[ℂ] H_neg) y⟫_ℂ
      rw [ContinuousLinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
      rfl
    rw [h_coe]
    exact LinearMap.finrank_range_adjoint (C.D_pos : H_pos →ₗ[ℂ] H_neg)
  have h_pos_z :
      (Module.finrank ℂ (LinearMap.range (C.D_pos : H_pos →ₗ[ℂ] H_neg)) : ℤ) +
        (Module.finrank ℂ C.D_pos.ker : ℤ) = (Module.finrank ℂ H_pos : ℤ) := by
    exact_mod_cast h_pos
  have h_neg_z :
      (Module.finrank ℂ (LinearMap.range (C.D_neg : H_neg →ₗ[ℂ] H_pos)) : ℤ) +
        (Module.finrank ℂ C.D_neg.ker : ℤ) = (Module.finrank ℂ H_neg : ℤ) := by
    exact_mod_cast h_neg
  have h_range_z :
      (Module.finrank ℂ (LinearMap.range (C.D_neg : H_neg →ₗ[ℂ] H_pos)) : ℤ) =
        (Module.finrank ℂ (LinearMap.range (C.D_pos : H_pos →ₗ[ℂ] H_neg)) : ℤ) := by
    exact_mod_cast h_adj_range
  unfold fredholmIndex
  omega

end GradedFredholmComplex

end FredholmComplex

section BlockOperators

variable {H_pos H_neg : Type*}
  [NormedAddCommGroup H_pos] [InnerProductSpace ℂ H_pos] [CompleteSpace H_pos]
  [NormedAddCommGroup H_neg] [InnerProductSpace ℂ H_neg] [CompleteSpace H_neg]

/-- Diagonal block operator `diag(A, B)` on `WithLp 2 (H_pos × H_neg)`. -/
def blockDiag (A : H_pos →L[ℂ] H_pos) (B : H_neg →L[ℂ] H_neg) :
    WithLp 2 (H_pos × H_neg) →L[ℂ] WithLp 2 (H_pos × H_neg) where
  toFun x := WithLp.toLp 2 (A x.ofLp.1, B x.ofLp.2)
  map_add' _ _ := WithLp.ofLp_injective 2 (Prod.ext (map_add A _ _) (map_add B _ _))
  map_smul' _ _ := WithLp.ofLp_injective 2 (Prod.ext (map_smul A _ _) (map_smul B _ _))
  cont := by
    refine (WithLp.prodContinuousLinearEquiv 2 ℂ H_pos H_neg).symm.continuous.comp ?_
    exact Continuous.prodMk
      (A.continuous.comp (WithLp.fstL 2 ℂ H_pos H_neg).continuous)
      (B.continuous.comp (WithLp.sndL 2 ℂ H_pos H_neg).continuous)

/-- Off-diagonal block operator `[[0, S], [T, 0]]` on `WithLp 2 (H_pos × H_neg)`. -/
def blockOffDiag (T : H_pos →L[ℂ] H_neg) (S : H_neg →L[ℂ] H_pos) :
    WithLp 2 (H_pos × H_neg) →L[ℂ] WithLp 2 (H_pos × H_neg) where
  toFun x := WithLp.toLp 2 (S x.ofLp.2, T x.ofLp.1)
  map_add' _ _ := WithLp.ofLp_injective 2 (Prod.ext (map_add S _ _) (map_add T _ _))
  map_smul' _ _ := WithLp.ofLp_injective 2 (Prod.ext (map_smul S _ _) (map_smul T _ _))
  cont := by
    refine (WithLp.prodContinuousLinearEquiv 2 ℂ H_pos H_neg).symm.continuous.comp ?_
    exact Continuous.prodMk
      (S.continuous.comp (WithLp.sndL 2 ℂ H_pos H_neg).continuous)
      (T.continuous.comp (WithLp.fstL 2 ℂ H_pos H_neg).continuous)

@[simp]
theorem blockDiag_apply (A : H_pos →L[ℂ] H_pos) (B : H_neg →L[ℂ] H_neg)
    (x : WithLp 2 (H_pos × H_neg)) :
    blockDiag A B x = WithLp.toLp 2 (A x.ofLp.1, B x.ofLp.2) := rfl

@[simp]
theorem blockOffDiag_apply (T : H_pos →L[ℂ] H_neg) (S : H_neg →L[ℂ] H_pos)
    (x : WithLp 2 (H_pos × H_neg)) :
    blockOffDiag T S x = WithLp.toLp 2 (S x.ofLp.2, T x.ofLp.1) := rfl

namespace GradedFredholmComplex

variable (C : GradedFredholmComplex H_pos H_neg)

/-- Canonical `ℤ₂`-grading operator `K = diag(I, -I)` on `WithLp 2 (H_pos × H_neg)`. -/
def gradingOp (_C : GradedFredholmComplex H_pos H_neg) :
    WithLp 2 (H_pos × H_neg) →L[ℂ] WithLp 2 (H_pos × H_neg) :=
  blockDiag (ContinuousLinearMap.id ℂ H_pos) (-ContinuousLinearMap.id ℂ H_neg)

/-- Self-adjoint odd supercharge / Dirac operator `Q_0 = [[0, D_-], [D_+, 0]]`. -/
def diracOp : WithLp 2 (H_pos × H_neg) →L[ℂ] WithLp 2 (H_pos × H_neg) :=
  blockOffDiag C.D_pos C.D_neg

/-- Supersymmetric Hamiltonian `H = Q_0 ∘L Q_0 = diag(D_- D_+, D_+ D_-)`. -/
def hamiltonianOp : WithLp 2 (H_pos × H_neg) →L[ℂ] WithLp 2 (H_pos × H_neg) :=
  C.diracOp ∘L C.diracOp

theorem gradingOp_selfAdjoint : IsSelfAdjoint C.gradingOp := by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
  change ⟪WithLp.toLp 2 (x.ofLp.1, -x.ofLp.2), y⟫_ℂ =
    ⟪x, WithLp.toLp 2 (y.ofLp.1, -y.ofLp.2)⟫_ℂ
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp only [inner_neg_left, inner_neg_right]

theorem gradingOp_involution :
    C.gradingOp ∘L C.gradingOp = ContinuousLinearMap.id ℂ (WithLp 2 (H_pos × H_neg)) := by
  apply ContinuousLinearMap.ext; intro x
  apply WithLp.ofLp_injective 2
  exact Prod.ext rfl (neg_neg _)

theorem diracOp_selfAdjoint : IsSelfAdjoint C.diracOp := by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
  change ⟪WithLp.toLp 2 (C.D_neg x.ofLp.2, C.D_pos x.ofLp.1), y⟫_ℂ =
    ⟪x, WithLp.toLp 2 (C.D_neg y.ofLp.2, C.D_pos y.ofLp.1)⟫_ℂ
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.adjoint_inner_right, add_comm]

theorem diracOp_odd : C.diracOp ∘L C.gradingOp = -(C.gradingOp ∘L C.diracOp) := by
  apply ContinuousLinearMap.ext; intro x
  apply WithLp.ofLp_injective 2
  exact Prod.ext (by simp [diracOp, gradingOp]) (by simp [diracOp, gradingOp])

theorem diracOp_sq_eq_blockDiag :
    C.diracOp ∘L C.diracOp = blockDiag C.laplacianPos C.laplacianNeg := by
  apply ContinuousLinearMap.ext; intro x
  apply WithLp.ofLp_injective 2
  exact Prod.ext rfl rfl

theorem hamiltonianOp_selfAdjoint : IsSelfAdjoint C.hamiltonianOp := by
  have hD := C.diracOp_selfAdjoint
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hD ⊢
  simp only [hamiltonianOp, ContinuousLinearMap.adjoint_comp, hD]

theorem hamiltonianOp_even : C.hamiltonianOp ∘L C.gradingOp = C.gradingOp ∘L C.hamiltonianOp := by
  apply ContinuousLinearMap.ext; intro x
  apply WithLp.ofLp_injective 2
  exact Prod.ext (by simp [hamiltonianOp, diracOp, gradingOp])
    (by simp [hamiltonianOp, diracOp, gradingOp])

/-- Construct the canonical `N = 1` supersymmetric quantum system on `WithLp 2 (H_pos × H_neg)`
from any 2-term graded Fredholm complex. -/
def toSUSYQuantumSystem : SUSYQuantumSystem 1 (WithLp 2 (H_pos × H_neg)) where
  K := C.gradingOp
  K_selfAdjoint := C.gradingOp_selfAdjoint
  K_involution := C.gradingOp_involution
  H := C.hamiltonianOp
  H_selfAdjoint := C.hamiltonianOp_selfAdjoint
  H_even := C.hamiltonianOp_even
  Q _ := C.diracOp
  Q_selfAdjoint _ := C.diracOp_selfAdjoint
  Q_odd _ := C.diracOp_odd
  superalgebra i j := by
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp only [↓reduceIte]
    rw [two_smul]
    rfl

private def zeroBosonEquivKerPos :
    C.toSUSYQuantumSystem.bosonicEigenspace 0 ≃ₗ[ℂ] C.D_pos.ker where
  toFun x := ⟨x.1.ofLp.1, by
    have hx := (C.toSUSYQuantumSystem.mem_bosonicEigenspace_iff.mp x.2).1
    have hx_lap : C.laplacianPos x.1.ofLp.1 = 0 := by
      have h1 := congr_arg (fun v : WithLp 2 (H_pos × H_neg) => v.ofLp.1) hx
      simpa [toSUSYQuantumSystem, hamiltonianOp, diracOp_sq_eq_blockDiag] using h1
    rw [← C.ker_laplacianPos_eq]
    exact hx_lap⟩
  invFun u := ⟨WithLp.toLp 2 (u.1, 0), by
    rw [C.toSUSYQuantumSystem.mem_bosonicEigenspace_iff]
    refine ⟨?_, ?_⟩
    · apply WithLp.ofLp_injective 2
      simp only [toSUSYQuantumSystem, hamiltonianOp, C.diracOp_sq_eq_blockDiag, blockDiag_apply,
        WithLp.ofLp_toLp, Complex.coe_smul, zero_smul]
      refine Prod.ext ?_ ?_
      · have hu : u.1 ∈ C.laplacianPos.ker := C.ker_laplacianPos_eq.symm ▸ u.2
        simpa using hu
      · simp
    · apply WithLp.ofLp_injective 2
      simp [toSUSYQuantumSystem, gradingOp]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    have hxK := (C.toSUSYQuantumSystem.mem_bosonicEigenspace_iff.mp x.2).2
    have hx2 : -x.1.ofLp.2 = x.1.ofLp.2 := by
      have h2 := congr_arg (fun v : WithLp 2 (H_pos × H_neg) => v.ofLp.2) hxK
      simpa [toSUSYQuantumSystem, gradingOp] using h2
    have hzero : x.1.ofLp.2 = 0 := by
      have h2 : (2 : ℂ) • x.1.ofLp.2 = 0 := by
        calc (2 : ℂ) • x.1.ofLp.2 = x.1.ofLp.2 + x.1.ofLp.2 := two_smul ℂ _
          _ = x.1.ofLp.2 + -x.1.ofLp.2 := by nth_rw 2 [← hx2]
          _ = 0 := add_neg_cancel _
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    exact Prod.ext rfl hzero.symm
  right_inv _ := rfl

private def zeroFermionEquivKerNeg :
    C.toSUSYQuantumSystem.fermionicEigenspace 0 ≃ₗ[ℂ] C.D_neg.ker where
  toFun x := ⟨x.1.ofLp.2, by
    have hx := (C.toSUSYQuantumSystem.mem_fermionicEigenspace_iff.mp x.2).1
    have hx_lap : C.laplacianNeg x.1.ofLp.2 = 0 := by
      have h2 := congr_arg (fun v : WithLp 2 (H_pos × H_neg) => v.ofLp.2) hx
      simpa [toSUSYQuantumSystem, hamiltonianOp, diracOp_sq_eq_blockDiag] using h2
    rw [← C.ker_laplacianNeg_eq]
    exact hx_lap⟩
  invFun v := ⟨WithLp.toLp 2 (0, v.1), by
    rw [C.toSUSYQuantumSystem.mem_fermionicEigenspace_iff]
    refine ⟨?_, ?_⟩
    · apply WithLp.ofLp_injective 2
      simp only [toSUSYQuantumSystem, hamiltonianOp, C.diracOp_sq_eq_blockDiag, blockDiag_apply,
        WithLp.ofLp_toLp, Complex.coe_smul, zero_smul]
      refine Prod.ext ?_ ?_
      · simp
      · have hv : v.1 ∈ C.laplacianNeg.ker := C.ker_laplacianNeg_eq.symm ▸ v.2
        simpa using hv
    · apply WithLp.ofLp_injective 2
      simp [toSUSYQuantumSystem, gradingOp]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    have hxK := (C.toSUSYQuantumSystem.mem_fermionicEigenspace_iff.mp x.2).2
    have hx1 : x.1.ofLp.1 = -x.1.ofLp.1 := by
      have h1 := congr_arg (fun v : WithLp 2 (H_pos × H_neg) => v.ofLp.1) hxK
      simpa [toSUSYQuantumSystem, gradingOp] using h1
    have hzero : x.1.ofLp.1 = 0 := by
      have h2 : (2 : ℂ) • x.1.ofLp.1 = 0 := by
        calc (2 : ℂ) • x.1.ofLp.1 = x.1.ofLp.1 + x.1.ofLp.1 := two_smul ℂ _
          _ = x.1.ofLp.1 + -x.1.ofLp.1 := by nth_rw 2 [hx1]
          _ = 0 := add_neg_cancel _
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    exact Prod.ext hzero.symm rfl
  right_inv _ := rfl

/-- The Witten index of `C.toSUSYQuantumSystem` equals `C.fredholmIndex`. -/
theorem toSUSYQuantumSystem_wittenIndex_eq_fredholmIndex :
    C.toSUSYQuantumSystem.wittenIndex = C.fredholmIndex := by
  unfold SUSYQuantumSystem.wittenIndex SUSYQuantumSystem.levelWittenDiff
    SUSYQuantumSystem.levelBosonDim SUSYQuantumSystem.levelFermionDim fredholmIndex
  rw [C.zeroBosonEquivKerPos.finrank_eq, C.zeroFermionEquivKerNeg.finrank_eq]

end GradedFredholmComplex

end BlockOperators

section RepoBridges

open InfoGeometry.IndexTheory.AtiyahSingerDirac
open InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace
open InfoGeometry.Algebra.FiniteSUSY

section AtiyahSingerBridge

variable {H_pos H_neg : Type*}
  [NormedAddCommGroup H_pos] [InnerProductSpace ℂ H_pos] [CompleteSpace H_pos]
  [NormedAddCommGroup H_neg] [InnerProductSpace ℂ H_neg] [CompleteSpace H_neg]

/-- Link to `InfoGeometry.IndexTheory.AtiyahSingerDirac.dirac_square_grading_commutes`:
the squared Dirac operator `D² = H` commutes with the grading `K`. -/
theorem diracOp_sq_grading_commutes (C : GradedFredholmComplex H_pos H_neg) :
    C.diracOp * C.diracOp * C.gradingOp - C.gradingOp * (C.diracOp * C.diracOp) = 0 := by
  refine dirac_square_grading_commutes ?_
  change C.diracOp ∘L C.gradingOp + C.gradingOp ∘L C.diracOp = 0
  rw [C.diracOp_odd, neg_add_cancel]

/-- Link to `InfoGeometry.IndexTheory.AtiyahSingerDirac.mckean_singer_cyclic_cancellation`
for an odd Dirac operator and even operator over any finite-dimensional complex matrix algebra. -/
theorem finiteMatrix_mckean_singer_supertrace_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {γ D X : Matrix ι ι ℂ} (hγD : γ * D = -(D * γ)) (hγX : γ * X = X * γ) :
    gradedTrace (Matrix.traceAddMonoidHom ι ℂ) γ (operatorAnticommutator D X) = 0 := by
  have hτ : IsCyclic (Matrix.traceAddMonoidHom ι ℂ) := fun A B => Matrix.trace_mul_comm A B
  exact mckean_singer_cyclic_cancellation (Matrix.traceAddMonoidHom ι ℂ) hτ hγD hγX

end AtiyahSingerBridge

section FiniteMatrixComplex

/-- Construct a `GradedFredholmComplex` between finite-dimensional Euclidean spaces from any
rectangular complex matrix `A : Matrix (Fin k) (Fin m) ℂ`. -/
def ofMatrix {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℂ) :
    GradedFredholmComplex (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin k)) where
  D_pos := A.toEuclideanLin.toContinuousLinearMap
  finDim_ker_pos := inferInstance
  finDim_ker_neg := inferInstance

theorem ofMatrix_D_neg_eq {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℂ) :
    (ofMatrix A).D_neg = Aᴴ.toEuclideanLin.toContinuousLinearMap := by
  ext x i
  have hM : Aᴴ.toEuclideanLin = A.toEuclideanLin.adjoint :=
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  change ((ofMatrix A).D_neg x).ofLp i = (Aᴴ.toEuclideanLin x).ofLp i
  rw [hM]
  rfl

/-- Bridge to `InfoGeometry.Algebra.FiniteSUSY`: for a `FiniteSUSYSystem m` with `A_dag = Aᴴ`,
the square matrix complex `ofMatrix F.A` has Laplacians matching `F.H_minus` and `F.H_plus`. -/
theorem ofMatrix_finiteSUSY_laplacians {m : ℕ} (F : FiniteSUSYSystem m) (h_herm : F.A_dag = F.Aᴴ) :
    (ofMatrix F.A).laplacianPos = F.H_minus.toEuclideanLin.toContinuousLinearMap ∧
      (ofMatrix F.A).laplacianNeg = F.H_plus.toEuclideanLin.toContinuousLinearMap := by
  constructor
  · ext x i
    change ((ofMatrix F.A).D_neg ((ofMatrix F.A).D_pos x)).ofLp i = (F.H_minus.toEuclideanLin x).ofLp i
    rw [ofMatrix_D_neg_eq, ← h_herm, FiniteSUSYSystem.h_minus_is_product, Matrix.toLpLin_mul_same]
    rfl
  · ext x i
    change ((ofMatrix F.A).D_pos ((ofMatrix F.A).D_neg x)).ofLp i = (F.H_plus.toEuclideanLin x).ofLp i
    rw [ofMatrix_D_neg_eq, ← h_herm, FiniteSUSYSystem.h_plus_is_product, Matrix.toLpLin_mul_same]
    rfl

end FiniteMatrixComplex

section NonCommutativeFredholmBridge

open NonCommutativeFredholmIndex

/-- Re-exported Connes–Chern–Fedosov pairing identity from `NonCommutativeFredholmIndex`:
`-τ₂^γ(D; P) = ind_FC(D, P) = tr(P_+) - tr(P_-)`. -/
theorem chiral_connes_chern_pairing {N : ℕ} {D E_pos E_neg P : Matrix (Fin N) (Fin N) ℂ}
    (hF : IsChiralFredholmModule D E_pos E_neg)
    (hP : IsEvenIdempotent P E_pos E_neg) :
    - gradedConnesCocycle (E_pos - E_neg) D P =
        fedosovAnalyticalIndex D E_pos E_neg P ∧
      fedosovAnalyticalIndex D E_pos E_neg P =
        chiralSupertraceIndex E_pos E_neg P :=
  connes_chern_index_pairing_formula hF hP

end NonCommutativeFredholmBridge

end RepoBridges

end InfoGeometry.IndexTheory.GradedFredholmWittenBridge

/-!
## Closed T17 Constructive Inhabitants and T16 Non-Commutativity Witnesses

Placed outside sections with ambient `variable`s and without `[InnerProductSpace]` binders.
-/

namespace InfoGeometry.IndexTheory.GradedFredholmWittenBridge

open NonCommutativeFredholmIndex

/-- Canonical 2-to-1 projection complex `D_+ = [[1, 0]] : ℂ² → ℂ¹` with index `+1`. -/
def canonicalIndexOneComplex :
    GradedFredholmComplex (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 1)) :=
  ofMatrix !![(1 : ℂ), 0]

/-- Canonical 1-to-2 inclusion complex `D_+ = [[1], [0]] : ℂ¹ → ℂ²` with index `-1`. -/
def canonicalIndexNegOneComplex :
    GradedFredholmComplex (EuclideanSpace ℂ (Fin 1)) (EuclideanSpace ℂ (Fin 2)) :=
  ofMatrix !![(1 : ℂ); 0]

theorem canonicalIndexOneComplex_index_eq_one :
    canonicalIndexOneComplex.fredholmIndex = 1 := by
  rw [canonicalIndexOneComplex.fredholmIndex_eq_finrank_sub]
  simp [finrank_euclideanSpace_fin]

theorem canonicalIndexNegOneComplex_index_eq_neg_one :
    canonicalIndexNegOneComplex.fredholmIndex = -1 := by
  rw [canonicalIndexNegOneComplex.fredholmIndex_eq_finrank_sub]
  simp [finrank_euclideanSpace_fin]

theorem canonicalIndexOneComplex_witten_eq_one :
    canonicalIndexOneComplex.toSUSYQuantumSystem.wittenIndex = 1 := by
  rw [canonicalIndexOneComplex.toSUSYQuantumSystem_wittenIndex_eq_fredholmIndex,
    canonicalIndexOneComplex_index_eq_one]

/-- T16 operator non-commutativity witness: `diracOp * gradingOp ≠ gradingOp * diracOp`. -/
theorem canonicalIndexOne_dirac_grading_noncomm :
    canonicalIndexOneComplex.diracOp * canonicalIndexOneComplex.gradingOp ≠
      canonicalIndexOneComplex.gradingOp * canonicalIndexOneComplex.diracOp := by
  intro h
  have h1 := congr_arg (fun T => (T (WithLp.toLp 2 (PiLp.single 2 (0 : Fin 2) (1 : ℂ), 0))).ofLp.2 0) h
  simp [GradedFredholmComplex.diracOp, GradedFredholmComplex.gradingOp,
    canonicalIndexOneComplex, ofMatrix, Matrix.ofLp_toLpLin, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at h1
  exact one_ne_zero (by linear_combination (1 / 2 : ℂ) * h1)

theorem canonicalIndexOne_dirac_grading_comp_noncomm :
    canonicalIndexOneComplex.diracOp ∘L canonicalIndexOneComplex.gradingOp ≠
      canonicalIndexOneComplex.gradingOp ∘L canonicalIndexOneComplex.diracOp :=
  canonicalIndexOne_dirac_grading_noncomm

/-! ### Concrete Index-1 `Fin 2 ⊕ Fin 2` Chiral Fredholm & Connes–Chern Witness -/

/-- Chiral Dirac operator `D = [[0, I₂], [I₂, 0]]` on `Fin 2 ⊕ Fin 2`. -/
def chiralDirac4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 0 1 1 0

/-- Positive-chirality projection `E_+ = diag(I₂, 0)` on `Fin 2 ⊕ Fin 2`. -/
def chiralEPos4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 1 0 0 0

/-- Negative-chirality projection `E_- = diag(0, I₂)` on `Fin 2 ⊕ Fin 2`. -/
def chiralENeg4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 0 0 0 1

/-- Uneven even idempotent stratum `P = diag(I₂, diag(1, 0))` on `Fin 2 ⊕ Fin 2`,
giving chiral supertrace index `tr(P_+) - tr(P_-) = 2 - 1 = 1`. -/
def chiralStratumP4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 1 0 0 !![1, 0; 0, 0]

theorem chiralDirac4_grading_noncomm :
    chiralDirac4 * (chiralEPos4 - chiralENeg4) ≠ (chiralEPos4 - chiralENeg4) * chiralDirac4 := by
  intro h
  have h00 := congr_fun (congr_fun h (Sum.inl 0)) (Sum.inr 0)
  simp [chiralDirac4, chiralEPos4, chiralENeg4, Matrix.mul_apply] at h00
  norm_num at h00

private lemma chiral4_isChiralFredholm :
    IsChiralFredholmModule chiralDirac4 chiralEPos4 chiralENeg4 where
  sq_D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      (fin_cases i <;> fin_cases j <;>
        simp [chiralDirac4, Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply])
  idem_pos := by
    refine ⟨?_⟩
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      (fin_cases i <;> fin_cases j <;>
        simp [chiralEPos4, Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply])
  idem_neg := by
    refine ⟨?_⟩
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      (fin_cases i <;> fin_cases j <;>
        simp [chiralENeg4, Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply])
  orth_chiral := ⟨by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [chiralEPos4, chiralENeg4, Matrix.fromBlocks, Matrix.mul_apply], by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [chiralEPos4, chiralENeg4, Matrix.fromBlocks, Matrix.mul_apply]⟩
  sum_one := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      (fin_cases i <;> fin_cases j <;>
        simp [chiralEPos4, chiralENeg4, Matrix.fromBlocks, Matrix.one_apply])
  odd_pos := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [chiralDirac4, chiralEPos4, Matrix.fromBlocks, Matrix.mul_apply]
  odd_neg := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [chiralDirac4, chiralENeg4, Matrix.fromBlocks, Matrix.mul_apply]

private lemma chiral4_isEvenIdempotent :
    IsEvenIdempotent chiralStratumP4 chiralEPos4 chiralENeg4 where
  idem := by
    refine ⟨?_⟩
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      (fin_cases i <;> fin_cases j <;>
        simp [chiralStratumP4, Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply])
  comm_pos := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      (fin_cases i <;> fin_cases j <;>
        simp [chiralStratumP4, chiralEPos4, Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two])
  comm_neg := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      (fin_cases i <;> fin_cases j <;>
        simp [chiralStratumP4, chiralENeg4, Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two])

/-- On `Fin 2 ⊕ Fin 2`, the Connes–Chern cocycle, Fedosov analytical index, and chiral
supertrace index all equal `(1 : ℂ)`, matching `canonicalIndexOneComplex.fredholmIndex = 1`. -/
theorem chiral_connes_chern_matches_fredholm :
    - gradedConnesCocycle (chiralEPos4 - chiralENeg4) chiralDirac4 chiralStratumP4 = 1 ∧
      fedosovAnalyticalIndex chiralDirac4 chiralEPos4 chiralENeg4 chiralStratumP4 = 1 ∧
      chiralSupertraceIndex chiralEPos4 chiralENeg4 chiralStratumP4 = 1 ∧
      canonicalIndexOneComplex.fredholmIndex = 1 := by
  have h_pair := connes_chern_index_pairing_formula chiral4_isChiralFredholm chiral4_isEvenIdempotent
  have h_st : chiralSupertraceIndex chiralEPos4 chiralENeg4 chiralStratumP4 = 1 := by
    simp [chiralSupertraceIndex, chiralProjPos, chiralProjNeg,
      chiralEPos4, chiralENeg4, chiralStratumP4, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, h_st, canonicalIndexOneComplex_index_eq_one⟩
  · rw [h_pair.1, h_pair.2, h_st]
  · rw [h_pair.2, h_st]

end InfoGeometry.IndexTheory.GradedFredholmWittenBridge
