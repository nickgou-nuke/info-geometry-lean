import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinModularBridge
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped InnerProductSpace

/-!
# Finite doubled chiral Krein frame

This is the finite `4 + 4` carrier behind the generic doubled construction.
The two sheets are null for the cross-sheet form, while a graph section
`E⁺ + H E⁻` acquires the symmetric form `H + Hᵀ`.

This owner is deliberately finite and algebraic.  It does not identify the
carrier with a spacetime tangent bundle, a holographic boundary, or a Tomita
commutant without additional structure.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealDoubledChiralKreinFrame

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements

abbrev FourSpace := EuclideanSpace ℝ (Fin 4)
abbrev KreinFrame4 := DoubledSpace FourSpace

noncomputable def frameBasis (i : Fin 4) : FourSpace :=
  EuclideanSpace.basisFun (Fin 4) ℝ i

noncomputable def plusFrame (i : Fin 4) : KreinFrame4 :=
  to_doubled (frameBasis i) 0

noncomputable def minusFrame (i : Fin 4) : KreinFrame4 :=
  to_doubled 0 (frameBasis i)

theorem fourSpace_finrank : Module.finrank ℝ FourSpace = 4 := by
  simp [FourSpace]

theorem kreinFrame4_finrank : Module.finrank ℝ KreinFrame4 = 8 := by
  change Module.finrank ℝ (WithLp (2 : ENNReal) (FourSpace × FourSpace)) = 8
  calc
    Module.finrank ℝ (WithLp (2 : ENNReal) (FourSpace × FourSpace)) =
        Module.finrank ℝ (FourSpace × FourSpace) :=
      (WithLp.linearEquiv (2 : ENNReal) ℝ (FourSpace × FourSpace)).finrank_eq
    _ = 8 := by rw [Module.finrank_prod, fourSpace_finrank]

theorem frameBasis_inner (i j : Fin 4) :
    inner ℝ (frameBasis i) (frameBasis j) = if i = j then 1 else 0 := by
  simpa [frameBasis] using
    (orthonormal_iff_ite.mp ((EuclideanSpace.basisFun (Fin 4) ℝ).orthonormal)) i j

theorem plusFrame_isotropic (i j : Fin 4) :
    chiralKreinForm (E := FourSpace) (plusFrame i) (plusFrame j) = 0 := by
  simp [plusFrame, chiralKreinForm_to_doubled]

theorem minusFrame_isotropic (i j : Fin 4) :
    chiralKreinForm (E := FourSpace) (minusFrame i) (minusFrame j) = 0 := by
  simp [minusFrame, chiralKreinForm_to_doubled]

theorem plusFrame_minusFrame_pairing (i j : Fin 4) :
    chiralKreinForm (E := FourSpace) (plusFrame i) (minusFrame j) =
      if i = j then 1 else 0 := by
  simp [plusFrame, minusFrame, chiralKreinForm_to_doubled, frameBasis_inner]

theorem minusFrame_plusFrame_pairing (i j : Fin 4) :
    chiralKreinForm (E := FourSpace) (minusFrame i) (plusFrame j) =
      if i = j then 1 else 0 := by
  simp [minusFrame, plusFrame, chiralKreinForm_to_doubled, frameBasis_inner]

@[simp] theorem etaChiral_plusFrame (i : Fin 4) :
    etaChiral (E := FourSpace) (plusFrame i) = minusFrame i := by
  simp [plusFrame, minusFrame, etaChiral, modular_j]

@[simp] theorem etaChiral_minusFrame (i : Fin 4) :
    etaChiral (E := FourSpace) (minusFrame i) = plusFrame i := by
  simp [plusFrame, minusFrame, etaChiral, modular_j]

@[simp] theorem gamma5_plusFrame (i : Fin 4) :
    gamma5 (E := FourSpace) (plusFrame i) = plusFrame i := by
  simp [plusFrame, gamma5, spectral_epsilon]

@[simp] theorem gamma5_minusFrame (i : Fin 4) :
    gamma5 (E := FourSpace) (minusFrame i) = -minusFrame i := by
  apply DoubledSpace.ext <;> simp [minusFrame, gamma5, spectral_epsilon]

/-! ## Fundamental symmetry, chirality, and the induced positive/symplectic forms -/

abbrev sheetFlip : KreinFrame4 →L[ℝ] KreinFrame4 := etaChiral (E := FourSpace)

abbrev chirality : KreinFrame4 →L[ℝ] KreinFrame4 := gamma5 (E := FourSpace)

abbrev doubledComplexStructure : KreinFrame4 →L[ℝ] KreinFrame4 :=
  chiralComplexStructure (E := FourSpace)

theorem sheetFlip_sq :
    sheetFlip.comp sheetFlip = ContinuousLinearMap.id ℝ KreinFrame4 := by
  exact etaChiral_involution (E := FourSpace)

theorem chirality_sq :
    chirality.comp chirality = ContinuousLinearMap.id ℝ KreinFrame4 := by
  exact gamma5_involution (E := FourSpace)

theorem sheetFlip_chirality_anticommute :
    sheetFlip.comp chirality = -(chirality.comp sheetFlip) := by
  exact etaChiral_gamma5_anticommute (E := FourSpace)

@[simp] theorem sheetFlip_plusFrame (i : Fin 4) :
    sheetFlip (plusFrame i) = minusFrame i := by
  exact etaChiral_plusFrame i

@[simp] theorem sheetFlip_minusFrame (i : Fin 4) :
    sheetFlip (minusFrame i) = plusFrame i := by
  exact etaChiral_minusFrame i

@[simp] theorem chirality_plusFrame (i : Fin 4) :
    chirality (plusFrame i) = plusFrame i := by
  exact gamma5_plusFrame i

@[simp] theorem chirality_minusFrame (i : Fin 4) :
    chirality (minusFrame i) = -minusFrame i := by
  exact gamma5_minusFrame i

theorem doubledComplexStructure_sq :
    doubledComplexStructure.comp doubledComplexStructure =
      -(ContinuousLinearMap.id ℝ KreinFrame4) := by
  exact chiralComplexStructure_sq (E := FourSpace)

@[simp] theorem doubledComplexStructure_plusFrame (i : Fin 4) :
    doubledComplexStructure (plusFrame i) = minusFrame i := by
  rw [plusFrame, complex_i_to_doubled]
  apply DoubledSpace.ext <;> simp [minusFrame]

@[simp] theorem doubledComplexStructure_minusFrame (i : Fin 4) :
    doubledComplexStructure (minusFrame i) = -plusFrame i := by
  rw [minusFrame, complex_i_to_doubled]
  apply DoubledSpace.ext <;> simp [plusFrame]

theorem hilbertizedForm_eq_inner (u v : KreinFrame4) :
    chiralHilbertForm (E := FourSpace) u v = inner ℝ u v := by
  exact chiralHilbertForm_eq_inner u v

theorem hilbertizedForm_self_nonneg (u : KreinFrame4) :
    0 ≤ chiralHilbertForm (E := FourSpace) u u := by
  exact chiralHilbertForm_self_nonneg u

theorem hilbertizedForm_self_pos {u : KreinFrame4} (hu : u ≠ 0) :
    0 < chiralHilbertForm (E := FourSpace) u u := by
  exact chiralHilbertForm_self_pos hu

theorem symplecticForm_swap (u v : KreinFrame4) :
    chiralSymplecticForm (E := FourSpace) u v =
      -chiralSymplecticForm (E := FourSpace) v u := by
  exact chiralSymplecticForm_swap u v

/-! The sign-correct relation between the cross-sheet symplectic form and the
Hilbertized complex structure `J = Γ ∘ R`.  With the convention
`H u v = K u (R v)`, one has `Ω u v = - H (J u) v`. -/
theorem symplecticForm_eq_neg_hilbertized_complexStructure
    (u v : KreinFrame4) :
    chiralSymplecticForm (E := FourSpace) u v =
      chiralHilbertForm (E := FourSpace)
        (doubledComplexStructure u) v := by
  have hu : to_doubled (WithLp.fst u) (WithLp.snd u) = u :=
    DoubledSpace.ext rfl rfl
  have hv : to_doubled (WithLp.fst v) (WithLp.snd v) = v :=
    DoubledSpace.ext rfl rfl
  rw [← hu, ← hv]
  simp [chiralSymplecticForm, chiralHilbertForm,
    doubledComplexStructure, chiralComplexStructure,
    chiralKreinForm, etaChiral, gamma5, modular_j, spectral_epsilon,
    WithLp.prod_inner_apply, real_inner_comm, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc]

noncomputable def graphFrame
    (H : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : KreinFrame4 :=
  to_doubled (frameBasis i) (∑ j, H i j • frameBasis j)

noncomputable def graphSection
    (H : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : KreinFrame4 :=
  plusFrame i + ∑ j, H i j • minusFrame j

theorem graphSection_eq_graphFrame
    (H : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) :
    graphSection H i = graphFrame H i := by
  apply DoubledSpace.ext
  · simp only [graphSection, graphFrame, plusFrame, minusFrame, WithLp.add_fst]
    have hsum :
        WithLp.fst (∑ j, H i j • to_doubled 0 (frameBasis j)) = 0 := by
      change (fst_L (E := FourSpace))
        (∑ j, H i j • to_doubled 0 (frameBasis j)) = 0
      rw [map_sum]
      simp [fst_L]
    rw [hsum]
    simp [frameBasis]
  · simp only [graphSection, graphFrame, plusFrame, minusFrame, WithLp.add_snd]
    have hsum :
        WithLp.snd (∑ j, H i j • to_doubled 0 (frameBasis j)) =
          ∑ j, H i j • frameBasis j := by
      change (snd_L (E := FourSpace))
        (∑ j, H i j • to_doubled 0 (frameBasis j)) = _
      rw [map_sum]
      simp [snd_L]
    rw [hsum]
    simp [frameBasis]

theorem graphFrame_metric
    (H : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    chiralKreinForm (E := FourSpace) (graphFrame H i) (graphFrame H j) =
      H i j + H j i := by
  rw [chiralKreinForm_to_doubled]
  simp only [graphFrame, frameBasis]
  simp_rw [inner_sum, sum_inner, real_inner_smul_right, real_inner_smul_left]
  simp [EuclideanSpace.inner_single_right, add_comm]

theorem graphFrame_metric_symmetric
    (H : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    chiralKreinForm (E := FourSpace) (graphFrame H i) (graphFrame H j) =
      H i j + H j i :=
  graphFrame_metric H i j

theorem graphSection_metric
    (H : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    chiralKreinForm (E := FourSpace) (graphSection H i) (graphSection H j) =
      H i j + H j i := by
  rw [graphSection_eq_graphFrame, graphSection_eq_graphFrame]
  exact graphFrame_metric H i j

noncomputable def symmetricPart
    (H : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • (H + H.transpose)

noncomputable def skewPart
    (H : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • (H - H.transpose)

theorem symmetricPart_add_skewPart
    (H : Matrix (Fin 4) (Fin 4) ℝ) :
    symmetricPart H + skewPart H = H := by
  ext i j
  simp [symmetricPart, skewPart, Matrix.transpose_apply]
  ring

theorem H_eq_symmetricPart_add_skewPart
    (H : Matrix (Fin 4) (Fin 4) ℝ) :
    H = symmetricPart H + skewPart H := by
  symm
  exact symmetricPart_add_skewPart H

theorem symmetricPart_transpose
    (H : Matrix (Fin 4) (Fin 4) ℝ) :
    (symmetricPart H).transpose = symmetricPart H := by
  ext i j
  simp [symmetricPart, Matrix.transpose_apply, add_comm]
  ring

theorem skewPart_transpose
    (H : Matrix (Fin 4) (Fin 4) ℝ) :
    (skewPart H).transpose = -skewPart H := by
  ext i j
  simp [skewPart, Matrix.transpose_apply, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc]

theorem graphSection_metric_eq_two_symmetricPart
    (H : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    chiralKreinForm (E := FourSpace) (graphSection H i) (graphSection H j) =
      2 * symmetricPart H i j := by
  rw [graphSection_metric]
  simp [symmetricPart, Matrix.transpose_apply]

theorem graphSection_metric_ignores_skewPart
    (H : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    chiralKreinForm (E := FourSpace) (graphSection H i) (graphSection H j) =
      symmetricPart H i j + symmetricPart H j i := by
  rw [graphSection_metric]
  simp [symmetricPart, Matrix.transpose_apply]
  ring

noncomputable def dualConnection
    (omegaPlus : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  -omegaPlus.transpose

theorem dualConnection_cross_pairing_compatibility
    (omegaPlus : Matrix (Fin 4) (Fin 4) ℝ) :
    omegaPlus.transpose + dualConnection omegaPlus = 0 := by
  ext i j
  simp [dualConnection, Matrix.transpose_apply]

theorem dualConnection_formula
    (omegaPlus : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    dualConnection omegaPlus i j = -omegaPlus j i := by
  rfl

/-! ## Metric-dependent dual connection -/

noncomputable def dualConnectionWithMetric
    (eta omegaPlus : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  -(eta⁻¹ * omegaPlus.transpose * eta)

theorem dualConnectionWithMetric_compatibility
    (eta omegaPlus : Matrix (Fin 4) (Fin 4) ℝ)
    (hη : IsUnit eta.det) :
    omegaPlus.transpose * eta +
        eta * dualConnectionWithMetric eta omegaPlus = 0 := by
  rw [dualConnectionWithMetric]
  calc
    omegaPlus.transpose * eta +
        eta * (-(eta⁻¹ * omegaPlus.transpose * eta)) =
        omegaPlus.transpose * eta -
          eta * (eta⁻¹ * omegaPlus.transpose * eta) := by
            simp [sub_eq_add_neg]
    _ = omegaPlus.transpose * eta -
          (eta * eta⁻¹) * omegaPlus.transpose * eta := by
            congr 1
            simp only [mul_assoc]
    _ = omegaPlus.transpose * eta -
          (1 : Matrix (Fin 4) (Fin 4) ℝ) * omegaPlus.transpose * eta := by
            rw [Matrix.mul_nonsing_inv eta hη]
    _ = 0 := by
      simp

theorem dualConnectionWithMetric_formula
    (eta omegaPlus : Matrix (Fin 4) (Fin 4) ℝ)
    (i j : Fin 4) :
    dualConnectionWithMetric eta omegaPlus i j =
      -∑ a, ∑ b, eta⁻¹ i a * omegaPlus b a * eta b j := by
  simp [dualConnectionWithMetric, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

theorem dualConnectionWithMetric_unique
    (eta omegaPlus omegaMinus : Matrix (Fin 4) (Fin 4) ℝ)
    (hη : IsUnit eta.det)
    (hcompat : omegaPlus.transpose * eta + eta * omegaMinus = 0) :
    omegaMinus = dualConnectionWithMetric eta omegaPlus := by
  have hsolve : eta * omegaMinus = -(omegaPlus.transpose * eta) := by
    exact eq_neg_of_add_eq_zero_right hcompat
  calc
    omegaMinus = 1 * omegaMinus := by simp
    _ = (eta⁻¹ * eta) * omegaMinus := by
      rw [Matrix.nonsing_inv_mul eta hη]
    _ = eta⁻¹ * (eta * omegaMinus) := by
      simp only [mul_assoc]
    _ = eta⁻¹ * (-(omegaPlus.transpose * eta)) := by rw [hsolve]
    _ = -(eta⁻¹ * omegaPlus.transpose * eta) := by
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = dualConnectionWithMetric eta omegaPlus := by
      rfl

end InfoGeometry.Canonical.RealDoubledChiralKreinFrame
