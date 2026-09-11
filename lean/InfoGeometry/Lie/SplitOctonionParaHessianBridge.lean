import InfoGeometry.Geometry.ParaHessianMixedPotential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionEllKleinFlow
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

/-!
# The active split-Zorn sector as a mixed para-Hessian geometry

The existing active-sector equivalence supplies the native Witt coordinates
`(x,y) : R^3 x R^3`.  This owner transports the mixed quadratic potential
`Phi(x,y) = x dot y`, its constant Hessian pairing, and its para-complex
grading to that actual Zorn subspace.

The resulting metric has zero same-root blocks and the ordinary dot product as
its mixed block.  It is exactly the negative polarization of the native Zorn
determinant.  This is a finite para-Hessian theorem, not an identification with
a statistical Fisher model or a physical surprisal.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionParaHessianBridge

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Geometry.DualFlatKreinLegendreGraph
open InfoGeometry.Geometry.ParaHessianMixedPotential
open InfoGeometry.Lie.SplitOctonionAxialKleinBridge
open InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor
open InfoGeometry.Lie.SplitOctonionAxialSupportGrading
open InfoGeometry.Lie.SplitOctonionAxialWittReduction
open InfoGeometry.Lie.SplitOctonionEllClosedFlow
open InfoGeometry.Lie.SplitOctonionEllKleinFlow
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev V3 := InfoGeometry.Algebra.FiniteSpin.Vec3R
abbrev Active :=
  InfoGeometry.Lie.SplitOctonionAxialWittReduction.ActiveSector

/-- The mixed potential in the native three-Witt-pair coordinates. -/
def wittPotential (X : WittCoordinates) : ℝ := dot X.1 X.2

/-- Its constant mixed Hessian pairing. -/
def wittMetric (U V : WittCoordinates) : ℝ :=
  dot U.1 V.2 + dot U.2 V.1

/-- The compatible skew pairing obtained from the signed Witt grading. -/
def wittSymplectic (U V : WittCoordinates) : ℝ :=
  dot U.1 V.2 - dot U.2 V.1

/-- The scalar potential transported to the actual active Zorn subtype. -/
def activePotential (X : Active) : ℝ :=
  wittPotential (activeSectorEquiv X)

/-- The transported mixed Hessian metric. -/
def activeMetric (X Y : Active) : ℝ :=
  wittMetric (activeSectorEquiv X) (activeSectorEquiv Y)

noncomputable def activeMetricBilin : LinearMap.BilinForm ℝ Active :=
  LinearMap.mk₂ ℝ
    (fun X Y => activeMetric X Y)
    (fun X₁ X₂ Y => by
      simp [activeMetric, wittMetric, dot, Finset.sum_add_distrib]
      ring)
    (fun r X Y => by
      simp [activeMetric, wittMetric, dot, Finset.smul_sum, smul_eq_mul]
      ring)
    (fun X Y₁ Y₂ => by
      simp [activeMetric, wittMetric, dot, Finset.sum_add_distrib]
      ring)
    (fun r X Y => by
      simp [activeMetric, wittMetric, dot, Finset.smul_sum, smul_eq_mul]
      ring)

@[simp] theorem activeMetricBilin_apply (X Y : Active) :
    activeMetricBilin X Y = activeMetric X Y := rfl

theorem activeMetricBilin_isSymm : activeMetricBilin.IsSymm := by
  refine ⟨?_⟩
  intro X Y
  simp [activeMetric, wittMetric, dot, mul_comm]
  ring

/-- The transported compatible skew form. -/
def activeSymplectic (X Y : Active) : ℝ :=
  wittSymplectic (activeSectorEquiv X) (activeSectorEquiv Y)

theorem activePotential_eq_half_activeMetric_self (X : Active) :
    activePotential X = (1 / 2 : ℝ) * activeMetric X X := by
  simp [activePotential, activeMetric, wittPotential, wittMetric, dot]
  ring

theorem activePotential_add (X Y : Active) :
    activePotential (X + Y) =
      activePotential X + activeMetric X Y + activePotential Y := by
  simp [activePotential, activeMetric, wittPotential, wittMetric, dot,
    Finset.sum_add_distrib]
  ring

theorem activeMetric_eq_potential_polarization (X Y : Active) :
    activeMetric X Y =
      activePotential (X + Y) - activePotential X - activePotential Y := by
  rw [activePotential_add]
  ring

theorem activePotential_grading (X : Active) :
    activePotential (axialGradingOnActive X) = -activePotential X := by
  rw [activePotential, activePotential, activeSectorEquiv_intertwines_grading]
  rcases activeSectorEquiv X with ⟨x, y⟩
  simp [wittPotential, signedWittGrading, dot]
  ring

/-- The positive and negative Witt-root inclusions. -/
def positiveRoot (x : V3) : Active := activeSectorEquiv.symm (x, 0)

def negativeRoot (y : V3) : Active := activeSectorEquiv.symm (0, y)

@[simp] theorem activeSectorEquiv_positiveRoot (x : V3) :
    activeSectorEquiv (positiveRoot x) = (x, 0) := by
  simp [positiveRoot]

@[simp] theorem activeSectorEquiv_negativeRoot (y : V3) :
    activeSectorEquiv (negativeRoot y) = (0, y) := by
  simp [negativeRoot]

theorem activePotential_root_sum (x y : V3) :
    activePotential (positiveRoot x + negativeRoot y) = dot x y := by
  simp [activePotential, wittPotential, positiveRoot, negativeRoot, dot]

@[simp] theorem activePotential_positiveRoot (x : V3) :
    activePotential (positiveRoot x) = 0 := by
  simp [activePotential, wittPotential, positiveRoot, dot]

@[simp] theorem activePotential_negativeRoot (y : V3) :
    activePotential (negativeRoot y) = 0 := by
  simp [activePotential, wittPotential, negativeRoot, dot]

/-- The potential is precisely minus the native active Zorn determinant. -/
theorem activePotential_eq_neg_detZ (X : Active) :
    activePotential X =
      -InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 X.1 := by
  rcases X with ⟨_, Y, rfl⟩
  rw [detZ_axialActiveSupport Y]
  simp [activePotential, wittPotential, activeSectorEquiv, axialActiveSupport_apply, dot]

/-- The Hessian pairing is exactly the negative raw polarization of the Zorn
quadratic form. -/
theorem activeMetric_eq_neg_detPolar (X Y : Active) :
    activeMetric X Y = -activeDetPolar X Y := by
  rw [activeMetric_eq_potential_polarization]
  rw [activePotential_eq_neg_detZ (X + Y)]
  rw [activePotential_eq_neg_detZ X]
  rw [activePotential_eq_neg_detZ Y]
  unfold activeDetPolar
  rw [Submodule.coe_add X Y]
  ring

theorem activeMetric_symmetric (X Y : Active) :
    activeMetric X Y = activeMetric Y X := by
  simp [activeMetric, wittMetric, dot, mul_comm]
  ring

/-- Each root half is totally isotropic. -/
@[simp] theorem activeMetric_positive_positive (x y : V3) :
    activeMetric (positiveRoot x) (positiveRoot y) = 0 := by
  simp [activeMetric, wittMetric, dot]

@[simp] theorem activeMetric_negative_negative (x y : V3) :
    activeMetric (negativeRoot x) (negativeRoot y) = 0 := by
  simp [activeMetric, wittMetric, dot]

/-- The mixed Hessian block is the native three-coordinate dot pairing. -/
@[simp] theorem activeMetric_positive_negative (x y : V3) :
    activeMetric (positiveRoot x) (negativeRoot y) = dot x y := by
  simp [activeMetric, wittMetric, dot]

@[simp] theorem activeMetric_negative_positive (x y : V3) :
    activeMetric (negativeRoot x) (positiveRoot y) = dot x y := by
  simp [activeMetric, wittMetric, dot, mul_comm]

/-! ## Native mixed Hessian matrix on the three coordinate modes -/

noncomputable def activeMixedHessianMatrix :
    Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
      activeMetric (positiveRoot (Pi.single i 1))
        (negativeRoot (Pi.single j 1))

theorem activeMetric_coordinate_mixed (i j : Fin 3) :
    activeMetric (positiveRoot (Pi.single i 1))
        (negativeRoot (Pi.single j 1)) =
      if i = j then 1 else 0 := by
  simp [activeMetric, wittMetric, InfoGeometry.Canonical.ZornMatrix.dot]
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Canonical.ZornMatrix.dot, Fin.sum_univ_three,
      Pi.single_apply]

theorem activeMixedHessianMatrix_eq_one :
    activeMixedHessianMatrix = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  change activeMetric (positiveRoot (Pi.single i 1))
      (negativeRoot (Pi.single j 1)) = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
  rw [activeMetric_coordinate_mixed]
  rw [Matrix.one_apply]

theorem activeMixedHessianMatrix_det :
    Matrix.det activeMixedHessianMatrix = 1 := by
  rw [activeMixedHessianMatrix_eq_one]
  simp

theorem activeMixedHessianMatrix_abs_det :
    |Matrix.det activeMixedHessianMatrix| = 1 := by
  rw [activeMixedHessianMatrix_det]
  norm_num

theorem activeMixedHessianMatrix_log_abs_det :
    Real.log |Matrix.det activeMixedHessianMatrix| = 0 := by
  rw [activeMixedHessianMatrix_abs_det]
  simp

/-- The native active grading is the transported para-complex grading. -/
theorem activeSectorEquiv_grading (X : Active) :
    activeSectorEquiv (axialGradingOnActive X) =
      signedWittGrading (activeSectorEquiv X) :=
  activeSectorEquiv_intertwines_grading X

/-- The para-complex grading is an anti-isometry of the mixed Hessian metric. -/
theorem activeMetric_grading_anti_isometry (X Y : Active) :
    activeMetric (axialGradingOnActive X) (axialGradingOnActive Y) =
      -activeMetric X Y := by
  simp only [activeMetric, activeSectorEquiv_grading]
  simp [wittMetric, signedWittGrading, dot]
  ring

/-- The transported skew form is `g(K·,·)`. -/
theorem activeSymplectic_eq_metric_grading (X Y : Active) :
    activeSymplectic X Y = activeMetric (axialGradingOnActive X) Y := by
  simp [activeSymplectic, activeMetric, wittSymplectic, wittMetric,
    activeSectorEquiv_grading, signedWittGrading, dot]
  ring

@[simp] theorem activeSymplectic_positive_positive (x y : V3) :
    activeSymplectic (positiveRoot x) (positiveRoot y) = 0 := by
  simp [activeSymplectic, wittSymplectic, positiveRoot, dot]

@[simp] theorem activeSymplectic_negative_negative (x y : V3) :
    activeSymplectic (negativeRoot x) (negativeRoot y) = 0 := by
  simp [activeSymplectic, wittSymplectic, negativeRoot, dot]

@[simp] theorem activeSymplectic_positive_negative (x y : V3) :
    activeSymplectic (positiveRoot x) (negativeRoot y) = dot x y := by
  simp [activeSymplectic, wittSymplectic, positiveRoot, negativeRoot, dot]

@[simp] theorem activeSymplectic_negative_positive (x y : V3) :
    activeSymplectic (negativeRoot x) (positiveRoot y) = -(dot x y) := by
  simp [activeSymplectic, wittSymplectic, positiveRoot, negativeRoot, dot]

theorem activeSymplectic_skew (X Y : Active) :
    activeSymplectic X Y = -activeSymplectic Y X := by
  simp [activeSymplectic, wittSymplectic, dot]
  ring

/-- The mixed Hessian pairing is nondegenerate on the actual active carrier. -/
theorem activeMetric_nondegenerate (X : Active)
    (h : ∀ Y : Active, activeMetric X Y = 0) : X = 0 := by
  let c := activeSectorEquiv X
  have hx := h (negativeRoot c.1)
  have hy := h (positiveRoot c.2)
  have hxsum : c.1 0 ^ 2 + c.1 1 ^ 2 + c.1 2 ^ 2 = 0 := by
    simpa [activeMetric, wittMetric, negativeRoot, c, dot, pow_two]
      using hx
  have hysum : c.2 0 ^ 2 + c.2 1 ^ 2 + c.2 2 ^ 2 = 0 := by
    simpa [activeMetric, wittMetric, positiveRoot, c, dot, pow_two,
      mul_comm] using hy
  have hx0 : c.1 0 = 0 := by nlinarith [sq_nonneg (c.1 1), sq_nonneg (c.1 2)]
  have hx1 : c.1 1 = 0 := by nlinarith [sq_nonneg (c.1 0), sq_nonneg (c.1 2)]
  have hx2 : c.1 2 = 0 := by nlinarith [sq_nonneg (c.1 0), sq_nonneg (c.1 1)]
  have hy0 : c.2 0 = 0 := by nlinarith [sq_nonneg (c.2 1), sq_nonneg (c.2 2)]
  have hy1 : c.2 1 = 0 := by nlinarith [sq_nonneg (c.2 0), sq_nonneg (c.2 2)]
  have hy2 : c.2 2 = 0 := by nlinarith [sq_nonneg (c.2 0), sq_nonneg (c.2 1)]
  apply activeSectorEquiv.injective
  change c = activeSectorEquiv 0
  apply Prod.ext
  · funext i
    fin_cases i <;> assumption
  · funext i
    fin_cases i <;> assumption

theorem axialGradingOnActive_sq (X : Active) :
    axialGradingOnActive (axialGradingOnActive X) = X := by
  apply activeSectorEquiv.injective
  rw [activeSectorEquiv_grading, activeSectorEquiv_grading]
  rcases activeSectorEquiv X with ⟨x, y⟩
  ext i <;> simp [signedWittGrading]

/-- Since `omega(X,Y)=g(KX,Y)` and `K` is invertible, the alternating form is
nondegenerate. -/
theorem activeSymplectic_nondegenerate (X : Active)
    (h : ∀ Y : Active, activeSymplectic X Y = 0) : X = 0 := by
  have hK : axialGradingOnActive X = 0 := activeMetric_nondegenerate
    (axialGradingOnActive X) (fun Y => by
      rw [← activeSymplectic_eq_metric_grading]
      exact h Y)
  have hKK := congrArg axialGradingOnActive hK
  rw [axialGradingOnActive_sq, map_zero] at hKK
  exact hKK

/-- The closed flow commutes with the active para-complex grading. -/
theorem ellFlowActive_commutes_grading (t : ℝ) (X : Active) :
    axialGradingOnActive (ellFlowActive t X) =
      ellFlowActive t (axialGradingOnActive X) := by
  apply Subtype.ext
  change axialGrading (ellFlowPhi t X.1) =
    ellFlowPhi t (axialGrading X.1)
  rw [axialGrading_apply, ellFlowPhi_coord, ellFlowPhi_coord,
    axialGrading_apply]
  ext i <;> simp

/-- The closed `ell` flow preserves the generating potential. -/
theorem ellFlowActive_preserves_potential (t : ℝ) (X : Active) :
    activePotential (ellFlowActive t X) = activePotential X := by
  rw [activePotential_eq_neg_detZ, activePotential_eq_neg_detZ]
  exact congrArg Neg.neg (ellFlowPhi_preserves_det t X.1)

/-- The closed `ell` flow preserves the full mixed Hessian pairing. -/
theorem ellFlowActive_preserves_metric (t : ℝ) (X Y : Active) :
    activeMetric (ellFlowActive t X) (ellFlowActive t Y) =
      activeMetric X Y := by
  rw [activeMetric_eq_neg_detPolar, activeMetric_eq_neg_detPolar]
  exact congrArg Neg.neg
    (show activeDetPolar (ellFlowActive t X) (ellFlowActive t Y) =
        activeDetPolar X Y by
      rw [← activeKleinLinearEquiv_preserves_polar,
        ← activeKleinLinearEquiv_preserves_polar]
      exact ellFlowActive_preserves_kleinPolar t X Y)

/-- The closed ell flow preserves the compatible alternating form. -/
theorem ellFlowActive_preserves_symplectic (t : ℝ) (X Y : Active) :
    activeSymplectic (ellFlowActive t X) (ellFlowActive t Y) =
      activeSymplectic X Y := by
  rw [activeSymplectic_eq_metric_grading,
    ellFlowActive_commutes_grading,
    ellFlowActive_preserves_metric,
    ← activeSymplectic_eq_metric_grading]

/-! ## Literal Fréchet-Hessian readout on the canonical Euclidean model

`Active` is intentionally retained as an algebraic subtype and is not given a
second topology here.  The actual Mathlib derivative lives on the canonical
Euclidean realization of its Witt coordinates; the following linear
equivalence transports its scalar and bilinear readouts to `Active`.
-/

abbrev EuclideanThree := EuclideanSpace ℝ (Fin 3)
abbrev HilbertWitt := EuclideanThree × EuclideanThree

/-- Forget the Euclidean wrapper on each finite coordinate triple. -/
noncomputable def hilbertWittLinearEquiv : HilbertWitt ≃ₗ[ℝ] WittCoordinates :=
  LinearEquiv.prodCongr
    (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv
    (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv

/-- Canonical Euclidean realization of the native active Zorn sector. -/
noncomputable def activeHilbertLinearEquiv : HilbertWitt ≃ₗ[ℝ] Active :=
  hilbertWittLinearEquiv.trans activeSectorEquiv.symm

/-- Pullback of the native active potential to its canonical Hilbert model. -/
def activePotentialHilbertReadout (X : HilbertWitt) : ℝ :=
  activePotential (activeHilbertLinearEquiv X)

theorem activePotentialHilbertReadout_eq_potential (X : HilbertWitt) :
    activePotentialHilbertReadout X =
      InfoGeometry.Geometry.ParaHessianMixedPotential.potential X := by
  rw [activePotentialHilbertReadout, activePotential, activeHilbertLinearEquiv]
  simp [hilbertWittLinearEquiv, wittPotential,
    InfoGeometry.Geometry.ParaHessianMixedPotential.potential]
  rw [PiLp.inner_apply]
  simp [dot, Fin.sum_univ_three]
  ring

/-- Pullback of the native active metric is the generic mixed metric. -/
theorem activeMetric_hilbertReadout_eq_metric (U V : HilbertWitt) :
    activeMetric (activeHilbertLinearEquiv U) (activeHilbertLinearEquiv V) =
      metric U V := by
  rw [activeMetric, activeHilbertLinearEquiv]
  simp [hilbertWittLinearEquiv, wittMetric, metric]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [dot, Fin.sum_univ_three]
  ring

/-- The native active potential has the literal Mathlib first derivative after
pullback to the canonical Euclidean realization. -/
theorem hasFDerivAt_activePotentialHilbertReadout (X : HilbertWitt) :
    HasFDerivAt activePotentialHilbertReadout
      (InfoGeometry.Geometry.ParaHessianMixedPotential.potentialDerivative X) X := by
  have hfun : activePotentialHilbertReadout =
      InfoGeometry.Geometry.ParaHessianMixedPotential.potential := by
    funext Y
    exact activePotentialHilbertReadout_eq_potential Y
  rw [hfun]
  exact InfoGeometry.Geometry.ParaHessianMixedPotential.hasFDerivAt_potential X

theorem fderiv_activePotentialHilbertReadout_apply
    (X U : HilbertWitt) :
    fderiv ℝ activePotentialHilbertReadout X U =
      activeMetric (activeHilbertLinearEquiv X)
        (activeHilbertLinearEquiv U) := by
  rw [(hasFDerivAt_activePotentialHilbertReadout X).fderiv]
  rw [activeMetric_hilbertReadout_eq_metric,
    InfoGeometry.Geometry.ParaHessianMixedPotential.potentialDerivative_eq_metric]

/-- Literal Hessian-generation theorem: pairing the Fréchet derivative of the
Riesz gradient equals the native active metric after the canonical transport.
The Hessian is constant, hence independent of the base point `X`. -/
theorem activeMetric_eq_fderiv_gradient_pairing
    (X U V : HilbertWitt) :
    productPairing
        (fderiv ℝ InfoGeometry.Geometry.ParaHessianMixedPotential.gradient X U) V =
      activeMetric (activeHilbertLinearEquiv U) (activeHilbertLinearEquiv V) := by
  rw [fderiv_gradient_inner_eq_metric, activeMetric_hilbertReadout_eq_metric]

/-! ## The native mixed-Hessian Legendre graph -/

/-- The duality map represented by the actual mixed Hessian. -/
noncomputable def mixedRieszDuality :
    HilbertWitt →ₗ[ℝ] Module.Dual ℝ HilbertWitt where
  toFun U :=
    { toFun := fun V => metric U V
      map_add' := by
        intro V W
        change inner ℝ U.1 (V.2 + W.2) + inner ℝ U.2 (V.1 + W.1) =
          (inner ℝ U.1 V.2 + inner ℝ U.2 V.1) +
            (inner ℝ U.1 W.2 + inner ℝ U.2 W.1)
        rw [inner_add_right, inner_add_right]
        abel
      map_smul' := by
        intro r V
        change inner ℝ U.1 (r • V.2) + inner ℝ U.2 (r • V.1) =
          r • (inner ℝ U.1 V.2 + inner ℝ U.2 V.1)
        rw [real_inner_smul_right, real_inner_smul_right]
        simp only [smul_eq_mul]
        ring }
  map_add' U V := by
    apply LinearMap.ext
    intro W
    change inner ℝ (U.1 + V.1) W.2 + inner ℝ (U.2 + V.2) W.1 =
      (inner ℝ U.1 W.2 + inner ℝ U.2 W.1) +
        (inner ℝ V.1 W.2 + inner ℝ V.2 W.1)
    rw [inner_add_left, inner_add_left]
    abel
  map_smul' r U := by
    apply LinearMap.ext
    intro W
    change inner ℝ (r • U.1) W.2 + inner ℝ (r • U.2) W.1 =
      r • (inner ℝ U.1 W.2 + inner ℝ U.2 W.1)
    rw [real_inner_smul_left, real_inner_smul_left]
    simp only [smul_eq_mul, RingHom.id_apply]
    ring

theorem mixedRieszDuality_apply (U V : HilbertWitt) :
    (mixedRieszDuality U) V = metric U V := by
  rfl

theorem activePotential_fderiv_eq_mixedRieszDuality
    (X U : HilbertWitt) :
    fderiv ℝ activePotentialHilbertReadout X U =
      (mixedRieszDuality X) U := by
  rw [fderiv_activePotentialHilbertReadout_apply,
    activeMetric_hilbertReadout_eq_metric,
    mixedRieszDuality_apply]

theorem activeHessian_eq_mixedRieszDuality
    (X U V : HilbertWitt) :
    productPairing
        (fderiv ℝ InfoGeometry.Geometry.ParaHessianMixedPotential.gradient X U) V =
      (mixedRieszDuality U) V := by
  rw [activeMetric_eq_fderiv_gradient_pairing,
    activeMetric_hilbertReadout_eq_metric,
    mixedRieszDuality_apply]

theorem mixedRieszDuality_symmetric :
    IsSymmetricDuality mixedRieszDuality := by
  intro U V
  rw [mixedRieszDuality_apply, mixedRieszDuality_apply]
  exact metric_symmetric U V

theorem mixedRieszDuality_injective :
    Function.Injective mixedRieszDuality := by
  intro U V hUV
  have hdiff :
      activeHilbertLinearEquiv U - activeHilbertLinearEquiv V = 0 := by
    apply activeMetric_nondegenerate
    intro Y
    let Z := activeHilbertLinearEquiv.symm Y
    have hZ := congrArg (fun L : Module.Dual ℝ HilbertWitt => L Z) hUV
    change (mixedRieszDuality U) Z = (mixedRieszDuality V) Z at hZ
    rw [mixedRieszDuality_apply, mixedRieszDuality_apply] at hZ
    have hYZ : activeHilbertLinearEquiv Z = Y := by
      exact activeHilbertLinearEquiv.apply_symm_apply Y
    calc
      activeMetric
          (activeHilbertLinearEquiv U - activeHilbertLinearEquiv V) Y =
          activeMetric (activeHilbertLinearEquiv U) Y -
            activeMetric (activeHilbertLinearEquiv V) Y := by
        simp [activeMetric, wittMetric, dot, sub_eq_add_neg]
        ring
      _ = metric U Z - metric V Z := by
        rw [← hYZ, activeMetric_hilbertReadout_eq_metric,
          activeMetric_hilbertReadout_eq_metric]
      _ = 0 := by rw [hZ]; ring
  apply activeHilbertLinearEquiv.injective
  exact sub_eq_zero.mp hdiff

theorem mixedRieszDuality_surjective :
    Function.Surjective mixedRieszDuality := by
  have hfin :
      Module.finrank ℝ HilbertWitt =
        Module.finrank ℝ (Module.Dual ℝ HilbertWitt) := by
    symm
    exact Subspace.dual_finrank_eq
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp
      mixedRieszDuality_injective

theorem mixedRieszDuality_bijective :
    Function.Bijective mixedRieszDuality :=
  ⟨mixedRieszDuality_injective, mixedRieszDuality_surjective⟩

/-- The mixed Hessian graph carries the transported active metric. -/
theorem mixedHessianGraph_neutral_pairing (U V : HilbertWitt) :
    normalizedNeutralPairing
        (graphLift mixedRieszDuality U)
        (graphLift mixedRieszDuality V) =
      activeMetric (activeHilbertLinearEquiv U)
        (activeHilbertLinearEquiv V) := by
  rw [graph_neutral_pairing mixedRieszDuality mixedRieszDuality_symmetric,
    mixedRieszDuality_apply, activeMetric_hilbertReadout_eq_metric]

/-- The mixed Hessian graph is isotropic for the canonical skew pairing. -/
theorem mixedHessianGraph_symplectic_isotropic (U V : HilbertWitt) :
    canonicalSymplectic
        (graphLift mixedRieszDuality U)
        (graphLift mixedRieszDuality V) = 0 := by
  exact graph_symplectic_isotropic mixedRieszDuality
    mixedRieszDuality_symmetric U V

end InfoGeometry.Lie.SplitOctonionParaHessianBridge
