import InfoGeometry.Canonical.SplitOctonionQuaternionGrassmannian
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitG2MetricDerivedHodgeStar
import InfoGeometry.Canonical.DiscreteSplitOctonionCauchyRiemann

namespace InfoGeometry.Canonical

/-!
# Calibration readout over the native split-quaternion Grassmannian

This file is deliberately a narrow bridge.  The split-quaternion carrier and
its intrinsic imaginary plane are owned by
`SplitOctonionQuaternionGrassmannian`; no second subalgebra carrier is
introduced here.  The Hodge owner currently stores a degree-reversing linear
equivalence, so this file records only algebraic three-form readouts and does
not claim a four-form calibration or a semi-Riemannian volume theorem.
-/

namespace SplitQuaternionAssociativeCoassociativeCalibrationBridge

noncomputable section

/-- Native basis vectors for the standard split-octonion imaginary carrier. -/
def imagI : imaginarySplitOctonion :=
  ⟨Pi.single IntegralSplitBasis.i (1 : ℚ), by
    simp [scalarPart]⟩

/-- Native basis vectors for the standard split-octonion imaginary carrier. -/
def imagIL : imaginarySplitOctonion :=
  ⟨Pi.single IntegralSplitBasis.il (1 : ℚ), by
    simp [scalarPart]⟩

/-- Native basis vectors for the standard split-octonion imaginary carrier. -/
def imagJ : imaginarySplitOctonion :=
  ⟨Pi.single IntegralSplitBasis.j (1 : ℚ), by
    simp [scalarPart]⟩

/-- Native basis vectors for the standard split-octonion imaginary carrier. -/
def imagJL : imaginarySplitOctonion :=
  ⟨Pi.single IntegralSplitBasis.jl (1 : ℚ), by
    simp [scalarPart]⟩

/-- Native basis vectors for the standard split-octonion imaginary carrier. -/
def imagK : imaginarySplitOctonion :=
  ⟨Pi.single IntegralSplitBasis.k (1 : ℚ), by
    simp [scalarPart]⟩

/-- Native basis vectors for the standard split-octonion imaginary carrier. -/
def imagKL : imaginarySplitOctonion :=
  ⟨Pi.single IntegralSplitBasis.kl (1 : ℚ), by
    simp [scalarPart]⟩

abbrev associativePlane (W : SplitQuaternionGrassmannian) :
    Submodule ℚ imaginarySplitOctonion :=
  imaginaryAssociativePlane W

theorem associativePlane_finrank (W : SplitQuaternionGrassmannian) :
    Module.finrank ℚ (associativePlane W) = 3 := by
  exact imaginaryAssociativePlane_finrank W

noncomputable abbrev associativeVolumeForm
    (W : SplitQuaternionGrassmannian) :
    associativePlane W → associativePlane W → associativePlane W → ℚ :=
  volumeForm W

theorem associativeVolumeForm_restriction
    (W : SplitQuaternionGrassmannian)
    (x y z : associativePlane W) :
    associativeVolumeForm W x y z =
      canonicalSplitG2ThreeFormValue
        (x : imaginarySplitOctonion)
        (y : imaginarySplitOctonion)
        (z : imaginarySplitOctonion) := by
  exact volumeForm_restriction W x y z

theorem standard_associative_three_form_value :
    canonicalSplitG2ThreeFormValue imagI imagJ imagK = 1 := by
  native_decide

theorem standard_coassociative_three_form_value :
    canonicalSplitG2ThreeFormValue imagIL imagJL imagKL = 0 := by
  native_decide

/-- The four named generators of the native standard coassociative plane. -/
def standardCoassociativeFrame : Fin 4 → imaginarySplitOctonion
  | 0 => imagIL
  | 1 => imagJL
  | 2 => imagKL
  | 3 => ⟨Pi.single IntegralSplitBasis.l (1 : ℚ), by simp [scalarPart]⟩

def standardCoassociativePlane : Submodule ℚ imaginarySplitOctonion :=
  Submodule.span ℚ ({imagIL, imagJL, imagKL,
    ⟨Pi.single IntegralSplitBasis.l (1 : ℚ), by simp [scalarPart]⟩} :
      Set imaginarySplitOctonion)

/-- Coordinate vanishing on every generator triple of the standard plane.

This is deliberately a finite coordinate property.  It does not yet claim
vanishing on the whole span; that requires the trilinear extension lemmas for
the canonical form and is a separate, explicit next step.
-/
theorem standard_coassociative_generator_three_form_zero
    (i j k : Fin 4) :
    canonicalSplitG2ThreeFormValue
      (standardCoassociativeFrame i)
      (standardCoassociativeFrame j)
      (standardCoassociativeFrame k) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> native_decide

lemma splitOctonionMulQ_add_left
    (x y z : StandardRationalSplitOctonion) :
    splitOctonionMulQ (x + y) z =
      splitOctonionMulQ x z + splitOctonionMulQ y z := by
  funext b
  fin_cases b <;>
    simp [splitOctonionMulQ, splitQuaternionOfQ, splitQuaternionLPartQ,
      splitQuaternionConjQ, splitQuaternionAddQ, splitQuaternionMulQ,
      splitOctonionOfQuaternionPairQ] <;> ring

lemma splitOctonionMulQ_add_right
    (x y z : StandardRationalSplitOctonion) :
    splitOctonionMulQ x (y + z) =
      splitOctonionMulQ x y + splitOctonionMulQ x z := by
  funext b
  fin_cases b <;>
    simp [splitOctonionMulQ, splitQuaternionOfQ, splitQuaternionLPartQ,
      splitQuaternionConjQ, splitQuaternionAddQ, splitQuaternionMulQ,
      splitOctonionOfQuaternionPairQ] <;> ring

lemma splitOctonionMulQ_smul_left
    (a : ℚ) (x y : StandardRationalSplitOctonion) :
    splitOctonionMulQ (a • x) y = a • splitOctonionMulQ x y := by
  funext b
  fin_cases b <;>
    simp [splitOctonionMulQ, splitQuaternionOfQ, splitQuaternionLPartQ,
      splitQuaternionConjQ, splitQuaternionAddQ, splitQuaternionMulQ,
      splitOctonionOfQuaternionPairQ] <;> ring

lemma splitOctonionMulQ_smul_right
    (a : ℚ) (x y : StandardRationalSplitOctonion) :
    splitOctonionMulQ x (a • y) = a • splitOctonionMulQ x y := by
  funext b
  fin_cases b <;>
    simp [splitOctonionMulQ, splitQuaternionOfQ, splitQuaternionLPartQ,
      splitQuaternionConjQ, splitQuaternionAddQ, splitQuaternionMulQ,
      splitOctonionOfQuaternionPairQ] <;> ring

lemma splitInner_zero_left (x : StandardRationalSplitOctonion) :
    splitInner 0 x = 0 := by
  simp [splitInner, coordinateSplitNorm]

lemma splitInner_zero_right (x : StandardRationalSplitOctonion) :
    splitInner x 0 = 0 := by
  simp [splitInner, coordinateSplitNorm]

lemma canonicalThreeForm_add_left
    (x y z w : StandardRationalSplitOctonion) :
    canonicalThreeForm (x + y) z w =
      canonicalThreeForm x z w + canonicalThreeForm y z w := by
  unfold canonicalThreeForm
  rw [splitOctonionMulQ_add_left]
  change splitOctonionMetric
      (splitOctonionMulQ x z + splitOctonionMulQ y z) w =
    splitOctonionMetric (splitOctonionMulQ x z) w +
      splitOctonionMetric (splitOctonionMulQ y z) w
  rw [map_add]
  rfl

lemma canonicalThreeForm_add_mid
    (x y z w : StandardRationalSplitOctonion) :
    canonicalThreeForm x (y + z) w =
      canonicalThreeForm x y w + canonicalThreeForm x z w := by
  unfold canonicalThreeForm
  rw [splitOctonionMulQ_add_right]
  change splitOctonionMetric
      (splitOctonionMulQ x y + splitOctonionMulQ x z) w =
    splitOctonionMetric (splitOctonionMulQ x y) w +
      splitOctonionMetric (splitOctonionMulQ x z) w
  rw [map_add]
  rfl

lemma canonicalThreeForm_add_right
    (x y z w : StandardRationalSplitOctonion) :
    canonicalThreeForm x y (z + w) =
      canonicalThreeForm x y z + canonicalThreeForm x y w := by
  unfold canonicalThreeForm
  change splitOctonionMetric (splitOctonionMulQ x y) (z + w) =
    splitOctonionMetric (splitOctonionMulQ x y) z +
      splitOctonionMetric (splitOctonionMulQ x y) w
  rw [map_add]

lemma canonicalThreeForm_smul_left
    (a : ℚ) (x y z : StandardRationalSplitOctonion) :
    canonicalThreeForm (a • x) y z =
      a * canonicalThreeForm x y z := by
  unfold canonicalThreeForm
  rw [splitOctonionMulQ_smul_left]
  change splitOctonionMetric (a • splitOctonionMulQ x y) z =
    a * splitOctonionMetric (splitOctonionMulQ x y) z
  rw [LinearMap.map_smul]
  rfl

lemma canonicalThreeForm_smul_mid
    (a : ℚ) (x y z : StandardRationalSplitOctonion) :
    canonicalThreeForm x (a • y) z =
      a * canonicalThreeForm x y z := by
  unfold canonicalThreeForm
  rw [splitOctonionMulQ_smul_right]
  change splitOctonionMetric (a • splitOctonionMulQ x y) z =
    a * splitOctonionMetric (splitOctonionMulQ x y) z
  rw [LinearMap.map_smul]
  rfl

lemma canonicalThreeForm_smul_right
    (a : ℚ) (x y z : StandardRationalSplitOctonion) :
    canonicalThreeForm x y (a • z) =
      a * canonicalThreeForm x y z := by
  unfold canonicalThreeForm
  change splitOctonionMetric (splitOctonionMulQ x y) (a • z) =
    a * splitOctonionMetric (splitOctonionMulQ x y) z
  rw [LinearMap.map_smul]
  rfl

lemma canonicalSplitG2ThreeFormValue_add_left
    (x y z w : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue (x + y) z w =
      canonicalSplitG2ThreeFormValue x z w +
        canonicalSplitG2ThreeFormValue y z w := by
  exact canonicalThreeForm_add_left x.1 y.1 z.1 w.1

lemma canonicalSplitG2ThreeFormValue_add_mid
    (x y z w : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue x (y + z) w =
      canonicalSplitG2ThreeFormValue x y w +
        canonicalSplitG2ThreeFormValue x z w := by
  exact canonicalThreeForm_add_mid x.1 y.1 z.1 w.1

lemma canonicalSplitG2ThreeFormValue_add_right
    (x y z w : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue x y (z + w) =
      canonicalSplitG2ThreeFormValue x y z +
        canonicalSplitG2ThreeFormValue x y w := by
  exact canonicalThreeForm_add_right x.1 y.1 z.1 w.1

lemma canonicalSplitG2ThreeFormValue_smul_left
    (a : ℚ) (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue (a • x) y z =
      a * canonicalSplitG2ThreeFormValue x y z := by
  exact canonicalThreeForm_smul_left a x.1 y.1 z.1

lemma canonicalSplitG2ThreeFormValue_smul_mid
    (a : ℚ) (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue x (a • y) z =
      a * canonicalSplitG2ThreeFormValue x y z := by
  exact canonicalThreeForm_smul_mid a x.1 y.1 z.1

lemma canonicalSplitG2ThreeFormValue_smul_right
    (a : ℚ) (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue x y (a • z) =
      a * canonicalSplitG2ThreeFormValue x y z := by
  exact canonicalThreeForm_smul_right a x.1 y.1 z.1

lemma standard_coassociative_generator_zero
    {x y z : imaginarySplitOctonion}
    (hx : x = imagIL ∨ x = imagJL ∨ x = imagKL ∨
      x = (⟨Pi.single IntegralSplitBasis.l (1 : ℚ), by simp [scalarPart]⟩ :
        imaginarySplitOctonion))
    (hy : y = imagIL ∨ y = imagJL ∨ y = imagKL ∨
      y = (⟨Pi.single IntegralSplitBasis.l (1 : ℚ), by simp [scalarPart]⟩ :
        imaginarySplitOctonion))
    (hz : z = imagIL ∨ z = imagJL ∨ z = imagKL ∨
      z = (⟨Pi.single IntegralSplitBasis.l (1 : ℚ), by simp [scalarPart]⟩ :
        imaginarySplitOctonion)) :
    canonicalSplitG2ThreeFormValue x y z = 0 := by
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl | rfl <;>
        native_decide

/-- The metric orthogonal complement of an intrinsic associative plane.

This is defined from the existing bilinear metric as an infimum of native
linear-map kernels.  No nondegeneracy, signature, or dimension claim is
silently added here.
-/
noncomputable def metricOrthogonalComplement
    (S : Submodule ℚ imaginarySplitOctonion) :
    Submodule ℚ imaginarySplitOctonion :=
  ⨅ s : S, LinearMap.ker (imaginarySplitMetric s)

theorem mem_metricOrthogonalComplement_iff
    (S : Submodule ℚ imaginarySplitOctonion)
    (x : imaginarySplitOctonion) :
    x ∈ metricOrthogonalComplement S ↔
      ∀ s : S, imaginarySplitMetric s x = 0 := by
  simp [metricOrthogonalComplement]

end

end SplitQuaternionAssociativeCoassociativeCalibrationBridge

end InfoGeometry.Canonical
