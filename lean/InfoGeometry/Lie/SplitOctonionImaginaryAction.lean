import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Algebra.ZornDerivationBridge
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
namespace InfoGeometry.Lie.SplitOctonionImaginaryAction

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

/-- The intrinsic trace as a real-linear map. -/
noncomputable def traceLinear : CanonicalZorn →ₗ[ℝ] ℝ where
  toFun := realZornTrace
  map_add' X Y := by
    change X.a + Y.a + (X.b + Y.b) = (X.a + X.b) + (Y.a + Y.b)
    ring
  map_smul' r X := by
    change (r • X).a + (r • X).b = r * (X.a + X.b)
    simp [Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv]
    ring

/-- Imaginary split octonions are exactly the trace-zero hyperplane. -/
noncomputable def Imaginary : Submodule ℝ CanonicalZorn :=
  LinearMap.ker traceLinear

@[simp] theorem mem_imaginary_iff (X : CanonicalZorn) :
    X ∈ Imaginary ↔ realZornTrace X = 0 := Iff.rfl

abbrev ImaginaryCoords := ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ)

/-- Trace-zero Zorn matrices have seven free coordinates. -/
noncomputable def imaginaryCoordLinearEquiv : Imaginary ≃ₗ[ℝ] ImaginaryCoords where
  toFun X := (X.1.a, X.1.x, X.1.y)
  invFun c := ⟨⟨c.1, -c.1, c.2.1, c.2.2⟩, by
    change c.1 + -c.1 = 0
    exact add_neg_cancel c.1⟩
  left_inv X := by
    apply Subtype.ext
    rcases X with ⟨⟨a, b, x, y⟩, h⟩
    change a + b = 0 at h
    change ({ a := a, b := -a, x := x, y := y } : CanonicalZorn) =
      { a := a, b := b, x := x, y := y }
    congr
    linarith
  right_inv c := rfl
  map_add' X Y := rfl
  map_smul' r X := by
    ext <;> rfl

@[simp] theorem imaginaryCoordLinearEquiv_symm_val (c : ImaginaryCoords) :
    (imaginaryCoordLinearEquiv.symm c : CanonicalZorn) = ⟨c.1, -c.1, c.2.1, c.2.2⟩ := rfl

/-- The imaginary split-octonion space has real dimension seven. -/
theorem finrank_imaginary : Module.finrank ℝ Imaginary = 7 := by
  calc
    Module.finrank ℝ Imaginary = Module.finrank ℝ ImaginaryCoords :=
      imaginaryCoordLinearEquiv.finrank_eq
    _ = 7 := by simp [ImaginaryCoords]

/-- A split-octonion automorphism restricts to the imaginary hyperplane. -/
noncomputable def imaginaryAut
    (φ : realZornCompositionAut) : Imaginary ≃ₗ[ℝ] Imaginary where
  toFun X := ⟨(φ : CanonicalLinearAut) X.1, by
    rw [mem_imaginary_iff, realZornCompositionAut_preserves_trace]
    exact X.2⟩
  invFun X := ⟨((φ⁻¹ : realZornCompositionAut) : CanonicalLinearAut) X.1, by
    rw [mem_imaginary_iff, realZornCompositionAut_preserves_trace]
    exact X.2⟩
  left_inv X := by
    apply Subtype.ext
    exact (φ : CanonicalLinearAut).symm_apply_apply X.1
  right_inv X := by
    apply Subtype.ext
    exact (φ : CanonicalLinearAut).apply_symm_apply X.1
  map_add' X Y := by
    apply Subtype.ext
    exact map_add (φ : CanonicalLinearAut) X.1 Y.1
  map_smul' r X := by
    apply Subtype.ext
    exact map_smul (φ : CanonicalLinearAut) r X.1

@[simp] theorem imaginaryAut_preserves_norm
    (φ : realZornCompositionAut) (X : Imaginary) :
    ZornMatrix.detZ (imaginaryAut φ X).1 =
      ZornMatrix.detZ X.1 :=
  realZornCompositionAut_preserves_det φ X.1

/-- The norm level set inside the seven-dimensional imaginary split-octonion
space. -/
def NormLevel (c : ℝ) : Set Imaginary :=
  {X | ZornMatrix.detZ X.1 = c}

@[simp] theorem mem_normLevel_iff (c : ℝ) (X : Imaginary) :
    X ∈ NormLevel c ↔ ZornMatrix.detZ X.1 = c := Iff.rfl

/-- Every imaginary norm level is invariant under every split-octonion
multiplication automorphism. -/
@[simp] theorem imaginaryAut_mem_normLevel_iff
    (φ : realZornCompositionAut) (c : ℝ) (X : Imaginary) :
    imaginaryAut φ X ∈ NormLevel c ↔ X ∈ NormLevel c := by
  simp only [mem_normLevel_iff, imaginaryAut_preserves_norm]

/-- In particular, the imaginary null cone is invariant. -/
@[simp] theorem imaginaryAut_preserves_null
    (φ : realZornCompositionAut) (X : Imaginary) :
    imaginaryAut φ X ∈ NormLevel 0 ↔ X ∈ NormLevel 0 :=
  imaginaryAut_mem_normLevel_iff φ 0 X

/-- On the imaginary hyperplane, null norm is equivalent to square-zero
multiplication. This is the algebraic point condition in the split-octonion
rolling geometry. -/
theorem mem_null_iff_square_zero (X : Imaginary) :
    X ∈ NormLevel 0 ↔ zMul X.1 X.1 = 0 := by
  rw [mem_normLevel_iff]
  have htrace : realZornTrace X.1 = 0 := (mem_imaginary_iff X.1).mp X.2
  constructor
  · intro hdet
    have hq := realZorn_quadratic X.1
    rw [htrace, hdet] at hq
    simpa using hq
  · intro hsq
    have hq := realZorn_quadratic X.1
    rw [htrace, hsq] at hq
    have ha := congrArg (fun Z : CanonicalZorn => Z.a) hq
    have h1a : (1 : CanonicalZorn).a = 1 := rfl
    simpa [Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv, h1a] using ha

/-- Right multiplication by an imaginary split octonion, as a real-linear map. -/
noncomputable def rightMulLinear (X : Imaginary) : Imaginary →ₗ[ℝ] CanonicalZorn where
  toFun Y := zMul Y.1 X.1
  map_add' Y Z := by
    change (Y.1 + Z.1) * X.1 = Y.1 * X.1 + Z.1 * X.1
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul _ _ _
  map_smul' r Y := by
    change (r • Y.1) * X.1 = r • (Y.1 * X.1)
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul _ _ _

/-- The right annihilator of an imaginary split octonion inside the imaginary
hyperplane. This is the native owner for `Annₓ = {y : yx = 0}`. -/
noncomputable def Annihilator (X : Imaginary) : Submodule ℝ Imaginary :=
  LinearMap.ker (rightMulLinear X)

@[simp] theorem mem_annihilator_iff (X Y : Imaginary) :
    Y ∈ Annihilator X ↔ zMul Y.1 X.1 = 0 := Iff.rfl

/-- Polarization of the canonical Zorn determinant on the imaginary
hyperplane. -/
def imaginaryPolar (X Y : Imaginary) : ℝ :=
    ZornMatrix.detZ (X.1 + Y.1) -
    ZornMatrix.detZ X.1 -
      ZornMatrix.detZ Y.1

/-- Polarized left alternativity transported from the native Zorn owner. -/
theorem canonical_left_linearized (X Y Z : CanonicalZorn) :
    (X * Y) * Z + (Y * X) * Z = X * (Y * Z) + Y * (X * Z) := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_add]
  exact InfoGeometry.Algebra.alternative_left_linearized
    (A := InfoGeometry.Algebra.ZornVectorMatrix ℝ)
      InfoGeometry.Algebra.zorn_left_alternative
      (canonicalVectorEquiv X) (canonicalVectorEquiv Y) (canonicalVectorEquiv Z)

/-- The anticommutator of two imaginary split octonions is the negative
determinant-polar scalar. -/
theorem imaginary_anticommutator_eq (X Y : Imaginary) :
    zMul X.1 Y.1 + zMul Y.1 X.1 = -(imaginaryPolar X Y) • (1 : CanonicalZorn) := by
  have htraceX : realZornTrace X.1 = 0 := (mem_imaginary_iff X.1).mp X.2
  have htraceY : realZornTrace Y.1 = 0 := (mem_imaginary_iff Y.1).mp Y.2
  have htraceAdd : realZornTrace (X.1 + Y.1) = 0 := by
    change traceLinear (X.1 + Y.1) = 0
    rw [map_add]
    change realZornTrace X.1 + realZornTrace Y.1 = 0
    rw [htraceX, htraceY, add_zero]
  have hsum := realZorn_quadratic (X.1 + Y.1)
  have hx := realZorn_quadratic X.1
  have hy := realZorn_quadratic Y.1
  rw [htraceAdd, zero_smul] at hsum
  rw [htraceX, zero_smul] at hx
  rw [htraceY, zero_smul] at hy
  change (X.1 + Y.1) * (X.1 + Y.1) +
    ZornMatrix.detZ (X.1 + Y.1) • (1 : CanonicalZorn) = 0 at hsum
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul] at hsum
  change X.1 * X.1 +
    ZornMatrix.detZ X.1 • (1 : CanonicalZorn) = 0 at hx
  change Y.1 * Y.1 +
    ZornMatrix.detZ Y.1 • (1 : CanonicalZorn) = 0 at hy
  change X.1 * Y.1 + Y.1 * X.1 =
    -(imaginaryPolar X Y) • (1 : CanonicalZorn)
  unfold imaginaryPolar
  rw [neg_smul, sub_smul, sub_smul]
  linear_combination (norm := abel) hsum - hx - hy

/-- The canonical split-octonion trace is symmetric on products. -/
theorem realZornTrace_mul_comm (X Y : CanonicalZorn) :
    realZornTrace (X * Y) = realZornTrace (Y * X) := by
  change InfoGeometry.Algebra.ZornVectorMatrix.trace (canonicalVectorEquiv (X * Y)) =
    InfoGeometry.Algebra.ZornVectorMatrix.trace (canonicalVectorEquiv (Y * X))
  rw [canonicalVectorEquiv_mul, canonicalVectorEquiv_mul,
    InfoGeometry.Algebra.ZornVectorMatrix.trace_mul_comm]

/-- The determinant polar form on imaginary split octonions, bundled as a
native Mathlib bilinear form. -/
noncomputable def imaginaryPolarBilin : LinearMap.BilinForm ℝ Imaginary :=
  LinearMap.mk₂ ℝ
    (fun X Y => -realZornTrace (X.1 * Y.1))
    (fun X₁ X₂ Y => by
      change -realZornTrace ((X₁.1 + X₂.1) * Y.1) =
        -realZornTrace (X₁.1 * Y.1) + -realZornTrace (X₂.1 * Y.1)
      rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul]
      change -traceLinear (X₁.1 * Y.1 + X₂.1 * Y.1) =
        -traceLinear (X₁.1 * Y.1) + -traceLinear (X₂.1 * Y.1)
      rw [map_add]
      ring)
    (fun r X Y => by
      change -realZornTrace ((r • X.1) * Y.1) = r • -realZornTrace (X.1 * Y.1)
      rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul]
      change -traceLinear (r • (X.1 * Y.1)) = r * -traceLinear (X.1 * Y.1)
      rw [map_smul]
      simp [smul_eq_mul])
    (fun X Y₁ Y₂ => by
      change -realZornTrace (X.1 * (Y₁.1 + Y₂.1)) =
        -realZornTrace (X.1 * Y₁.1) + -realZornTrace (X.1 * Y₂.1)
      rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add]
      change -traceLinear (X.1 * Y₁.1 + X.1 * Y₂.1) =
        -traceLinear (X.1 * Y₁.1) + -traceLinear (X.1 * Y₂.1)
      rw [map_add]
      ring)
    (fun r X Y => by
      change -realZornTrace (X.1 * (r • Y.1)) = r • -realZornTrace (X.1 * Y.1)
      rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul]
      change -traceLinear (r • (X.1 * Y.1)) = r * -traceLinear (X.1 * Y.1)
      rw [map_smul]
      simp [smul_eq_mul])

/-- The bundled form agrees with determinant polarization. -/
@[simp] theorem imaginaryPolarBilin_apply (X Y : Imaginary) :
    imaginaryPolarBilin X Y = imaginaryPolar X Y := by
  have hanti := imaginary_anticommutator_eq X Y
  have htrace := congrArg realZornTrace hanti
  change realZornTrace (X.1 * Y.1 + Y.1 * X.1) =
    realZornTrace (-(imaginaryPolar X Y) • (1 : CanonicalZorn)) at htrace
  change traceLinear (X.1 * Y.1 + Y.1 * X.1) =
    traceLinear (-(imaginaryPolar X Y) • (1 : CanonicalZorn)) at htrace
  rw [map_add, map_smul] at htrace
  change realZornTrace (X.1 * Y.1) + realZornTrace (Y.1 * X.1) =
    -(imaginaryPolar X Y) * realZornTrace (1 : CanonicalZorn) at htrace
  rw [realZornTrace_mul_comm Y.1 X.1] at htrace
  change realZornTrace (X.1 * Y.1) + realZornTrace (X.1 * Y.1) =
    -(imaginaryPolar X Y) * realZornTrace (1 : CanonicalZorn) at htrace
  have hone : realZornTrace (1 : CanonicalZorn) = 2 := by
    have h1a : (1 : CanonicalZorn).a = 1 := rfl
    have h1b : (1 : CanonicalZorn).b = 1 := rfl
    change (1 : CanonicalZorn).a + (1 : CanonicalZorn).b = 2
    rw [h1a, h1b]
    norm_num
  rw [hone] at htrace
  change -realZornTrace (X.1 * Y.1) = imaginaryPolar X Y
  linarith

/-- Two elements of the right annihilator of a nonzero imaginary split
octonion are orthogonal for the determinant polar form. -/
theorem imaginaryPolar_eq_zero_of_mem_annihilator
    {X Y Z : Imaginary} (hX : X ≠ 0)
    (hY : Y ∈ Annihilator X) (hZ : Z ∈ Annihilator X) :
    imaginaryPolar Y Z = 0 := by
  have hYX : Y.1 * X.1 = 0 := (mem_annihilator_iff X Y).mp hY
  have hZX : Z.1 * X.1 = 0 := (mem_annihilator_iff X Z).mp hZ
  have hlin := canonical_left_linearized Y.1 Z.1 X.1
  rw [hYX, hZX,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    add_zero] at hlin
  have hmul : (Y.1 * Z.1 + Z.1 * Y.1) * X.1 = 0 := by
    rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul]
    exact hlin
  have hanti := imaginary_anticommutator_eq Y Z
  change Y.1 * Z.1 + Z.1 * Y.1 =
    -(imaginaryPolar Y Z) • (1 : CanonicalZorn) at hanti
  rw [hanti] at hmul
  change (-(imaginaryPolar Y Z) • (1 : CanonicalZorn)) * X.1 = 0 at hmul
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul] at hmul
  have hone : (1 : CanonicalZorn) * X.1 = X.1 := one_zMul X.1
  rw [hone] at hmul
  have hX0 : X.1 ≠ 0 := by
    intro h
    apply hX
    apply Subtype.ext
    exact h
  have hpneg : -(imaginaryPolar Y Z) = 0 :=
    (smul_eq_zero.mp hmul).resolve_right hX0
  exact neg_eq_zero.mp hpneg

/-- The determinant polar form on the imaginary split octonions is symmetric. -/
theorem imaginaryPolarBilin_isSymm : imaginaryPolarBilin.IsSymm := by
  refine ⟨fun X Y => ?_⟩
  change -realZornTrace (X.1 * Y.1) = -realZornTrace (Y.1 * X.1)
  rw [realZornTrace_mul_comm]

/-- A subspace is totally isotropic when every pair of its vectors is
orthogonal for the native determinant polar form. -/
def IsTotallyIsotropic (V : Submodule ℝ Imaginary) : Prop :=
  ∀ Y ∈ V, ∀ Z ∈ V, imaginaryPolarBilin.IsOrtho Y Z

/-- The right annihilator of a nonzero imaginary split octonion is totally
isotropic for the determinant polar form. -/
theorem annihilator_isTotallyIsotropic {X : Imaginary} (hX : X ≠ 0) :
    IsTotallyIsotropic (Annihilator X) := by
  intro Y hY Z hZ
  change imaginaryPolarBilin Y Z = 0
  rw [imaginaryPolarBilin_apply]
  exact imaginaryPolar_eq_zero_of_mem_annihilator hX hY hZ

/-- Elements of the right annihilator of a nonzero imaginary split octonion
pairwise anticommute. -/
theorem annihilator_anticommutes
    {X Y Z : Imaginary} (hX : X ≠ 0)
    (hY : Y ∈ Annihilator X) (hZ : Z ∈ Annihilator X) :
    zMul Y.1 Z.1 + zMul Z.1 Y.1 = 0 := by
  rw [imaginary_anticommutator_eq,
    imaginaryPolar_eq_zero_of_mem_annihilator hX hY hZ, neg_zero, zero_smul]

/-- Every element of the right annihilator of a nonzero imaginary split
octonion is itself null. -/
theorem annihilator_mem_null
    {X Y : Imaginary} (hX : X ≠ 0) (hY : Y ∈ Annihilator X) :
    Y ∈ NormLevel 0 := by
  have hanti := annihilator_anticommutes hX hY hY
  have htwo : (2 : ℝ) • zMul Y.1 Y.1 = 0 := by
    simpa [two_smul ℝ] using hanti
  have hsq : zMul Y.1 Y.1 = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact (mem_null_iff_square_zero Y).mpr hsq

@[simp] theorem imaginaryAut_mem_annihilator_iff
    (φ : realZornCompositionAut) (X Y : Imaginary) :
    imaginaryAut φ Y ∈ Annihilator (imaginaryAut φ X) ↔ Y ∈ Annihilator X := by
  rw [mem_annihilator_iff, mem_annihilator_iff]
  change zMul ((φ : CanonicalLinearAut) Y.1) ((φ : CanonicalLinearAut) X.1) = 0 ↔
    zMul Y.1 X.1 = 0
  rw [← realZornCompositionAut_preserves_mul]
  exact (φ : CanonicalLinearAut).map_eq_zero_iff

/-- A real subspace of imaginary split octonions on which every ordered product
vanishes. These are precisely the null subalgebras used as points and lines in
the split-octonion incidence model. -/
def IsNullSubalgebra (V : Submodule ℝ Imaginary) : Prop :=
  ∀ X ∈ V, ∀ Y ∈ V, zMul X.1 Y.1 = 0

/-- Every element of a null subalgebra is determinant-null. -/
theorem IsNullSubalgebra.mem_normLevel_zero
    {V : Submodule ℝ Imaginary} (hV : IsNullSubalgebra V)
    {X : Imaginary} (hX : X ∈ V) : X ∈ NormLevel 0 := by
  exact (mem_null_iff_square_zero X).mpr (hV X hX X hX)

/-- A nonzero null vector and any vector in its right annihilator generate a
null subalgebra. This is the native algebraic construction behind incidence
lines; it makes no dimension claim when the two generators are dependent. -/
theorem annihilator_pair_span_isNullSubalgebra
    {X Y : Imaginary} (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0)
    (hY : Y ∈ Annihilator X) :
    IsNullSubalgebra (Submodule.span ℝ ({X, Y} : Set Imaginary)) := by
  have hXX : zMul X.1 X.1 = 0 := (mem_null_iff_square_zero X).mp hXnull
  have hYX : zMul Y.1 X.1 = 0 := (mem_annihilator_iff X Y).mp hY
  have hXann : X ∈ Annihilator X := (mem_annihilator_iff X X).mpr hXX
  have hXY : zMul X.1 Y.1 = 0 := by
    have hanti := annihilator_anticommutes hX0 hXann hY
    rw [hYX, add_zero] at hanti
    exact hanti
  have hYY : zMul Y.1 Y.1 = 0 :=
    (mem_null_iff_square_zero Y).mp (annihilator_mem_null hX0 hY)
  change X.1 * X.1 = 0 at hXX
  change Y.1 * X.1 = 0 at hYX
  change X.1 * Y.1 = 0 at hXY
  change Y.1 * Y.1 = 0 at hYY
  intro U hU V hV
  rw [Submodule.mem_span_pair] at hU hV
  rcases hU with ⟨a, b, hab⟩
  rcases hV with ⟨c, d, hcd⟩
  rw [← hab, ← hcd]
  change (a • X.1 + b • Y.1) * (c • X.1 + d • Y.1) = 0
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul]
  simp only [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul, smul_smul]
  rw [hXX, hXY, hYX, hYY]
  simp

/-- Every imaginary null vector spans a null subalgebra. -/
theorem span_isNullSubalgebra_of_mem_null (X : Imaginary) (hX : X ∈ NormLevel 0) :
    IsNullSubalgebra (ℝ ∙ X) := by
  intro Y hY Z hZ
  rcases Submodule.mem_span_singleton.mp hY with ⟨r, hr⟩
  rcases Submodule.mem_span_singleton.mp hZ with ⟨s, hs⟩
  rw [← hr, ← hs]
  change (r • X.1) * (s • X.1) = 0
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul]
  have hsq := (mem_null_iff_square_zero X).mp hX
  change X.1 * X.1 = 0 at hsq
  simp [hsq]

/-- The image of an imaginary subspace under a split-octonion automorphism. -/
noncomputable def mapSubmodule
    (φ : realZornCompositionAut) (V : Submodule ℝ Imaginary) : Submodule ℝ Imaginary :=
  V.map (imaginaryAut φ).toLinearMap

@[simp] theorem finrank_mapSubmodule
    (φ : realZornCompositionAut) (V : Submodule ℝ Imaginary) :
    Module.finrank ℝ (mapSubmodule φ V) = Module.finrank ℝ V :=
  LinearEquiv.finrank_map_eq (imaginaryAut φ) V

/-- Split-octonion automorphisms carry null subalgebras to null subalgebras.
This is the algebraic symmetry theorem underlying preservation of rolling lines. -/
theorem IsNullSubalgebra.map
    {V : Submodule ℝ Imaginary} (hV : IsNullSubalgebra V)
    (φ : realZornCompositionAut) : IsNullSubalgebra (mapSubmodule φ V) := by
  intro X hX Y hY
  rcases hX with ⟨X, hXV, rfl⟩
  rcases hY with ⟨Y, hYV, rfl⟩
  change zMul ((φ : CanonicalLinearAut) X.1) ((φ : CanonicalLinearAut) Y.1) = 0
  rw [← realZornCompositionAut_preserves_mul, hV X hXV Y hYV, map_zero]

/-- A point of the algebraic incidence geometry is a one-dimensional null
subalgebra of the imaginary split octonions. -/
def IsNullPoint (V : Submodule ℝ Imaginary) : Prop :=
  Module.finrank ℝ V = 1 ∧ IsNullSubalgebra V

/-- A nonzero imaginary null vector spans an incidence point. -/
theorem span_isNullPoint_of_mem_null
    (X : Imaginary) (hX0 : X ≠ 0) (hX : X ∈ NormLevel 0) :
    IsNullPoint (ℝ ∙ X) := by
  exact ⟨finrank_span_singleton hX0, span_isNullSubalgebra_of_mem_null X hX⟩

/-- The span of an imaginary vector is a null point exactly when the vector is
nonzero and determinant-null. -/
theorem span_isNullPoint_iff (X : Imaginary) :
    IsNullPoint (ℝ ∙ X) ↔ X ≠ 0 ∧ X ∈ NormLevel 0 := by
  constructor
  · intro h
    have hne : X ≠ 0 := by
      intro hX
      subst X
      have hzero := h.1
      rw [Submodule.span_zero_singleton] at hzero
      simp at hzero
    exact ⟨hne, h.2.mem_normLevel_zero (Submodule.mem_span_singleton_self X)⟩
  · rintro ⟨hne, hnull⟩
    exact span_isNullPoint_of_mem_null X hne hnull

/-- Every null point is the span of each of its nonzero elements. -/
theorem IsNullPoint.eq_span_of_mem
    {V : Submodule ℝ Imaginary} (hV : IsNullPoint V)
    {X : Imaginary} (hX : X ∈ V) (hX0 : X ≠ 0) :
    V = ℝ ∙ X := by
  letI : FiniteDimensional ℝ Imaginary :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_imaginary]; norm_num)
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hX)
  · calc
      Module.finrank ℝ (ℝ ∙ X) = 1 := finrank_span_singleton hX0
      _ = Module.finrank ℝ V := hV.1.symm

/-- A line of the algebraic incidence geometry is a two-dimensional null
subalgebra of the imaginary split octonions. -/
def IsNullLine (V : Submodule ℝ Imaginary) : Prop :=
  Module.finrank ℝ V = 2 ∧ IsNullSubalgebra V

/-- A linearly independent pair consisting of a nonzero null vector and an
element of its right annihilator spans a genuine two-dimensional null line. -/
theorem annihilator_pair_span_isNullLine
    {X Y : Imaginary} (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0)
    (hY : Y ∈ Annihilator X) (hLI : LinearIndependent ℝ ![X, Y]) :
    IsNullLine (Submodule.span ℝ ({X, Y} : Set Imaginary)) := by
  refine ⟨?_, annihilator_pair_span_isNullSubalgebra hX0 hXnull hY⟩
  have hrange : Set.range (![X, Y] : Fin 2 → Imaginary) = {X, Y} := by
    ext Z
    simp [or_comm]
  rw [← hrange, finrank_span_eq_card hLI, Fintype.card_fin]

/-- Split-octonion automorphisms preserve algebraic incidence points. -/
theorem IsNullPoint.map {V : Submodule ℝ Imaginary} (hV : IsNullPoint V)
    (φ : realZornCompositionAut) : IsNullPoint (mapSubmodule φ V) := by
  exact ⟨by simpa using hV.1, hV.2.map φ⟩

/-- Split-octonion automorphisms preserve algebraic incidence lines. -/
theorem IsNullLine.map {V : Submodule ℝ Imaginary} (hV : IsNullLine V)
    (φ : realZornCompositionAut) : IsNullLine (mapSubmodule φ V) := by
  exact ⟨by simpa using hV.1, hV.2.map φ⟩

instance : SMul realZornCompositionAut Imaginary where
  smul := fun φ X => imaginaryAut φ X

instance : MulAction realZornCompositionAut Imaginary where
  one_smul X := by
    apply Subtype.ext
    rfl
  mul_smul φ ψ X := by
    apply Subtype.ext
    rfl

/-- The point stabilizer for the split-octonion automorphism action on its
imaginary hyperplane. The `SL₃(ℝ)` and `SU(2,1)` identification lane is carried
by separate classification files. -/
def PointStabilizer (X : Imaginary) : Subgroup realZornCompositionAut :=
  MulAction.stabilizer realZornCompositionAut X

/-- The genuine orbit of an imaginary split octonion under multiplication
automorphisms. -/
def Orbit (X : Imaginary) : Set Imaginary :=
  MulAction.orbit realZornCompositionAut X

@[simp] theorem mem_pointStabilizer_iff
    (X : Imaginary) (φ : realZornCompositionAut) :
    φ ∈ PointStabilizer X ↔ imaginaryAut φ X = X := Iff.rfl

/-- Every automorphism orbit is contained in the norm level through its base
point. -/
theorem orbit_subset_normLevel (X : Imaginary) :
    Orbit X ⊆ NormLevel (ZornMatrix.detZ X.1) := by
  intro Y hY
  rcases hY with ⟨φ, rfl⟩
  change ZornMatrix.detZ (imaginaryAut φ X).1 =
    ZornMatrix.detZ X.1
  exact imaginaryAut_preserves_norm φ X

/-- Concrete imaginary split-octonion examples for the nonmultiplicativity obstruction. -/
noncomputable def ex_X : Imaginary :=
  imaginaryCoordLinearEquiv.symm (-1, ![1, 0, 0], ![1, 0, 0])

noncomputable def ex_Y : Imaginary :=
  imaginaryCoordLinearEquiv.symm (0, ![0, 1, 0], ![0, 1, 0])

noncomputable def ex_Z : Imaginary :=
  imaginaryCoordLinearEquiv.symm (0, ![0, 0, 1], 0)

end InfoGeometry.Lie.SplitOctonionImaginaryAction
