import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornAlternativeLaws

/-!
# Dimension of null split-octonion annihilators

This module proves structurally that the right annihilator, inside the
seven-dimensional imaginary hyperplane, of a nonzero null real split octonion
has dimension three.  The proof uses the nondegenerate transported Kingdon
polar form, polarized Kirmse contraction, rank-nullity on full right
multiplication, and the trace-zero slice.  It performs no coordinate
case-enumeration.
-/

noncomputable section
namespace InfoGeometry.Lie.SplitOctonionImaginaryAction

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion

/-- Polarization of the canonical determinant on the full split-octonion
space. -/
def canonicalPolar (X Y : CanonicalZorn) : ℝ :=
  ZornMatrix.detZ realCrossProduct3 (X + Y) -
    ZornMatrix.detZ realCrossProduct3 X -
      ZornMatrix.detZ realCrossProduct3 Y

/-- The canonical determinant polar form is nondegenerate.  This transports the
already proved real Kingdon nondegeneracy theorem through the canonical linear
equivalence. -/
theorem canonicalPolar_nondegenerate (X : CanonicalZorn)
    (h : ∀ Y : CanonicalZorn, canonicalPolar X Y = 0) : X = 0 := by
  let x : AbstractKingdon := kingdonCanonicalLinearEquiv.symm X
  have hx : x = 0 := kingdonPolar_nondegenerate x (fun y => by
    have hxy := h (kingdonCanonicalLinearEquiv y)
    unfold canonicalPolar at hxy
    have hxX : kingdonCanonicalLinearEquiv x = X := by simp [x]
    rw [← hxX, ← map_add] at hxy
    rw [← kingdonNorm_eq_realZorn_det,
      ← kingdonNorm_eq_realZorn_det,
      ← kingdonNorm_eq_realZorn_det] at hxy
    unfold kingdonPolar
    rw [hxy]
    norm_num)
  apply kingdonCanonicalLinearEquiv.symm.injective
  simpa [x] using hx

/-- Canonical conjugation transported from the native Zorn owner. -/
def canonicalConj (X : CanonicalZorn) : CanonicalZorn :=
  canonicalVectorEquiv.symm
    (InfoGeometry.Algebra.ZornVectorMatrix.conj (canonicalVectorEquiv X))

@[simp] theorem canonicalVectorEquiv_canonicalConj (X : CanonicalZorn) :
    canonicalVectorEquiv (canonicalConj X) =
      InfoGeometry.Algebra.ZornVectorMatrix.conj (canonicalVectorEquiv X) := by
  simp [canonicalConj]

@[simp] theorem canonicalConj_add (X Z : CanonicalZorn) :
    canonicalConj (X + Z) = canonicalConj X + canonicalConj Z := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_canonicalConj, canonicalVectorEquiv_add,
    InfoGeometry.Algebra.ZornVectorMatrix.conj_add]

/-- The native Zorn norm agrees with the canonical determinant. -/
theorem vector_norm_eq_canonical_det (X : CanonicalZorn) :
    InfoGeometry.Algebra.ZornVectorMatrix.norm (canonicalVectorEquiv X) =
      ZornMatrix.detZ realCrossProduct3 X := by
  simp [InfoGeometry.Algebra.ZornVectorMatrix.norm, ZornMatrix.detZ,
    realCrossProduct3, InfoGeometry.Algebra.ZornVec3.dot,
    InfoGeometry.Canonical.ZornMatrix.dot, Fin.sum_univ_three]

/-- Kirmse right contraction on the canonical carrier. -/
theorem canonical_kirmse_right (X Y : CanonicalZorn) :
    (Y * X) * canonicalConj X =
      ZornMatrix.detZ realCrossProduct3 X • Y := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_canonicalConj,
    canonicalVectorEquiv_smul]
  rw [← vector_norm_eq_canonical_det]
  exact InfoGeometry.Algebra.ZornVectorMatrix.kirmse_right (R := ℝ) _ _

/-- Polarized Kirmse right contraction. -/
theorem canonical_kirmse_right_polarized (X Z Y : CanonicalZorn) :
    (Y * X) * canonicalConj Z + (Y * Z) * canonicalConj X =
      canonicalPolar X Z • Y := by
  have hsum := canonical_kirmse_right (X + Z) Y
  have hx := canonical_kirmse_right X Y
  have hz := canonical_kirmse_right Z Y
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add,
    canonicalConj_add,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul] at hsum
  unfold canonicalPolar
  rw [sub_smul, sub_smul]
  linear_combination (norm := abel) hsum - hx - hz

/-- Conjugation is trace minus the original element. -/
theorem canonicalConj_eq_trace_sub (X : CanonicalZorn) :
    canonicalConj X = realZornTrace X • (1 : CanonicalZorn) - X := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_canonicalConj, canonicalVectorEquiv_sub,
    canonicalVectorEquiv_smul, canonicalVectorEquiv_one]
  ext i <;> simp [InfoGeometry.Algebra.ZornVectorMatrix.conj,
    InfoGeometry.Algebra.ZornVectorMatrix.sub,
    InfoGeometry.Algebra.ZornVectorMatrix.add,
    InfoGeometry.Algebra.ZornVectorMatrix.neg,
    InfoGeometry.Algebra.ZornVectorMatrix.smul,
    InfoGeometry.Algebra.ZornVectorMatrix.one,
    realZornTrace, canonicalVectorEquiv]

@[simp] theorem canonicalConj_eq_neg_of_trace_zero {X : CanonicalZorn}
    (hX : realZornTrace X = 0) : canonicalConj X = -X := by
  rw [canonicalConj_eq_trace_sub, hX, zero_smul, zero_sub]

/-- Full-space right multiplication by a canonical split octonion. -/
noncomputable def fullRightMulLinear (X : CanonicalZorn) :
    CanonicalZorn →ₗ[ℝ] CanonicalZorn where
  toFun Y := Y * X
  map_add' Y Z :=
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul Y Z X
  map_smul' r Y :=
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul r Y X

@[simp] theorem fullRightMulLinear_apply (X Y : CanonicalZorn) :
    fullRightMulLinear X Y = Y * X := rfl

/-- Right alternativity transported to the canonical carrier. -/
theorem canonical_right_alternative (X Y : CanonicalZorn) :
    (Y * X) * X = Y * (X * X) := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul]
  exact InfoGeometry.Algebra.zorn_right_alternative _ _

/-- For a nonzero null imaginary element, full right multiplication has equal
range and kernel.  The reverse inclusion is the contracting-homotopy argument
provided by polarized Kirmse contraction and polar nondegeneracy. -/
theorem fullRightMul_range_eq_ker {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0) :
    LinearMap.range (fullRightMulLinear X.1) =
      LinearMap.ker (fullRightMulLinear X.1) := by
  apply le_antisymm
  · rintro Y ⟨Z, rfl⟩
    change (Z * X.1) * X.1 = 0
    rw [canonical_right_alternative]
    have hsq := (mem_null_iff_square_zero X).mp hXnull
    change X.1 * X.1 = 0 at hsq
    rw [hsq, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero]
  · intro Y hY
    change Y * X.1 = 0 at hY
    have hXcarrier : X.1 ≠ 0 := by
      intro h
      apply hX0
      apply Subtype.ext
      exact h
    obtain ⟨Z, hpolar⟩ : ∃ Z : CanonicalZorn, canonicalPolar X.1 Z ≠ 0 := by
      by_contra h
      push_neg at h
      exact hXcarrier (canonicalPolar_nondegenerate X.1 h)
    have htrace : realZornTrace X.1 = 0 := (mem_imaginary_iff X.1).mp X.2
    have hk := canonical_kirmse_right_polarized X.1 Z Y
    rw [hY, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
      zero_add, canonicalConj_eq_neg_of_trace_zero htrace] at hk
    rw [show -X.1 = (-1 : ℝ) • X.1 by simp] at hk
    rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul] at hk
    refine ⟨(-(canonicalPolar X.1 Z)⁻¹) • (Y * Z), ?_⟩
    change ((-(canonicalPolar X.1 Z)⁻¹) • (Y * Z)) * X.1 = Y
    rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul]
    calc
      (-(canonicalPolar X.1 Z)⁻¹) • ((Y * Z) * X.1) =
          (canonicalPolar X.1 Z)⁻¹ •
            ((-1 : ℝ) • ((Y * Z) * X.1)) := by module
      _ = (canonicalPolar X.1 Z)⁻¹ • (canonicalPolar X.1 Z • Y) := by rw [hk]
      _ = Y := by simp [smul_smul, hpolar]

/-- The canonical real split-octonion carrier has dimension eight. -/
theorem canonicalZorn_finrank : Module.finrank ℝ CanonicalZorn = 8 := by
  rw [← kingdonCanonicalLinearEquiv.finrank_eq]
  exact abstractKingdon_finrank

/-- The full right annihilator of a nonzero null imaginary element has dimension
four. -/
theorem fullRightMul_ker_finrank {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0) :
    Module.finrank ℝ (LinearMap.ker (fullRightMulLinear X.1)) = 4 := by
  letI : FiniteDimensional ℝ CanonicalZorn :=
    FiniteDimensional.of_finrank_eq_succ canonicalZorn_finrank
  have hrk := LinearMap.finrank_range_add_finrank_ker (fullRightMulLinear X.1)
  rw [fullRightMul_range_eq_ker hX0 hXnull, canonicalZorn_finrank] at hrk
  omega

/-- Polarization is the trace of conjugate-left multiplication. -/
theorem canonicalPolar_eq_trace_conj_mul (X Z : CanonicalZorn) :
    canonicalPolar X Z = realZornTrace (canonicalConj Z * X) := by
  calc
    canonicalPolar X Z =
        InfoGeometry.Algebra.ZornVectorMatrix.norm
            (canonicalVectorEquiv (X + Z)) -
          InfoGeometry.Algebra.ZornVectorMatrix.norm (canonicalVectorEquiv X) -
          InfoGeometry.Algebra.ZornVectorMatrix.norm (canonicalVectorEquiv Z) := by
            unfold canonicalPolar
            rw [vector_norm_eq_canonical_det, vector_norm_eq_canonical_det,
              vector_norm_eq_canonical_det]
    _ = InfoGeometry.Algebra.ZornVectorMatrix.trace
          (InfoGeometry.Algebra.ZornVectorMatrix.mul
            (canonicalVectorEquiv X)
            (InfoGeometry.Algebra.ZornVectorMatrix.conj (canonicalVectorEquiv Z))) := by
          rw [canonicalVectorEquiv_add,
            InfoGeometry.Algebra.ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj]
          abel
    _ = InfoGeometry.Algebra.ZornVectorMatrix.trace
          (InfoGeometry.Algebra.ZornVectorMatrix.mul
            (InfoGeometry.Algebra.ZornVectorMatrix.conj (canonicalVectorEquiv Z))
            (canonicalVectorEquiv X)) := by
          rw [InfoGeometry.Algebra.ZornVectorMatrix.trace_mul_comm]
    _ = realZornTrace (canonicalConj Z * X) := by
          have hmap := canonicalVectorEquiv_mul (canonicalConj Z) X
          rw [canonicalVectorEquiv_canonicalConj] at hmap
          exact (congrArg InfoGeometry.Algebra.ZornVectorMatrix.trace hmap).symm

/-- Trace restricted to the full right annihilator. -/
noncomputable def fullAnnihilatorTrace (X : Imaginary) :
    LinearMap.ker (fullRightMulLinear X.1) →ₗ[ℝ] ℝ :=
  traceLinear.domRestrict (LinearMap.ker (fullRightMulLinear X.1))

/-- The trace restriction to the full annihilator is nonzero. -/
theorem fullAnnihilatorTrace_ne_zero {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0) :
    fullAnnihilatorTrace X ≠ 0 := by
  have hXcarrier : X.1 ≠ 0 := by
    intro h
    apply hX0
    apply Subtype.ext
    exact h
  obtain ⟨Z, hpolar⟩ : ∃ Z : CanonicalZorn, canonicalPolar X.1 Z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hXcarrier (canonicalPolar_nondegenerate X.1 h)
  have hmem : canonicalConj Z * X.1 ∈
      LinearMap.ker (fullRightMulLinear X.1) := by
    rw [← fullRightMul_range_eq_ker hX0 hXnull]
    exact ⟨canonicalConj Z, rfl⟩
  intro hzero
  have happ := LinearMap.congr_fun hzero ⟨canonicalConj Z * X.1, hmem⟩
  change realZornTrace (canonicalConj Z * X.1) = 0 at happ
  rw [← canonicalPolar_eq_trace_conj_mul] at happ
  exact hpolar happ

/-- The trace-zero slice of the full right annihilator has dimension three. -/
theorem fullAnnihilatorTrace_ker_finrank {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0) :
    Module.finrank ℝ (LinearMap.ker (fullAnnihilatorTrace X)) = 3 := by
  letI : FiniteDimensional ℝ
      (LinearMap.ker (fullRightMulLinear X.1)) :=
    FiniteDimensional.of_finrank_eq_succ
      (fullRightMul_ker_finrank hX0 hXnull)
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero
    (fullAnnihilatorTrace_ne_zero hX0 hXnull)
  rw [fullRightMul_ker_finrank hX0 hXnull] at hdim
  omega

/-- The imaginary right annihilator is the trace-zero slice of the full right
annihilator. -/
noncomputable def annihilatorFullTraceKerEquiv (X : Imaginary) :
    Annihilator X ≃ₗ[ℝ] LinearMap.ker (fullAnnihilatorTrace X) where
  toFun Y := by
    let yFull : LinearMap.ker (fullRightMulLinear X.1) :=
      ⟨Y.1.1, (mem_annihilator_iff X Y.1).mp Y.2⟩
    exact ⟨yFull, (mem_imaginary_iff Y.1.1).mp Y.1.2⟩
  invFun Y := by
    let yImaginary : Imaginary :=
      ⟨Y.1.1, (mem_imaginary_iff Y.1.1).mpr Y.2⟩
    exact ⟨yImaginary, (mem_annihilator_iff X yImaginary).mpr Y.1.2⟩
  left_inv Y := rfl
  right_inv Y := rfl
  map_add' Y Z := rfl
  map_smul' r Y := rfl

/-- Baez--Huerta Proposition 7 dimension statement: the right annihilator of a
nonzero null imaginary split octonion is three-dimensional. -/
theorem annihilator_finrank_eq_three {X : Imaginary}
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0) :
    Module.finrank ℝ (Annihilator X) = 3 := by
  rw [annihilatorFullTraceKerEquiv X |>.finrank_eq]
  exact fullAnnihilatorTrace_ker_finrank hX0 hXnull

end InfoGeometry.Lie.SplitOctonionImaginaryAction
