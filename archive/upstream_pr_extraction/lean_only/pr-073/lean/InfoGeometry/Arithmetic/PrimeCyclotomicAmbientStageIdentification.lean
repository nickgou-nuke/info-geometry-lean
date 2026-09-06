import Mathlib
import InfoGeometry.Arithmetic.PrimeCyclotomicAmbientTower

/-!
# Identification of the literal ambient stages with native cyclotomic fields

For each stage of the six-prime conductor tower, the element
`stageRoot i = ζ₃₀₀₃₀ ^ rootExponent i` is a primitive
`conductor i`-th root of unity. Hence the literal intermediate field
`fieldStage i = ℚ⟮stageRoot i⟯` is itself a `{conductor i}`-cyclotomic extension.

Mathlib's uniqueness theorem for cyclotomic extensions then gives a genuine
`ℚ`-algebra equivalence

  `CyclotomicField (conductor i) ℚ ≃ₐ[ℚ] fieldStage i`.

This closes the carrier-identification frontier without importing any CAS
assertion and transports the native Galois/abelian-Galois structure to the
literal nested stages in the common ambient field `K∞`.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeCyclotomicAmbientStageIdentification

open InfoGeometry.Arithmetic.PrimeCyclotomicDirectedTower
open InfoGeometry.Arithmetic.PrimeCyclotomicAmbientTower

/-- Every cumulative conductor is nonzero, bundled for cyclotomic APIs. -/
instance conductor_neZero (i : Fin 7) : NeZero (conductor i) :=
  ⟨conductor_ne_zero i⟩

/-- The terminal chosen root is primitive of order `30030`. -/
theorem zetaInfinity_isPrimitiveRoot : IsPrimitiveRoot ζ∞ 30030 := by
  exact IsCyclotomicExtension.zeta_spec 30030 ℚ K∞

/-- The stage generator is exactly a primitive root of the stage conductor. -/
theorem stageRoot_isPrimitiveRoot (i : Fin 7) :
    IsPrimitiveRoot (stageRoot i) (conductor i) := by
  exact zetaInfinity_isPrimitiveRoot.pow (by norm_num)
    (rootExponent_mul_conductor i).symm

/-- The ambient terminal cyclotomic field is integral over `ℚ`. -/
instance ambient_isIntegral : Algebra.IsIntegral ℚ K∞ :=
  IsCyclotomicExtension.integral ({30030} : Set ℕ) ℚ K∞

/-- Each literal nested intermediate field is itself the cyclotomic extension
of the corresponding cumulative conductor. -/
instance fieldStage_isCyclotomicExtension (i : Fin 7) :
    IsCyclotomicExtension {conductor i} ℚ (fieldStage i) := by
  simpa [fieldStage] using
    (stageRoot_isPrimitiveRoot i).intermediateField_adjoin_isCyclotomicExtension ℚ

/-- Native carrier identification: the separately constructed Mathlib
cyclotomic field and the literal nested ambient stage are the same cyclotomic
extension up to `ℚ`-algebra equivalence. -/
def stageAlgEquiv (i : Fin 7) :
    StageField i ≃ₐ[ℚ] fieldStage i :=
  IsCyclotomicExtension.algEquiv {conductor i} ℚ (StageField i) (fieldStage i)

/-- Every literal ambient stage is natively Galois over `ℚ`. -/
instance fieldStage_isGalois (i : Fin 7) : IsGalois ℚ (fieldStage i) :=
  IsCyclotomicExtension.isGalois {conductor i} ℚ (fieldStage i)

/-- Every literal ambient stage is in fact abelian Galois. -/
theorem fieldStage_isAbelianGalois (i : Fin 7) :
    IsAbelianGalois ℚ (fieldStage i) :=
  IsCyclotomicExtension.isAbelianGalois {conductor i} ℚ (fieldStage i)

/-- Constant-size terminal consumer: the literal terminal intermediate field
is Galois over `ℚ`. -/
theorem terminal_fieldStage_isGalois : IsGalois ℚ (fieldStage 6) := by
  infer_instance

/-- Constant-size terminal consumer: the literal terminal stage is abelian
Galois over `ℚ`. -/
theorem terminal_fieldStage_isAbelianGalois :
    IsAbelianGalois ℚ (fieldStage 6) :=
  fieldStage_isAbelianGalois 6

/-- Every directed stage in the literal nested tower carries the native Galois
structure; the proof depends only on the endpoint stage, not on a chosen path. -/
theorem directed_stage_isGalois {i j : Fin 7}
    (_p : DirectedPath i j) : IsGalois ℚ (fieldStage j) := by
  infer_instance

end InfoGeometry.Arithmetic.PrimeCyclotomicAmbientStageIdentification
