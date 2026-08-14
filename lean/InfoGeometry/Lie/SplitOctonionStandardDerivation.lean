import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.Algebra.Zorn.CanonicalDerivationBridge
import InfoGeometry.Lie.CanonicalZornDerivationDimension

noncomputable section
namespace InfoGeometry.Lie.SplitOctonionStandardDerivation

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Kingdon
open InfoGeometry.Algebra.Kingdon.Algebra
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.CanonicalDerivationBridge
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion
open InfoGeometry.Lie.CanonicalZornDerivation

/-- Baez's standard alternative-algebra derivation on the real split Kingdon owner. -/
noncomputable def kingdonStandardDerivation (x y : AbstractKingdon) :
    NonAssocDerivation ℝ AbstractKingdon :=
  stanDerivation (R := ℝ)
    (alternative_left formedBilin) (alternative_right formedBilin) x y

/-- Transport of a standard split-octonion derivation to the canonical Zorn carrier. -/
noncomputable def canonicalStandardEnd (x y : AbstractKingdon) : EndCZ :=
  kingdonCanonicalLinearEquiv.toLinearMap.comp
    ((kingdonStandardDerivation x y).toLinearMap.comp
      kingdonCanonicalLinearEquiv.symm.toLinearMap)

private theorem kingdonCanonicalLinearEquiv_symm_mul (X Y : CanonicalZorn) :
    kingdonCanonicalLinearEquiv.symm (X * Y) =
      kingdonCanonicalLinearEquiv.symm X * kingdonCanonicalLinearEquiv.symm Y := by
  apply kingdonCanonicalLinearEquiv.injective
  rw [kingdonCanonicalLinearEquiv.apply_symm_apply,
    kingdonCanonicalLinearEquiv_mul,
    kingdonCanonicalLinearEquiv.apply_symm_apply,
    kingdonCanonicalLinearEquiv.apply_symm_apply]
  rfl

/-- The transported Baez operator satisfies Leibniz on canonical Zorn matrices. -/
theorem canonicalStandardEnd_isDerivation (x y : AbstractKingdon) :
    IsDerivation (canonicalStandardEnd x y) := by
  intro X Y
  change kingdonCanonicalLinearEquiv
      ((kingdonStandardDerivation x y)
        (kingdonCanonicalLinearEquiv.symm (X * Y))) =
    kingdonCanonicalLinearEquiv
        ((kingdonStandardDerivation x y) (kingdonCanonicalLinearEquiv.symm X)) * Y +
      X * kingdonCanonicalLinearEquiv
        ((kingdonStandardDerivation x y) (kingdonCanonicalLinearEquiv.symm Y))
  rw [kingdonCanonicalLinearEquiv_symm_mul,
    (kingdonStandardDerivation x y).leibniz]
  simp only [map_add, kingdonCanonicalLinearEquiv_mul,
    zMul_eq_canonical_mul, LinearEquiv.apply_symm_apply]

/-- Baez's standard derivation as an element of the canonical split-octonion
14-dimensional derivation Lie algebra. -/
noncomputable def canonicalStandardDerivation (x y : AbstractKingdon) :
    canonicalZornDerivations :=
  ⟨canonicalStandardEnd x y, canonicalStandardEnd_isDerivation x y⟩

/-- Native target-space dimension for all canonical split-octonion derivations. -/
theorem canonical_derivation_finrank :
    Module.finrank ℝ canonicalZornDerivations = 14 :=
  CanonicalZornDerivationDimension.finrank_canonicalZornDerivations

private def canonicalL (x : CanonicalZorn) : CanonicalZorn →ₗ[ℝ] CanonicalZorn where
  toFun z := x * z
  map_add' := mul_add x
  map_smul' r z := mul_smul r x z

private def canonicalR (x : CanonicalZorn) : CanonicalZorn →ₗ[ℝ] CanonicalZorn where
  toFun z := z * x
  map_add' z w := add_mul z w x
  map_smul' r z := smul_mul r z x

/-- The standard endomorphism written directly in canonical Zorn coordinates. -/
def directCanonicalStanDerMap (x y : CanonicalZorn) :
    CanonicalZorn →ₗ[ℝ] CanonicalZorn :=
  canonicalL x ∘ₗ canonicalL y - canonicalL y ∘ₗ canonicalL x +
  (canonicalL x ∘ₗ canonicalR y - canonicalR y ∘ₗ canonicalL x) +
  (canonicalR x ∘ₗ canonicalR y - canonicalR y ∘ₗ canonicalR x)

@[simp] theorem directCanonicalStanDerMap_apply (x y z : CanonicalZorn) :
    directCanonicalStanDerMap x y z =
      (x * (y * z) - y * (x * z)) +
      (x * (z * y) - (x * z) * y) +
      ((z * y) * x - (z * x) * y) := rfl

/-- The Kingdon-transported standard derivation is exactly the direct
six-term standard endomorphism in canonical Zorn coordinates. -/
theorem canonicalStandardEnd_transport_eq_direct (x y : CanonicalZorn) :
    canonicalStandardEnd (kingdonCanonicalLinearEquiv.symm x)
      (kingdonCanonicalLinearEquiv.symm y) = directCanonicalStanDerMap x y := by
  apply LinearMap.ext
  intro z
  change kingdonCanonicalLinearEquiv
      (stanDerMap (R := ℝ) (kingdonCanonicalLinearEquiv.symm x)
        (kingdonCanonicalLinearEquiv.symm y) (kingdonCanonicalLinearEquiv.symm z)) = _
  simp [stanDerMap, L_map, R_map, directCanonicalStanDerMap, canonicalL, canonicalR,
    kingdonCanonicalLinearEquiv_mul, zMul_eq_canonical_mul]

/-! The normal form below is the structural replacement for expanding the
standard derivation into six coordinate products. -/

theorem directCanonicalStanDerMap_apply_normal_form (x y z : CanonicalZorn) :
    directCanonicalStanDerMap x y z =
      ((x * y - y * x) * z - z * (x * y - y * x)) -
        3 • ((x * y) * z - x * (y * z)) := by
  have ht := congrArg (fun F : EndCZ => F z)
    (canonicalStandardEnd_transport_eq_direct x y)
  change kingdonCanonicalLinearEquiv
      ((kingdonStandardDerivation (kingdonCanonicalLinearEquiv.symm x)
          (kingdonCanonicalLinearEquiv.symm y))
        (kingdonCanonicalLinearEquiv.symm z)) = directCanonicalStanDerMap x y z at ht
  let X := kingdonCanonicalLinearEquiv.symm x
  let Y := kingdonCanonicalLinearEquiv.symm y
  let Z := kingdonCanonicalLinearEquiv.symm z
  have hinner :
      (kingdonStandardDerivation X Y) Z =
      ((X * Y - Y * X) * Z - Z * (X * Y - Y * X)) -
        3 • ((X * Y) * Z - X * (Y * Z)) := by
    change stanDerMap _ _ _ = _
    rw [stanDerMap_apply_normal_form
      (InfoGeometry.Algebra.Kingdon.Algebra.alternative_left formedBilin)
      (InfoGeometry.Algebra.Kingdon.Algebra.alternative_right formedBilin)]
    rw [associator_apply]
  calc
    directCanonicalStanDerMap x y z =
        kingdonCanonicalLinearEquiv ((kingdonStandardDerivation X Y) Z) := ht.symm
    _ = kingdonCanonicalLinearEquiv
        (((X * Y - Y * X) * Z - Z * (X * Y - Y * X)) -
          3 • ((X * Y) * Z - X * (Y * Z))) := congrArg _ hinner
    _ = ((x * y - y * x) * z - z * (x * y - y * x)) -
        3 • ((x * y) * z - x * (y * z)) := by
      simp only [X, Y, Z, map_sub, map_nsmul, zMul_eq_canonical_mul,
        kingdonCanonicalLinearEquiv_mul, LinearEquiv.apply_symm_apply]

/-- Baez's standard derivation with canonical split-octonion inputs. -/
noncomputable def canonicalStandardDerivationOfCanonical (x y : CanonicalZorn) :
    canonicalZornDerivations :=
  ⟨directCanonicalStanDerMap x y, by
    rw [← canonicalStandardEnd_transport_eq_direct]
    exact canonicalStandardEnd_isDerivation _ _⟩

open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.CanonicalZornDerivationDimension

/-- Canonical diagonal basis element transported from the vector-Zorn owner. -/
abbrev canonicalE11 : CanonicalZorn := canonicalVectorEquiv.symm E11

/-- Canonical upper-vector basis element transported from the vector-Zorn owner. -/
abbrev canonicalU (i : Fin 3) : CanonicalZorn := canonicalVectorEquiv.symm (U i)

/-- Canonical lower-vector basis element transported from the vector-Zorn owner. -/
abbrev canonicalV (i : Fin 3) : CanonicalZorn := canonicalVectorEquiv.symm (V i)

/-- A scaled coordinate vector in the fourteen-parameter derivation model. -/
def parameterUnit (j : Fin 14) (r : ℝ := 1) : Params :=
  fun i => if i = j then r else 0

@[simp] private theorem neg_one_add_neg_one_sub_one :
    (-1 : ℝ) + (-1 - 1) = -3 := by norm_num

@[simp] private theorem neg_one_add_neg_one :
    (-1 : ℝ) + -1 = -2 := by norm_num

theorem standardColumn_E11_U0 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 0)) =
        parameterUnit 10 (-1) := by
  funext i
  by_cases h : i = 10 <;>
    simp_all [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalE11, canonicalU,
      E11, E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem standardColumn_E11_U1 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 1)) =
        parameterUnit 9 := by
  funext i
  by_cases h : i = 9 <;>
    simp_all [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalE11, canonicalU,
      E11, E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem standardColumn_E11_U2 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 2)) =
        parameterUnit 4 (-1) := by
  funext i
  by_cases h : i = 4 <;>
    simp_all [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalE11, canonicalU,
      E11, E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem standardColumn_E11_V0 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 0)) =
        parameterUnit 0 := by
  funext i
  by_cases h : i = 0 <;>
    simp_all [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalE11, canonicalV,
      E11, E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem standardColumn_E11_V1 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 1)) =
        parameterUnit 3 := by
  funext i
  by_cases h : i = 3 <;>
    simp_all [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalE11, canonicalV,
      E11, E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem standardColumn_E11_V2 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 2)) =
        parameterUnit 8 := by
  funext i
  by_cases h : i = 8 <;>
    simp_all [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalE11, canonicalV,
      E11, E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem standardColumn_U0_V0 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0)) =
        parameterUnit 6 + parameterUnit 13 := by
  funext i
  by_cases h6 : i = 6 <;> by_cases h13 : i = 13 <;>
    simp [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalU, canonicalV,
      E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv, h6, h13] ; omega

theorem standardColumn_U0_V1 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 1)) =
        parameterUnit 5 (-3) := by
  funext i
  by_cases h : i = 5 <;>
    simp_all [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalU, canonicalV,
      E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem standardColumn_U0_V2 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 2)) =
        parameterUnit 11 (-3) := by
  funext i
  by_cases h : i = 11 <;>
    simp_all [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalU, canonicalV,
      E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem standardColumn_U1_V0 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0)) =
        parameterUnit 1 (-3) := by
  funext i
  by_cases h : i = 1 <;>
    simp_all [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalU, canonicalV,
      E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem standardColumn_U1_V1 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1)) =
        parameterUnit 6 (-2) + parameterUnit 13 := by
  funext i
  by_cases h6 : i = 6 <;> by_cases h13 : i = 13 <;>
    simp [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalU, canonicalV,
      E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv, h6, h13] ; omega

theorem standardColumn_U1_V2 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 2)) =
        parameterUnit 12 (-3) := by
  funext i
  by_cases h : i = 12 <;>
    simp_all [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalU, canonicalV,
      E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem standardColumn_U2_V0 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0)) =
        parameterUnit 2 (-3) := by
  funext i
  by_cases h : i = 2 <;>
    simp_all [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalU, canonicalV,
      E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem standardColumn_U2_V1 :
    canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1)) =
        parameterUnit 7 (-3) := by
  funext i
  by_cases h : i = 7 <;>
    simp_all [canonicalParameterLinearEquiv, parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      parameterUnit, derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalU, canonicalV,
      E22, U, V, ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

/-- The subspace generated by all canonical standard derivations. -/
abbrev standardDerivationSpan : Submodule ℝ canonicalZornDerivations :=
  Submodule.span ℝ (Set.range (fun p : CanonicalZorn × CanonicalZorn =>
    canonicalStandardDerivationOfCanonical p.1 p.2))

private theorem canonicalStandardDerivation_mem_span (x y : CanonicalZorn) :
    canonicalStandardDerivationOfCanonical x y ∈ standardDerivationSpan :=
  Submodule.subset_span ⟨(x, y), rfl⟩

theorem parameterUnit_eq_smul (j : Fin 14) (r : ℝ) :
    parameterUnit j r = r • parameterUnit j := by
  funext i
  by_cases h : i = j <;> simp [parameterUnit, h]

private theorem scaledParameterUnit_mem
    (x y : CanonicalZorn) (j : Fin 14) (r : ℝ)
    (hr : r ≠ 0)
    (hcol : canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical x y) = parameterUnit j r) :
    canonicalParameterLinearEquiv (parameterUnit j) ∈ standardDerivationSpan := by
  have hm := standardDerivationSpan.smul_mem r⁻¹
    (canonicalStandardDerivation_mem_span x y)
  have heq : r⁻¹ • canonicalStandardDerivationOfCanonical x y =
      canonicalParameterLinearEquiv (parameterUnit j) := by
    apply canonicalParameterLinearEquiv.symm.injective
    rw [map_smul, hcol, parameterUnit_eq_smul]
    simp [smul_smul, hr]
  rwa [heq] at hm

theorem parameterUnit_six_mem :
    canonicalParameterLinearEquiv (parameterUnit 6) ∈ standardDerivationSpan := by
  let A := canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0)
  let B := canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1)
  have hA : A ∈ standardDerivationSpan := canonicalStandardDerivation_mem_span _ _
  have hB : B ∈ standardDerivationSpan := canonicalStandardDerivation_mem_span _ _
  have hm := standardDerivationSpan.smul_mem (1 / 3 : ℝ)
    (standardDerivationSpan.sub_mem hA hB)
  have heq : (1 / 3 : ℝ) • (A - B) =
      canonicalParameterLinearEquiv (parameterUnit 6) := by
    apply canonicalParameterLinearEquiv.symm.injective
    rw [map_smul, map_sub]
    change (1 / 3 : ℝ) •
        (canonicalParameterLinearEquiv.symm A - canonicalParameterLinearEquiv.symm B) = _
    rw [show canonicalParameterLinearEquiv.symm A =
          parameterUnit 6 + parameterUnit 13 by exact standardColumn_U0_V0,
      show canonicalParameterLinearEquiv.symm B =
          parameterUnit 6 (-2) + parameterUnit 13 by exact standardColumn_U1_V1]
    funext i
    by_cases h6 : i = 6 <;> by_cases h13 : i = 13 <;>
      norm_num [parameterUnit, h6, h13, Fin.ext_iff]
  rwa [heq] at hm

theorem parameterUnit_thirteen_mem :
    canonicalParameterLinearEquiv (parameterUnit 13) ∈ standardDerivationSpan := by
  let A := canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0)
  let B := canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1)
  have hA : A ∈ standardDerivationSpan := canonicalStandardDerivation_mem_span _ _
  have hB : B ∈ standardDerivationSpan := canonicalStandardDerivation_mem_span _ _
  have hm := standardDerivationSpan.smul_mem (1 / 3 : ℝ)
    (standardDerivationSpan.add_mem (standardDerivationSpan.smul_mem (2 : ℝ) hA) hB)
  have heq : (1 / 3 : ℝ) • ((2 : ℝ) • A + B) =
      canonicalParameterLinearEquiv (parameterUnit 13) := by
    apply canonicalParameterLinearEquiv.symm.injective
    rw [map_smul, map_add, map_smul]
    change (1 / 3 : ℝ) •
        (2 • canonicalParameterLinearEquiv.symm A +
          canonicalParameterLinearEquiv.symm B) = _
    rw [show canonicalParameterLinearEquiv.symm A =
          parameterUnit 6 + parameterUnit 13 by exact standardColumn_U0_V0,
      show canonicalParameterLinearEquiv.symm B =
          parameterUnit 6 (-2) + parameterUnit 13 by exact standardColumn_U1_V1]
    funext i
    by_cases h6 : i = 6 <;> by_cases h13 : i = 13 <;>
      norm_num [parameterUnit, h6, h13, Fin.ext_iff]
  rwa [heq] at hm

noncomputable def parameterUnitsInSpan : Fin 14 → standardDerivationSpan := ![
  ⟨canonicalParameterLinearEquiv (parameterUnit 0),
    scaledParameterUnit_mem canonicalE11 (canonicalV 0) 0 1 (by norm_num)
      standardColumn_E11_V0⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 1),
    scaledParameterUnit_mem (canonicalU 1) (canonicalV 0) 1 (-3) (by norm_num)
      standardColumn_U1_V0⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 2),
    scaledParameterUnit_mem (canonicalU 2) (canonicalV 0) 2 (-3) (by norm_num)
      standardColumn_U2_V0⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 3),
    scaledParameterUnit_mem canonicalE11 (canonicalV 1) 3 1 (by norm_num)
      standardColumn_E11_V1⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 4),
    scaledParameterUnit_mem canonicalE11 (canonicalU 2) 4 (-1) (by norm_num)
      standardColumn_E11_U2⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 5),
    scaledParameterUnit_mem (canonicalU 0) (canonicalV 1) 5 (-3) (by norm_num)
      standardColumn_U0_V1⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 6), parameterUnit_six_mem⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 7),
    scaledParameterUnit_mem (canonicalU 2) (canonicalV 1) 7 (-3) (by norm_num)
      standardColumn_U2_V1⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 8),
    scaledParameterUnit_mem canonicalE11 (canonicalV 2) 8 1 (by norm_num)
      standardColumn_E11_V2⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 9),
    scaledParameterUnit_mem canonicalE11 (canonicalU 1) 9 1 (by norm_num)
      standardColumn_E11_U1⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 10),
    scaledParameterUnit_mem canonicalE11 (canonicalU 0) 10 (-1) (by norm_num)
      standardColumn_E11_U0⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 11),
    scaledParameterUnit_mem (canonicalU 0) (canonicalV 2) 11 (-3) (by norm_num)
      standardColumn_U0_V2⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 12),
    scaledParameterUnit_mem (canonicalU 1) (canonicalV 2) 12 (-3) (by norm_num)
      standardColumn_U1_V2⟩,
  ⟨canonicalParameterLinearEquiv (parameterUnit 13), parameterUnit_thirteen_mem⟩
]

theorem parameterUnitsInSpan_coe (j : Fin 14) :
    (parameterUnitsInSpan j : canonicalZornDerivations) =
      canonicalParameterLinearEquiv (parameterUnit j) := by
  revert j
  simp [Fin.forall_iff_succ, parameterUnitsInSpan]

theorem parameterUnit_mem (j : Fin 14) :
    canonicalParameterLinearEquiv (parameterUnit j) ∈ standardDerivationSpan := by
  rw [← parameterUnitsInSpan_coe j]
  exact (parameterUnitsInSpan j).property

private theorem parameters_decompose (p : Params) :
    p = ∑ i : Fin 14, p i • parameterUnit i := by
  funext j
  simp [parameterUnit]

/-- Every canonical split-octonion derivation is a finite real-linear
combination of Baez standard derivations `D_{x,y}`. -/
theorem standardDerivations_span_top :
    standardDerivationSpan = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro D
  let p := canonicalParameterLinearEquiv.symm D
  have hp : p = ∑ i : Fin 14, p i • parameterUnit i := parameters_decompose p
  have hD : D = ∑ i : Fin 14,
      p i • canonicalParameterLinearEquiv (parameterUnit i) := by
    rw [← canonicalParameterLinearEquiv.apply_symm_apply D]
    change canonicalParameterLinearEquiv p = _
    calc
      canonicalParameterLinearEquiv p =
          canonicalParameterLinearEquiv (∑ i : Fin 14, p i • parameterUnit i) :=
        congrArg canonicalParameterLinearEquiv hp
      _ = _ := by simp only [map_sum, map_smul]
  rw [hD]
  exact Submodule.sum_mem standardDerivationSpan
    (fun i _ => standardDerivationSpan.smul_mem _ (parameterUnit_mem i))

end InfoGeometry.Lie.SplitOctonionStandardDerivation
