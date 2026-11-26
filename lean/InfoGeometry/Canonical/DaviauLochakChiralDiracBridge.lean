/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge
import InfoGeometry.Canonical.GeometroMagnetoGravityCrankingDirac
import InfoGeometry.Clifford.DaviauRealDirac8x8
import InfoGeometry.Clifford.DaviauChiralPeirceSU2
import InfoGeometry.Clifford.LochakRodichevFierzKrein
import Mathlib.Tactic

/-!
# Daviau–Lochak Chiral Peirce `su(2) ⊕ su(2)` & Fierz–Takabayasi Bridge

Constructs the exact bridge connecting our canonical 8D real Majorana–Dirac bispinor modules
(`DiracSpinCasimirNambuModulesBridge` and `GeometroMagnetoGravityCrankingDirac`) to the
existing Daviau–Lochak `M₈(ℝ)` Clifford spine (`DaviauRealDirac8x8`, `DaviauChiralPeirceSU2`,
and `LochakRodichevFierzKrein`):

1. **Exact `O(8)` Orthogonal Intertwiner (`daviau_chiral_peirce_su2_orthogonal_intertwiner`)**:
   Explicit sparse orthogonal matrix `daviauIntertwinerR = (1 / √2) • castZ8 daviauIntertwinerZ`
   (`Uᵀ U = U Uᵀ = I₈`) intertwining:
   - `peirceRight 2 ↔ pPlus2 ⊗ₖ I₄`, `peirceLeft 2 ↔ pMinus2 ⊗ₖ I₄`,
   - `gamma0123R * quatPR 2 ↔ bispinorCut`,
   - `bispinorMir ↔ gammaR 0 = kreinMetric8`,
   - `(1/2) • genY 2 k ↔ chiralSpinB (spinJ_{k+1}) (boostK_{k+1})` and
     `(1/2) • genB 2 k ↔ chiralSpinA (spinJ_{k+1}) (boostK_{k+1})` for `k = 0, 1, 2`.
2. **Lochak Eq. (39) ↔ Chiral Null Current Identities (`lochak_eq39_matches_geometromagnetogravity_chiral_currents`)**:
   Explicit linear coordinate identification `Φ : Vec8R ↦ (a₁, b₁, a₂, b₂, c₁, d₁, c₂, d₂)`
   matching `diracVectorCurrent = electricCurrentJ`, `diracAxialCurrent = axialCurrentSigma`,
   `diracScalarOmega1 = omega1`, `diracPseudoscalarOmega2 = -omega2`, Minkowski Fierz–Kofink
   pairings, `lochak_eq39_fierz_takabayasi`, and Einstein–Cartan axial torsion cranking.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE THEOREMS
* `daviau_chiral_peirce_su2_orthogonal_intertwiner`
* `lochak_eq39_matches_geometromagnetogravity_chiral_currents`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* None (all identities hold unconditionally over `ℝ`).

#### BUCKET 3: OPEN CLOSURE DEBT
* Continuum spacetime Dirac–Lochak PDE solutions remain outside this finite-dimensional bridge.
-/

noncomputable section

open scoped BigOperators Kronecker
open Matrix

namespace InfoGeometry.Canonical.DaviauLochakChiralDiracBridge

open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
open InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
open InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge
open InfoGeometry.Canonical.GeometroMagnetoGravityCrankingDirac
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Clifford.DaviauRealDirac8x8
open InfoGeometry.Clifford.DaviauChiralPeirceSU2
open InfoGeometry.Clifford.LochakRodichevFierzKrein
open InfoGeometry.Canonical.KreinMajoranaBlockInvariance (kreinMetric8 kreinInnerProduct)

/-! ### Part 1: Exact `O(8)` Orthogonal Intertwiner (`M₈(ℝ)` Bispinor ↔ `DaviauChiralPeirceSU2`) -/

/-- Flatten `(a, (i, j)) ∈ Fin 2 × (Fin 2 × Fin 2)` to `Fin 8` via `4 a + 2 i + j`. -/
def bispinorToFin8 (p : Fin 2 × (Fin 2 × Fin 2)) : Fin 8 :=
  ⟨4 * p.1.val + 2 * p.2.1.val + p.2.2.val, by omega⟩

/-- Unflatten `k ∈ Fin 8` back to `Fin 2 × (Fin 2 × Fin 2)`. -/
def fin8ToBispinor (k : Fin 8) : Fin 2 × (Fin 2 × Fin 2) :=
  (⟨k.val / 4, by omega⟩, (⟨(k.val % 4) / 2, by omega⟩, ⟨k.val % 2, by omega⟩))

/-- Explicit coordinate equivalence `Fin 2 × (Fin 2 × Fin 2) ≃ Fin 8`. -/
def bispinorIdxEquiv : Fin 2 × (Fin 2 × Fin 2) ≃ Fin 8 where
  toFun := bispinorToFin8
  invFun := fin8ToBispinor
  left_inv := by
    rintro ⟨a, ⟨i, j⟩⟩
    fin_cases a <;> fin_cases i <;> fin_cases j <;> decide
  right_inv := by
    intro k
    fin_cases k <;> decide

/-- Reindex a real `Fin 2 × (Fin 2 × Fin 2)` operator into `Mat8R`. -/
def bispinorToDaviauMat
    (A : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℝ) : Mat8R :=
  Matrix.reindex bispinorIdxEquiv bispinorIdxEquiv A

/-- Reindex an integer `Fin 2 × (Fin 2 × Fin 2)` operator into `Mat8Z`. -/
def bispinorToDaviauZ
    (A : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℤ) : Mat8Z :=
  Matrix.reindex bispinorIdxEquiv bispinorIdxEquiv A

/-- Scaled `ℤ`-matrix `M = √2 • U ∈ M₈(ℤ)` defining the orthogonal intertwiner `U`. -/
def daviauIntertwinerZ : Mat8Z :=
  !![-1,  0,  0,  0, -1,  0,  0,  0;
      0,  0,  0,  1,  0,  0,  0,  1;
      0,  0,  1,  0,  0,  0,  1,  0;
      0,  1,  0,  0,  0,  1,  0,  0;
      0,  1,  0,  0,  0, -1,  0,  0;
      0,  0, -1,  0,  0,  0,  1,  0;
      0,  0,  0, -1,  0,  0,  0,  1;
     -1,  0,  0,  0,  1,  0,  0,  0]

/-- Exact `O(8)` orthogonal intertwiner `U = (1 / √2) • M ∈ M₈(ℝ)`. -/
def daviauIntertwinerR : Mat8R :=
  (1 / Real.sqrt 2 : ℝ) • castZ8 daviauIntertwinerZ

private def id2Z' : Matrix (Fin 2) (Fin 2) ℤ := 1
private def pPlus2Z' : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]
private def pMinus2Z' : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 0, 1]
private def zCut2Z' : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]
private def xMir2Z' : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
private def eps2Z' : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]
private def id4Z' : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ := 1

private def dGamma0Z4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ := eps2Z' ⊗ₖ id2Z'
private def dGamma1Z4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ := xMir2Z' ⊗ₖ zCut2Z'
private def dGamma2Z4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ := xMir2Z' ⊗ₖ xMir2Z'
private def dGamma3Z4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ := zCut2Z' ⊗ₖ id2Z'
private def dOmegaZ4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ :=
  dGamma0Z4 * dGamma1Z4 * dGamma2Z4 * dGamma3Z4

private lemma intertwinerZ_mul_transpose :
    daviauIntertwinerZ * daviauIntertwinerZᵀ = (2 : ℤ) • (1 : Mat8Z) := by
  decide

private lemma intertwinerZ_transpose_mul :
    daviauIntertwinerZᵀ * daviauIntertwinerZ = (2 : ℤ) • (1 : Mat8Z) := by
  decide

private lemma intertwinerZ_peirceRight :
    daviauIntertwinerZᵀ * twoPeirceRightZ ⟨2, by decide⟩ * daviauIntertwinerZ =
      (4 : ℤ) • bispinorToDaviauZ (pPlus2Z' ⊗ₖ id4Z') := by
  decide

private lemma intertwinerZ_peirceLeft :
    daviauIntertwinerZᵀ * twoPeirceLeftZ ⟨2, by decide⟩ * daviauIntertwinerZ =
      (4 : ℤ) • bispinorToDaviauZ (pMinus2Z' ⊗ₖ id4Z') := by
  decide

private lemma intertwinerZ_cut :
    daviauIntertwinerZᵀ * (gamma0123Z * quatPZ ⟨2, by decide⟩) * daviauIntertwinerZ =
      (2 : ℤ) • bispinorToDaviauZ (zCut2Z' ⊗ₖ id4Z') := by
  decide

private lemma intertwinerZ_mir :
    daviauIntertwinerZ * bispinorToDaviauZ (xMir2Z' ⊗ₖ id4Z') * daviauIntertwinerZᵀ =
      (2 : ℤ) • gamma0Z := by
  decide

private lemma intertwinerZ_genY0 :
    daviauIntertwinerZᵀ * twoGenYZ ⟨2, by decide⟩ ⟨0, by decide⟩ * daviauIntertwinerZ =
      (-4 : ℤ) • bispinorToDaviauZ (pPlus2Z' ⊗ₖ (dGamma2Z4 * dGamma3Z4)) := by
  decide

private lemma intertwinerZ_genY1 :
    daviauIntertwinerZᵀ * twoGenYZ ⟨2, by decide⟩ ⟨1, by decide⟩ * daviauIntertwinerZ =
      (-4 : ℤ) • bispinorToDaviauZ (pPlus2Z' ⊗ₖ (dGamma3Z4 * dGamma1Z4)) := by
  decide

private lemma intertwinerZ_genY2 :
    daviauIntertwinerZᵀ * twoGenYZ ⟨2, by decide⟩ ⟨2, by decide⟩ * daviauIntertwinerZ =
      (-4 : ℤ) • bispinorToDaviauZ (pPlus2Z' ⊗ₖ (dGamma1Z4 * dGamma2Z4)) := by
  decide

private lemma intertwinerZ_genB0 :
    daviauIntertwinerZᵀ * twoGenBZ ⟨2, by decide⟩ ⟨0, by decide⟩ * daviauIntertwinerZ =
      (-4 : ℤ) • bispinorToDaviauZ (pMinus2Z' ⊗ₖ (dGamma2Z4 * dGamma3Z4)) := by
  decide

private lemma intertwinerZ_genB1 :
    daviauIntertwinerZᵀ * twoGenBZ ⟨2, by decide⟩ ⟨1, by decide⟩ * daviauIntertwinerZ =
      (-4 : ℤ) • bispinorToDaviauZ (pMinus2Z' ⊗ₖ (dGamma3Z4 * dGamma1Z4)) := by
  decide

private lemma intertwinerZ_genB2 :
    daviauIntertwinerZᵀ * twoGenBZ ⟨2, by decide⟩ ⟨2, by decide⟩ * daviauIntertwinerZ =
      (-4 : ℤ) • bispinorToDaviauZ (pMinus2Z' ⊗ₖ (dGamma1Z4 * dGamma2Z4)) := by
  decide

private lemma omegaZ4_mul_boostZ :
    (dOmegaZ4 * (dGamma0Z4 * dGamma1Z4) = dGamma2Z4 * dGamma3Z4) ∧
    (dOmegaZ4 * (dGamma0Z4 * dGamma2Z4) = dGamma3Z4 * dGamma1Z4) ∧
    (dOmegaZ4 * (dGamma0Z4 * dGamma3Z4) = dGamma1Z4 * dGamma2Z4) := by
  decide

private lemma inv_sqrt_two_sq :
    (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ) = (1 / 2 : ℝ) := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc
    (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ)
        = 1 / (Real.sqrt 2 * Real.sqrt 2) := by ring
    _ = 1 / 2 := by rw [hsq]

private lemma scalar_half_two_eq_one : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by ring
private lemma scalar_quarter_four_eq_one : ((1 / 2 : ℝ) * (1 / 2 : ℝ)) * (4 : ℝ) = 1 := by ring
private lemma scalar_eighth_neg_four_eq_neg_half :
    ((1 / 2 : ℝ) * ((1 / 2 : ℝ) * (1 / 2 : ℝ))) * (-4 : ℝ) = -(1 / 2 : ℝ) := by ring

private lemma bispinorToDaviauMat_cast
    (A : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℤ) :
    castZ8 (bispinorToDaviauZ A) = bispinorToDaviauMat ((Int.castRingHom ℝ).mapMatrix A) := by
  ext i j
  simp [bispinorToDaviauMat, bispinorToDaviauZ, castZ8, Matrix.reindex_apply]

private def cast4' (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (Int.castRingHom ℝ).mapMatrix A

private lemma cast4'_mul (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ) :
    cast4' (A * B) = cast4' A * cast4' B :=
  (Int.castRingHom ℝ).mapMatrix.map_mul A B

private lemma cast4'_dGamma0 : cast4' dGamma0Z4 = diracGamma0 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [cast4', dGamma0Z4, diracGamma0, eps2Z', id2Z', eps2, Matrix.kroneckerMap_apply]

private lemma cast4'_dGamma1 : cast4' dGamma1Z4 = diracGamma1 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [cast4', dGamma1Z4, diracGamma1, xMir2Z', zCut2Z', xMir2, zCut2, Matrix.kroneckerMap_apply]

private lemma cast4'_dGamma2 : cast4' dGamma2Z4 = diracGamma2 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [cast4', dGamma2Z4, diracGamma2, xMir2Z', xMir2, Matrix.kroneckerMap_apply]

private lemma cast4'_dGamma3 : cast4' dGamma3Z4 = diracGamma3 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [cast4', dGamma3Z4, diracGamma3, zCut2Z', id2Z', zCut2, Matrix.kroneckerMap_apply]

private lemma cast_kron_mapMatrix {n₁ : Type*} [Fintype n₁] [DecidableEq n₁]
    (A : Matrix (Fin 2) (Fin 2) ℤ) (B : Matrix n₁ n₁ ℤ) :
    (Int.castRingHom ℝ).mapMatrix (A ⊗ₖ B) =
      ((Int.castRingHom ℝ).mapMatrix A) ⊗ₖ ((Int.castRingHom ℝ).mapMatrix B) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [Matrix.kroneckerMap_apply, Int.cast_mul]

private lemma cast_pPlus2Z : (Int.castRingHom ℝ).mapMatrix pPlus2Z' = pPlus2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pPlus2Z', pPlus2]

private lemma cast_pMinus2Z : (Int.castRingHom ℝ).mapMatrix pMinus2Z' = pMinus2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pMinus2Z', pMinus2]

private lemma cast_id4Z :
    cast4' id4Z' = (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [cast4', id4Z']

private lemma cast_zCut2_kron_id4 :
    (Int.castRingHom ℝ).mapMatrix (zCut2Z' ⊗ₖ id4Z') = bispinorCut := by
  ext ⟨a, ⟨i₁, i₂⟩⟩ ⟨b, ⟨j₁, j₂⟩⟩
  fin_cases a <;> fin_cases b <;>
    simp [bispinorCut, zCut2Z', id4Z', zCut2, Matrix.kroneckerMap_apply, Matrix.one_apply]

private lemma cast_xMir2_kron_id4 :
    (Int.castRingHom ℝ).mapMatrix (xMir2Z' ⊗ₖ id4Z') = bispinorMir := by
  ext ⟨a, ⟨i₁, i₂⟩⟩ ⟨b, ⟨j₁, j₂⟩⟩
  fin_cases a <;> fin_cases b <;>
    simp [bispinorMir, xMir2Z', id4Z', xMir2, Matrix.kroneckerMap_apply, Matrix.one_apply]

private lemma castZ8_gamma0Z_eq_kreinMetric8 : castZ8 gamma0Z = kreinMetric8 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [castZ8, gamma0Z, kreinMetric8]

private lemma kron_smul_left' {a : Type*} (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (B : Matrix a a ℝ) : (c • A) ⊗ₖ B = c • (A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.kroneckerMap_apply, mul_assoc]

private lemma kron_smul_right' {a : Type*} (c : ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) (M : Matrix a a ℝ) :
    P ⊗ₖ (c • M) = c • (P ⊗ₖ M) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.kroneckerMap_apply, mul_left_comm]

private lemma kron_sub_left' {a : Type*} (A₁ A₂ : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix a a ℝ) :
    (A₁ - A₂) ⊗ₖ B = A₁ ⊗ₖ B - A₂ ⊗ₖ B := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.kroneckerMap_apply, sub_mul]

private lemma kron_add_left' {a : Type*} (A₁ A₂ : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix a a ℝ) :
    (A₁ + A₂) ⊗ₖ B = A₁ ⊗ₖ B + A₂ ⊗ₖ B := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.kroneckerMap_apply, add_mul]

private lemma kron_neg_right' {a : Type*} (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix a a ℝ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.kroneckerMap_apply]

private lemma zCut2_half_sub_add :
    (1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) - zCut2) = pMinus2 ∧
    (1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) + zCut2) = pPlus2 := by
  constructor <;>
    { ext i j; fin_cases i <;> fin_cases j <;> (simp [zCut2, pPlus2, pMinus2]; try norm_num) }

private lemma chiralSpin_of_boost_eq
    (J K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) (hOK : diracOmega4 * K = -J) :
    chiralSpinA J K = pMinus2 ⊗ₖ J ∧ chiralSpinB J K = pPlus2 ⊗ₖ J := by
  have hProd : bispinorIcplx * bispinorK K = -(zCut2 ⊗ₖ J) := by
    unfold bispinorIcplx bispinorK
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hOK, kron_neg_right']
  constructor
  · unfold chiralSpinA bispinorJ
    rw [hProd, ← sub_eq_add_neg, ← kron_sub_left', ← kron_smul_left', zCut2_half_sub_add.1]
  · unfold chiralSpinB bispinorJ
    rw [hProd, sub_neg_eq_add, ← kron_add_left', ← kron_smul_left', zCut2_half_sub_add.2]

private lemma diracOmega4_mul_boosts' :
    diracOmega4 * boostK1 = -spinJ1 ∧
    diracOmega4 * boostK2 = -spinJ2 ∧
    diracOmega4 * boostK3 = -spinJ3 := by
  have hZ := omegaZ4_mul_boostZ
  have hOm : diracOmega4 = cast4' dOmegaZ4 := by
    unfold diracOmega4 dOmegaZ4
    rw [cast4'_mul, cast4'_mul, cast4'_mul, cast4'_dGamma0, cast4'_dGamma1, cast4'_dGamma2,
      cast4'_dGamma3]
  refine ⟨?_, ?_, ?_⟩
  · unfold boostK1 spinJ1
    rw [hOm, ← cast4'_dGamma0, ← cast4'_dGamma1, ← cast4'_dGamma2, ← cast4'_dGamma3,
      ← cast4'_mul, Matrix.mul_smul, ← cast4'_mul, hZ.1, cast4'_mul, neg_smul, neg_neg]
  · unfold boostK2 spinJ2
    rw [hOm, ← cast4'_dGamma0, ← cast4'_dGamma2, ← cast4'_dGamma3, ← cast4'_dGamma1,
      ← cast4'_mul, Matrix.mul_smul, ← cast4'_mul, hZ.2.1, cast4'_mul, neg_smul, neg_neg]
  · unfold boostK3 spinJ3
    rw [hOm, ← cast4'_dGamma0, ← cast4'_dGamma3, ← cast4'_dGamma1, ← cast4'_dGamma2,
      ← cast4'_mul, Matrix.mul_smul, ← cast4'_mul, hZ.2.2, cast4'_mul, neg_smul, neg_neg]

private lemma scalar_intertwiner_gen :
    1 / Real.sqrt 2 * (1 / 2 * (1 / 2) * (1 / Real.sqrt 2)) * ((-4 : ℤ) : ℝ) = -(1 / 2 : ℝ) := by
  calc
    1 / Real.sqrt 2 * (1 / 2 * (1 / 2) * (1 / Real.sqrt 2)) * ((-4 : ℤ) : ℝ)
        = (1 / Real.sqrt 2 * (1 / Real.sqrt 2)) * (-1 : ℝ) := by push_cast; ring
    _ = -(1 / 2 : ℝ) := by rw [inv_sqrt_two_sq]; norm_num

private lemma intertwiner_conj_twoGenYZ (k : Fin 3)
    (G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ)
    (hZ : daviauIntertwinerZᵀ * twoGenYZ ⟨2, by decide⟩ k * daviauIntertwinerZ =
      (-4 : ℤ) • bispinorToDaviauZ (pPlus2Z' ⊗ₖ G)) :
    daviauIntertwinerRᵀ * ((1 / 2 : ℝ) • genY ⟨2, by decide⟩ k) * daviauIntertwinerR =
      bispinorToDaviauMat (pPlus2 ⊗ₖ (-(1 / 2 : ℝ) • cast4' G)) := by
  unfold daviauIntertwinerR genY
  simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← castZ8_transpose, ← castZ8_mul, ← castZ8_mul, hZ, castZ8_zsmul, smul_smul]
  rw [scalar_intertwiner_gen, bispinorToDaviauMat_cast, cast_kron_mapMatrix,
    cast_pPlus2Z, kron_smul_right']
  ext i j
  simp [bispinorToDaviauMat, cast4', Matrix.reindex_apply]

private lemma intertwiner_conj_twoGenBZ (k : Fin 3)
    (G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ)
    (hZ : daviauIntertwinerZᵀ * twoGenBZ ⟨2, by decide⟩ k * daviauIntertwinerZ =
      (-4 : ℤ) • bispinorToDaviauZ (pMinus2Z' ⊗ₖ G)) :
    daviauIntertwinerRᵀ * ((1 / 2 : ℝ) • genB ⟨2, by decide⟩ k) * daviauIntertwinerR =
      bispinorToDaviauMat (pMinus2 ⊗ₖ (-(1 / 2 : ℝ) • cast4' G)) := by
  unfold daviauIntertwinerR genB
  simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← castZ8_transpose, ← castZ8_mul, ← castZ8_mul, hZ, castZ8_zsmul, smul_smul]
  rw [scalar_intertwiner_gen, bispinorToDaviauMat_cast, cast_kron_mapMatrix,
    cast_pMinus2Z, kron_smul_right']
  ext i j
  simp [bispinorToDaviauMat, cast4', Matrix.reindex_apply]

/-- **Theorem 1 (Exact `O(8)` Orthogonal Intertwiner: `DiracSpinCasimirNambuModulesBridge` ↔ `DaviauChiralPeirceSU2`)**:
1. `Uᵀ U = U Uᵀ = I₈` (`U ∈ O(8)`).
2. Chiral Peirce projectors match:
   `Uᵀ p'₂ U = P₊ ⊗ₖ I₄`, `Uᵀ p₂ U = P₋ ⊗ₖ I₄`, and `Uᵀ (Γ^{0123} P₃) U = bispinorCut`.
3. Mirror exchange intertwines `bispinorMir` onto the Krein fundamental symmetry `Γ⁰ = kreinMetric8`.
4. All six chiral `su(2)` spin generators match identically for `k = 0, 1, 2`:
   `Uᵀ ((1/2) • Y_k) U = chiralSpinB J_{k+1} K_{k+1}` and
   `Uᵀ ((1/2) • B_k) U = chiralSpinA J_{k+1} K_{k+1}`. -/
theorem daviau_chiral_peirce_su2_orthogonal_intertwiner :
    let U := daviauIntertwinerR
    let j3 : Fin 3 := ⟨2, by decide⟩
    (Uᵀ * U = 1 ∧ U * Uᵀ = 1) ∧
    (Uᵀ * peirceRight j3 * U =
      bispinorToDaviauMat (pPlus2 ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ))) ∧
    (Uᵀ * peirceLeft j3 * U =
      bispinorToDaviauMat (pMinus2 ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ))) ∧
    (Uᵀ * (gamma0123R * quatPR j3) * U = bispinorToDaviauMat bispinorCut) ∧
    (U * bispinorToDaviauMat bispinorMir * Uᵀ = gammaR 0 ∧
      U * bispinorToDaviauMat bispinorMir * Uᵀ = kreinMetric8) ∧
    (Uᵀ * ((1 / 2 : ℝ) • genY j3 ⟨0, by decide⟩) * U =
      bispinorToDaviauMat (chiralSpinB spinJ1 boostK1) ∧
     Uᵀ * ((1 / 2 : ℝ) • genY j3 ⟨1, by decide⟩) * U =
      bispinorToDaviauMat (chiralSpinB spinJ2 boostK2) ∧
     Uᵀ * ((1 / 2 : ℝ) • genY j3 ⟨2, by decide⟩) * U =
      bispinorToDaviauMat (chiralSpinB spinJ3 boostK3)) ∧
    (Uᵀ * ((1 / 2 : ℝ) • genB j3 ⟨0, by decide⟩) * U =
      bispinorToDaviauMat (chiralSpinA spinJ1 boostK1) ∧
     Uᵀ * ((1 / 2 : ℝ) • genB j3 ⟨1, by decide⟩) * U =
      bispinorToDaviauMat (chiralSpinA spinJ2 boostK2) ∧
     Uᵀ * ((1 / 2 : ℝ) • genB j3 ⟨2, by decide⟩) * U =
      bispinorToDaviauMat (chiralSpinA spinJ3 boostK3)) := by
  dsimp only
  have hInv : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ) = (1 / 2 : ℝ) := inv_sqrt_two_sq
  have hOrthL : daviauIntertwinerRᵀ * daviauIntertwinerR = 1 := by
    unfold daviauIntertwinerR
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← castZ8_transpose, ← castZ8_mul, intertwinerZ_transpose_mul, castZ8_zsmul, castZ8_one,
      smul_smul]
    have hSc : 1 / Real.sqrt 2 * (1 / Real.sqrt 2) * ((2 : ℤ) : ℝ) = 1 := by rw [hInv]; norm_num
    rw [hSc, one_smul]
  have hOrthR : daviauIntertwinerR * daviauIntertwinerRᵀ = 1 := by
    unfold daviauIntertwinerR
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← castZ8_transpose, ← castZ8_mul, intertwinerZ_mul_transpose, castZ8_zsmul, castZ8_one,
      smul_smul]
    have hSc : 1 / Real.sqrt 2 * (1 / Real.sqrt 2) * ((2 : ℤ) : ℝ) = 1 := by rw [hInv]; norm_num
    rw [hSc, one_smul]
  have hPR : daviauIntertwinerRᵀ * peirceRight ⟨2, by decide⟩ * daviauIntertwinerR =
      bispinorToDaviauMat (pPlus2 ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) := by
    unfold daviauIntertwinerR
    rw [peirceRight_eq_half_cast]
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← castZ8_transpose, ← castZ8_mul, ← castZ8_mul, intertwinerZ_peirceRight,
      castZ8_zsmul, smul_smul]
    have hSc : 1 / Real.sqrt 2 * (1 / 2 * (1 / Real.sqrt 2)) * ((4 : ℤ) : ℝ) = 1 := by
      calc
        1 / Real.sqrt 2 * (1 / 2 * (1 / Real.sqrt 2)) * ((4 : ℤ) : ℝ)
            = (1 / Real.sqrt 2 * (1 / Real.sqrt 2)) * 2 := by push_cast; ring
        _ = 1 := by rw [hInv]; norm_num
    rw [hSc, one_smul, bispinorToDaviauMat_cast, cast_kron_mapMatrix, cast_pPlus2Z]
    change bispinorToDaviauMat (pPlus2 ⊗ₖ cast4' id4Z') = _
    rw [cast_id4Z]
  have hPL : daviauIntertwinerRᵀ * peirceLeft ⟨2, by decide⟩ * daviauIntertwinerR =
      bispinorToDaviauMat (pMinus2 ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) := by
    unfold daviauIntertwinerR
    rw [peirceLeft_eq_half_cast]
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← castZ8_transpose, ← castZ8_mul, ← castZ8_mul, intertwinerZ_peirceLeft,
      castZ8_zsmul, smul_smul]
    have hSc : 1 / Real.sqrt 2 * (1 / 2 * (1 / Real.sqrt 2)) * ((4 : ℤ) : ℝ) = 1 := by
      calc
        1 / Real.sqrt 2 * (1 / 2 * (1 / Real.sqrt 2)) * ((4 : ℤ) : ℝ)
            = (1 / Real.sqrt 2 * (1 / Real.sqrt 2)) * 2 := by push_cast; ring
        _ = 1 := by rw [hInv]; norm_num
    rw [hSc, one_smul, bispinorToDaviauMat_cast, cast_kron_mapMatrix, cast_pMinus2Z]
    change bispinorToDaviauMat (pMinus2 ⊗ₖ cast4' id4Z') = _
    rw [cast_id4Z]
  have hCut : daviauIntertwinerRᵀ * (gamma0123R * quatPR ⟨2, by decide⟩) * daviauIntertwinerR =
      bispinorToDaviauMat bispinorCut := by
    unfold daviauIntertwinerR
    dsimp [gamma0123R, quatPR]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← castZ8_transpose, ← castZ8_mul, ← castZ8_mul, ← castZ8_mul,
      show (2 : Fin 3) = ⟨2, by decide⟩ from rfl, intertwinerZ_cut,
      castZ8_zsmul, smul_smul]
    have hSc : 1 / Real.sqrt 2 * (1 / Real.sqrt 2) * ((2 : ℤ) : ℝ) = 1 := by rw [hInv]; norm_num
    rw [hSc, one_smul, bispinorToDaviauMat_cast, cast_zCut2_kron_id4]
  have hMir0 : daviauIntertwinerR * bispinorToDaviauMat bispinorMir * daviauIntertwinerRᵀ =
      gammaR 0 := by
    unfold daviauIntertwinerR
    rw [← cast_xMir2_kron_id4, ← bispinorToDaviauMat_cast]
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← castZ8_transpose, ← castZ8_mul, ← castZ8_mul, intertwinerZ_mir,
      castZ8_zsmul, smul_smul]
    have hSc : 1 / Real.sqrt 2 * (1 / Real.sqrt 2) * ((2 : ℤ) : ℝ) = 1 := by rw [hInv]; norm_num
    rw [hSc, one_smul]
    rfl
  have hMirK : daviauIntertwinerR * bispinorToDaviauMat bispinorMir * daviauIntertwinerRᵀ =
      kreinMetric8 := by
    rw [hMir0]
    dsimp [gammaR, gammaZ]
    exact castZ8_gamma0Z_eq_kreinMetric8
  have hOB := diracOmega4_mul_boosts'
  have hChi1 := chiralSpin_of_boost_eq spinJ1 boostK1 hOB.1
  have hChi2 := chiralSpin_of_boost_eq spinJ2 boostK2 hOB.2.1
  have hChi3 := chiralSpin_of_boost_eq spinJ3 boostK3 hOB.2.2
  have hY0 : daviauIntertwinerRᵀ * ((1 / 2 : ℝ) • genY ⟨2, by decide⟩ ⟨0, by decide⟩) *
      daviauIntertwinerR = bispinorToDaviauMat (chiralSpinB spinJ1 boostK1) := by
    rw [intertwiner_conj_twoGenYZ ⟨0, by decide⟩ (dGamma2Z4 * dGamma3Z4) intertwinerZ_genY0,
      cast4'_mul, cast4'_dGamma2, cast4'_dGamma3, hChi1.2]
    simp only [spinJ1, neg_smul]
  have hY1 : daviauIntertwinerRᵀ * ((1 / 2 : ℝ) • genY ⟨2, by decide⟩ ⟨1, by decide⟩) *
      daviauIntertwinerR = bispinorToDaviauMat (chiralSpinB spinJ2 boostK2) := by
    rw [intertwiner_conj_twoGenYZ ⟨1, by decide⟩ (dGamma3Z4 * dGamma1Z4) intertwinerZ_genY1,
      cast4'_mul, cast4'_dGamma3, cast4'_dGamma1, hChi2.2]
    simp only [spinJ2, neg_smul]
  have hY2 : daviauIntertwinerRᵀ * ((1 / 2 : ℝ) • genY ⟨2, by decide⟩ ⟨2, by decide⟩) *
      daviauIntertwinerR = bispinorToDaviauMat (chiralSpinB spinJ3 boostK3) := by
    rw [intertwiner_conj_twoGenYZ ⟨2, by decide⟩ (dGamma1Z4 * dGamma2Z4) intertwinerZ_genY2,
      cast4'_mul, cast4'_dGamma1, cast4'_dGamma2, hChi3.2]
    simp only [spinJ3, neg_smul]
  have hB0 : daviauIntertwinerRᵀ * ((1 / 2 : ℝ) • genB ⟨2, by decide⟩ ⟨0, by decide⟩) *
      daviauIntertwinerR = bispinorToDaviauMat (chiralSpinA spinJ1 boostK1) := by
    rw [intertwiner_conj_twoGenBZ ⟨0, by decide⟩ (dGamma2Z4 * dGamma3Z4) intertwinerZ_genB0,
      cast4'_mul, cast4'_dGamma2, cast4'_dGamma3, hChi1.1]
    simp only [spinJ1, neg_smul]
  have hB1 : daviauIntertwinerRᵀ * ((1 / 2 : ℝ) • genB ⟨2, by decide⟩ ⟨1, by decide⟩) *
      daviauIntertwinerR = bispinorToDaviauMat (chiralSpinA spinJ2 boostK2) := by
    rw [intertwiner_conj_twoGenBZ ⟨1, by decide⟩ (dGamma3Z4 * dGamma1Z4) intertwinerZ_genB1,
      cast4'_mul, cast4'_dGamma3, cast4'_dGamma1, hChi2.1]
    simp only [spinJ2, neg_smul]
  have hB2 : daviauIntertwinerRᵀ * ((1 / 2 : ℝ) • genB ⟨2, by decide⟩ ⟨2, by decide⟩) *
      daviauIntertwinerR = bispinorToDaviauMat (chiralSpinA spinJ3 boostK3) := by
    rw [intertwiner_conj_twoGenBZ ⟨2, by decide⟩ (dGamma1Z4 * dGamma2Z4) intertwinerZ_genB2,
      cast4'_mul, cast4'_dGamma1, cast4'_dGamma2, hChi3.1]
    simp only [spinJ3, neg_smul]
  exact ⟨⟨hOrthL, hOrthR⟩, hPR, hPL, hCut, ⟨hMir0, hMirK⟩, ⟨hY0, hY1, hY2⟩, ⟨hB0, hB1, hB2⟩⟩

/-! ### Part 2: Lochak Eq. (39) ↔ `GeometroMagnetoGravityCrankingDirac` Chiral Currents -/

private structure LocalSp8 where
  col : Fin 8 → Fin 8
  sgn : Fin 8 → ℤ

private def LocalSp8.toMat (A : LocalSp8) : Mat8Z :=
  Matrix.of fun i j => if j = A.col i then A.sgn i else 0

private def g1SpL : LocalSp8 := ⟨![5, 4, 7, 6, 1, 0, 3, 2], ![1, -1, -1, 1, 1, -1, -1, 1]⟩
private def g2SpL : LocalSp8 := ⟨![6, 7, 4, 5, 2, 3, 0, 1], ![1, -1, 1, -1, -1, 1, -1, 1]⟩
private def g3SpL : LocalSp8 := ⟨![7, 6, 5, 4, 3, 2, 1, 0], ![1, 1, 1, 1, -1, -1, -1, -1]⟩

private def s1SpL : LocalSp8 := ⟨![2, 3, 0, 1, 6, 7, 4, 5], ![-1, -1, -1, -1, -1, -1, -1, -1]⟩
private def s2SpL : LocalSp8 := ⟨![1, 0, 3, 2, 5, 4, 7, 6], ![-1, -1, 1, 1, 1, 1, -1, -1]⟩
private def s3SpL : LocalSp8 := ⟨![0, 1, 2, 3, 4, 5, 6, 7], ![1, -1, -1, 1, -1, 1, 1, -1]⟩

private lemma g1SpL_toMat : g1SpL.toMat = gamma1Z := by decide
private lemma g2SpL_toMat : g2SpL.toMat = gamma2Z := by decide
private lemma g3SpL_toMat : g3SpL.toMat = gamma3Z := by decide

private lemma s1SpL_toMat : s1SpL.toMat = gamma1Z * (gamma0123Z * quatPZ ⟨2, by decide⟩) := by decide
private lemma s2SpL_toMat : s2SpL.toMat = gamma2Z * (gamma0123Z * quatPZ ⟨2, by decide⟩) := by decide
private lemma s3SpL_toMat : s3SpL.toMat = gamma3Z * (gamma0123Z * quatPZ ⟨2, by decide⟩) := by decide

private lemma kreinInnerProduct_eq' (u v : Vec8R) :
    kreinInnerProduct u v =
      u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 -
        u 4 * v 4 - u 5 * v 5 - u 6 * v 6 - u 7 * v 7 := by
  dsimp [kreinInnerProduct, kreinMetric8]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  ring

private lemma kreinInner_localSp (A : LocalSp8) (Φ : Vec8R) :
    kreinInnerProduct Φ ((castZ8 A.toMat).mulVec Φ) =
      Φ 0 * ((A.sgn 0 : ℝ) * Φ (A.col 0)) +
      Φ 1 * ((A.sgn 1 : ℝ) * Φ (A.col 1)) +
      Φ 2 * ((A.sgn 2 : ℝ) * Φ (A.col 2)) +
      Φ 3 * ((A.sgn 3 : ℝ) * Φ (A.col 3)) -
      Φ 4 * ((A.sgn 4 : ℝ) * Φ (A.col 4)) -
      Φ 5 * ((A.sgn 5 : ℝ) * Φ (A.col 5)) -
      Φ 6 * ((A.sgn 6 : ℝ) * Φ (A.col 6)) -
      Φ 7 * ((A.sgn 7 : ℝ) * Φ (A.col 7)) := by
  have hRow : ∀ i : Fin 8, (castZ8 A.toMat).mulVec Φ i = (A.sgn i : ℝ) * Φ (A.col i) := by
    intro i
    dsimp [Matrix.mulVec, dotProduct, castZ8]
    rw [Finset.sum_eq_single (A.col i)]
    · simp [LocalSp8.toMat]
    · intro b _ hb; simp [LocalSp8.toMat, hb]
    · intro hm; exact False.elim (hm (Finset.mem_univ _))
  rw [kreinInnerProduct_eq']
  simp only [hRow]

private lemma electricCurrentJ_expand_all (Φ : Vec8R) :
    electricCurrentJ Φ 0 =
      Φ 0 ^ 2 + Φ 1 ^ 2 + Φ 2 ^ 2 + Φ 3 ^ 2 + Φ 4 ^ 2 + Φ 5 ^ 2 + Φ 6 ^ 2 + Φ 7 ^ 2 ∧
    electricCurrentJ Φ 1 = 2 * (Φ 0 * Φ 5 - Φ 1 * Φ 4 - Φ 2 * Φ 7 + Φ 3 * Φ 6) ∧
    electricCurrentJ Φ 2 = 2 * (Φ 0 * Φ 6 - Φ 1 * Φ 7 + Φ 2 * Φ 4 - Φ 3 * Φ 5) ∧
    electricCurrentJ Φ 3 = 2 * (Φ 0 * Φ 7 + Φ 1 * Φ 6 + Φ 2 * Φ 5 + Φ 3 * Φ 4) := by
  refine ⟨electricCurrentJ0_expand Φ, ?_, ?_, ?_⟩
  · change kreinInnerProduct Φ ((castZ8 (gammaZ 1)).mulVec Φ) = _
    rw [gammaZ.eq_def, ← g1SpL_toMat, kreinInner_localSp]
    simp [g1SpL]; ring
  · change kreinInnerProduct Φ ((castZ8 (gammaZ 2)).mulVec Φ) = _
    rw [gammaZ.eq_def, ← g2SpL_toMat, kreinInner_localSp]
    simp [g2SpL]; ring
  · change kreinInnerProduct Φ ((castZ8 (gammaZ 3)).mulVec Φ) = _
    rw [gammaZ.eq_def, ← g3SpL_toMat, kreinInner_localSp]
    simp [g3SpL]; ring

private lemma axialCurrentSigma_expand_all (Φ : Vec8R) :
    axialCurrentSigma Φ 0 = 2 * (Φ 0 * Φ 7 - Φ 1 * Φ 6 - Φ 2 * Φ 5 + Φ 3 * Φ 4) ∧
    axialCurrentSigma Φ 1 = 2 * (-Φ 0 * Φ 2 - Φ 1 * Φ 3 + Φ 4 * Φ 6 + Φ 5 * Φ 7) ∧
    axialCurrentSigma Φ 2 = 2 * (-Φ 0 * Φ 1 + Φ 2 * Φ 3 - Φ 4 * Φ 5 + Φ 6 * Φ 7) ∧
    axialCurrentSigma Φ 3 =
      Φ 0 ^ 2 - Φ 1 ^ 2 - Φ 2 ^ 2 + Φ 3 ^ 2 + Φ 4 ^ 2 - Φ 5 ^ 2 - Φ 6 ^ 2 + Φ 7 ^ 2 := by
  refine ⟨axialCurrentSigma0_expand Φ, ?_, ?_, ?_⟩
  · change kreinInnerProduct Φ
        ((castZ8 (gammaZ 1) * (castZ8 gamma0123Z * castZ8 (quatPZ ⟨2, by decide⟩))).mulVec Φ) = _
    rw [gammaZ.eq_def, ← castZ8_mul, ← castZ8_mul, ← s1SpL_toMat, kreinInner_localSp]
    simp [s1SpL]; ring
  · change kreinInnerProduct Φ
        ((castZ8 (gammaZ 2) * (castZ8 gamma0123Z * castZ8 (quatPZ ⟨2, by decide⟩))).mulVec Φ) = _
    rw [gammaZ.eq_def, ← castZ8_mul, ← castZ8_mul, ← s2SpL_toMat, kreinInner_localSp]
    simp [s2SpL]; ring
  · change kreinInnerProduct Φ
        ((castZ8 (gammaZ 3) * (castZ8 gamma0123Z * castZ8 (quatPZ ⟨2, by decide⟩))).mulVec Φ) = _
    rw [gammaZ.eq_def, ← castZ8_mul, ← castZ8_mul, ← s3SpL_toMat, kreinInner_localSp]
    simp [s3SpL]; ring

/-- Explicit chiral spinor coordinates `(a₁, b₁, a₂, b₂, c₁, d₁, c₂, d₂)` extracted from `Φ : Vec8R`. -/
def lochakA1 (Φ : Vec8R) : ℝ := Φ 0 + Φ 7
def lochakB1 (Φ : Vec8R) : ℝ := -(Φ 3 + Φ 4)
def lochakA2 (Φ : Vec8R) : ℝ := -(Φ 2 - Φ 5)
def lochakB2 (Φ : Vec8R) : ℝ := Φ 1 - Φ 6
def lochakC1 (Φ : Vec8R) : ℝ := Φ 2 + Φ 5
def lochakD1 (Φ : Vec8R) : ℝ := Φ 1 + Φ 6
def lochakC2 (Φ : Vec8R) : ℝ := Φ 0 - Φ 7
def lochakD2 (Φ : Vec8R) : ℝ := Φ 3 - Φ 4

private lemma lochak_poly_identities (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : ℝ) :
    let a₁ := x₀ + x₇
    let b₁ := -(x₃ + x₄)
    let a₂ := -(x₂ - x₅)
    let b₂ := x₁ - x₆
    let c₁ := x₂ + x₅
    let d₁ := x₁ + x₆
    let c₂ := x₀ - x₇
    let d₂ := x₃ - x₄
    (((a₁ ^ 2 + b₁ ^ 2 + a₂ ^ 2 + b₂ ^ 2) / 2 + (c₁ ^ 2 + d₁ ^ 2 + c₂ ^ 2 + d₂ ^ 2) / 2 =
        x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 + x₅ ^ 2 + x₆ ^ 2 + x₇ ^ 2) ∧
      ((a₁ * a₂ + b₁ * b₂) + (c₁ * c₂ + d₁ * d₂) =
        2 * (x₀ * x₅ - x₁ * x₄ - x₂ * x₇ + x₃ * x₆)) ∧
      ((b₁ * a₂ - a₁ * b₂) + (d₁ * c₂ - c₁ * d₂) =
        2 * (x₀ * x₆ - x₁ * x₇ + x₂ * x₄ - x₃ * x₅)) ∧
      ((a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2) / 2 + (c₁ ^ 2 + d₁ ^ 2 - c₂ ^ 2 - d₂ ^ 2) / 2 =
        2 * (x₀ * x₇ + x₁ * x₆ + x₂ * x₅ + x₃ * x₄))) ∧
    (((a₁ ^ 2 + b₁ ^ 2 + a₂ ^ 2 + b₂ ^ 2) / 2 - (c₁ ^ 2 + d₁ ^ 2 + c₂ ^ 2 + d₂ ^ 2) / 2 =
        2 * (x₀ * x₇ - x₁ * x₆ - x₂ * x₅ + x₃ * x₄)) ∧
      ((a₁ * a₂ + b₁ * b₂) - (c₁ * c₂ + d₁ * d₂) =
        2 * (-x₀ * x₂ - x₁ * x₃ + x₄ * x₆ + x₅ * x₇)) ∧
      ((b₁ * a₂ - a₁ * b₂) - (d₁ * c₂ - c₁ * d₂) =
        2 * (-x₀ * x₁ + x₂ * x₃ - x₄ * x₅ + x₆ * x₇)) ∧
      ((a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2) / 2 - (c₁ ^ 2 + d₁ ^ 2 - c₂ ^ 2 - d₂ ^ 2) / 2 =
        x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 - x₅ ^ 2 - x₆ ^ 2 + x₇ ^ 2)) ∧
    (a₁ * c₂ - b₁ * d₂ - a₂ * c₁ + b₂ * d₁ =
      x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 - x₄ ^ 2 - x₅ ^ 2 - x₆ ^ 2 - x₇ ^ 2) ∧
    (a₁ * d₂ + b₁ * c₂ - a₂ * d₁ - b₂ * c₁ =
      -(2 * (x₀ * x₄ + x₁ * x₅ - x₂ * x₆ - x₃ * x₇))) := by
  refine ⟨⟨by ring, by ring, by ring, by ring⟩, ⟨by ring, by ring, by ring, by ring⟩,
    by ring, by ring⟩

private lemma neg_sq_add_sq_scalar (o₁ o₂ κ : ℝ) :
    o₁ ^ 2 + (-o₂) ^ 2 = o₁ ^ 2 + o₂ ^ 2 ∧
    -(o₁ ^ 2 + (-o₂) ^ 2) = -(o₁ ^ 2 + o₂ ^ 2) ∧
    κ * (o₁ ^ 2 + (-o₂) ^ 2) = κ * (o₁ ^ 2 + o₂ ^ 2) := by
  refine ⟨by ring, by ring, by ring⟩

/-- **Theorem 2 (Lochak Eq. 39 ↔ `GeometroMagnetoGravityCrankingDirac` Bridge)**:
Under the exact linear coordinate map `Φ ↦ (lochakA1 Φ, ..., lochakD2 Φ)`:
1. `diracVectorCurrent = electricCurrentJ` and `diracAxialCurrent = axialCurrentSigma`.
2. `diracScalarOmega1 = omega1 Φ` and `diracPseudoscalarOmega2 = -omega2 Φ`.
3. `minkPair J J = Ω₁² + Ω₂²`, `minkPair Σ Σ = -(Ω₁² + Ω₂²)`, `minkPair J Σ = 0`, matching
   `LochakRodichevFierzKrein.lochak_eq39_fierz_takabayasi Φ`.
4. Einstein–Cartan axial torsion self-interaction satisfies `-minkPair (κ_EC Σ) Σ = κ_EC (Ω₁² + Ω₂²)`. -/
theorem lochak_eq39_matches_geometromagnetogravity_chiral_currents (Φ : Vec8R) (κ_EC : ℝ) :
    let a₁ := lochakA1 Φ
    let b₁ := lochakB1 Φ
    let a₂ := lochakA2 Φ
    let b₂ := lochakB2 Φ
    let c₁ := lochakC1 Φ
    let d₁ := lochakD1 Φ
    let c₂ := lochakC2 Φ
    let d₂ := lochakD2 Φ
    (diracVectorCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ = electricCurrentJ Φ) ∧
    (diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ = axialCurrentSigma Φ) ∧
    (diracScalarOmega1 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ = omega1 Φ) ∧
    (diracPseudoscalarOmega2 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ = -omega2 Φ) ∧
    (minkPair (electricCurrentJ Φ) (electricCurrentJ Φ) = omega1 Φ ^ 2 + omega2 Φ ^ 2) ∧
    (minkPair (axialCurrentSigma Φ) (axialCurrentSigma Φ) = -(omega1 Φ ^ 2 + omega2 Φ ^ 2)) ∧
    (minkPair (electricCurrentJ Φ) (axialCurrentSigma Φ) = 0) ∧
    (-lochakDot (electricCurrentJ Φ) (electricCurrentJ Φ) =
        lochakDot (axialCurrentSigma Φ) (axialCurrentSigma Φ) ∧
      lochakDot (axialCurrentSigma Φ) (axialCurrentSigma Φ) = omega1 Φ ^ 2 + omega2 Φ ^ 2) ∧
    (-minkPair (fun μ => κ_EC * axialCurrentSigma Φ μ) (axialCurrentSigma Φ) =
      κ_EC * (omega1 Φ ^ 2 + omega2 Φ ^ 2)) := by
  dsimp only
  have hP := lochak_poly_identities (Φ 0) (Φ 1) (Φ 2) (Φ 3) (Φ 4) (Φ 5) (Φ 6) (Φ 7)
  have hJ := electricCurrentJ_expand_all Φ
  have hS := axialCurrentSigma_expand_all Φ
  have hJeq : diracVectorCurrent (lochakA1 Φ) (lochakB1 Φ) (lochakA2 Φ) (lochakB2 Φ)
      (lochakC1 Φ) (lochakD1 Φ) (lochakC2 Φ) (lochakD2 Φ) = electricCurrentJ Φ := by
    ext μ
    fin_cases μ
    · dsimp [diracVectorCurrent, chiralNullCurrent, lochakA1, lochakB1, lochakA2, lochakB2,
        lochakC1, lochakD1, lochakC2, lochakD2]
      rw [hJ.1]; exact hP.1.1
    · dsimp [diracVectorCurrent, chiralNullCurrent, lochakA1, lochakB1, lochakA2, lochakB2,
        lochakC1, lochakD1, lochakC2, lochakD2]
      rw [hJ.2.1]; exact hP.1.2.1
    · dsimp [diracVectorCurrent, chiralNullCurrent, lochakA1, lochakB1, lochakA2, lochakB2,
        lochakC1, lochakD1, lochakC2, lochakD2]
      rw [hJ.2.2.1]; exact hP.1.2.2.1
    · dsimp [diracVectorCurrent, chiralNullCurrent, lochakA1, lochakB1, lochakA2, lochakB2,
        lochakC1, lochakD1, lochakC2, lochakD2]
      rw [hJ.2.2.2]; exact hP.1.2.2.2
  have hSeq : diracAxialCurrent (lochakA1 Φ) (lochakB1 Φ) (lochakA2 Φ) (lochakB2 Φ)
      (lochakC1 Φ) (lochakD1 Φ) (lochakC2 Φ) (lochakD2 Φ) = axialCurrentSigma Φ := by
    ext μ
    fin_cases μ
    · dsimp [diracAxialCurrent, chiralNullCurrent, lochakA1, lochakB1, lochakA2, lochakB2,
        lochakC1, lochakD1, lochakC2, lochakD2]
      rw [hS.1]; exact hP.2.1.1
    · dsimp [diracAxialCurrent, chiralNullCurrent, lochakA1, lochakB1, lochakA2, lochakB2,
        lochakC1, lochakD1, lochakC2, lochakD2]
      rw [hS.2.1]; exact hP.2.1.2.1
    · dsimp [diracAxialCurrent, chiralNullCurrent, lochakA1, lochakB1, lochakA2, lochakB2,
        lochakC1, lochakD1, lochakC2, lochakD2]
      rw [hS.2.2.1]; exact hP.2.1.2.2.1
    · dsimp [diracAxialCurrent, chiralNullCurrent, lochakA1, lochakB1, lochakA2, lochakB2,
        lochakC1, lochakD1, lochakC2, lochakD2]
      rw [hS.2.2.2]; exact hP.2.1.2.2.2
  have hOm1eq : diracScalarOmega1 (lochakA1 Φ) (lochakB1 Φ) (lochakA2 Φ) (lochakB2 Φ)
      (lochakC1 Φ) (lochakD1 Φ) (lochakC2 Φ) (lochakD2 Φ) = omega1 Φ := by
    dsimp [diracScalarOmega1, lochakA1, lochakB1, lochakA2, lochakB2,
      lochakC1, lochakD1, lochakC2, lochakD2]
    rw [omega1_expand]; exact hP.2.2.1
  have hOm2eq : diracPseudoscalarOmega2 (lochakA1 Φ) (lochakB1 Φ) (lochakA2 Φ) (lochakB2 Φ)
      (lochakC1 Φ) (lochakD1 Φ) (lochakC2 Φ) (lochakD2 Φ) = -omega2 Φ := by
    dsimp [diracPseudoscalarOmega2, lochakA1, lochakB1, lochakA2, lochakB2,
      lochakC1, lochakD1, lochakC2, lochakD2]
    rw [omega2_expand]; exact hP.2.2.2
  have hFKR := fierz_kofink_rodichev_chiral_null_current_identities
    (lochakA1 Φ) (lochakB1 Φ) (lochakA2 Φ) (lochakB2 Φ)
    (lochakC1 Φ) (lochakD1 Φ) (lochakC2 Φ) (lochakD2 Φ) κ_EC
  have hNorms := neg_sq_add_sq_scalar (omega1 Φ) (omega2 Φ) κ_EC
  refine ⟨hJeq, hSeq, hOm1eq, hOm2eq, ?_, ?_, ?_, lochak_eq39_fierz_takabayasi Φ, ?_⟩
  · simpa [hJeq, hOm1eq, hOm2eq, hNorms.1] using hFKR.2.1
  · simpa [hSeq, hOm1eq, hOm2eq, hNorms.2.1] using hFKR.2.2.1
  · simpa [hJeq, hSeq] using hFKR.2.2.2.1
  · simpa [hSeq, hOm1eq, hOm2eq, hNorms.2.2] using hFKR.2.2.2.2

end InfoGeometry.Canonical.DaviauLochakChiralDiracBridge
