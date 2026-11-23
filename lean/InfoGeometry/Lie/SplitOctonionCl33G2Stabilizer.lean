/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Determinant
import InfoGeometry.Canonical.SplitOctonionCayleyDickson
import InfoGeometry.Canonical.SplitOctonionChiralNullDecomposition
import InfoGeometry.Canonical.MajoranaEightByEightJW
import InfoGeometry.Canonical.SplitOctonionJordanWignerIntertwiner
import InfoGeometry.Canonical.SplitOctonionAutomorphismCore
import InfoGeometry.Canonical.SplitOctonionAutomorphism
import InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge
import InfoGeometry.Lie.CanonicalZornPeirceUnitaryPhase
import InfoGeometry.Physics.ThreeColorSL3ZornAction
import InfoGeometry.Lie.SplitG2RealFormCapstone

/-!
# Polarized $\mathrm{Cl}(3,3) \simeq M_8(\mathbb{R})$ and $G_{2(2)}$ Stabilizer on `SplitOctCD`

This module formalizes Milestone M3 (Features F9–F12) on the canonical Cayley–Dickson
split-octonion carrier `SplitOctCD`:

1. **Symmetric fermionic CAR relations (F9)** on `{ePlusCD j, eMinusCD k}`:
   `(e_j^\pm)^2 = 0`, `e_j^+ e_k^- = -\delta_{jk} u_+`, `e_k^- e_j^+ = -\delta_{jk} u_-`,
   `\{e_j^\pm, e_k^\pm\} = 0`, and `\{e_j^+, e_k^-\} = -\delta_{jk} \cdot 1`.
2. **Chirality-flipping cross products and singlet triple products (F11)**:
   `e_j^+ e_k^+ = \sum_m \varepsilon_{jkm} e_m^-`,
   `e_j^- e_k^- = \sum_m \varepsilon_{jkm} e_m^+`, `(e_0^+ e_1^+) e_2^+ = -u_-`, and
   `(e_0^- e_1^-) e_2^- = -u_+`.
3. **Operator CAR and genuine `Cl(3,3) ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ` (F10)**:
   using `carAnnihilateMat j := leftMulMat (ePlusCD j)` and
   `carCreateMat k := -leftMulMat (eMinusCD k)`, together with Majorana generators
   `majoranaPlusMat j = leftMulMat (sCD j)` and `majoranaMinusMat j = leftMulMat (iCD j)`,
   isometric quadratic-form bridges (`Q33`, alternating Majorana form, `(Fin 3 ⊕ Fin 3)` form),
   and `cliffordQ33ToMat8 : CliffordAlgebra Q33 ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ`.
4. **$G_{2(2)} = \mathrm{Aut}(\widetilde{\mathbb{O}}) \subset \mathrm{SO}(4,4)$ and
   $\mathrm{SL}_3(\mathbb{R}) / \mathrm{SU}(3)$ stabilizer `1 ⊕ 1 ⊕ 3 ⊕ 3̄` (F12)**:
   including algebraic `det = +1` via `oct7Form`, converse `ellStabilizer ≃* SL(3, ℝ)`,
   Lie-algebra equivalence to `CanonicalZornPeirceStabilizer.peirceStabilizer` and `SL3`, and
   complexified `ℂ ⊗[ℝ] SplitOctCD` / `SU(3) ≤ SL(3, ℂ)` action via
   `ThreeColorSL3ZornAction.zornSL3Action`.
   Note (`[bucket_3_open_debt]`): global 14D `Aut(𝕆̃) ≃* G_{2(2)}` classification remains
   open debt outside this stabilizer module.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCl33G2Stabilizer

open InfoGeometry.Canonical
open InfoGeometry.Canonical.SplitOctonionCayleyDickson
open InfoGeometry.Canonical.SplitOctonionChiralNullDecomposition
open InfoGeometry.Canonical.MajoranaEightByEightJW
open InfoGeometry.Canonical.SplitOctonionJordanWignerIntertwiner
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open scoped TensorProduct Matrix

/-! ## Section 1: Symmetric Fermionic CAR Relations on `SplitOctCD` (Feature F9) -/

theorem ePlusCD_sq (j : Fin 3) : ePlusCD j * ePlusCD j = 0 := by
  fin_cases j <;> ext <;> simp [ePlusCD_components, qBasis]

theorem eMinusCD_sq (j : Fin 3) : eMinusCD j * eMinusCD j = 0 := by
  fin_cases j <;> ext <;> simp [eMinusCD_components, qBasis]

theorem ePlusCD_mul_eMinusCD (j k : Fin 3) :
    ePlusCD j * eMinusCD k = -(if j = k then (1 : ℝ) else 0) • uPlusCD := by
  fin_cases j <;> fin_cases k <;>
    ext <;> simp [ePlusCD_components, eMinusCD_components, uPlusCD_components, qBasis] <;>
    norm_num

theorem eMinusCD_mul_ePlusCD (j k : Fin 3) :
    eMinusCD j * ePlusCD k = -(if j = k then (1 : ℝ) else 0) • uMinusCD := by
  fin_cases j <;> fin_cases k <;>
    ext <;> simp [ePlusCD_components, eMinusCD_components, uMinusCD_components, qBasis] <;>
    norm_num

theorem ePlusCD_anticomm (j k : Fin 3) :
    ePlusCD j * ePlusCD k + ePlusCD k * ePlusCD j = 0 := by
  fin_cases j <;> fin_cases k <;>
    ext <;> simp [ePlusCD_components, qBasis]

theorem eMinusCD_anticomm (j k : Fin 3) :
    eMinusCD j * eMinusCD k + eMinusCD k * eMinusCD j = 0 := by
  fin_cases j <;> fin_cases k <;>
    ext <;> simp [eMinusCD_components, qBasis]

theorem ePlusCD_eMinusCD_anticomm (j k : Fin 3) :
    ePlusCD j * eMinusCD k + eMinusCD k * ePlusCD j =
      -(if j = k then (1 : ℝ) else 0) • oneCD := by
  rw [ePlusCD_mul_eMinusCD j k, eMinusCD_mul_ePlusCD k j]
  by_cases hjk : j = k
  · subst hjk
    (ext <;> simp [uPlusCD_components, uMinusCD_components, oneCD]); norm_num
  · simp [hjk, Ne.symm hjk]

/-! ## Section 2: Chirality-Flipping Cross Products and Singlet Triple Product (Feature F11) -/

/-- Totally antisymmetric 3D Levi-Civita symbol `ε_{jkm}` on `Fin 3`. -/
def leviCivita3 (j k m : Fin 3) : ℝ :=
  if (j = 0 ∧ k = 1 ∧ m = 2) ∨ (j = 1 ∧ k = 2 ∧ m = 0) ∨ (j = 2 ∧ k = 0 ∧ m = 1) then 1
  else if (j = 1 ∧ k = 0 ∧ m = 2) ∨ (j = 2 ∧ k = 1 ∧ m = 0) ∨ (j = 0 ∧ k = 2 ∧ m = 1) then -1
  else 0

theorem ePlusCD_cross (j k : Fin 3) :
    ePlusCD j * ePlusCD k = ∑ m : Fin 3, leviCivita3 j k m • eMinusCD m := by
  rw [Fin.sum_univ_three]
  fin_cases j <;> fin_cases k <;>
    ext <;> simp [leviCivita3, ePlusCD_components, eMinusCD_components, qBasis] <;> norm_num

theorem eMinusCD_cross (j k : Fin 3) :
    eMinusCD j * eMinusCD k = ∑ m : Fin 3, leviCivita3 j k m • ePlusCD m := by
  rw [Fin.sum_univ_three]
  fin_cases j <;> fin_cases k <;>
    ext <;> simp [leviCivita3, ePlusCD_components, eMinusCD_components, qBasis] <;> norm_num

theorem ePlusCD_triple_singlet :
    (ePlusCD 0 * ePlusCD 1) * ePlusCD 2 = -uMinusCD := by
  have h01 : ePlusCD 0 * ePlusCD 1 = eMinusCD 2 := by
    rw [ePlusCD_cross 0 1, Fin.sum_univ_three]
    simp [leviCivita3]
  rw [h01, eMinusCD_mul_ePlusCD 2 2]
  simp

theorem eMinusCD_triple_singlet :
    (eMinusCD 0 * eMinusCD 1) * eMinusCD 2 = -uPlusCD := by
  have h01 : eMinusCD 0 * eMinusCD 1 = ePlusCD 2 := by
    rw [eMinusCD_cross 0 1, Fin.sum_univ_three]
    simp [leviCivita3]
  rw [h01, ePlusCD_mul_eMinusCD 2 2]
  simp

/-! ## Section 3: Operator CAR and `Cl(3,3) ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ` (Feature F10) -/

/-- Fermionic annihilation matrix `a_j = L_{e_j^+}` on `SplitOctCD`. -/
def carAnnihilateMat (j : Fin 3) : Matrix (Fin 8) (Fin 8) ℝ :=
  leftMulMat (ePlusCD j)

/-- Fermionic creation matrix `a_k^\dagger = -L_{e_k^-}` on `SplitOctCD`. -/
def carCreateMat (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℝ :=
  -leftMulMat (eMinusCD k)

theorem carAnnihilateMat_sq (j : Fin 3) :
    carAnnihilateMat j * carAnnihilateMat j = 0 := by
  unfold carAnnihilateMat
  rw [leftMulMat_sq, ePlusCD_sq, leftMulMat_zero]

theorem carCreateMat_sq (k : Fin 3) :
    carCreateMat k * carCreateMat k = 0 := by
  unfold carCreateMat
  rw [neg_mul_neg, leftMulMat_sq, eMinusCD_sq, leftMulMat_zero]

theorem carAnnihilateMat_anticomm (j k : Fin 3) :
    carAnnihilateMat j * carAnnihilateMat k + carAnnihilateMat k * carAnnihilateMat j = 0 := by
  unfold carAnnihilateMat
  rw [leftMulMat_anticommutator, ePlusCD_anticomm, leftMulMat_zero]

theorem carCreateMat_anticomm (j k : Fin 3) :
    carCreateMat j * carCreateMat k + carCreateMat k * carCreateMat j = 0 := by
  unfold carCreateMat
  rw [neg_mul_neg, neg_mul_neg, leftMulMat_anticommutator, eMinusCD_anticomm, leftMulMat_zero]

theorem carAnnihilateMat_carCreateMat_anticomm (j k : Fin 3) :
    carAnnihilateMat j * carCreateMat k + carCreateMat k * carAnnihilateMat j =
      (if j = k then (1 : ℝ) else 0) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  unfold carAnnihilateMat carCreateMat
  have hlin :
      leftMulMat (ePlusCD j) * (-leftMulMat (eMinusCD k)) +
        (-leftMulMat (eMinusCD k)) * leftMulMat (ePlusCD j) =
      -(leftMulMat (ePlusCD j) * leftMulMat (eMinusCD k) +
        leftMulMat (eMinusCD k) * leftMulMat (ePlusCD j)) := by
    simp [mul_neg, neg_mul, neg_add_rev, add_comm]
  rw [hlin, leftMulMat_anticommutator, ePlusCD_eMinusCD_anticomm, leftMulMat_smul,
    show oneCD = (1 : SplitOctCD) from oneCD_def.symm, leftMulMat_one]
  by_cases hjk : j = k <;> simp [hjk]

/-- Combined 3-mode CAR statement on `{L_{e_j^+}, -L_{e_k^-}}`. -/
theorem leftMulMat_chiral_car (j k : Fin 3) :
    (carAnnihilateMat j * carAnnihilateMat k + carAnnihilateMat k * carAnnihilateMat j = 0) ∧
    (carCreateMat j * carCreateMat k + carCreateMat k * carCreateMat j = 0) ∧
    (carAnnihilateMat j * carCreateMat k + carCreateMat k * carAnnihilateMat j =
      (if j = k then (1 : ℝ) else 0) • (1 : Matrix (Fin 8) (Fin 8) ℝ)) :=
  ⟨carAnnihilateMat_anticomm j k, carCreateMat_anticomm j k,
    carAnnihilateMat_carCreateMat_anticomm j k⟩

/-- Positive-square Majorana generator `M_j^+ = a_j + a_j^\dagger = L_{s_j}`. -/
def majoranaPlusMat (j : Fin 3) : Matrix (Fin 8) (Fin 8) ℝ :=
  carAnnihilateMat j + carCreateMat j

/-- Negative-square Majorana generator `M_j^- = a_j - a_j^\dagger = L_{i_j}`. -/
def majoranaMinusMat (j : Fin 3) : Matrix (Fin 8) (Fin 8) ℝ :=
  carAnnihilateMat j - carCreateMat j

theorem majoranaPlusMat_eq_leftMulMat_sCD (j : Fin 3) :
    majoranaPlusMat j = leftMulMat (sCD j) := by
  unfold majoranaPlusMat carAnnihilateMat carCreateMat
  rw [← leftMulMat_neg, ← leftMulMat_add]
  congr 1
  rw [ePlusCD_eq_half_add, eMinusCD_eq_half_sub]
  ext <;> simp [sCD_formula, iCD, qBasis] <;> ring

theorem majoranaMinusMat_eq_leftMulMat_iCD (j : Fin 3) :
    majoranaMinusMat j = leftMulMat (iCD j) := by
  unfold majoranaMinusMat carAnnihilateMat carCreateMat
  rw [sub_neg_eq_add, ← leftMulMat_add]
  congr 1
  rw [ePlusCD_eq_half_add, eMinusCD_eq_half_sub]
  ext <;> simp [sCD_formula, iCD, qBasis] <;> ring

/-- Split `(3,3)` signature weights `(+1, +1, +1, -1, -1, -1)` on `Fin 6`. -/
def q33Sig : Fin 6 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => -1
  | 4 => -1
  | 5 => -1

/-- Standard split `(3,3)` quadratic form on `Fin 6 → ℝ`:
`Q33 x = x₀² + x₁² + x₂² - x₃² - x₄² - x₅²`. -/
def Q33 : QuadraticForm ℝ (Fin 6 → ℝ) :=
  ∑ a : Fin 6, q33Sig a • QuadraticMap.linMulLin (LinearMap.proj a) (LinearMap.proj a)

@[simp] theorem Q33_apply (x : Fin 6 → ℝ) :
    Q33 x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - x 3 ^ 2 - x 4 ^ 2 - x 5 ^ 2 := by
  simp [Q33, QuadraticMap.linMulLin, Fin.sum_univ_six, q33Sig, pow_two]
  ring

/-- Alternating-signature quadratic form matching `MathlibCliffordUniversalLiftSynthesis`. -/
def cl33AlternatingQuadratic : QuadraticForm ℝ (Fin 6 → ℝ) :=
  ∑ a : Fin 6, majoranaSignatureR a •
    QuadraticMap.linMulLin (LinearMap.proj a) (LinearMap.proj a)

@[simp] theorem cl33AlternatingQuadratic_apply (x : Fin 6 → ℝ) :
    cl33AlternatingQuadratic x = ∑ a : Fin 6, majoranaSignatureR a * (x a) ^ 2 := by
  simp [cl33AlternatingQuadratic, QuadraticMap.linMulLin, pow_two]

/-- Split `(Fin 3 ⊕ Fin 3) → ℝ` quadratic form matching `Cl11GradedProjectorDefects.Q33`. -/
def cl33SplitPairWeight : (Fin 3 ⊕ Fin 3) → ℝ
  | .inl _ => 1
  | .inr _ => -1

def cl33SplitPairQuadratic : QuadraticForm ℝ ((Fin 3 ⊕ Fin 3) → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ cl33SplitPairWeight

/-- Split phase-space quadratic form matching `cl33PhaseQuadratic` (`q(u, v) = u · v`). -/
def cl33PhaseQuadratic : QuadraticForm ℝ ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
  ∑ k : Fin 3, QuadraticMap.linMulLin
    (LinearMap.proj k ∘ₗ LinearMap.fst ℝ (Fin 3 → ℝ) (Fin 3 → ℝ))
    (LinearMap.proj k ∘ₗ LinearMap.snd ℝ (Fin 3 → ℝ) (Fin 3 → ℝ))

@[simp] theorem cl33PhaseQuadratic_apply (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    cl33PhaseQuadratic z = ∑ k : Fin 3, z.1 k * z.2 k := by
  simp [cl33PhaseQuadratic, QuadraticMap.linMulLin]

private def q33AltPerm : Equiv.Perm (Fin 6) where
  toFun
    | 0 => 0
    | 1 => 2
    | 2 => 4
    | 3 => 1
    | 4 => 3
    | 5 => 5
  invFun
    | 0 => 0
    | 1 => 3
    | 2 => 1
    | 3 => 4
    | 4 => 2
    | 5 => 5
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Explicit isometry `Q33 ≃ᵢ cl33AlternatingQuadratic`. -/
def q33AlternatingIsometry : Q33.IsometryEquiv cl33AlternatingQuadratic where
  toFun x i := x (q33AltPerm.symm i)
  invFun y j := y (q33AltPerm j)
  left_inv x := by funext j; simp
  right_inv y := by funext i; simp
  map_add' x y := by funext i; rfl
  map_smul' r x := by funext i; rfl
  map_app' x := by
    rw [cl33AlternatingQuadratic_apply, Q33_apply, Fin.sum_univ_six]
    simp [q33AltPerm, majoranaSignatureR, majoranaSignatureZ]
    ring

/-- Explicit Clifford algebra isomorphism to the alternating `Cl(3,3)` form. -/
def cliffordQ33EquivAlternating :
    CliffordAlgebra Q33 ≃ₐ[ℝ] CliffordAlgebra cl33AlternatingQuadratic :=
  CliffordAlgebra.equivOfIsometry q33AlternatingIsometry

private def fin6ToSumEquiv : Fin 6 ≃ (Fin 3 ⊕ Fin 3) where
  toFun
    | 0 => .inl 0
    | 1 => .inl 1
    | 2 => .inl 2
    | 3 => .inr 0
    | 4 => .inr 1
    | 5 => .inr 2
  invFun
    | .inl 0 => 0
    | .inl 1 => 1
    | .inl 2 => 2
    | .inr 0 => 3
    | .inr 1 => 4
    | .inr 2 => 5
  left_inv i := by fin_cases i <;> rfl
  right_inv s := by rcases s with i | i <;> fin_cases i <;> rfl

/-- Explicit isometry `Q33 ≃ᵢ cl33SplitPairQuadratic`. -/
def q33SplitPairIsometry : Q33.IsometryEquiv cl33SplitPairQuadratic where
  toFun x s := x (fin6ToSumEquiv.symm s)
  invFun y i := y (fin6ToSumEquiv i)
  left_inv x := by funext i; simp
  right_inv y := by funext s; simp
  map_add' x y := by funext s; rfl
  map_smul' r x := by funext s; rfl
  map_app' x := by
    unfold cl33SplitPairQuadratic
    rw [QuadraticMap.weightedSumSquares_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, Fin.sum_univ_three, Q33_apply]
    simp [cl33SplitPairWeight, fin6ToSumEquiv, sq]
    ring

/-- Explicit Clifford algebra isomorphism to the `(Fin 3 ⊕ Fin 3)` split `Cl(3,3)` form. -/
def cliffordQ33EquivSplitPair :
    CliffordAlgebra Q33 ≃ₐ[ℝ] CliffordAlgebra cl33SplitPairQuadratic :=
  CliffordAlgebra.equivOfIsometry q33SplitPairIsometry

private def phaseIdxPlus (k : Fin 3) : Fin 6 := ⟨k.val, by omega⟩
private def phaseIdxMinus (k : Fin 3) : Fin 6 := ⟨k.val + 3, by omega⟩

/-- Explicit isometry `Q33 ≃ᵢ cl33PhaseQuadratic`. -/
def q33PhaseIsometry : Q33.IsometryEquiv cl33PhaseQuadratic where
  toFun x := (fun k => x (phaseIdxPlus k) + x (phaseIdxMinus k),
    fun k => x (phaseIdxPlus k) - x (phaseIdxMinus k))
  invFun z i := if hi : i.val < 3 then
      (z.1 ⟨i.val, hi⟩ + z.2 ⟨i.val, hi⟩) / 2
    else
      (z.1 ⟨i.val - 3, by omega⟩ - z.2 ⟨i.val - 3, by omega⟩) / 2
  left_inv x := by
    funext i
    fin_cases i <;> simp [phaseIdxPlus, phaseIdxMinus]
  right_inv z := by
    rcases z with ⟨u, v⟩
    ext k
    · fin_cases k <;> simp [phaseIdxPlus, phaseIdxMinus] <;> ring
    · fin_cases k <;> simp [phaseIdxPlus, phaseIdxMinus] <;> ring
  map_add' x y := by
    ext k <;> simp [phaseIdxPlus, phaseIdxMinus] <;> ring
  map_smul' r x := by
    ext k <;> simp [phaseIdxPlus, phaseIdxMinus] <;> ring
  map_app' x := by
    rw [cl33PhaseQuadratic_apply, Q33_apply, Fin.sum_univ_three]
    simp [phaseIdxPlus, phaseIdxMinus]
    ring

/-- Explicit Clifford algebra isomorphism to the phase-space `Cl(3,3)` form. -/
def cliffordQ33EquivPhase :
    CliffordAlgebra Q33 ≃ₐ[ℝ] CliffordAlgebra cl33PhaseQuadratic :=
  CliffordAlgebra.equivOfIsometry q33PhaseIsometry

/-- Six Majorana matrix generators `[M₀⁺, M₁⁺, M₂⁺, M₀⁻, M₁⁻, M₂⁻]` on `Fin 8`. -/
def q33GenMat : Fin 6 → Matrix (Fin 8) (Fin 8) ℝ
  | 0 => majoranaPlusMat 0
  | 1 => majoranaPlusMat 1
  | 2 => majoranaPlusMat 2
  | 3 => majoranaMinusMat 0
  | 4 => majoranaMinusMat 1
  | 5 => majoranaMinusMat 2

private def q33ToSevenIdx : Fin 6 → Fin 7
  | 0 => 4
  | 1 => 5
  | 2 => 6
  | 3 => 0
  | 4 => 1
  | 5 => 2

theorem q33GenMat_eq_sevenAnticommOps (a : Fin 6) :
    q33GenMat a = sevenAnticommOps (q33ToSevenIdx a) := by
  fin_cases a
  · exact majoranaPlusMat_eq_leftMulMat_sCD 0
  · exact majoranaPlusMat_eq_leftMulMat_sCD 1
  · exact majoranaPlusMat_eq_leftMulMat_sCD 2
  · exact majoranaMinusMat_eq_leftMulMat_iCD 0
  · exact majoranaMinusMat_eq_leftMulMat_iCD 1
  · exact majoranaMinusMat_eq_leftMulMat_iCD 2

theorem q33GenMat_sq (a : Fin 6) :
    q33GenMat a * q33GenMat a = q33Sig a • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [q33GenMat_eq_sevenAnticommOps, sevenAnticommOps_sq]
  fin_cases a <;> rfl

theorem q33GenMat_anticomm {a b : Fin 6} (hab : a ≠ b) :
    q33GenMat a * q33GenMat b + q33GenMat b * q33GenMat a = 0 := by
  rw [q33GenMat_eq_sevenAnticommOps, q33GenMat_eq_sevenAnticommOps]
  apply sevenAnticommOps_anticomm
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | decide

/-- Linear map `(Fin 6 → ℝ) →ₗ[ℝ] Matrix (Fin 8) (Fin 8) ℝ` sending `e_a` to `q33GenMat a`. -/
def q33VecToMat : (Fin 6 → ℝ) →ₗ[ℝ] Matrix (Fin 8) (Fin 8) ℝ where
  toFun c := ∑ a : Fin 6, c a • q33GenMat a
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_smul]

private theorem q33_sum_sq_id (c : Fin 6 → ℝ) :
    (∑ a : Fin 6, 2 * q33Sig a * c a ^ 2) =
      2 * (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 - c 3 ^ 2 - c 4 ^ 2 - c 5 ^ 2) := by
  simp [Fin.sum_univ_six, q33Sig]
  ring

theorem q33VecToMat_sq (c : Fin 6 → ℝ) :
    q33VecToMat c * q33VecToMat c = algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ) (Q33 c) := by
  have h2 : (2 : ℝ) • (q33VecToMat c * q33VecToMat c) =
      (2 : ℝ) • algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ) (Q33 c) := by
    have hsum : (2 : ℝ) • (q33VecToMat c * q33VecToMat c) =
        ∑ a : Fin 6, ∑ b : Fin 6,
          (c a * c b) • (q33GenMat a * q33GenMat b + q33GenMat b * q33GenMat a) := by
      have hLHS : q33VecToMat c * q33VecToMat c =
          ∑ a : Fin 6, ∑ b : Fin 6, (c a * c b) • (q33GenMat a * q33GenMat b) := by
        unfold q33VecToMat
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [Matrix.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Matrix.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hRHS : q33VecToMat c * q33VecToMat c =
          ∑ a : Fin 6, ∑ b : Fin 6, (c a * c b) • (q33GenMat b * q33GenMat a) := by
        rw [hLHS, Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
        rw [mul_comm (c a) (c b)]
      rw [two_smul]
      conv_lhs => arg 1; rw [hLHS]
      conv_lhs => arg 2; rw [hRHS]
      simp_rw [← Finset.sum_add_distrib, ← smul_add]
    rw [hsum]
    have hdiag : ∀ a : Fin 6,
        (∑ b : Fin 6, (c a * c b) • (q33GenMat a * q33GenMat b + q33GenMat b * q33GenMat a)) =
          (2 * q33Sig a * (c a) ^ 2) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
      intro a
      rw [Finset.sum_eq_single a]
      · rw [← two_smul ℝ (q33GenMat a * q33GenMat a), q33GenMat_sq a, smul_smul, smul_smul]
        congr 1
        simp only [sq, mul_assoc, mul_comm]
      · intro b _ hba
        rw [q33GenMat_anticomm hba.symm, smul_zero]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    simp_rw [hdiag, ← Finset.sum_smul, Algebra.algebraMap_eq_smul_one, smul_smul, Q33_apply]
    congr 1
    exact q33_sum_sq_id c
  have hsub : (2 : ℝ) • (q33VecToMat c * q33VecToMat c -
      algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ) (Q33 c)) = 0 := by
    rw [smul_sub, h2, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_left (by norm_num))

/-- Universal Clifford algebra homomorphism `Cl(3,3) →ₐ[ℝ] M₈(ℝ)`. -/
def cliffordQ33ToMat8Hom : CliffordAlgebra Q33 →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  CliffordAlgebra.lift Q33 ⟨q33VecToMat, q33VecToMat_sq⟩

theorem cliffordQ33ToMat8Hom_gen (a : Fin 6) :
    cliffordQ33ToMat8Hom (CliffordAlgebra.ι Q33 (Pi.single a 1)) = q33GenMat a := by
  unfold cliffordQ33ToMat8Hom
  rw [CliffordAlgebra.lift_ι_apply]
  change (∑ b : Fin 6, (Pi.single a (1 : ℝ) : Fin 6 → ℝ) b • q33GenMat b) = q33GenMat a
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [Pi.single_eq_of_ne hba]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private def q33PlusIdx : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2

private def q33MinusIdx : Fin 3 → Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 5

theorem cliffordQ33ToMat8Hom_car_plus (k : Fin 3) :
    cliffordQ33ToMat8Hom ((1 / 2 : ℝ) •
      (CliffordAlgebra.ι Q33 (Pi.single (q33PlusIdx k) 1) +
        CliffordAlgebra.ι Q33 (Pi.single (q33MinusIdx k) 1))) = carAnnihilateMat k := by
  rw [map_smul, map_add, cliffordQ33ToMat8Hom_gen, cliffordQ33ToMat8Hom_gen]
  have hp : q33GenMat (q33PlusIdx k) = majoranaPlusMat k := by fin_cases k <;> rfl
  have hm : q33GenMat (q33MinusIdx k) = majoranaMinusMat k := by fin_cases k <;> rfl
  rw [hp, hm, majoranaPlusMat, majoranaMinusMat]
  ext i j
  simp [smul_eq_mul]
  ring

theorem cliffordQ33ToMat8Hom_car_minus (k : Fin 3) :
    cliffordQ33ToMat8Hom ((1 / 2 : ℝ) •
      (CliffordAlgebra.ι Q33 (Pi.single (q33PlusIdx k) 1) -
        CliffordAlgebra.ι Q33 (Pi.single (q33MinusIdx k) 1))) = carCreateMat k := by
  rw [map_smul, map_sub, cliffordQ33ToMat8Hom_gen, cliffordQ33ToMat8Hom_gen]
  have hp : q33GenMat (q33PlusIdx k) = majoranaPlusMat k := by fin_cases k <;> rfl
  have hm : q33GenMat (q33MinusIdx k) = majoranaMinusMat k := by fin_cases k <;> rfl
  rw [hp, hm, majoranaPlusMat, majoranaMinusMat]
  ext i j
  simp [smul_eq_mul]
  ring

private def zornZMat (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ :=
  majoranaGenZ (modeEvenIdx k) * majoranaGenZ (modeOddIdx k)

private def slotUnitZ (k : Fin 3) (a b : Fin 2) : Matrix (Fin 8) (Fin 8) ℤ :=
  let prefixZ : Matrix (Fin 8) (Fin 8) ℤ := match k with
    | 0 => 1
    | 1 => zornZMat 0
    | 2 => zornZMat 0 * zornZMat 1
  match a, b with
  | 0, 0 => 1 + zornZMat k
  | 0, 1 => prefixZ * twoFockAnnihilate8Z k
  | 1, 0 => prefixZ * twoFockCreate8Z k
  | 1, 1 => 1 - zornZMat k

private theorem slotUnitZ_prod (p q : Fin 8) :
    slotUnitZ 0 ⟨p.val / 4, by omega⟩ ⟨q.val / 4, by omega⟩ *
      slotUnitZ 1 ⟨(p.val / 2) % 2, by omega⟩ ⟨(q.val / 2) % 2, by omega⟩ *
      slotUnitZ 2 ⟨p.val % 2, by omega⟩ ⟨q.val % 2, by omega⟩ =
      (8 : ℤ) • Matrix.single p q 1 := by
  revert p q
  decide

private def jwMatrixSubalgebra : Subalgebra ℝ (Matrix (Fin 8) (Fin 8) ℝ) :=
  Algebra.adjoin ℝ (Set.range majoranaGenR)

private theorem majoranaGenR_mem_jw (a : Fin 6) : majoranaGenR a ∈ jwMatrixSubalgebra :=
  Algebra.subset_adjoin (Set.mem_range_self a)

private theorem mapMatrix_zornZMat_mem_jw (k : Fin 3) :
    (Int.castRingHom ℝ).mapMatrix (zornZMat k) ∈ jwMatrixSubalgebra := by
  unfold zornZMat
  rw [map_mul]
  exact Subalgebra.mul_mem _ (majoranaGenR_mem_jw _) (majoranaGenR_mem_jw _)

private theorem mapMatrix_twoFockCreate8Z_mem_jw (k : Fin 3) :
    (Int.castRingHom ℝ).mapMatrix (twoFockCreate8Z k) ∈ jwMatrixSubalgebra := by
  unfold twoFockCreate8Z
  rw [map_add]
  exact Subalgebra.add_mem _ (majoranaGenR_mem_jw _) (majoranaGenR_mem_jw _)

private theorem mapMatrix_twoFockAnnihilate8Z_mem_jw (k : Fin 3) :
    (Int.castRingHom ℝ).mapMatrix (twoFockAnnihilate8Z k) ∈ jwMatrixSubalgebra := by
  unfold twoFockAnnihilate8Z
  rw [map_sub]
  exact Subalgebra.sub_mem _ (majoranaGenR_mem_jw _) (majoranaGenR_mem_jw _)

private theorem mapMatrix_slotUnitZ_mem_jw (k : Fin 3) (a b : Fin 2) :
    (Int.castRingHom ℝ).mapMatrix (slotUnitZ k a b) ∈ jwMatrixSubalgebra := by
  have hpref : ∀ m : Fin 3,
      (Int.castRingHom ℝ).mapMatrix (match m with
        | 0 => (1 : Matrix (Fin 8) (Fin 8) ℤ)
        | 1 => zornZMat 0
        | 2 => zornZMat 0 * zornZMat 1) ∈ jwMatrixSubalgebra := by
    intro m
    fin_cases m
    · rw [map_one]; exact Subalgebra.one_mem _
    · exact mapMatrix_zornZMat_mem_jw 0
    · rw [map_mul]; exact Subalgebra.mul_mem _ (mapMatrix_zornZMat_mem_jw 0)
        (mapMatrix_zornZMat_mem_jw 1)
  fin_cases a <;> fin_cases b
  · dsimp [slotUnitZ]; rw [map_add, map_one]
    exact Subalgebra.add_mem _ (Subalgebra.one_mem _) (mapMatrix_zornZMat_mem_jw k)
  · dsimp [slotUnitZ]; rw [map_mul]
    exact Subalgebra.mul_mem _ (hpref k) (mapMatrix_twoFockAnnihilate8Z_mem_jw k)
  · dsimp [slotUnitZ]; rw [map_mul]
    exact Subalgebra.mul_mem _ (hpref k) (mapMatrix_twoFockCreate8Z_mem_jw k)
  · dsimp [slotUnitZ]; rw [map_sub, map_one]
    exact Subalgebra.sub_mem _ (Subalgebra.one_mem _) (mapMatrix_zornZMat_mem_jw k)

private theorem jwMatrixSubalgebra_eq_top : jwMatrixSubalgebra = ⊤ := by
  rw [eq_top_iff]
  intro M _
  have hsingle : ∀ p q : Fin 8, Matrix.single p q (1 : ℝ) ∈ jwMatrixSubalgebra := by
    intro p q
    have hprod := congrArg ((Int.castRingHom ℝ).mapMatrix) (slotUnitZ_prod p q)
    rw [map_mul, map_mul] at hprod
    have hmem : (Int.castRingHom ℝ).mapMatrix ((8 : ℤ) • Matrix.single p q (1 : ℤ)) ∈
        jwMatrixSubalgebra := by
      rw [← hprod]
      exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _
        (mapMatrix_slotUnitZ_mem_jw 0 _ _) (mapMatrix_slotUnitZ_mem_jw 1 _ _))
        (mapMatrix_slotUnitZ_mem_jw 2 _ _)
    have hcast : (Int.castRingHom ℝ).mapMatrix ((8 : ℤ) • Matrix.single p q (1 : ℤ)) =
        (8 : ℝ) • Matrix.single p q (1 : ℝ) := by
      ext i j
      simp [Matrix.single]
    rw [hcast] at hmem
    have hscaled := Subalgebra.smul_mem jwMatrixSubalgebra hmem (1 / 8 : ℝ)
    rwa [smul_smul, show (1 / 8 : ℝ) * 8 = 1 by norm_num, one_smul] at hscaled
  rw [Matrix.matrix_eq_sum_single M]
  exact Subalgebra.sum_mem _ fun p _ => Subalgebra.sum_mem _ fun q _ =>
    by
      rw [← mul_one (M p q), ← smul_eq_mul, ← Matrix.smul_single]
      exact Subalgebra.smul_mem _ (hsingle p q) (M p q)

private def cdJWConjMat : Matrix (Fin 8) (Fin 8) ℝ :=
  zornToCDMatrix * zornJWConjugator

private def cdJWConjMatInv : Matrix (Fin 8) (Fin 8) ℝ :=
  zornJWConjugator * cdToZornMatrix

private theorem cdJWConjMat_mul_inv : cdJWConjMat * cdJWConjMatInv = 1 := by
  calc cdJWConjMat * cdJWConjMatInv
      = zornToCDMatrix * (zornJWConjugator * zornJWConjugator) * cdToZornMatrix := by
          simp [cdJWConjMat, cdJWConjMatInv, Matrix.mul_assoc]
    _ = zornToCDMatrix * cdToZornMatrix := by rw [zornJWConjugator_sq, Matrix.mul_one]
    _ = 1 := zornToCDMatrix_mul_cdToZornMatrix

private theorem cdJWConjMatInv_mul : cdJWConjMatInv * cdJWConjMat = 1 := by
  calc cdJWConjMatInv * cdJWConjMat
      = zornJWConjugator * (cdToZornMatrix * zornToCDMatrix) * zornJWConjugator := by
          simp [cdJWConjMat, cdJWConjMatInv, Matrix.mul_assoc]
    _ = zornJWConjugator * zornJWConjugator := by
          rw [cdToZornMatrix_mul_zornToCDMatrix, Matrix.mul_one]
    _ = 1 := zornJWConjugator_sq

private def cdJWConjEquiv : Matrix (Fin 8) (Fin 8) ℝ ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ where
  toFun M := cdJWConjMat * M * cdJWConjMatInv
  invFun N := cdJWConjMatInv * N * cdJWConjMat
  left_inv M := by
    calc cdJWConjMatInv * (cdJWConjMat * M * cdJWConjMatInv) * cdJWConjMat
        = (cdJWConjMatInv * cdJWConjMat) * M * (cdJWConjMatInv * cdJWConjMat) := by
            simp only [Matrix.mul_assoc]
      _ = M := by rw [cdJWConjMatInv_mul, Matrix.one_mul, Matrix.mul_one]
  right_inv N := by
    calc cdJWConjMat * (cdJWConjMatInv * N * cdJWConjMat) * cdJWConjMatInv
        = (cdJWConjMat * cdJWConjMatInv) * N * (cdJWConjMat * cdJWConjMatInv) := by
            simp only [Matrix.mul_assoc]
      _ = N := by rw [cdJWConjMat_mul_inv, Matrix.one_mul, Matrix.mul_one]
  map_mul' M N := by
    calc cdJWConjMat * (M * N) * cdJWConjMatInv
        = cdJWConjMat * (M * (1 * N)) * cdJWConjMatInv := by rw [Matrix.one_mul]
      _ = cdJWConjMat * (M * ((cdJWConjMatInv * cdJWConjMat) * N)) * cdJWConjMatInv := by
            rw [cdJWConjMatInv_mul]
      _ = (cdJWConjMat * M * cdJWConjMatInv) * (cdJWConjMat * N * cdJWConjMatInv) := by
            simp only [Matrix.mul_assoc]
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      cdJWConjMat_mul_inv]

private theorem zornLeftActMatrix_sCD_eq_neg_majorana (k : Fin 3) :
    zornLeftActMatrix (splitOctCDEquivZornSplitOctonion (sCD k)) =
      -zornLeftActMatrix (embedVec (zornMajoranaPlusVector k)) := by
  unfold zornLeftActMatrix
  rw [← map_neg]
  congr 1
  apply LinearMap.ext; intro v; funext i
  change zornLeftActFin8 (splitOctCDEquivZornSplitOctonion (sCD k)) v i =
    -(zornLeftActFin8 (embedVec (zornMajoranaPlusVector k)) v i)
  fin_cases k <;> fin_cases i <;>
    simp [zornLeftActFin8, splitOctCDEquivZornSplitOctonion, sCD_formula, qBasis, embedVec,
      zornMajoranaPlusVector, zornMul, vec3Dot, vec3Cross, zornToFin8, fin8ToZorn]

private theorem zornLeftActMatrix_iCD_eq_neg_majorana (k : Fin 3) :
    zornLeftActMatrix (splitOctCDEquivZornSplitOctonion (iCD k)) =
      -zornLeftActMatrix (embedVec (zornMajoranaMinusVector k)) := by
  unfold zornLeftActMatrix
  rw [← map_neg]
  congr 1
  apply LinearMap.ext; intro v; funext i
  change zornLeftActFin8 (splitOctCDEquivZornSplitOctonion (iCD k)) v i =
    -(zornLeftActFin8 (embedVec (zornMajoranaMinusVector k)) v i)
  fin_cases k <;> fin_cases i <;>
    simp [zornLeftActFin8, splitOctCDEquivZornSplitOctonion, iCD, qBasis, embedVec,
      zornMajoranaMinusVector, zornMul, vec3Dot, vec3Cross, zornToFin8, fin8ToZorn]

private theorem cdJWConjEquiv_majoranaGenR (a : Fin 6) :
    cdJWConjEquiv (-majoranaGenR a) ∈ Algebra.adjoin ℝ (Set.range q33GenMat) := by
  have hmem : ∀ x : Fin 6, q33GenMat x ∈ Algebra.adjoin ℝ (Set.range q33GenMat) :=
    fun x => Algebra.subset_adjoin (Set.mem_range_self x)
  have hplus : ∀ k : Fin 3,
      cdJWConjEquiv (-majoranaGenR (modeEvenIdx k)) = majoranaPlusMat k := by
    intro k
    rw [majoranaPlusMat_eq_leftMulMat_sCD, leftMulMat_conj_zornLeftActMatrix,
      zornLeftActMatrix_sCD_eq_neg_majorana, ← zornMajoranaVec_modeEvenIdx k,
      zornLeftActMatrix_majorana_eq_conjugate]
    change cdJWConjMat * (-majoranaGenR (modeEvenIdx k)) * cdJWConjMatInv = _
    simp only [cdJWConjMat, cdJWConjMatInv, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hminus : ∀ k : Fin 3,
      cdJWConjEquiv (-majoranaGenR (modeOddIdx k)) = majoranaMinusMat k := by
    intro k
    rw [majoranaMinusMat_eq_leftMulMat_iCD, leftMulMat_conj_zornLeftActMatrix,
      zornLeftActMatrix_iCD_eq_neg_majorana, ← zornMajoranaVec_modeOddIdx k,
      zornLeftActMatrix_majorana_eq_conjugate]
    change cdJWConjMat * (-majoranaGenR (modeOddIdx k)) * cdJWConjMatInv = _
    simp only [cdJWConjMat, cdJWConjMatInv, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  fin_cases a
  · change cdJWConjEquiv (-majoranaGenR (modeEvenIdx 0)) ∈ _
    rw [hplus 0]; exact hmem 0
  · change cdJWConjEquiv (-majoranaGenR (modeOddIdx 0)) ∈ _
    rw [hminus 0]; exact hmem 3
  · change cdJWConjEquiv (-majoranaGenR (modeEvenIdx 1)) ∈ _
    rw [hplus 1]; exact hmem 1
  · change cdJWConjEquiv (-majoranaGenR (modeOddIdx 1)) ∈ _
    rw [hminus 1]; exact hmem 4
  · change cdJWConjEquiv (-majoranaGenR (modeEvenIdx 2)) ∈ _
    rw [hplus 2]; exact hmem 2
  · change cdJWConjEquiv (-majoranaGenR (modeOddIdx 2)) ∈ _
    rw [hminus 2]; exact hmem 5

private theorem cdJWConjEquiv_mem_q33 {N : Matrix (Fin 8) (Fin 8) ℝ}
    (hN : N ∈ jwMatrixSubalgebra) :
    cdJWConjEquiv N ∈ Algebra.adjoin ℝ (Set.range q33GenMat) := by
  induction hN using Algebra.adjoin_induction with
  | mem x hx =>
      rcases hx with ⟨a, rfl⟩
      have hneg := cdJWConjEquiv_majoranaGenR a
      rw [map_neg] at hneg
      have hpos := Subalgebra.neg_mem _ hneg
      rwa [neg_neg] at hpos
  | algebraMap r =>
      rw [AlgEquiv.commutes]
      exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy =>
      rw [map_add]
      exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
      rw [map_mul]
      exact Subalgebra.mul_mem _ hx hy

private theorem mem_adjoin_q33GenMat (M : Matrix (Fin 8) (Fin 8) ℝ) :
    M ∈ Algebra.adjoin ℝ (Set.range q33GenMat) := by
  have hN : cdJWConjEquiv.symm M ∈ jwMatrixSubalgebra := by
    rw [jwMatrixSubalgebra_eq_top]
    trivial
  have h := cdJWConjEquiv_mem_q33 hN
  rwa [AlgEquiv.apply_symm_apply] at h

theorem cliffordQ33ToMat8Hom_surjective : Function.Surjective cliffordQ33ToMat8Hom := by
  intro M
  have hM := mem_adjoin_q33GenMat M
  induction hM using Algebra.adjoin_induction with
  | mem x hx =>
      rcases hx with ⟨a, rfl⟩
      exact ⟨CliffordAlgebra.ι Q33 (Pi.single a 1), cliffordQ33ToMat8Hom_gen a⟩
  | algebraMap r =>
      exact ⟨algebraMap ℝ (CliffordAlgebra Q33) r, AlgHom.commutes cliffordQ33ToMat8Hom r⟩
  | add x y _ _ hx hy =>
      rcases hx with ⟨ax, rfl⟩
      rcases hy with ⟨ay, rfl⟩
      exact ⟨ax + ay, map_add cliffordQ33ToMat8Hom ax ay⟩
  | mul x y _ _ hx hy =>
      rcases hx with ⟨ax, rfl⟩
      rcases hy with ⟨ay, rfl⟩
      exact ⟨ax * ay, map_mul cliffordQ33ToMat8Hom ax ay⟩

private local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

theorem cliffordQ33_finrank : Module.finrank ℝ (CliffordAlgebra Q33) = 64 := by
  let extBasis : Module.Basis (Finset (Fin 6)) ℝ (ExteriorAlgebra ℝ (Fin 6 → ℝ)) :=
    (Pi.basisFun ℝ (Fin 6)).ExteriorAlgebra
  rw [LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior Q33),
    Module.finrank_eq_card_basis extBasis]
  simp [Fintype.card_finset]

theorem cliffordQ33ToMat8Hom_injective : Function.Injective cliffordQ33ToMat8Hom := by
  let extBasis : Module.Basis (Finset (Fin 6)) ℝ (ExteriorAlgebra ℝ (Fin 6 → ℝ)) :=
    (Pi.basisFun ℝ (Fin 6)).ExteriorAlgebra
  have : FiniteDimensional ℝ (ExteriorAlgebra ℝ (Fin 6 → ℝ)) :=
    Module.Basis.finiteDimensional_of_finite extBasis
  have : FiniteDimensional ℝ (CliffordAlgebra Q33) :=
    LinearEquiv.finiteDimensional (CliffordAlgebra.equivExterior Q33).symm
  have hrank : Module.finrank ℝ (CliffordAlgebra Q33) =
      Module.finrank ℝ (Matrix (Fin 8) (Fin 8) ℝ) := by
    rw [cliffordQ33_finrank, Module.finrank_matrix]
    norm_num
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := cliffordQ33ToMat8Hom.toLinearMap) hrank).mpr cliffordQ33ToMat8Hom_surjective

/-- Genuine `ℝ`-algebra isomorphism `Cl(3,3) ≃ₐ[ℝ] M₈(ℝ)`. -/
def cliffordQ33ToMat8 : CliffordAlgebra Q33 ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  AlgEquiv.ofBijective cliffordQ33ToMat8Hom
    ⟨cliffordQ33ToMat8Hom_injective, cliffordQ33ToMat8Hom_surjective⟩

theorem cliffordQ33ToMat8_car_plus (k : Fin 3) :
    cliffordQ33ToMat8 ((1 / 2 : ℝ) •
      (CliffordAlgebra.ι Q33 (Pi.single (q33PlusIdx k) 1) +
        CliffordAlgebra.ι Q33 (Pi.single (q33MinusIdx k) 1))) = carAnnihilateMat k :=
  cliffordQ33ToMat8Hom_car_plus k

theorem cliffordQ33ToMat8_car_minus (k : Fin 3) :
    cliffordQ33ToMat8 ((1 / 2 : ℝ) •
      (CliffordAlgebra.ι Q33 (Pi.single (q33PlusIdx k) 1) -
        CliffordAlgebra.ι Q33 (Pi.single (q33MinusIdx k) 1))) = carCreateMat k :=
  cliffordQ33ToMat8Hom_car_minus k

/-! ## Section 4: `SplitOctCDAut`, `G_{2(2)} ⊂ SO(4,4)`, and `SL₃(ℝ)` Stabilizer (Feature F12) -/

/-- Predicate for `ℝ`-linear automorphisms of `SplitOctCD`. -/
def isSplitOctCDAut (f : SplitOctCD ≃ₗ[ℝ] SplitOctCD) : Prop :=
  f (1 : SplitOctCD) = 1 ∧ ∀ x y : SplitOctCD, f (x * y) = f x * f y

private theorem splitOctCDEquivZornMatrix_symm_one :
    splitOctCDEquivZornMatrix.symm (1 : ZornMatrix ℝ) = 1 := by
  apply splitOctCDEquivZornMatrix.injective
  rw [splitOctCDEquivZornMatrix.apply_symm_apply, splitOctCDEquivZornMatrix_one]

private theorem splitOctCDEquivZornMatrix_symm_mul (X Y : ZornMatrix ℝ) :
    splitOctCDEquivZornMatrix.symm (X * Y) =
      splitOctCDEquivZornMatrix.symm X * splitOctCDEquivZornMatrix.symm Y := by
  apply splitOctCDEquivZornMatrix.injective
  rw [splitOctCDEquivZornMatrix_mul, splitOctCDEquivZornMatrix.apply_symm_apply,
    splitOctCDEquivZornMatrix.apply_symm_apply, splitOctCDEquivZornMatrix.apply_symm_apply]

theorem isSplitOctCDAut_of_mul (f : SplitOctCD ≃ₗ[ℝ] SplitOctCD)
    (hmul : ∀ x y : SplitOctCD, f (x * y) = f x * f y) : isSplitOctCDAut f := by
  refine ⟨?_, hmul⟩
  have h : f (f.symm 1 * 1) = f (f.symm 1) * f 1 := hmul (f.symm 1) 1
  rw [mul_one, f.apply_symm_apply, one_mul] at h
  exact h.symm

/-- Subgroup of `ℝ`-linear algebra automorphisms of `SplitOctCD`. -/
def splitOctCDAutSubgroup : Subgroup (SplitOctCD ≃ₗ[ℝ] SplitOctCD) where
  carrier := {f | isSplitOctCDAut f}
  one_mem' := ⟨rfl, fun _ _ => rfl⟩
  mul_mem' {f g} hf hg := by
    refine ⟨?_, fun x y => ?_⟩
    · change f (g 1) = 1
      rw [hg.1, hf.1]
    · change f (g (x * y)) = f (g x) * f (g y)
      rw [hg.2, hf.2]
  inv_mem' {f} hf := by
    refine ⟨?_, fun x y => ?_⟩
    · apply f.injective
      change f (f.symm 1) = f 1
      rw [f.apply_symm_apply, hf.1]
    · apply f.injective
      change f (f.symm (x * y)) = f (f.symm x * f.symm y)
      rw [f.apply_symm_apply, hf.2, f.apply_symm_apply, f.apply_symm_apply]

/-- The split-octonion automorphism group `G_{2(2)} = Aut(SplitOctCD)`. -/
abbrev SplitOctCDAut : Type := ↥splitOctCDAutSubgroup

instance : Inhabited SplitOctCDAut := ⟨1⟩

/-- Group isomorphism `SplitOctCDAut ≃* RealSplitOctonionAut` via `splitOctCDEquivZornMatrix`. -/
def splitOctCDAutMulEquivRealSplitOctonionAut : SplitOctCDAut ≃* RealSplitOctonionAut where
  toFun φ :=
    ⟨splitOctCDEquivZornMatrix.symm.trans (φ.1.trans splitOctCDEquivZornMatrix), by
      refine ⟨?_, fun X Y => ?_⟩
      · change splitOctCDEquivZornMatrix (φ.1 (splitOctCDEquivZornMatrix.symm 1)) = 1
        rw [splitOctCDEquivZornMatrix_symm_one, φ.2.1, splitOctCDEquivZornMatrix_one]
      · change splitOctCDEquivZornMatrix (φ.1 (splitOctCDEquivZornMatrix.symm (X * Y))) =
          splitOctCDEquivZornMatrix (φ.1 (splitOctCDEquivZornMatrix.symm X)) *
            splitOctCDEquivZornMatrix (φ.1 (splitOctCDEquivZornMatrix.symm Y))
        rw [splitOctCDEquivZornMatrix_symm_mul, φ.2.2, splitOctCDEquivZornMatrix_mul]⟩
  invFun ψ :=
    ⟨splitOctCDEquivZornMatrix.trans (ψ.1.trans splitOctCDEquivZornMatrix.symm), by
      refine ⟨?_, fun x y => ?_⟩
      · change splitOctCDEquivZornMatrix.symm
            (ψ.1 (splitOctCDEquivZornMatrix 1)) = 1
        rw [splitOctCDEquivZornMatrix_one, ψ.2.1, splitOctCDEquivZornMatrix_symm_one]
      · change splitOctCDEquivZornMatrix.symm
            (ψ.1 (splitOctCDEquivZornMatrix (x * y))) =
          splitOctCDEquivZornMatrix.symm (ψ.1 (splitOctCDEquivZornMatrix x)) *
            splitOctCDEquivZornMatrix.symm (ψ.1 (splitOctCDEquivZornMatrix y))
        rw [splitOctCDEquivZornMatrix_mul, ψ.2.2, splitOctCDEquivZornMatrix_symm_mul]⟩
  left_inv φ := by
    apply Subtype.ext; apply LinearEquiv.ext; intro x
    show splitOctCDEquivZornMatrix.symm
      (splitOctCDEquivZornMatrix (φ.1 (splitOctCDEquivZornMatrix.symm
        (splitOctCDEquivZornMatrix x)))) = φ.1 x
    rw [splitOctCDEquivZornMatrix.symm_apply_apply, splitOctCDEquivZornMatrix.symm_apply_apply]
  right_inv ψ := by
    apply Subtype.ext; apply LinearEquiv.ext; intro X
    show splitOctCDEquivZornMatrix
      (splitOctCDEquivZornMatrix.symm (ψ.1 (splitOctCDEquivZornMatrix
        (splitOctCDEquivZornMatrix.symm X)))) = ψ.1 X
    rw [splitOctCDEquivZornMatrix.apply_symm_apply, splitOctCDEquivZornMatrix.apply_symm_apply]
  map_mul' φ ψ := by
    apply Subtype.ext; apply LinearEquiv.ext; intro X
    show splitOctCDEquivZornMatrix (φ.1 (ψ.1 (splitOctCDEquivZornMatrix.symm X))) =
      splitOctCDEquivZornMatrix (φ.1 (splitOctCDEquivZornMatrix.symm
        (splitOctCDEquivZornMatrix (ψ.1 (splitOctCDEquivZornMatrix.symm X)))))
    rw [splitOctCDEquivZornMatrix.symm_apply_apply]

theorem SplitOctCDAut.preserves_one (φ : SplitOctCDAut) : φ.1 1 = 1 :=
  φ.2.1

theorem SplitOctCDAut.preserves_mul (φ : SplitOctCDAut) (x y : SplitOctCD) :
    φ.1 (x * y) = φ.1 x * φ.1 y :=
  φ.2.2 x y

theorem SplitOctCDAut.preserves_cdNorm (φ : SplitOctCDAut) (x : SplitOctCD) :
    cdNorm (φ.1 x) = cdNorm x := by
  have h := RealSplitOctonionAut.preserves_detZ (splitOctCDAutMulEquivRealSplitOctonionAut φ)
    (splitOctCDEquivZornMatrix x)
  rw [← splitOctCDEquivZornMatrix_detZ, ← splitOctCDEquivZornMatrix_detZ]
  change (splitOctCDEquivZornMatrix
    (φ.1 (splitOctCDEquivZornMatrix.symm (splitOctCDEquivZornMatrix x)))).detZ = _ at h
  rw [splitOctCDEquivZornMatrix.symm_apply_apply] at h
  exact h

theorem SplitOctCDAut.preserves_cdKreinForm (φ : SplitOctCDAut) (x y : SplitOctCD) :
    cdKreinForm (φ.1 x) (φ.1 y) = cdKreinForm x y := by
  unfold cdKreinForm
  rw [← φ.1.map_add, φ.preserves_cdNorm, φ.preserves_cdNorm, φ.preserves_cdNorm]

/-- Real trace `tr(x) = 2 * x.fst.re` on `SplitOctCD`. -/
def cdTrace (x : SplitOctCD) : ℝ := 2 * x.fst.re

theorem cdKreinForm_one_right (x : SplitOctCD) : cdKreinForm x 1 = x.fst.re := by
  simp [cdKreinForm, cdNorm, Quaternion.normSq_def']
  ring

theorem cdConj_eq_trace_sub (x : SplitOctCD) : cdConj x = cdTrace x • (1 : SplitOctCD) - x := by
  (ext <;> simp [cdConj, cdTrace, oneCD_def]); ring

theorem SplitOctCDAut.preserves_cdTrace (φ : SplitOctCDAut) (x : SplitOctCD) :
    cdTrace (φ.1 x) = cdTrace x := by
  have h := φ.preserves_cdKreinForm x 1
  rw [φ.preserves_one, cdKreinForm_one_right, cdKreinForm_one_right] at h
  simp [cdTrace, h]

theorem SplitOctCDAut.preserves_cdConj (φ : SplitOctCDAut) (x : SplitOctCD) :
    φ.1 (cdConj x) = cdConj (φ.1 x) := by
  rw [cdConj_eq_trace_sub, cdConj_eq_trace_sub, map_sub, map_smul, φ.preserves_one,
    φ.preserves_cdTrace]

/-- Diagonal `(4,4)` Krein metric matrix `J₄₄ = diag(1, 1, 1, 1, -1, -1, -1, -1)`. -/
def J44 : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.diagonal ![1, 1, 1, 1, -1, -1, -1, -1]

/-- Matrix predicate for `SO(4,4)` in `basisCD` coordinates. -/
def IsSO44Matrix (M : Matrix (Fin 8) (Fin 8) ℝ) : Prop :=
  Mᵀ * J44 * M = J44 ∧ M.det = 1

/-- Subgroup `SO(4,4) ≤ GL₈(ℝ)` preserving `J44` with determinant `1`. -/
def SO44Subgroup : Subgroup (Matrix.GeneralLinearGroup (Fin 8) ℝ) where
  carrier := {M | IsSO44Matrix M.1}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' {M N} hM hN := by
    refine ⟨?_, ?_⟩
    · calc (M.1 * N.1)ᵀ * J44 * (M.1 * N.1)
          = N.1ᵀ * (M.1ᵀ * J44 * M.1) * N.1 := by
              rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
        _ = N.1ᵀ * J44 * N.1 := by rw [hM.1]
        _ = J44 := hN.1
    · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hM.2, hN.2, one_mul]
  inv_mem' {M} hM := by
    have hinv : M.1 * (M⁻¹).1 = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
    refine ⟨?_, ?_⟩
    · calc (M⁻¹).1ᵀ * J44 * (M⁻¹).1
          = (M⁻¹).1ᵀ * (M.1ᵀ * J44 * M.1) * (M⁻¹).1 := by rw [hM.1]
        _ = (M.1 * (M⁻¹).1)ᵀ * J44 * (M.1 * (M⁻¹).1) := by
              rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
        _ = J44 := by rw [hinv, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    · have hd := congrArg Matrix.det hinv
      rw [Matrix.det_mul, Matrix.det_one, hM.2, one_mul] at hd
      exact hd

private def cdKreinLinearRight (y : SplitOctCD) : SplitOctCD →ₗ[ℝ] ℝ where
  toFun x := cdKreinForm x y
  map_add' x₁ x₂ := cdKreinForm_add_left x₁ x₂ y
  map_smul' r x := cdKreinForm_smul_left r x y

private theorem cdKreinForm_basisCD_expand (x y : SplitOctCD) :
    cdKreinForm x y =
      ∑ r : Fin 8, (basisCD.repr x r) * (basisCD.repr y r) * J44 r r := by
  have hx : x = ∑ r : Fin 8, basisCD.repr x r • basisCD r := (basisCD.sum_repr x).symm
  have hy : y = ∑ s : Fin 8, basisCD.repr y s • basisCD s := (basisCD.sum_repr y).symm
  conv_lhs => rw [hx, hy]
  have hlinL : ∀ (s : Fin 8),
      cdKreinForm (∑ r : Fin 8, basisCD.repr x r • basisCD r) (basisCD s) =
        ∑ r : Fin 8, basisCD.repr x r * cdKreinForm (basisCD r) (basisCD s) := by
    intro s
    change cdKreinLinearRight (basisCD s) (∑ r, basisCD.repr x r • basisCD r) = _
    rw [map_sum]
    simp [cdKreinLinearRight, smul_eq_mul]
  have hlinR :
      cdKreinForm (∑ r : Fin 8, basisCD.repr x r • basisCD r)
        (∑ s : Fin 8, basisCD.repr y s • basisCD s) =
        ∑ s : Fin 8, basisCD.repr y s *
          cdKreinForm (∑ r : Fin 8, basisCD.repr x r • basisCD r) (basisCD s) := by
    rw [cdKreinForm_symm]
    change cdKreinLinearRight _ (∑ s, basisCD.repr y s • basisCD s) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [cdKreinLinearRight, cdKreinForm_symm]
  rw [hlinR]
  simp_rw [hlinL, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single r]
  · rw [cdKreinForm_basisCD r r]
    fin_cases r <;> simp [J44, mul_comm]
  · intro s _ hsr
    rw [cdKreinForm_basisCD r s]
    simp [hsr.symm]
  · intro hr
    exact absurd (Finset.mem_univ r) hr

/-- Purely imaginary 7D submodule `Im(SplitOctCD) = {x | x.fst.re = 0}`. -/
def imagSubmodule : Submodule ℝ SplitOctCD :=
  LinearMap.ker (cdKreinLinearRight 1)

theorem mem_imagSubmodule_iff (x : SplitOctCD) :
    x ∈ imagSubmodule ↔ x.fst.re = 0 := by
  change cdKreinForm x 1 = 0 ↔ x.fst.re = 0
  rw [cdKreinForm_one_right]

private def bImagVec (k : Fin 7) : imagSubmodule :=
  ⟨basisCD k.succ, by
    rw [mem_imagSubmodule_iff]
    fin_cases k <;> simp [basisCD_one, basisCD_two, basisCD_three, basisCD_four,
      basisCD_five, basisCD_six, basisCD_seven, iCD, ellCD, sCD_formula, qBasis]⟩

private def bImag : Module.Basis (Fin 7) ℝ imagSubmodule :=
  Module.Basis.mk (v := bImagVec)
    (by
      have hind := basisCD.linearIndependent.comp Fin.succ (Fin.succ_injective (n := 7))
      rw [Fintype.linearIndependent_iff] at hind ⊢
      intro g hg i
      apply hind g
      simpa [bImagVec] using congrArg Subtype.val hg)
    (by
      intro x _
      have hx0 : basisCD.repr x.1 0 = 0 := by
        simpa [basisCD_repr_apply, cdToFin8] using (mem_imagSubmodule_iff x.1).mp x.2
      have hsum : x.1 = ∑ k : Fin 7, basisCD.repr x.1 k.succ • basisCD k.succ := by
        have h := (basisCD.sum_repr x.1).symm
        rw [Fin.sum_univ_succ, hx0, zero_smul, zero_add] at h
        exact h
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun k => basisCD.repr x.1 k.succ, ?_⟩
      apply Subtype.ext
      simpa [bImagVec] using hsum.symm)

private theorem bImag_apply (k : Fin 7) : (bImag k).1 = basisCD k.succ := by
  simp [bImag, bImagVec]

attribute [irreducible] bImag

private theorem imag_anticomm_leftMulEnd {x y : imagSubmodule} (hxy : cdKreinForm x.1 y.1 = 0) :
    leftMulEnd x.1 * leftMulEnd y.1 = -(leftMulEnd y.1 * leftMulEnd x.1) := by
  have hx0 : x.1.fst.re = 0 := (mem_imagSubmodule_iff x.1).mp x.2
  have hy0 : y.1.fst.re = 0 := (mem_imagSubmodule_iff y.1).mp y.2
  have hmul : x.1 * y.1 + y.1 * x.1 = (-2 * cdKreinForm x.1 y.1) • (1 : SplitOctCD) := by
    ext <;> simp [cdNorm, cdKreinForm, Quaternion.normSq_def', oneCD_def, hx0, hy0] <;> ring
  rw [hxy, mul_zero, zero_smul] at hmul
  have hEnd := leftMulEnd_anticommutator x.1 y.1
  rw [hmul, leftMulEnd_zero] at hEnd
  exact eq_neg_of_add_eq_zero_left hEnd

private def prodEndFin : ∀ (n : ℕ), (Fin n → Module.End ℝ SplitOctCD) → Module.End ℝ SplitOctCD
  | 0, _ => 1
  | _ + 1, A => A 0 * prodEndFin _ (fun i => A i.succ)

private theorem prodEndFin_pull {n : ℕ} (A : Fin (n + 1) → Module.End ℝ SplitOctCD)
    (hanti : ∀ i j, i ≠ j → A i * A j = -(A j * A i)) (k : Fin (n + 1)) :
    prodEndFin (n + 1) A =
      ((-1 : ℝ) ^ k.val) • (A k * prodEndFin n (fun i => A (k.succAbove i))) := by
  induction n with
  | zero =>
      fin_cases k
      simp [prodEndFin]
  | succ m ih =>
      refine Fin.cases ?_ ?_ k
      · simp [prodEndFin]
      · intro j
        have hrec := ih (fun i => A i.succ)
          (fun i₁ i₂ h => hanti _ _ (fun hs => h (Fin.succ_inj.mp hs))) j
        have hstep : prodEndFin (m + 2) A = A 0 * prodEndFin (m + 1) (fun i => A i.succ) := rfl
        rw [hstep, hrec, Algebra.mul_smul_comm]
        have hswap : A 0 * A j.succ = (-1 : ℝ) • (A j.succ * A 0) := by
          rw [hanti 0 j.succ (Fin.succ_ne_zero j).symm, neg_one_smul]
        rw [← mul_assoc, hswap, smul_mul_assoc, smul_smul]
        have htail : prodEndFin (m + 1) (fun i => A ((j.succ).succAbove i)) =
            A 0 * prodEndFin m (fun i => A (j.succAbove i).succ) := by
          change A ((j.succ).succAbove 0) *
              prodEndFin m (fun i => A ((j.succ).succAbove i.succ)) = _
          simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
        rw [htail, mul_assoc, Fin.val_succ, pow_succ', mul_comm ((-1 : ℝ) ^ j.val) (-1)]

private theorem prodEndFin_swap {n : ℕ} (A : Fin n → Module.End ℝ SplitOctCD)
    (hanti : ∀ i j, i ≠ j → A i * A j = -(A j * A i)) {i j : Fin n} (hij : i ≠ j) :
    prodEndFin n (A ∘ Equiv.swap i j) = -prodEndFin n A := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      wlog hij_lt : i < j generalizing i j
      · have hji : j < i := lt_of_le_of_ne (not_lt.mp hij_lt) hij.symm
        rw [Equiv.swap_comm]
        exact this hij.symm hji
      cases n with
      | zero =>
          fin_cases i; fin_cases j
          exact absurd rfl hij
      | succ m =>
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
            · exact absurd rfl hij
            · let B : Fin (m + 2) → Module.End ℝ SplitOctCD := A ∘ Equiv.swap 0 k.succ
              have hB0 : B 0 = A k.succ := by simp [B]
              have hBk : B k.succ = A 0 := by simp [B]
              have hBrest : ∀ r : Fin m, B (k.succAbove r).succ = A (k.succAbove r).succ := by
                intro r
                have hne0 : (k.succAbove r).succ ≠ 0 := Fin.succ_ne_zero _
                have hnek : (k.succAbove r).succ ≠ k.succ :=
                  fun hs => Fin.succAbove_ne k r (Fin.succ_inj.mp hs)
                simp [B, Equiv.swap_apply_of_ne_of_ne hne0 hnek]
              have hpullB : prodEndFin (m + 1) (fun r => B r.succ) =
                  ((-1 : ℝ) ^ k.val) •
                    (A 0 * prodEndFin m (fun r => A (k.succAbove r).succ)) := by
                have hp := prodEndFin_pull (fun r : Fin (m + 1) => B r.succ)
                  (fun a b hab => hanti _ _ (fun hs =>
                    hab (Fin.succ_inj.mp ((Equiv.swap _ _).injective hs)))) k
                rw [hp, hBk]
                congr 2; congr 1
                funext r
                exact hBrest r
              have hpullA : prodEndFin (m + 2) A =
                  ((-1 : ℝ) ^ (k.val + 1)) •
                    (A k.succ * (A 0 * prodEndFin m (fun r => A (k.succAbove r).succ))) := by
                have hp := prodEndFin_pull A hanti k.succ
                rw [hp]
                congr 1
                have htail : prodEndFin (m + 1) (fun r => A (k.succ.succAbove r)) =
                    A 0 * prodEndFin m (fun r => A (k.succAbove r).succ) := by
                  change A (k.succ.succAbove 0) *
                      prodEndFin m (fun r => A (k.succ.succAbove r.succ)) = _
                  simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
                rw [htail]
              have hstepB : prodEndFin (m + 2) B =
                  B 0 * prodEndFin (m + 1) (fun r => B r.succ) := rfl
              rw [show prodEndFin (m + 2) (A ∘ Equiv.swap 0 k.succ) = prodEndFin (m + 2) B from rfl,
                hstepB, hB0, hpullB, Algebra.mul_smul_comm, hpullA, pow_succ', neg_one_mul,
                neg_smul, neg_neg]
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
            · exact absurd hij_lt (Fin.not_lt_zero _)
            · have hij' : i' ≠ j' := fun hs => hij (congrArg Fin.succ hs)
              have hswap_succ :
                  (fun r : Fin (m + 1) => (A ∘ Equiv.swap i'.succ j'.succ) r.succ) =
                  (fun r : Fin (m + 1) => A r.succ) ∘ Equiv.swap i' j' := by
                funext r
                by_cases hr1 : r = i'
                · subst hr1; simp
                · by_cases hr2 : r = j'
                  · subst hr2; simp
                  · simp [Equiv.swap_apply_of_ne_of_ne hr1 hr2,
                      Equiv.swap_apply_of_ne_of_ne (fun hs => hr1 (Fin.succ_inj.mp hs))
                        (fun hs => hr2 (Fin.succ_inj.mp hs))]
              have h0 : (A ∘ Equiv.swap i'.succ j'.succ) 0 = A 0 := by
                simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i').symm
                  (Fin.succ_ne_zero j').symm]
              have hstep1 : prodEndFin (m + 2) (A ∘ Equiv.swap i'.succ j'.succ) =
                  (A ∘ Equiv.swap i'.succ j'.succ) 0 *
                    prodEndFin (m + 1) (fun r => (A ∘ Equiv.swap i'.succ j'.succ) r.succ) := rfl
              have hstep2 : prodEndFin (m + 2) A =
                  A 0 * prodEndFin (m + 1) (fun r => A r.succ) := rfl
              rw [hstep1, h0, hswap_succ, ih (fun r => A r.succ)
                (fun a b hab => hanti _ _ (fun hs => hab (Fin.succ_inj.mp hs))) hij',
                mul_neg, ← hstep2]

private theorem prodEndFin_perm {n : ℕ} (A : Fin n → Module.End ℝ SplitOctCD)
    (hanti : ∀ i j, i ≠ j → A i * A j = -(A j * A i)) (σ : Equiv.Perm (Fin n)) :
    prodEndFin n (A ∘ σ) = (Equiv.Perm.sign σ : ℝ) • prodEndFin n A := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul f x y hxy ih =>
      have hanti_f : ∀ i j, i ≠ j → (A ∘ f) i * (A ∘ f) j = -((A ∘ f) j * (A ∘ f) i) :=
        fun i j hij => hanti _ _ (f.injective.ne hij)
      have hcomp : A ∘ ⇑(Equiv.swap x y * f) = (A ∘ f) ∘ Equiv.swap (f.symm x) (f.symm y) := by
        funext r
        dsimp
        congr 1
        simp only [Equiv.swap_apply_def]
        by_cases h1 : f r = x
        · have h1' : r = f.symm x := by rw [← h1, Equiv.symm_apply_apply]
          simp [h1']
        · by_cases h2 : f r = y
          · have h2' : r = f.symm y := by rw [← h2, Equiv.symm_apply_apply]
            have hne : r ≠ f.symm x := fun h => h1 (by rw [h, Equiv.apply_symm_apply])
            simp [h2', hxy.symm]
          · have h1' : r ≠ f.symm x := fun h => h1 (by rw [h, Equiv.apply_symm_apply])
            have h2' : r ≠ f.symm y := fun h => h2 (by rw [h, Equiv.apply_symm_apply])
            simp [h1, h2, h1', h2']
      rw [hcomp, prodEndFin_swap (A ∘ f) hanti_f (f.symm.injective.ne hxy), ih,
        Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy, Units.val_mul, Units.val_neg, Units.val_one,
        Int.cast_mul, Int.cast_neg, Int.cast_one, neg_one_mul, neg_smul]

private theorem prodEndFin_update_add {n : ℕ} (A : Fin n → Module.End ℝ SplitOctCD)
    (i : Fin n) (x y : Module.End ℝ SplitOctCD) :
    prodEndFin n (Function.update A i (x + y)) =
      prodEndFin n (Function.update A i x) + prodEndFin n (Function.update A i y) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · have h0 : ∀ z, prodEndFin (n + 1) (Function.update A 0 z) =
            z * prodEndFin n (fun r => A r.succ) := by
          intro z
          change Function.update A 0 z 0 *
              prodEndFin n (fun r => Function.update A 0 z r.succ) = _
          rw [Function.update_self,
            show (fun r : Fin n => Function.update A 0 z r.succ) = fun r => A r.succ from
              funext fun r => Function.update_of_ne (Fin.succ_ne_zero r) z A]
        rw [h0 (x + y), h0 x, h0 y, add_mul]
      · have hstep : ∀ z, prodEndFin (n + 1) (Function.update A j.succ z) =
            A 0 * prodEndFin n (Function.update (fun r => A r.succ) j z) := by
          intro z
          change Function.update A j.succ z 0 *
              prodEndFin n (fun r => Function.update A j.succ z r.succ) = _
          rw [Function.update_of_ne (Fin.succ_ne_zero j).symm]
          congr 1; congr 1
          funext r
          by_cases hr : r = j
          · subst hr; simp
          · simp [Function.update_of_ne hr,
              Function.update_of_ne (fun hs => hr (Fin.succ_inj.mp hs))]
        rw [hstep (x + y), hstep x, hstep y, ih, mul_add]

private theorem prodEndFin_update_smul {n : ℕ} (A : Fin n → Module.End ℝ SplitOctCD)
    (i : Fin n) (r : ℝ) (x : Module.End ℝ SplitOctCD) :
    prodEndFin n (Function.update A i (r • x)) =
      r • prodEndFin n (Function.update A i x) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · have h0 : ∀ z, prodEndFin (n + 1) (Function.update A 0 z) =
            z * prodEndFin n (fun s => A s.succ) := by
          intro z
          change Function.update A 0 z 0 *
              prodEndFin n (fun s => Function.update A 0 z s.succ) = _
          rw [Function.update_self,
            show (fun s : Fin n => Function.update A 0 z s.succ) = fun s => A s.succ from
              funext fun s => Function.update_of_ne (Fin.succ_ne_zero s) z A]
        rw [h0 (r • x), h0 x, smul_mul_assoc]
      · have hstep : ∀ z, prodEndFin (n + 1) (Function.update A j.succ z) =
            A 0 * prodEndFin n (Function.update (fun s => A s.succ) j z) := by
          intro z
          change Function.update A j.succ z 0 *
              prodEndFin n (fun s => Function.update A j.succ z s.succ) = _
          rw [Function.update_of_ne (Fin.succ_ne_zero j).symm]
          congr 1; congr 1
          funext s
          by_cases hs : s = j
          · subst hs; simp
          · simp [Function.update_of_ne hs,
              Function.update_of_ne (fun h => hs (Fin.succ_inj.mp h))]
        rw [hstep (r • x), hstep x, ih, Algebra.mul_smul_comm]

private def leftMulProd7 :
    MultilinearMap ℝ (fun _ : Fin 7 => imagSubmodule) (Module.End ℝ SplitOctCD) where
  toFun v := prodEndFin 7 (fun i => leftMulEnd (v i).1)
  map_update_add' v i x y := by
    have hadd : leftMulEnd (x + y).1 = leftMulEnd x.1 + leftMulEnd y.1 := by
      apply LinearMap.ext; intro z
      change (x.1 + y.1) * z = x.1 * z + y.1 * z
      exact add_mul _ _ _
    have h1 : (fun j => leftMulEnd (Function.update v i (x + y) j).1) =
        @Function.update (Fin 7) (fun _ => Module.End ℝ SplitOctCD) (instDecidableEqFin 7)
          (fun j => leftMulEnd (v j).1) i (leftMulEnd x.1 + leftMulEnd y.1) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_apply, ↓reduceIte, hadd]
      · simp only [Function.update_apply, hj, ↓reduceIte]
    have h2 : (fun j => leftMulEnd (Function.update v i x j).1) =
        @Function.update (Fin 7) (fun _ => Module.End ℝ SplitOctCD) (instDecidableEqFin 7)
          (fun j => leftMulEnd (v j).1) i (leftMulEnd x.1) := by
      funext j
      by_cases hj : j = i <;> simp only [Function.update_apply, hj, ↓reduceIte]
    have h3 : (fun j => leftMulEnd (Function.update v i y j).1) =
        @Function.update (Fin 7) (fun _ => Module.End ℝ SplitOctCD) (instDecidableEqFin 7)
          (fun j => leftMulEnd (v j).1) i (leftMulEnd y.1) := by
      funext j
      by_cases hj : j = i <;> simp only [Function.update_apply, hj, ↓reduceIte]
    change prodEndFin 7 (fun j => leftMulEnd (Function.update v i (x + y) j).1) =
      prodEndFin 7 (fun j => leftMulEnd (Function.update v i x j).1) +
        prodEndFin 7 (fun j => leftMulEnd (Function.update v i y j).1)
    rw [h1, h2, h3, prodEndFin_update_add]
  map_update_smul' v i r x := by
    have hsmul : leftMulEnd (r • x).1 = r • leftMulEnd x.1 := by
      apply LinearMap.ext; intro z
      change (r • x.1) * z = r • (x.1 * z)
      exact cdMul_smul_left _ _ _
    have h1 : (fun j => leftMulEnd (Function.update v i (r • x) j).1) =
        @Function.update (Fin 7) (fun _ => Module.End ℝ SplitOctCD) (instDecidableEqFin 7)
          (fun j => leftMulEnd (v j).1) i (r • leftMulEnd x.1) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_apply, ↓reduceIte, hsmul]
      · simp only [Function.update_apply, hj, ↓reduceIte]
    have h2 : (fun j => leftMulEnd (Function.update v i x j).1) =
        @Function.update (Fin 7) (fun _ => Module.End ℝ SplitOctCD) (instDecidableEqFin 7)
          (fun j => leftMulEnd (v j).1) i (leftMulEnd x.1) := by
      funext j
      by_cases hj : j = i <;> simp only [Function.update_apply, hj, ↓reduceIte]
    change prodEndFin 7 (fun j => leftMulEnd (Function.update v i (r • x) j).1) =
      r • prodEndFin 7 (fun j => leftMulEnd (Function.update v i x j).1)
    rw [h1, h2, prodEndFin_update_smul]

private theorem leftMulProd7_apply (v : Fin 7 → imagSubmodule) :
    leftMulProd7 v = prodEndFin 7 (fun i => leftMulEnd (v i).1) := rfl

private theorem leftMulEnd_apply_cd (x z : SplitOctCD) : leftMulEnd x z = x * z := rfl

private def evalOneRe : Module.End ℝ SplitOctCD →ₗ[ℝ] ℝ where
  toFun E := (E 1).fst.re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evalOneRe_leftMulProd7 (v : Fin 7 → imagSubmodule) :
    evalOneRe (leftMulProd7 v) = (prodEndFin 7 (fun i => leftMulEnd (v i).1) 1).fst.re := rfl

private def oct7Form : imagSubmodule [⋀^Fin 7]→ₗ[ℝ] ℝ :=
  (evalOneRe.compMultilinearMap leftMulProd7).alternatization

private theorem oct7Form_ortho (v : Fin 7 → imagSubmodule)
    (hortho : ∀ i j : Fin 7, i ≠ j → cdKreinForm (v i).1 (v j).1 = 0) :
    oct7Form v = (5040 : ℝ) * evalOneRe (leftMulProd7 v) := by
  unfold oct7Form
  rw [MultilinearMap.alternatization_apply]
  have hanti : ∀ i j : Fin 7, i ≠ j →
      leftMulEnd (v i).1 * leftMulEnd (v j).1 = -(leftMulEnd (v j).1 * leftMulEnd (v i).1) :=
    fun i j hij => imag_anticomm_leftMulEnd (hortho i j hij)
  have hterm : ∀ σ : Equiv.Perm (Fin 7),
      Equiv.Perm.sign σ • ((evalOneRe.compMultilinearMap leftMulProd7).domDomCongr σ v) =
        evalOneRe (leftMulProd7 v) := by
    intro σ
    simp only [MultilinearMap.domDomCongr_apply, LinearMap.compMultilinearMap_apply]
    have hperm := prodEndFin_perm (fun i => leftMulEnd (v i).1) hanti σ
    have hval : evalOneRe (leftMulProd7 (fun i => v (σ i))) =
        (Equiv.Perm.sign σ : ℝ) * evalOneRe (leftMulProd7 v) := by
      rw [leftMulProd7_apply,
        show (fun i => leftMulEnd (v (σ i)).1) = (fun i => leftMulEnd (v i).1) ∘ σ from rfl,
        hperm, ← leftMulProd7_apply, map_smul, smul_eq_mul]
    rw [Units.smul_def, zsmul_eq_mul, hval]
    have hsq : ((Equiv.Perm.sign σ : ℤ) : ℝ) * (Equiv.Perm.sign σ : ℝ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [← mul_assoc, hsq, one_mul]
  simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  norm_num

attribute [irreducible] oct7Form

private theorem bImag_prod_one : (leftMulProd7 bImag) 1 = 1 := by
  have h7 : basisCD (Fin.succ 6) * (1 : SplitOctCD) = sCD 2 := by
    rw [show (Fin.succ 6 : Fin 8) = 7 from rfl, basisCD_seven, mul_one]
  have h6 : basisCD (Fin.succ 5) * sCD 2 = iCD 0 := by
    rw [show (Fin.succ 5 : Fin 8) = 6 from rfl, basisCD_six]
    ext <;> simp [sCD_formula, iCD, qBasis]
  have h5 : basisCD (Fin.succ 4) * iCD 0 = -ellCD := by
    rw [show (Fin.succ 4 : Fin 8) = 5 from rfl, basisCD_five]
    ext <;> simp [sCD_formula, iCD, ellCD, qBasis]
  have h4 : basisCD (Fin.succ 3) * (-ellCD) = (-1 : SplitOctCD) := by
    rw [show (Fin.succ 3 : Fin 8) = 4 from rfl, basisCD_four, mul_neg, ellCD_sq,
      show oneCD = (1 : SplitOctCD) from oneCD_def.symm]
  have h3 : basisCD (Fin.succ 2) * (-1 : SplitOctCD) = -iCD 2 := by
    rw [show (Fin.succ 2 : Fin 8) = 3 from rfl, basisCD_three, mul_neg, mul_one]
  have h2 : basisCD (Fin.succ 1) * (-iCD 2) = -iCD 0 := by
    rw [show (Fin.succ 1 : Fin 8) = 2 from rfl, basisCD_two, mul_neg, iCD_mul_12]
  have h1 : basisCD (Fin.succ 0) * (-iCD 0) = (1 : SplitOctCD) := by
    rw [show (Fin.succ 0 : Fin 8) = 1 from rfl, basisCD_one, mul_neg, iCD_sq, neg_neg,
      show oneCD = (1 : SplitOctCD) from oneCD_def.symm]
  change (leftMulEnd (bImag 0).1 * (leftMulEnd (bImag 1).1 * (leftMulEnd (bImag 2).1 *
    (leftMulEnd (bImag 3).1 * (leftMulEnd (bImag 4).1 * (leftMulEnd (bImag 5).1 *
    (leftMulEnd (bImag 6).1 * 1))))))) 1 = 1
  simp only [Module.End.mul_apply, Module.End.one_apply, leftMulEnd_apply_cd, bImag_apply]
  rw [h7, h6, h5, h4, h3, h2, h1]

private theorem leftMulEnd_aut_conj (φ : SplitOctCDAut) (x z : SplitOctCD) :
    leftMulEnd (φ.1 x) z = φ.1 (leftMulEnd x (φ.1.symm z)) := by
  change φ.1 x * z = φ.1 (x * φ.1.symm z)
  rw [φ.preserves_mul, φ.1.apply_symm_apply]

private theorem prodEndFin_aut_conj {n : ℕ} (φ : SplitOctCDAut) (v : Fin n → SplitOctCD)
    (z : SplitOctCD) :
    prodEndFin n (fun i => leftMulEnd (φ.1 (v i))) z =
      φ.1 (prodEndFin n (fun i => leftMulEnd (v i)) (φ.1.symm z)) := by
  induction n generalizing z with
  | zero => simp [prodEndFin]
  | succ n ih =>
      have hstep1 : prodEndFin (n + 1) (fun i => leftMulEnd (φ.1 (v i))) z =
          leftMulEnd (φ.1 (v 0)) (prodEndFin n (fun i => leftMulEnd (φ.1 (v i.succ))) z) := rfl
      have hstep2 : prodEndFin (n + 1) (fun i => leftMulEnd (v i)) (φ.1.symm z) =
          leftMulEnd (v 0) (prodEndFin n (fun i => leftMulEnd (v i.succ)) (φ.1.symm z)) := rfl
      rw [hstep1, ih (fun i => v i.succ) z, leftMulEnd_aut_conj, φ.1.symm_apply_apply, hstep2]

private def restrictImag (φ : SplitOctCDAut) : imagSubmodule →ₗ[ℝ] imagSubmodule where
  toFun x := ⟨φ.1 x.1, by
    rw [mem_imagSubmodule_iff]
    have htr := φ.preserves_cdTrace x.1
    unfold cdTrace at htr
    linarith [(mem_imagSubmodule_iff x.1).mp x.2]⟩
  map_add' x y := Subtype.ext (φ.1.map_add x.1 y.1)
  map_smul' r x := Subtype.ext (φ.1.map_smul r x.1)

private theorem leftMulProd7_aut_evalOneRe (φ : SplitOctCDAut) (v : Fin 7 → imagSubmodule) :
    evalOneRe (leftMulProd7 (restrictImag φ ∘ v)) = evalOneRe (leftMulProd7 v) := by
  rw [evalOneRe_leftMulProd7, evalOneRe_leftMulProd7]
  have hcoe : (fun i : Fin 7 => leftMulEnd (restrictImag φ (v i)).1) =
      fun i : Fin 7 => leftMulEnd (φ.1 (v i).1) := rfl
  dsimp only [Function.comp_def]
  rw [hcoe, prodEndFin_aut_conj]
  have hsymm1 : φ.1.symm 1 = 1 := by
    apply φ.1.injective
    rw [φ.1.apply_symm_apply, φ.preserves_one]
  rw [hsymm1]
  have htr := φ.preserves_cdTrace (prodEndFin 7 (fun i => leftMulEnd (v i).1) 1)
  unfold cdTrace at htr
  linarith

private theorem bImag_ortho (i j : Fin 7) (hij : i ≠ j) :
    cdKreinForm (bImag i).1 (bImag j).1 = 0 := by
  rw [bImag_apply, bImag_apply, cdKreinForm_basisCD,
    ite_eq_right (fun hs => hij (Fin.succ_inj.mp hs))]

private theorem evalOneRe_leftMulProd7_bImag : evalOneRe (leftMulProd7 bImag) = 1 := by
  rw [evalOneRe_leftMulProd7, ← leftMulProd7_apply, bImag_prod_one]
  rfl

private theorem oct7Form_bImag : oct7Form bImag = 5040 := by
  rw [oct7Form_ortho bImag bImag_ortho, evalOneRe_leftMulProd7_bImag, mul_one]

private theorem restrictImag_apply (φ : SplitOctCDAut) (x : imagSubmodule) :
    (restrictImag φ x).1 = φ.1 x.1 := rfl

private theorem alternating_matrix_det_one_rn
    (g : (Fin 7 → ℝ) [⋀^Fin 7]→ₗ[ℝ] ℝ) (A : Matrix (Fin 7) (Fin 7) ℝ)
    (hb : g (Pi.basisFun ℝ (Fin 7)) = 5040)
    (hfb : g (A.mulVecLin ∘ Pi.basisFun ℝ (Fin 7)) = 5040) :
    A.det = 1 := by
  have hrow : Matrix.detRowAlternating (⇑A.mulVecLin ∘ ⇑(Pi.basisFun ℝ (Fin 7))) = A.det := by
    change Matrix.det (⇑A.mulVecLin ∘ ⇑(Pi.basisFun ℝ (Fin 7))) = A.det
    rw [← Matrix.det_transpose]
    congr 1
    ext i j
    simp [Matrix.mulVec_single]
  have heq : g (A.mulVecLin ∘ Pi.basisFun ℝ (Fin 7)) =
      g (Pi.basisFun ℝ (Fin 7)) * A.det := by
    conv_lhs => rw [g.eq_smul_basis_det (Pi.basisFun ℝ (Fin 7))]
    simp [hrow]
  rw [hb, hfb] at heq
  linarith

private def bImagLin : (Fin 7 → ℝ) →ₗ[ℝ] imagSubmodule :=
  bImag.equivFun.symm.toLinearMap

private theorem bImagLin_single (k : Fin 7) :
    bImagLin (Pi.basisFun ℝ (Fin 7) k) = bImag k := by
  dsimp only [bImagLin, LinearEquiv.coe_toLinearMap]
  rw [Pi.basisFun_apply, Module.Basis.equivFun_symm_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi
    simp [hi]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private def oct7FormRn : (Fin 7 → ℝ) [⋀^Fin 7]→ₗ[ℝ] ℝ :=
  oct7Form.compLinearMap bImagLin

private theorem oct7FormRn_basis : oct7FormRn (Pi.basisFun ℝ (Fin 7)) = 5040 := by
  have hcomp : (fun i => bImagLin (Pi.basisFun ℝ (Fin 7) i)) = ⇑bImag := by
    funext k
    exact bImagLin_single k
  dsimp only [oct7FormRn]
  rw [AlternatingMap.compLinearMap_apply, hcomp]
  exact oct7Form_bImag

private theorem oct7Form_restrictImag_bImag (φ : SplitOctCDAut) :
    oct7Form (restrictImag φ ∘ bImag) = 5040 := by
  have hφb_ortho : ∀ i j : Fin 7, i ≠ j →
      cdKreinForm ((restrictImag φ) (bImag i)).1 ((restrictImag φ) (bImag j)).1 = 0 := by
    intro i j hij
    rw [restrictImag_apply, restrictImag_apply, φ.preserves_cdKreinForm]
    exact bImag_ortho i j hij
  rw [oct7Form_ortho (restrictImag φ ∘ bImag) hφb_ortho,
    leftMulProd7_aut_evalOneRe φ bImag, evalOneRe_leftMulProd7_bImag, mul_one]

private theorem oct7FormRn_mulVecLin (φ : SplitOctCDAut) :
    oct7FormRn ((LinearMap.toMatrix bImag bImag (restrictImag φ)).mulVecLin ∘
      Pi.basisFun ℝ (Fin 7)) = 5040 := by
  have hcomp :
      (fun j => bImagLin (((LinearMap.toMatrix bImag bImag (restrictImag φ)).mulVecLin ∘
        Pi.basisFun ℝ (Fin 7)) j)) = (⇑(restrictImag φ) ∘ ⇑bImag) := by
    funext j
    dsimp only [Function.comp_def, bImagLin, LinearEquiv.coe_toLinearMap]
    rw [Pi.basisFun_apply, Matrix.mulVecLin_apply, Module.Basis.equivFun_symm_apply]
    simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
      LinearMap.toMatrix_apply]
    exact bImag.sum_repr (restrictImag φ (bImag j))
  dsimp only [oct7FormRn]
  rw [AlternatingMap.compLinearMap_apply, hcomp]
  exact oct7Form_restrictImag_bImag φ

private theorem submatrix_bImag_det_one (φ : SplitOctCDAut) :
    (LinearMap.toMatrix bImag bImag (restrictImag φ)).det = 1 :=
  alternating_matrix_det_one_rn oct7FormRn (LinearMap.toMatrix bImag bImag (restrictImag φ))
    oct7FormRn_basis (oct7FormRn_mulVecLin φ)

theorem SplitOctCDAut.matrix_det_one (φ : SplitOctCDAut) :
    (LinearMap.toMatrix basisCD basisCD φ.1.toLinearMap).det = 1 := by
  let φImag := restrictImag φ
  let M := LinearMap.toMatrix basisCD basisCD φ.1.toLinearMap
  have hcol0 : ∀ i : Fin 8, M i 0 = if i = 0 then 1 else 0 := by
    intro i
    dsimp only [M]
    rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, basisCD_zero,
      show oneCD = (1 : SplitOctCD) from oneCD_def.symm, φ.preserves_one,
      show (1 : SplitOctCD) = basisCD 0 from by rw [basisCD_zero]; exact oneCD_def]
    rw [basisCD.repr_self]
    fin_cases i <;> simp
  have hsub : M.submatrix Fin.succ Fin.succ = LinearMap.toMatrix bImag bImag φImag := by
    ext i j
    simp only [M, Matrix.submatrix_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe]
    have hcoe : (φImag (bImag j)).1 =
        ∑ r : Fin 7, bImag.repr (φImag (bImag j)) r • (bImag r).1 := by
      change imagSubmodule.subtype (φImag (bImag j)) = _
      conv_lhs => rw [← bImag.sum_repr (φImag (bImag j))]
      rw [map_sum]
      simp only [map_smul]
      rfl
    have hcoe' : φ.1 (basisCD j.succ) =
        ∑ r : Fin 7, bImag.repr (φImag (bImag j)) r • basisCD r.succ := by
      simpa [bImag_apply, φImag, restrictImag] using hcoe
    rw [hcoe', map_sum]
    simp only [map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, basisCD.repr_self, Finsupp.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro r _ hri
      have hne : r.succ ≠ i.succ := fun hs => hri (Fin.succ_inj.mp hs)
      simp [hne]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hrest : ∑ i : Fin 7, (-1 : ℝ) ^ i.succ.val * M i.succ 0 *
      (M.submatrix i.succ.succAbove Fin.succ).det = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hcol0 i.succ]
    simp
  rw [hrest, add_zero]
  have h00 : M 0 0 = 1 := by rw [hcol0 0]; simp
  change (-1 : ℝ) ^ (0 : Fin 8).val * M 0 0 * (M.submatrix (0 : Fin 8).succAbove Fin.succ).det = 1
  rw [h00, Fin.val_zero, pow_zero, one_mul, one_mul, Fin.succAbove_zero, hsub]
  exact submatrix_bImag_det_one φ

/-- Embedding `G_{2(2)} = Aut(SplitOctCD) →* SO(4,4)`. -/
def splitOctCDAut_to_SO44 : SplitOctCDAut →* SO44Subgroup where
  toFun φ :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
        (LinearMap.toMatrix basisCD basisCD φ.1.toLinearMap)
        (by rw [φ.matrix_det_one]; norm_num),
      by
        refine ⟨?_, φ.matrix_det_one⟩
        ext i j
        change ((LinearMap.toMatrix basisCD basisCD φ.1.toLinearMap)ᵀ * J44 *
          LinearMap.toMatrix basisCD basisCD φ.1.toLinearMap) i j = J44 i j
        have hM : ∀ k r, (LinearMap.toMatrix basisCD basisCD φ.1.toLinearMap) r k =
            basisCD.repr (φ.1 (basisCD k)) r := fun _ _ =>
          LinearMap.toMatrix_apply basisCD basisCD φ.1.toLinearMap _ _
        have hform :
            (LinearMap.toMatrix basisCD basisCD φ.1.toLinearMap)ᵀ * J44 *
              (LinearMap.toMatrix basisCD basisCD φ.1.toLinearMap) =
              fun a b => cdKreinForm (φ.1 (basisCD a)) (φ.1 (basisCD b)) := by
          ext a b
          simp only [Matrix.mul_apply, Matrix.transpose_apply, J44, Matrix.diagonal_apply]
          rw [cdKreinForm_basisCD_expand (φ.1 (basisCD a)) (φ.1 (basisCD b))]
          simp_rw [hM]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_eq_single r]
          · simp [J44]; ring
          · intro s _ hsr
            simp [hsr]
          · intro hr
            exact absurd (Finset.mem_univ r) hr
        have hent := congrFun (congrFun hform i) j
        rw [hent, φ.preserves_cdKreinForm, cdKreinForm_basisCD]
        fin_cases i <;> fin_cases j <;> simp [J44]⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp
  map_mul' φ ψ := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp [LinearMap.toMatrix_mul]

theorem splitOctCDAut_to_SO44_injective : Function.Injective splitOctCDAut_to_SO44 := by
  intro φ ψ h
  have hm : LinearMap.toMatrix basisCD basisCD φ.1.toLinearMap =
      LinearMap.toMatrix basisCD basisCD ψ.1.toLinearMap := by
    simpa [splitOctCDAut_to_SO44] using
      congrArg (fun g : SO44Subgroup => (g.1 : Matrix (Fin 8) (Fin 8) ℝ)) h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hlin : φ.1.toLinearMap = ψ.1.toLinearMap :=
    (LinearMap.toMatrix basisCD basisCD).injective hm
  exact congrArg (fun f : SplitOctCD →ₗ[ℝ] SplitOctCD => f x) hlin

/-! ### Polymorphic 3D Cross-Product / Cofactor Identities (over `[CommRing R]`) -/

/-- Three-dimensional cross product over any ring `R`. -/
def cross3R {R : Type*} [Ring R] (u v : Fin 3 → R) : Fin 3 → R :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- Three-dimensional dot product over any ring `R`. -/
def dot3R {R : Type*} [Ring R] (u v : Fin 3 → R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Cofactor matrix `(A.adjugate)ᵀ` over any commutative ring `R`. -/
def cofactor3 {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R :=
  A.adjugateᵀ

theorem cross3R_mulVec {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) (u v : Fin 3 → R) :
    cross3R (A *ᵥ u) (A *ᵥ v) = cofactor3 A *ᵥ cross3R u v := by
  funext i
  fin_cases i <;>
    simp [cross3R, cofactor3, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.adjugate_fin_three] <;> ring

theorem cross3R_cofactor3_mulVec {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R)
    (u v : Fin 3 → R) :
    cross3R (cofactor3 A *ᵥ u) (cofactor3 A *ᵥ v) = A.det • (A *ᵥ cross3R u v) := by
  funext i
  fin_cases i <;>
    simp [cross3R, cofactor3, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.adjugate_fin_three, Matrix.det_fin_three] <;> ring

theorem dot3R_mulVec_cofactor3 {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R)
    (u v : Fin 3 → R) :
    dot3R (A *ᵥ u) (cofactor3 A *ᵥ v) = A.det * dot3R u v := by
  simp [dot3R, cofactor3, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.adjugate_fin_three, Matrix.det_fin_three]
  ring

theorem dot3R_cofactor3_mulVec {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R)
    (u v : Fin 3 → R) :
    dot3R (cofactor3 A *ᵥ u) (A *ᵥ v) = A.det * dot3R u v := by
  simp [dot3R, cofactor3, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.adjugate_fin_three, Matrix.det_fin_three]
  ring

theorem cofactor3_sl_eq_inv_transpose {R : Type*} [CommRing R]
    (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    cofactor3 (g : Matrix (Fin 3) (Fin 3) R) =
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)ᵀ := by
  have h1 : (g : Matrix (Fin 3) (Fin 3) R) * (g : Matrix (Fin 3) (Fin 3) R).adjugate = 1 := by
    rw [Matrix.mul_adjugate, g.2, one_smul]
  have h2 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) *
      (g : Matrix (Fin 3) (Fin 3) R) = 1 := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using
      congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) R => (x : Matrix (Fin 3) (Fin 3) R))
        (inv_mul_cancel g)
  have hadj : (g : Matrix (Fin 3) (Fin 3) R).adjugate =
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
    calc (g : Matrix (Fin 3) (Fin 3) R).adjugate
        = 1 * (g : Matrix (Fin 3) (Fin 3) R).adjugate := (Matrix.one_mul _).symm
      _ = (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) *
            (g : Matrix (Fin 3) (Fin 3) R)) * (g : Matrix (Fin 3) (Fin 3) R).adjugate := by rw [h2]
      _ = ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) *
            ((g : Matrix (Fin 3) (Fin 3) R) * (g : Matrix (Fin 3) (Fin 3) R).adjugate) :=
              Matrix.mul_assoc _ _ _
      _ = ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
            rw [h1, Matrix.mul_one]
  unfold cofactor3
  rw [hadj]

private theorem zornDot_eq_dot3R (u v : Fin 3 → ℝ) : ZornMatrix.dot u v = dot3R u v := by
  simp [ZornMatrix.dot, dot3R]

private theorem zornCross_eq_cross3R (u v : Fin 3 → ℝ) :
    ZornMatrix.cross u v = cross3R u v := by
  funext i
  fin_cases i <;> simp [ZornMatrix.cross, cross3R]

private def sl3DualMat (g : Matrix.SpecialLinearGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ

private theorem sl3DualMat_mul (g h : Matrix.SpecialLinearGroup (Fin 3) ℝ) :
    sl3DualMat (g * h) = sl3DualMat g * sl3DualMat h := by
  unfold sl3DualMat
  rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

private theorem sl3DualMat_one : sl3DualMat 1 = 1 := by
  simp [sl3DualMat]

private theorem sl3DualMat_inv (g : Matrix.SpecialLinearGroup (Fin 3) ℝ) :
    sl3DualMat g⁻¹ = (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
  simp [sl3DualMat]

private theorem chiralZornEquiv_reconstruct (α₁ α₂ : ℝ) (a b : Fin 3 → ℝ) :
    chiralZornEquiv (chiralZornReconstruct α₁ α₂ a b) = (α₁, α₂, a, b) :=
  chiralZornEquiv.right_inv (α₁, α₂, a, b)

private def sl3LinearEquiv (g : Matrix.SpecialLinearGroup (Fin 3) ℝ) :
    SplitOctCD ≃ₗ[ℝ] SplitOctCD where
  toFun x :=
    let p := chiralZornEquiv x
    chiralZornReconstruct p.1 p.2.1 (g.1 *ᵥ p.2.2.1) (sl3DualMat g *ᵥ p.2.2.2)
  invFun y :=
    let p := chiralZornEquiv y
    chiralZornReconstruct p.1 p.2.1 (g⁻¹.1 *ᵥ p.2.2.1) (sl3DualMat g⁻¹ *ᵥ p.2.2.2)
  left_inv x := by
    obtain ⟨⟨α₁, α₂, a, b⟩, rfl⟩ := chiralZornEquiv.symm.surjective x
    simp only [chiralZornEquiv_symm_apply, chiralZornEquiv_reconstruct]
    have hg1 : g⁻¹.1 *ᵥ (g.1 *ᵥ a) = a := by
      rw [Matrix.mulVec_mulVec]
      have h : g⁻¹.1 * g.1 = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [h, Matrix.one_mulVec]
    have hg2 : sl3DualMat g⁻¹ *ᵥ (sl3DualMat g *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec, ← sl3DualMat_mul, inv_mul_cancel, sl3DualMat_one, Matrix.one_mulVec]
    rw [hg1, hg2]
  right_inv y := by
    obtain ⟨⟨α₁, α₂, a, b⟩, rfl⟩ := chiralZornEquiv.symm.surjective y
    simp only [chiralZornEquiv_symm_apply, chiralZornEquiv_reconstruct]
    have hg1 : g.1 *ᵥ (g⁻¹.1 *ᵥ a) = a := by
      rw [Matrix.mulVec_mulVec]
      have h : g.1 * g⁻¹.1 = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [h, Matrix.one_mulVec]
    have hg2 : sl3DualMat g *ᵥ (sl3DualMat g⁻¹ *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec, ← sl3DualMat_mul, mul_inv_cancel, sl3DualMat_one, Matrix.one_mulVec]
    rw [hg1, hg2]
  map_add' x y := by
    apply chiralZornEquiv.injective
    simp only [map_add, chiralZornEquiv_reconstruct, Prod.fst_add, Prod.snd_add, Matrix.mulVec_add]
    rfl
  map_smul' r x := by
    apply chiralZornEquiv.injective
    simp only [map_smul, chiralZornEquiv_reconstruct, RingHom.id_apply, Prod.smul_fst,
      Prod.smul_snd, Matrix.mulVec_smul]
    rfl

private theorem sl3LinearEquiv_apply (g : Matrix.SpecialLinearGroup (Fin 3) ℝ) (x : SplitOctCD) :
    sl3LinearEquiv g x = chiralZornReconstruct (chiralZornEquiv x).1 (chiralZornEquiv x).2.1
      (g.1 *ᵥ (chiralZornEquiv x).2.2.1) (sl3DualMat g *ᵥ (chiralZornEquiv x).2.2.2) := rfl

private theorem sl3LinearEquiv_reconstruct (g : Matrix.SpecialLinearGroup (Fin 3) ℝ)
    (α₁ α₂ : ℝ) (a b : Fin 3 → ℝ) :
    sl3LinearEquiv g (chiralZornReconstruct α₁ α₂ a b) =
      chiralZornReconstruct α₁ α₂ (g.1 *ᵥ a) (sl3DualMat g *ᵥ b) := by
  rw [sl3LinearEquiv_apply, chiralZornEquiv_reconstruct]

private theorem sl3LinearEquiv_mul (g : Matrix.SpecialLinearGroup (Fin 3) ℝ) (x y : SplitOctCD) :
    sl3LinearEquiv g (x * y) = sl3LinearEquiv g x * sl3LinearEquiv g y := by
  obtain ⟨⟨α₁, β₁, a₁, b₁⟩, rfl⟩ := chiralZornEquiv.symm.surjective x
  obtain ⟨⟨α₂, β₂, a₂, b₂⟩, rfl⟩ := chiralZornEquiv.symm.surjective y
  simp only [chiralZornEquiv_symm_apply]
  rw [chiralZornReconstruct_mul, sl3LinearEquiv_reconstruct, sl3LinearEquiv_reconstruct,
    sl3LinearEquiv_reconstruct, chiralZornReconstruct_mul]
  have hdot1 : ZornMatrix.dot (g.1 *ᵥ a₁) (sl3DualMat g *ᵥ b₂) = ZornMatrix.dot a₁ b₂ := by
    rw [zornDot_eq_dot3R, zornDot_eq_dot3R, show sl3DualMat g = cofactor3 g.1 from
      (cofactor3_sl_eq_inv_transpose g).symm, dot3R_mulVec_cofactor3, g.2, one_mul]
  have hdot2 : ZornMatrix.dot (sl3DualMat g *ᵥ b₁) (g.1 *ᵥ a₂) = ZornMatrix.dot b₁ a₂ := by
    rw [zornDot_eq_dot3R, zornDot_eq_dot3R, show sl3DualMat g = cofactor3 g.1 from
      (cofactor3_sl_eq_inv_transpose g).symm, dot3R_cofactor3_mulVec, g.2, one_mul]
  have hcross1 : ZornMatrix.cross (sl3DualMat g *ᵥ b₁) (sl3DualMat g *ᵥ b₂) =
      g.1 *ᵥ ZornMatrix.cross b₁ b₂ := by
    rw [zornCross_eq_cross3R, zornCross_eq_cross3R, show sl3DualMat g = cofactor3 g.1 from
      (cofactor3_sl_eq_inv_transpose g).symm, cross3R_cofactor3_mulVec, g.2, one_smul]
  have hcross2 : ZornMatrix.cross (g.1 *ᵥ a₁) (g.1 *ᵥ a₂) =
      sl3DualMat g *ᵥ ZornMatrix.cross a₁ a₂ := by
    rw [zornCross_eq_cross3R, zornCross_eq_cross3R, show sl3DualMat g = cofactor3 g.1 from
      (cofactor3_sl_eq_inv_transpose g).symm, cross3R_mulVec]
  rw [hdot1, hdot2, hcross1, hcross2]
  congr 1
  · funext i; simp [Matrix.mulVec_add, Matrix.mulVec_smul]
  · funext i; simp [Matrix.mulVec_add, Matrix.mulVec_smul]

/-- Group homomorphism `SL₃(ℝ) →* SplitOctCDAut` (`G_{2(2)}` stabilizer of `ℓ`). -/
def sl3ToSplitOctCDAut : Matrix.SpecialLinearGroup (Fin 3) ℝ →* SplitOctCDAut where
  toFun g :=
    ⟨sl3LinearEquiv g, by
      refine ⟨?_, sl3LinearEquiv_mul g⟩
      have h1 : (1 : SplitOctCD) = chiralZornReconstruct 1 1 0 0 := by
        unfold chiralZornReconstruct
        simp [uPlusCD_add_uMinusCD]
      rw [h1, sl3LinearEquiv_reconstruct]
      simp⟩
  map_one' := by
    apply Subtype.ext; apply LinearEquiv.ext; intro x
    change chiralZornReconstruct (chiralZornEquiv x).1 (chiralZornEquiv x).2.1
      ((1 : Matrix.SpecialLinearGroup (Fin 3) ℝ).1 *ᵥ (chiralZornEquiv x).2.2.1)
      (sl3DualMat 1 *ᵥ (chiralZornEquiv x).2.2.2) = x
    rw [Matrix.SpecialLinearGroup.coe_one, sl3DualMat_one, Matrix.one_mulVec, Matrix.one_mulVec]
    exact chiralZornEquiv.left_inv x
  map_mul' g h := by
    apply Subtype.ext; apply LinearEquiv.ext; intro x
    change sl3LinearEquiv (g * h) x = sl3LinearEquiv g (sl3LinearEquiv h x)
    rw [sl3LinearEquiv_apply, sl3LinearEquiv_apply, sl3LinearEquiv_apply,
      chiralZornEquiv_reconstruct, Matrix.SpecialLinearGroup.coe_mul, sl3DualMat_mul,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem sl3ToSplitOctCDAut_uPlus (g : Matrix.SpecialLinearGroup (Fin 3) ℝ) :
    (sl3ToSplitOctCDAut g).1 uPlusCD = uPlusCD := by
  have h : uPlusCD = chiralZornReconstruct 1 0 0 0 := by
    unfold chiralZornReconstruct; simp
  rw [h, show (sl3ToSplitOctCDAut g).1 _ = sl3LinearEquiv g _ from rfl,
    sl3LinearEquiv_reconstruct]
  simp

theorem sl3ToSplitOctCDAut_uMinus (g : Matrix.SpecialLinearGroup (Fin 3) ℝ) :
    (sl3ToSplitOctCDAut g).1 uMinusCD = uMinusCD := by
  have h : uMinusCD = chiralZornReconstruct 0 1 0 0 := by
    unfold chiralZornReconstruct; simp
  rw [h, show (sl3ToSplitOctCDAut g).1 _ = sl3LinearEquiv g _ from rfl,
    sl3LinearEquiv_reconstruct]
  simp

theorem sl3ToSplitOctCDAut_ell (g : Matrix.SpecialLinearGroup (Fin 3) ℝ) :
    (sl3ToSplitOctCDAut g).1 ellCD = ellCD := by
  rw [← uPlusCD_sub_uMinusCD, map_sub, sl3ToSplitOctCDAut_uPlus, sl3ToSplitOctCDAut_uMinus]

theorem sl3ToSplitOctCDAut_ePlus (g : Matrix.SpecialLinearGroup (Fin 3) ℝ) (j : Fin 3) :
    (sl3ToSplitOctCDAut g).1 (ePlusCD j) = ∑ i : Fin 3, (g.1 i j) • ePlusCD i := by
  have h : ePlusCD j = chiralZornReconstruct 0 0 (Pi.single j 1) 0 := by
    unfold chiralZornReconstruct
    simp [Finset.sum_eq_single j]
  rw [h, show (sl3ToSplitOctCDAut g).1 _ = sl3LinearEquiv g _ from rfl, sl3LinearEquiv_reconstruct]
  unfold chiralZornReconstruct
  simp only [zero_smul, zero_add, add_zero, Matrix.mulVec_zero, Pi.zero_apply,
    Finset.sum_const_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_single, Pi.smul_apply]
  simp

theorem sl3ToSplitOctCDAut_eMinus (g : Matrix.SpecialLinearGroup (Fin 3) ℝ) (j : Fin 3) :
    (sl3ToSplitOctCDAut g).1 (eMinusCD j) = ∑ i : Fin 3, (sl3DualMat g i j) • eMinusCD i := by
  have h : eMinusCD j = chiralZornReconstruct 0 0 0 (Pi.single j 1) := by
    unfold chiralZornReconstruct
    simp [Finset.sum_eq_single j]
  rw [h, show (sl3ToSplitOctCDAut g).1 _ = sl3LinearEquiv g _ from rfl, sl3LinearEquiv_reconstruct]
  unfold chiralZornReconstruct
  simp only [zero_smul, zero_add, add_zero, Matrix.mulVec_zero, Pi.zero_apply,
    Finset.sum_const_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_single, Pi.smul_apply]
  simp

/-- `1` singlet submodule `ℝ u₊`. -/
def singletPlusSubmodule : Submodule ℝ SplitOctCD := Submodule.span ℝ {uPlusCD}

/-- `1` singlet submodule `ℝ u₋`. -/
def singletMinusSubmodule : Submodule ℝ SplitOctCD := Submodule.span ℝ {uMinusCD}

/-- `3` fundamental triplet submodule `span {e₀⁺, e₁⁺, e₂⁺}`. -/
def tripletPlusSubmodule : Submodule ℝ SplitOctCD := Submodule.span ℝ (Set.range ePlusCD)

/-- `3̄` dual triplet submodule `span {e₀⁻, e₁⁻, e₂⁻}`. -/
def tripletMinusSubmodule : Submodule ℝ SplitOctCD := Submodule.span ℝ (Set.range eMinusCD)

/-- Indexed `1 ⊕ 1 ⊕ 3 ⊕ 3̄` family of chiral submodules of `SplitOctCD`. -/
def chiralSubmodules : Fin 4 → Submodule ℝ SplitOctCD
  | 0 => singletPlusSubmodule
  | 1 => singletMinusSubmodule
  | 2 => tripletPlusSubmodule
  | 3 => tripletMinusSubmodule

private def chiralCoordZero (i : Fin 4) : Submodule ℝ SplitOctCD where
  carrier := {y | match i with
    | 0 => (chiralZornEquiv y).1 = 0
    | 1 => (chiralZornEquiv y).2.1 = 0
    | 2 => (chiralZornEquiv y).2.2.1 = 0
    | 3 => (chiralZornEquiv y).2.2.2 = 0}
  zero_mem' := by fin_cases i <;> simp
  add_mem' {u v} hu hv := by
    fin_cases i
    · change (chiralZornEquiv u).1 = 0 at hu; change (chiralZornEquiv v).1 = 0 at hv
      change (chiralZornEquiv (u + v)).1 = 0
      rw [map_add, Prod.fst_add, hu, hv, add_zero]
    · change (chiralZornEquiv u).2.1 = 0 at hu; change (chiralZornEquiv v).2.1 = 0 at hv
      change (chiralZornEquiv (u + v)).2.1 = 0
      rw [map_add, Prod.snd_add, Prod.fst_add, hu, hv, add_zero]
    · change (chiralZornEquiv u).2.2.1 = 0 at hu; change (chiralZornEquiv v).2.2.1 = 0 at hv
      change (chiralZornEquiv (u + v)).2.2.1 = 0
      rw [map_add, Prod.snd_add, Prod.snd_add, Prod.fst_add, hu, hv, add_zero]
    · change (chiralZornEquiv u).2.2.2 = 0 at hu; change (chiralZornEquiv v).2.2.2 = 0 at hv
      change (chiralZornEquiv (u + v)).2.2.2 = 0
      rw [map_add, Prod.snd_add, Prod.snd_add, Prod.snd_add, hu, hv, add_zero]
  smul_mem' r {u} hu := by
    fin_cases i
    · change (chiralZornEquiv u).1 = 0 at hu
      change (chiralZornEquiv (r • u)).1 = 0
      rw [map_smul, Prod.smul_fst, hu, smul_zero]
    · change (chiralZornEquiv u).2.1 = 0 at hu
      change (chiralZornEquiv (r • u)).2.1 = 0
      rw [map_smul, Prod.smul_snd, Prod.smul_fst, hu, smul_zero]
    · change (chiralZornEquiv u).2.2.1 = 0 at hu
      change (chiralZornEquiv (r • u)).2.2.1 = 0
      rw [map_smul, Prod.smul_snd, Prod.smul_snd, Prod.smul_fst, hu, smul_zero]
    · change (chiralZornEquiv u).2.2.2 = 0 at hu
      change (chiralZornEquiv (r • u)).2.2.2 = 0
      rw [map_smul, Prod.smul_snd, Prod.smul_snd, Prod.smul_snd, hu, smul_zero]

theorem chiralSubmodules_isInternal : DirectSum.IsInternal chiralSubmodules := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · intro i
    rw [Submodule.disjoint_def]
    intro x hx hsum
    have hmem : ∀ j : Fin 4, ∀ y ∈ chiralSubmodules j,
        match j with
        | 0 => (chiralZornEquiv y).2.1 = 0 ∧ (chiralZornEquiv y).2.2.1 = 0 ∧
            (chiralZornEquiv y).2.2.2 = 0
        | 1 => (chiralZornEquiv y).1 = 0 ∧ (chiralZornEquiv y).2.2.1 = 0 ∧
            (chiralZornEquiv y).2.2.2 = 0
        | 2 => (chiralZornEquiv y).1 = 0 ∧ (chiralZornEquiv y).2.1 = 0 ∧
            (chiralZornEquiv y).2.2.2 = 0
        | 3 => (chiralZornEquiv y).1 = 0 ∧ (chiralZornEquiv y).2.1 = 0 ∧
            (chiralZornEquiv y).2.2.1 = 0 := by
      intro j y hy
      fin_cases j
      · rw [chiralSubmodules.eq_def] at hy; dsimp only at hy
        rw [singletPlusSubmodule, Submodule.mem_span_singleton] at hy
        rcases hy with ⟨c, rfl⟩
        simp [uPlusCD_components]
      · rw [chiralSubmodules.eq_def] at hy; dsimp only at hy
        rw [singletMinusSubmodule, Submodule.mem_span_singleton] at hy
        rcases hy with ⟨c, rfl⟩
        simp [uMinusCD_components]
      · rw [chiralSubmodules.eq_def] at hy; dsimp only at hy
        rw [tripletPlusSubmodule, Submodule.mem_span_range_iff_exists_fun] at hy
        rcases hy with ⟨c, rfl⟩
        simp [ePlusCD_components, qBasis, Fin.sum_univ_three]
      · rw [chiralSubmodules.eq_def] at hy; dsimp only at hy
        rw [tripletMinusSubmodule, Submodule.mem_span_range_iff_exists_fun] at hy
        rcases hy with ⟨c, rfl⟩
        simp [eMinusCD_components, qBasis, Fin.sum_univ_three]
    have hle : (⨆ (j) (_ : j ≠ i), chiralSubmodules j) ≤ chiralCoordZero i := by
      refine iSup₂_le fun j hj y hy => ?_
      have hy' := hmem j y hy
      fin_cases i <;> fin_cases j <;> simp_all [chiralCoordZero]
    have hx1 := hmem i x hx
    have hx2 := hle hsum
    apply chiralZornEquiv.injective
    rw [map_zero]
    fin_cases i
    · rcases hx1 with ⟨hA, hB, hC⟩
      change (chiralZornEquiv x).1 = 0 at hx2
      exact Prod.ext hx2 (Prod.ext hA (Prod.ext hB hC))
    · rcases hx1 with ⟨hA, hB, hC⟩
      change (chiralZornEquiv x).2.1 = 0 at hx2
      exact Prod.ext hA (Prod.ext hx2 (Prod.ext hB hC))
    · rcases hx1 with ⟨hA, hB, hC⟩
      change (chiralZornEquiv x).2.2.1 = 0 at hx2
      exact Prod.ext hA (Prod.ext hB (Prod.ext hx2 hC))
    · rcases hx1 with ⟨hA, hB, hC⟩
      change (chiralZornEquiv x).2.2.2 = 0 at hx2
      exact Prod.ext hA (Prod.ext hB (Prod.ext hC hx2))
  · rw [eq_top_iff]
    intro x _
    have hx : x = chiralZornReconstruct (chiralZornEquiv x).1 (chiralZornEquiv x).2.1
        (chiralZornEquiv x).2.2.1 (chiralZornEquiv x).2.2.2 :=
      (chiralZornEquiv.left_inv x).symm
    rw [hx]
    unfold chiralZornReconstruct
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
    · exact Submodule.mem_iSup_of_mem 0 (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    · exact Submodule.mem_iSup_of_mem 1 (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    · refine Submodule.mem_iSup_of_mem 2 (Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
    · refine Submodule.mem_iSup_of_mem 3 (Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem singletPlusSubmodule_finrank : Module.finrank ℝ singletPlusSubmodule = 1 := by
  have hne : uPlusCD ≠ 0 := by
    intro h
    have := congrArg (fun x : SplitOctCD => x.fst.re) h
    norm_num [uPlusCD_components] at this
  exact finrank_span_singleton hne

theorem singletMinusSubmodule_finrank : Module.finrank ℝ singletMinusSubmodule = 1 := by
  have hne : uMinusCD ≠ 0 := by
    intro h
    have := congrArg (fun x : SplitOctCD => x.fst.re) h
    norm_num [uMinusCD_components] at this
  exact finrank_span_singleton hne

theorem ePlusCD_linearIndependent : LinearIndependent ℝ ePlusCD := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have h0 := congrArg (fun x : SplitOctCD => (chiralZornEquiv x).2.2.1 k) hc
  rw [map_zero] at h0
  have hsum : (chiralZornEquiv (∑ i : Fin 3, c i • ePlusCD i)).2.2.1 k = c k := by
    simp [Fin.sum_univ_three, ePlusCD_components, qBasis]
    fin_cases k <;> simp <;> ring
  rw [hsum] at h0
  exact h0

theorem eMinusCD_linearIndependent : LinearIndependent ℝ eMinusCD := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have h0 := congrArg (fun x : SplitOctCD => (chiralZornEquiv x).2.2.2 k) hc
  rw [map_zero] at h0
  have hsum : (chiralZornEquiv (∑ i : Fin 3, c i • eMinusCD i)).2.2.2 k = c k := by
    simp [Fin.sum_univ_three, eMinusCD_components, qBasis]
    fin_cases k <;> simp <;> ring
  rw [hsum] at h0
  exact h0

theorem tripletPlusSubmodule_finrank : Module.finrank ℝ tripletPlusSubmodule = 3 := by
  rw [tripletPlusSubmodule, finrank_span_eq_card ePlusCD_linearIndependent, Fintype.card_fin]

theorem tripletMinusSubmodule_finrank : Module.finrank ℝ tripletMinusSubmodule = 3 := by
  rw [tripletMinusSubmodule, finrank_span_eq_card eMinusCD_linearIndependent, Fintype.card_fin]

/-- Complete `1 ⊕ 1 ⊕ 3 ⊕ 3̄` representation splitting under `SL₃(ℝ)`. -/
theorem sl3ToSplitOctCDAut_splitting_1133bar :
    DirectSum.IsInternal chiralSubmodules ∧
    Module.finrank ℝ singletPlusSubmodule = 1 ∧
    Module.finrank ℝ singletMinusSubmodule = 1 ∧
    Module.finrank ℝ tripletPlusSubmodule = 3 ∧
    Module.finrank ℝ tripletMinusSubmodule = 3 ∧
    (∀ g : Matrix.SpecialLinearGroup (Fin 3) ℝ,
      (∀ x ∈ singletPlusSubmodule, (sl3ToSplitOctCDAut g).1 x = x) ∧
      (∀ x ∈ singletMinusSubmodule, (sl3ToSplitOctCDAut g).1 x = x) ∧
      (∀ x ∈ tripletPlusSubmodule, (sl3ToSplitOctCDAut g).1 x ∈ tripletPlusSubmodule) ∧
      (∀ x ∈ tripletMinusSubmodule, (sl3ToSplitOctCDAut g).1 x ∈ tripletMinusSubmodule)) := by
  refine ⟨chiralSubmodules_isInternal, singletPlusSubmodule_finrank,
    singletMinusSubmodule_finrank, tripletPlusSubmodule_finrank, tripletMinusSubmodule_finrank,
    fun g => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro x hx
    rw [singletPlusSubmodule, Submodule.mem_span_singleton] at hx
    rcases hx with ⟨c, rfl⟩
    rw [map_smul, sl3ToSplitOctCDAut_uPlus]
  · intro x hx
    rw [singletMinusSubmodule, Submodule.mem_span_singleton] at hx
    rcases hx with ⟨c, rfl⟩
    rw [map_smul, sl3ToSplitOctCDAut_uMinus]
  · intro x hx
    rw [tripletPlusSubmodule, Submodule.mem_span_range_iff_exists_fun] at hx
    rcases hx with ⟨c, rfl⟩
    rw [map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, sl3ToSplitOctCDAut_ePlus]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · intro x hx
    rw [tripletMinusSubmodule, Submodule.mem_span_range_iff_exists_fun] at hx
    rcases hx with ⟨c, rfl⟩
    rw [map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, sl3ToSplitOctCDAut_eMinus]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-- Subgroup `Stab_{Aut(SplitOctCD)}(ℓ)` fixing `ellCD`. -/
def ellStabilizerSubgroup : Subgroup SplitOctCDAut where
  carrier := {φ | φ.1 ellCD = ellCD}
  one_mem' := rfl
  mul_mem' {φ ψ} hφ hψ := by
    change φ.1 (ψ.1 ellCD) = ellCD
    rw [hψ, hφ]
  inv_mem' {φ} hφ := by
    change φ.1.symm ellCD = ellCD
    apply φ.1.injective
    rw [φ.1.apply_symm_apply, hφ]

private theorem peirce_proj_ePlus (α₁ α₂ : ℝ) (a b : Fin 3 → ℝ) :
    (uPlusCD * chiralZornReconstruct α₁ α₂ a b) * uMinusCD =
      ∑ i : Fin 3, a i • ePlusCD i := by
  have huP : uPlusCD = chiralZornReconstruct 1 0 0 0 := by unfold chiralZornReconstruct; simp
  have huM : uMinusCD = chiralZornReconstruct 0 1 0 0 := by unfold chiralZornReconstruct; simp
  rw [huP, huM, chiralZornReconstruct_mul, chiralZornReconstruct_mul]
  unfold chiralZornReconstruct
  simp [ZornMatrix.dot, ZornMatrix.cross, Fin.sum_univ_three]

private theorem peirce_proj_eMinus (α₁ α₂ : ℝ) (a b : Fin 3 → ℝ) :
    (uMinusCD * chiralZornReconstruct α₁ α₂ a b) * uPlusCD =
      ∑ i : Fin 3, b i • eMinusCD i := by
  have huP : uPlusCD = chiralZornReconstruct 1 0 0 0 := by unfold chiralZornReconstruct; simp
  have huM : uMinusCD = chiralZornReconstruct 0 1 0 0 := by unfold chiralZornReconstruct; simp
  rw [huP, huM, chiralZornReconstruct_mul, chiralZornReconstruct_mul]
  unfold chiralZornReconstruct
  simp [ZornMatrix.dot, ZornMatrix.cross, Fin.sum_univ_three]

private theorem ellStabilizer_fixes_uPlus {φ : SplitOctCDAut} (hφ : φ.1 ellCD = ellCD) :
    φ.1 uPlusCD = uPlusCD := by
  have h1 : φ.1 oneCD = oneCD := by
    rw [show oneCD = (1 : SplitOctCD) from oneCD_def.symm]
    exact φ.preserves_one
  rw [uPlusCD, map_smul, map_add, h1, hφ]

private theorem ellStabilizer_fixes_uMinus {φ : SplitOctCDAut} (hφ : φ.1 ellCD = ellCD) :
    φ.1 uMinusCD = uMinusCD := by
  have h1 : φ.1 oneCD = oneCD := by
    rw [show oneCD = (1 : SplitOctCD) from oneCD_def.symm]
    exact φ.preserves_one
  rw [uMinusCD, map_smul, map_sub, h1, hφ]

private theorem ellStabilizer_reconstruct {φ : SplitOctCDAut} (hφ : φ.1 ellCD = ellCD) :
    ∃ (M N : Matrix (Fin 3) (Fin 3) ℝ),
      (∀ α₁ α₂ a b, φ.1 (chiralZornReconstruct α₁ α₂ a b) =
        chiralZornReconstruct α₁ α₂ (M *ᵥ a) (N *ᵥ b)) ∧
      Mᵀ * N = 1 ∧ M.det = 1 := by
  have huP := ellStabilizer_fixes_uPlus hφ
  have huM := ellStabilizer_fixes_uMinus hφ
  have heP_mem : ∀ j : Fin 3, φ.1 (ePlusCD j) ∈ tripletPlusSubmodule := by
    intro j
    have heq : (uPlusCD * ePlusCD j) * uMinusCD = ePlusCD j := by
      have h := peirce_proj_ePlus 0 0 (Pi.single j 1) 0
      simpa [chiralZornReconstruct, Finset.sum_eq_single j] using h
    have hmap : (uPlusCD * φ.1 (ePlusCD j)) * uMinusCD = φ.1 (ePlusCD j) := by
      calc (uPlusCD * φ.1 (ePlusCD j)) * uMinusCD
          = (φ.1 uPlusCD * φ.1 (ePlusCD j)) * φ.1 uMinusCD := by rw [huP, huM]
        _ = φ.1 ((uPlusCD * ePlusCD j) * uMinusCD) := by
              rw [← φ.preserves_mul, ← φ.preserves_mul]
        _ = φ.1 (ePlusCD j) := by rw [heq]
    obtain ⟨⟨α₁, α₂, a, b⟩, hrec⟩ := chiralZornEquiv.symm.surjective (φ.1 (ePlusCD j))
    simp only [chiralZornEquiv_symm_apply] at hrec
    rw [← hrec, peirce_proj_ePlus] at hmap
    rw [← hrec, ← hmap]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have heM_mem : ∀ j : Fin 3, φ.1 (eMinusCD j) ∈ tripletMinusSubmodule := by
    intro j
    have heq : (uMinusCD * eMinusCD j) * uPlusCD = eMinusCD j := by
      have h := peirce_proj_eMinus 0 0 0 (Pi.single j 1)
      simpa [chiralZornReconstruct, Finset.sum_eq_single j] using h
    have hmap : (uMinusCD * φ.1 (eMinusCD j)) * uPlusCD = φ.1 (eMinusCD j) := by
      calc (uMinusCD * φ.1 (eMinusCD j)) * uPlusCD
          = (φ.1 uMinusCD * φ.1 (eMinusCD j)) * φ.1 uPlusCD := by rw [huP, huM]
        _ = φ.1 ((uMinusCD * eMinusCD j) * uPlusCD) := by
              rw [← φ.preserves_mul, ← φ.preserves_mul]
        _ = φ.1 (eMinusCD j) := by rw [heq]
    obtain ⟨⟨α₁, α₂, a, b⟩, hrec⟩ := chiralZornEquiv.symm.surjective (φ.1 (eMinusCD j))
    simp only [chiralZornEquiv_symm_apply] at hrec
    rw [← hrec, peirce_proj_eMinus] at hmap
    rw [← hrec, ← hmap]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let M : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (chiralZornEquiv (φ.1 (ePlusCD j))).2.2.1 i
  let N : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (chiralZornEquiv (φ.1 (eMinusCD j))).2.2.2 i
  have hφ_eP : ∀ j : Fin 3, φ.1 (ePlusCD j) = ∑ i : Fin 3, M i j • ePlusCD i := by
    intro j
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (heP_mem j)
    have hc' : ∀ i : Fin 3, M i j = c i := by
      intro i
      change (chiralZornEquiv (φ.1 (ePlusCD j))).2.2.1 i = c i
      rw [← hc]
      simp [Fin.sum_univ_three, ePlusCD_components, qBasis]
      fin_cases i <;> simp <;> ring
    simp_rw [hc']
    exact hc.symm
  have hφ_eM : ∀ j : Fin 3, φ.1 (eMinusCD j) = ∑ i : Fin 3, N i j • eMinusCD i := by
    intro j
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (heM_mem j)
    have hc' : ∀ i : Fin 3, N i j = c i := by
      intro i
      change (chiralZornEquiv (φ.1 (eMinusCD j))).2.2.2 i = c i
      rw [← hc]
      simp [Fin.sum_univ_three, eMinusCD_components, qBasis]
      fin_cases i <;> simp <;> ring
    simp_rw [hc']
    exact hc.symm
  have hrec : ∀ α₁ α₂ a b, φ.1 (chiralZornReconstruct α₁ α₂ a b) =
      chiralZornReconstruct α₁ α₂ (M *ᵥ a) (N *ᵥ b) := by
    intro α₁ α₂ a b
    unfold chiralZornReconstruct
    simp only [map_add, map_smul, map_sum, huP, huM, hφ_eP, hφ_eM]
    congr 1
    · congr 1
      simp only [Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => mul_comm _ _
    · simp only [Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hMN : Mᵀ * N = 1 := by
    ext j k
    have hcar : φ.1 (ePlusCD j * eMinusCD k) =
        -(if j = k then (1 : ℝ) else 0) • uPlusCD := by
      rw [ePlusCD_mul_eMinusCD, map_smul, huP]
    have hcar' : φ.1 (ePlusCD j) * φ.1 (eMinusCD k) =
        chiralZornReconstruct (-dot3R (fun i => M i j) (fun i => N i k)) 0 0 0 := by
      rw [hφ_eP j, hφ_eM k]
      have ha : (∑ i : Fin 3, M i j • ePlusCD i) =
          chiralZornReconstruct 0 0 (fun i => M i j) 0 := by
        unfold chiralZornReconstruct; simp
      have hb : (∑ i : Fin 3, N i k • eMinusCD i) =
          chiralZornReconstruct 0 0 0 (fun i => N i k) := by
        unfold chiralZornReconstruct; simp
      rw [ha, hb, chiralZornReconstruct_mul, zornDot_eq_dot3R]
      congr 1
      · simp
      · simp [ZornMatrix.dot]
      · funext i; fin_cases i <;> simp [ZornMatrix.cross]
      · funext i; fin_cases i <;> simp [ZornMatrix.cross]
    rw [φ.preserves_mul, hcar'] at hcar
    have hcoord := congrArg (fun x : SplitOctCD => (chiralZornEquiv x).1) hcar
    rw [chiralZornEquiv_reconstruct] at hcoord
    have h2 : (chiralZornEquiv (-(if j = k then (1 : ℝ) else 0) • uPlusCD)).1 =
        -(if j = k then (1 : ℝ) else 0) := by
      (by_cases hjk : j = k <;> simp [hjk, uPlusCD_components]); ring
    rw [h2] at hcoord
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    have hdot : (∑ i : Fin 3, M i j * N i k) = dot3R (fun i => M i j) (fun i => N i k) := by
      simp [dot3R, Fin.sum_univ_three]
    rw [hdot]
    linarith
  have hdet : M.det = 1 := by
    have hsing : φ.1 ((ePlusCD 0 * ePlusCD 1) * ePlusCD 2) = -uMinusCD := by
      rw [ePlusCD_triple_singlet, map_neg, huM]
    have ha0 : φ.1 (ePlusCD 0) = chiralZornReconstruct 0 0 (fun i => M i 0) 0 := by
      rw [hφ_eP 0]; unfold chiralZornReconstruct; simp
    have ha1 : φ.1 (ePlusCD 1) = chiralZornReconstruct 0 0 (fun i => M i 1) 0 := by
      rw [hφ_eP 1]; unfold chiralZornReconstruct; simp
    have ha2 : φ.1 (ePlusCD 2) = chiralZornReconstruct 0 0 (fun i => M i 2) 0 := by
      rw [hφ_eP 2]; unfold chiralZornReconstruct; simp
    rw [φ.preserves_mul, φ.preserves_mul, ha0, ha1, ha2,
      chiralZornReconstruct_mul, chiralZornReconstruct_mul] at hsing
    have hcoord := congrArg (fun x : SplitOctCD => (chiralZornEquiv x).2.1) hsing
    rw [chiralZornEquiv_reconstruct] at hcoord
    have h2 : (chiralZornEquiv (-uMinusCD)).2.1 = -1 := by
      rw [map_neg, Prod.snd_neg, Prod.fst_neg]
      simp [uMinusCD_components]
      ring
    rw [h2] at hcoord
    rw [Matrix.det_fin_three]
    simp [ZornMatrix.dot, ZornMatrix.cross] at hcoord
    linear_combination -hcoord
  exact ⟨M, N, hrec, hMN, hdet⟩

/-- Converse isomorphism `Stab_{Aut(SplitOctCD)}(ℓ) ≃* SL₃(ℝ)`. -/
def sl3ToSplitOctCDAut_equiv_ellStabilizer :
    ↥ellStabilizerSubgroup ≃* Matrix.SpecialLinearGroup (Fin 3) ℝ :=
  MulEquiv.symm
    { toFun := fun g => ⟨sl3ToSplitOctCDAut g, sl3ToSplitOctCDAut_ell g⟩
      invFun := fun φ =>
        let M : Matrix (Fin 3) (Fin 3) ℝ :=
          fun i j => (chiralZornEquiv (φ.1.1 (ePlusCD j))).2.2.1 i
        have hdet : M.det = 1 := by
          rcases ellStabilizer_reconstruct φ.2 with ⟨M', N', hrec, _, hdet'⟩
          have hMeq : M = M' := by
            ext i j
            have he : ePlusCD j = chiralZornReconstruct 0 0 (Pi.single j 1) 0 := by
              unfold chiralZornReconstruct; simp [Finset.sum_eq_single j]
            change (chiralZornEquiv (φ.1.1 (ePlusCD j))).2.2.1 i = M' i j
            rw [he, hrec, chiralZornEquiv_reconstruct]
            simp [Matrix.mulVec_single]
          rw [hMeq, hdet']
        ⟨M, hdet⟩
      left_inv := fun g => by
        apply Subtype.ext
        ext i j
        change (chiralZornEquiv ((sl3ToSplitOctCDAut g).1 (ePlusCD j))).2.2.1 i = g.1 i j
        rw [sl3ToSplitOctCDAut_ePlus]
        simp [Fin.sum_univ_three, ePlusCD_components, qBasis]
        fin_cases i <;> simp <;> ring
      right_inv := fun φ => by
        rcases ellStabilizer_reconstruct φ.2 with ⟨M, N, hrec, hMN, hdet⟩
        let Mφ : Matrix (Fin 3) (Fin 3) ℝ :=
          fun i j => (chiralZornEquiv (φ.1.1 (ePlusCD j))).2.2.1 i
        have hM_eq : M = Mφ := by
          ext i j
          have he : ePlusCD j = chiralZornReconstruct 0 0 (Pi.single j 1) 0 := by
            unfold chiralZornReconstruct; simp [Finset.sum_eq_single j]
          change M i j = (chiralZornEquiv (φ.1.1 (ePlusCD j))).2.2.1 i
          rw [he, hrec, chiralZornEquiv_reconstruct]
          simp [Matrix.mulVec_single]
        let g : Matrix.SpecialLinearGroup (Fin 3) ℝ := ⟨M, hdet⟩
        have hN_eq : N = sl3DualMat g := by
          have hNT : Nᵀ * M = 1 := by
            calc Nᵀ * M = (Mᵀ * N)ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
              _ = 1ᵀ := by rw [hMN]
              _ = 1 := Matrix.transpose_one
          have hT : (g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ).1 = Nᵀ := by
            have hM1 : M * (g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ).1 = 1 := by
              change g.1 * (g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ).1 = 1
              rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
                Matrix.SpecialLinearGroup.coe_one]
            calc (g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ).1
                = (Nᵀ * M) * (g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ).1 := by
                    rw [hNT, Matrix.one_mul]
              _ = Nᵀ * (M * (g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ).1) :=
                    Matrix.mul_assoc _ _ _
              _ = Nᵀ := by rw [hM1, Matrix.mul_one]
          unfold sl3DualMat
          rw [hT, Matrix.transpose_transpose]
        apply Subtype.ext; apply Subtype.ext; apply LinearEquiv.ext; intro x
        obtain ⟨⟨α₁, α₂, a, b⟩, rfl⟩ := chiralZornEquiv.symm.surjective x
        simp only [chiralZornEquiv_symm_apply]
        have hg_eq : (⟨Mφ, by rw [← hM_eq]; exact hdet⟩ :
            Matrix.SpecialLinearGroup (Fin 3) ℝ) = g := by
          apply Subtype.ext; exact hM_eq.symm
        change (sl3ToSplitOctCDAut ⟨Mφ, _⟩).1 (chiralZornReconstruct α₁ α₂ a b) =
          φ.1.1 (chiralZornReconstruct α₁ α₂ a b)
        rw [hg_eq, show (sl3ToSplitOctCDAut g).1 _ = sl3LinearEquiv g _ from rfl,
          sl3LinearEquiv_reconstruct, hrec, ← hN_eq]
      map_mul' := fun g h => by
        apply Subtype.ext
        exact map_mul sl3ToSplitOctCDAut g h }

/-! ## Section 5: Lie Algebra and Complexified `SU(3)` Bridges (Feature F12) -/

local instance : LieRing (Module.End ℝ SplitOctCD) := LieRing.ofAssociativeRing

/-- Derivation Lie subalgebra `Der(SplitOctCD) ≤ End(SplitOctCD)`. -/
def cdDerivSubalgebra : LieSubalgebra ℝ (Module.End ℝ SplitOctCD) where
  carrier := {D | ∀ x y : SplitOctCD, D (x * y) = D x * y + x * D y}
  zero_mem' x y := by simp
  add_mem' {D E} hD hE x y := by
    simp only [LinearMap.add_apply]
    rw [hD, hE, add_mul, mul_add]
    abel
  smul_mem' {r D} hD x y := by
    simp only [LinearMap.smul_apply]
    rw [hD, cdMul_smul_left, cdMul_smul_right, smul_add]
  lie_mem' {D E} hD hE x y := by
    rw [LieRing.of_associative_ring_bracket]
    change D (E (x * y)) - E (D (x * y)) =
      (D (E x) - E (D x)) * y + x * (D (E y) - E (D y))
    rw [hE, hD, map_add, map_add, hD, hD, hE, hE, sub_mul, mul_sub]
    abel

/-- Derivations of `SplitOctCD` annihilating `ellCD`. -/
def cdEllDerivStabilizer : LieSubalgebra ℝ cdDerivSubalgebra where
  carrier := {D | D.1 ellCD = 0}
  zero_mem' := rfl
  add_mem' {D E} hD hE := by
    change D.1 ellCD + E.1 ellCD = 0
    rw [hD, hE, add_zero]
  smul_mem' {r D} hD := by
    change r • D.1 ellCD = 0
    rw [hD, smul_zero]
  lie_mem' {D E} hD hE := by
    change D.1 (E.1 ellCD) - E.1 (D.1 ellCD) = 0
    rw [hD, hE, map_zero, map_zero, sub_zero]

private theorem cdDeriv_one (D : cdDerivSubalgebra) : D.1 (1 : SplitOctCD) = 0 := by
  have h := D.2 (1 : SplitOctCD) 1
  simp only [mul_one, one_mul] at h
  calc D.1 (1 : SplitOctCD)
      = D.1 (1 : SplitOctCD) + D.1 (1 : SplitOctCD) - D.1 (1 : SplitOctCD) :=
          (add_sub_cancel_right _ _).symm
    _ = D.1 (1 : SplitOctCD) - D.1 (1 : SplitOctCD) := by rw [← h]
    _ = 0 := sub_self _

private def conjDerivToZorn (D : cdDerivSubalgebra) :
    CanonicalZornDerivation.canonicalZornDerivations :=
  ⟨splitOctCDEquivZornMatrix.toLinearMap ∘ₗ D.1 ∘ₗ splitOctCDEquivZornMatrix.symm.toLinearMap,
    by
      intro X Y
      change splitOctCDEquivZornMatrix (D.1 (splitOctCDEquivZornMatrix.symm (X * Y))) =
        splitOctCDEquivZornMatrix (D.1 (splitOctCDEquivZornMatrix.symm X)) * Y +
          X * splitOctCDEquivZornMatrix (D.1 (splitOctCDEquivZornMatrix.symm Y))
      rw [splitOctCDEquivZornMatrix_symm_mul, D.2, map_add, splitOctCDEquivZornMatrix_mul,
        splitOctCDEquivZornMatrix_mul, splitOctCDEquivZornMatrix.apply_symm_apply,
        splitOctCDEquivZornMatrix.apply_symm_apply]⟩

private def conjDerivFromZorn (D : CanonicalZornDerivation.canonicalZornDerivations) :
    cdDerivSubalgebra :=
  ⟨splitOctCDEquivZornMatrix.symm.toLinearMap ∘ₗ D.1 ∘ₗ splitOctCDEquivZornMatrix.toLinearMap,
    by
      intro x y
      change splitOctCDEquivZornMatrix.symm (D.1 (splitOctCDEquivZornMatrix (x * y))) =
        splitOctCDEquivZornMatrix.symm (D.1 (splitOctCDEquivZornMatrix x)) * y +
          x * splitOctCDEquivZornMatrix.symm (D.1 (splitOctCDEquivZornMatrix y))
      rw [splitOctCDEquivZornMatrix_mul, D.2, map_add, splitOctCDEquivZornMatrix_symm_mul,
        splitOctCDEquivZornMatrix_symm_mul, splitOctCDEquivZornMatrix.symm_apply_apply,
        splitOctCDEquivZornMatrix.symm_apply_apply]⟩

/-- Lie algebra isomorphism
`cdEllDerivStabilizer ≃ₗ⁅ℝ⁆ CanonicalZornPeirceStabilizer.peirceStabilizer`. -/
def sl3Stabilizer_lie_equiv_peirceStabilizer :
    cdEllDerivStabilizer ≃ₗ⁅ℝ⁆ CanonicalZornPeirceStabilizer.peirceStabilizer where
  toFun D :=
    ⟨conjDerivToZorn D.1, by
      have h1 : D.1.1 1 = 0 := cdDeriv_one D.1
      have hell : D.1.1 ellCD = 0 := D.2
      have hp : D.1.1 uPlusCD = 0 := by
        rw [uPlusCD, show oneCD = (1 : SplitOctCD) from oneCD_def.symm, map_smul, map_add,
          h1, hell, add_zero, smul_zero]
      have hm : D.1.1 uMinusCD = 0 := by
        rw [uMinusCD, show oneCD = (1 : SplitOctCD) from oneCD_def.symm, map_smul, map_sub,
          h1, hell, sub_zero, smul_zero]
      constructor
      · change splitOctCDEquivZornMatrix (D.1.1 (splitOctCDEquivZornMatrix.symm
            CanonicalZornPeirceStabilizer.peircePlus)) = 0
        have hu : CanonicalZornPeirceStabilizer.peircePlus = splitOctCDEquivZornMatrix uPlusCD :=
          splitOctCDEquivZornMatrix_uPlusCD.symm
        rw [hu, splitOctCDEquivZornMatrix.symm_apply_apply, hp, map_zero]
      · change splitOctCDEquivZornMatrix (D.1.1 (splitOctCDEquivZornMatrix.symm
            CanonicalZornPeirceStabilizer.peirceMinus)) = 0
        have hu : CanonicalZornPeirceStabilizer.peirceMinus = splitOctCDEquivZornMatrix uMinusCD :=
          splitOctCDEquivZornMatrix_uMinusCD.symm
        rw [hu, splitOctCDEquivZornMatrix.symm_apply_apply, hm, map_zero]⟩
  invFun E :=
    ⟨conjDerivFromZorn E.1, by
      have huP : E.1.1 (splitOctCDEquivZornMatrix uPlusCD) = 0 := by
        rw [splitOctCDEquivZornMatrix_uPlusCD]; exact E.2.1
      have huM : E.1.1 (splitOctCDEquivZornMatrix uMinusCD) = 0 := by
        rw [splitOctCDEquivZornMatrix_uMinusCD]; exact E.2.2
      change splitOctCDEquivZornMatrix.symm (E.1.1 (splitOctCDEquivZornMatrix ellCD)) = 0
      rw [← uPlusCD_sub_uMinusCD, map_sub, map_sub, huP, huM, sub_zero, map_zero]⟩
  left_inv D := by
    apply Subtype.ext; apply Subtype.ext; apply LinearMap.ext; intro x
    simp only [conjDerivFromZorn, conjDerivToZorn, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  right_inv E := by
    apply Subtype.ext; apply Subtype.ext; apply LinearMap.ext; intro X
    simp only [conjDerivToZorn, conjDerivFromZorn, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  map_add' D₁ D₂ := by
    apply Subtype.ext; apply Subtype.ext; apply LinearMap.ext; intro X
    change splitOctCDEquivZornMatrix
        (D₁.1.1 (splitOctCDEquivZornMatrix.symm X) + D₂.1.1 (splitOctCDEquivZornMatrix.symm X)) =
      splitOctCDEquivZornMatrix (D₁.1.1 (splitOctCDEquivZornMatrix.symm X)) +
        splitOctCDEquivZornMatrix (D₂.1.1 (splitOctCDEquivZornMatrix.symm X))
    exact map_add _ _ _
  map_smul' r D := by
    apply Subtype.ext; apply Subtype.ext; apply LinearMap.ext; intro X
    change splitOctCDEquivZornMatrix (r • D.1.1 (splitOctCDEquivZornMatrix.symm X)) =
      r • splitOctCDEquivZornMatrix (D.1.1 (splitOctCDEquivZornMatrix.symm X))
    exact map_smul _ _ _
  map_lie' {D₁ D₂} := by
    apply Subtype.ext; apply Subtype.ext; apply LinearMap.ext; intro X
    change splitOctCDEquivZornMatrix
        ((D₁.1.1 * D₂.1.1 - D₂.1.1 * D₁.1.1) (splitOctCDEquivZornMatrix.symm X)) =
      splitOctCDEquivZornMatrix (D₁.1.1 (splitOctCDEquivZornMatrix.symm
        (splitOctCDEquivZornMatrix (D₂.1.1 (splitOctCDEquivZornMatrix.symm X))))) -
      splitOctCDEquivZornMatrix (D₂.1.1 (splitOctCDEquivZornMatrix.symm
        (splitOctCDEquivZornMatrix (D₁.1.1 (splitOctCDEquivZornMatrix.symm X)))))
    simp only [LinearEquiv.symm_apply_apply, LinearMap.sub_apply, Module.End.mul_apply, map_sub]

/-- Coordinate equivalence `cdEllDerivStabilizer ≃ SL3` preserving `+`, `•`, and Lie bracket. -/
def cdEllDerivStabilizerEquivSL3 :
    cdEllDerivStabilizer ≃ CanonicalZornPeirceSL3Bridge.SL3 :=
  sl3Stabilizer_lie_equiv_peirceStabilizer.toLinearEquiv.toEquiv.trans
    CanonicalZornPeirceSL3Bridge.peirceStabilizerEquivSL3

theorem cdEllDerivStabilizerEquivSL3_lie (D E : cdEllDerivStabilizer) :
    cdEllDerivStabilizerEquivSL3 ⁅D, E⁆ =
      InfoGeometry.Physics.SplitG2SL3Concrete.commutator
        (cdEllDerivStabilizerEquivSL3 D) (cdEllDerivStabilizerEquivSL3 E) := by
  dsimp [cdEllDerivStabilizerEquivSL3]
  rw [sl3Stabilizer_lie_equiv_peirceStabilizer.map_lie D E]
  exact CanonicalZornPeirceSL3Bridge.stabilizerMatrixSL3_lie _ _

theorem splitG2_exp_to_SplitOctCDAut
    (D : CanonicalZornDerivation.canonicalZornDerivations) (t : ℝ) :
    ∃ φ : SplitOctCDAut,
      splitOctCDAutMulEquivRealSplitOctonionAut φ =
        CanonicalZornDerivationRealAutBridge.zornFlowRealAut D t :=
  ⟨splitOctCDAutMulEquivRealSplitOctonionAut.symm
    (CanonicalZornDerivationRealAutBridge.zornFlowRealAut D t), by simp⟩

/-! ### Complexified `ℂ ⊗[ℝ] SplitOctCD` and `SU(3) ≤ SL(3, ℂ)` Action -/

private def complexZornBilinear : ℂ →ₗ[ℂ] (SplitOctCD →ₗ[ℝ] ZornMatrix ℂ) where
  toFun c :=
    { toFun := fun x =>
        let z := splitOctCDEquivZornMatrix x
        c • (⟨(z.a : ℂ), (z.b : ℂ), fun i => (z.x i : ℂ), fun i => (z.y i : ℂ)⟩ : ZornMatrix ℂ)
      map_add' := fun x y => by
        have h : splitOctCDEquivZornMatrix (x + y) =
            splitOctCDEquivZornMatrix x + splitOctCDEquivZornMatrix y := map_add _ x y
        rw [← smul_add]
        apply ZornMatrix.ext
        · simp [h]
        · simp [h]
        · funext i; fin_cases i <;> simp [h]
        · funext i; fin_cases i <;> simp [h]
      map_smul' := fun r x => by
        have h : splitOctCDEquivZornMatrix (r • x) = r • splitOctCDEquivZornMatrix x :=
          map_smul _ r x
        dsimp only
        rw [RingHom.id_apply, ← smul_assoc, Algebra.smul_def, Complex.coe_algebraMap]
        apply ZornMatrix.ext
        · simp [h, ZornMatrix.smul_a, Complex.ofReal_mul, Complex.ofReal_add]; ring
        · simp [h, ZornMatrix.smul_b, Complex.ofReal_mul, Complex.ofReal_sub]; ring
        · funext i
          fin_cases i <;>
            simp [h, ZornMatrix.smul_x, Complex.ofReal_mul, Complex.ofReal_sub] <;> ring
        · funext i
          fin_cases i <;>
            simp [h, ZornMatrix.smul_y, Complex.ofReal_mul, Complex.ofReal_add] <;> ring }
  map_add' c₁ c₂ := by
    apply LinearMap.ext; intro x
    simp [add_smul]
  map_smul' r c := by
    apply LinearMap.ext; intro x
    simp [smul_smul]

/-- Complex-linear isomorphism `(ℂ ⊗[ℝ] SplitOctCD) ≃ₗ[ℂ] ZornMatrix ℂ`. -/
def complexifiedSplitOctCD_equiv_zornMatrixC :
    (ℂ ⊗[ℝ] SplitOctCD) ≃ₗ[ℂ] ZornMatrix ℂ where
  toLinearMap := TensorProduct.AlgebraTensorModule.lift complexZornBilinear
  invFun Z :=
    Z.a ⊗ₜ[ℝ] uPlusCD + Z.b ⊗ₜ[ℝ] uMinusCD +
      ∑ i : Fin 3, (-Z.x i) ⊗ₜ[ℝ] ePlusCD i + ∑ i : Fin 3, (Z.y i) ⊗ₜ[ℝ] eMinusCD i
  left_inv w := by
    induction w using TensorProduct.inductionOn with
    | tmul c x =>
        let z := splitOctCDEquivZornMatrix x
        have hx : x = z.a • uPlusCD + z.b • uMinusCD +
            ∑ i : Fin 3, (-z.x i) • ePlusCD i + ∑ i : Fin 3, (z.y i) • eMinusCD i := by
          apply splitOctCDEquivZornMatrix.injective
          rw [show z.a • uPlusCD + z.b • uMinusCD +
              ∑ i : Fin 3, (-z.x i) • ePlusCD i + ∑ i : Fin 3, (z.y i) • eMinusCD i =
            chiralZornReconstruct z.a z.b (-z.x) z.y from rfl,
            splitOctCDEquivZornMatrix_chiralZornReconstruct]
          apply ZornMatrix.ext
          · rfl
          · rfl
          · funext i; fin_cases i <;> simp [z, splitOctCDEquivZornMatrix]
          · rfl
        have hlift : TensorProduct.AlgebraTensorModule.lift complexZornBilinear (c ⊗ₜ[ℝ] x) =
            c • (⟨(z.a : ℂ), (z.b : ℂ),
              fun i => (z.x i : ℂ), fun i => (z.y i : ℂ)⟩ : ZornMatrix ℂ) := rfl
        have hsmul : ∀ (r : ℝ) (v : SplitOctCD),
            (c * (r : ℂ)) ⊗ₜ[ℝ] v = c ⊗ₜ[ℝ] (r • v) := fun r v => by
          rw [mul_comm, ← Complex.coe_algebraMap, ← Algebra.smul_def,
            ← TensorProduct.smul_tmul']
          exact TensorProduct.smul_tmul r c v
        have hsmul_neg : ∀ (r : ℝ) (v : SplitOctCD),
            (-(c * (r : ℂ))) ⊗ₜ[ℝ] v = c ⊗ₜ[ℝ] ((-r) • v) := fun r v => by
          rw [← mul_neg, ← Complex.ofReal_neg, hsmul (-r) v]
        change (fun Z : ZornMatrix ℂ => Z.a ⊗ₜ[ℝ] uPlusCD + Z.b ⊗ₜ[ℝ] uMinusCD +
          ∑ i : Fin 3, (-Z.x i) ⊗ₜ[ℝ] ePlusCD i + ∑ i : Fin 3, (Z.y i) ⊗ₜ[ℝ] eMinusCD i)
          (TensorProduct.AlgebraTensorModule.lift complexZornBilinear (c ⊗ₜ[ℝ] x)) = c ⊗ₜ[ℝ] x
        rw [hlift]
        simp only [ZornMatrix.smul_a, ZornMatrix.smul_b, ZornMatrix.smul_x, ZornMatrix.smul_y,
          Pi.smul_apply, smul_eq_mul, hsmul, hsmul_neg, ← TensorProduct.tmul_sum,
          ← TensorProduct.tmul_add, ← hx]
    | add u v hu hv =>
        have hadd : (TensorProduct.AlgebraTensorModule.lift complexZornBilinear) (u + v) =
            (TensorProduct.AlgebraTensorModule.lift complexZornBilinear) u +
            (TensorProduct.AlgebraTensorModule.lift complexZornBilinear) v := map_add _ u v
        have hu' :
            (TensorProduct.AlgebraTensorModule.lift complexZornBilinear u).a ⊗ₜ[ℝ] uPlusCD +
              (TensorProduct.AlgebraTensorModule.lift complexZornBilinear u).b ⊗ₜ[ℝ] uMinusCD +
              ∑ i : Fin 3,
                (-(TensorProduct.AlgebraTensorModule.lift complexZornBilinear u).x i) ⊗ₜ[ℝ]
                  ePlusCD i +
              ∑ i : Fin 3,
                (TensorProduct.AlgebraTensorModule.lift complexZornBilinear u).y i ⊗ₜ[ℝ]
                  eMinusCD i = u := hu
        have hv' :
            (TensorProduct.AlgebraTensorModule.lift complexZornBilinear v).a ⊗ₜ[ℝ] uPlusCD +
              (TensorProduct.AlgebraTensorModule.lift complexZornBilinear v).b ⊗ₜ[ℝ] uMinusCD +
              ∑ i : Fin 3,
                (-(TensorProduct.AlgebraTensorModule.lift complexZornBilinear v).x i) ⊗ₜ[ℝ]
                  ePlusCD i +
              ∑ i : Fin 3,
                (TensorProduct.AlgebraTensorModule.lift complexZornBilinear v).y i ⊗ₜ[ℝ]
                  eMinusCD i = v := hv
        change (TensorProduct.AlgebraTensorModule.lift complexZornBilinear (u + v)).a ⊗ₜ[ℝ]
            uPlusCD +
          (TensorProduct.AlgebraTensorModule.lift complexZornBilinear (u + v)).b ⊗ₜ[ℝ] uMinusCD +
          ∑ i : Fin 3,
            (-(TensorProduct.AlgebraTensorModule.lift complexZornBilinear (u + v)).x i) ⊗ₜ[ℝ]
              ePlusCD i +
          ∑ i : Fin 3,
            (TensorProduct.AlgebraTensorModule.lift complexZornBilinear (u + v)).y i ⊗ₜ[ℝ]
              eMinusCD i = u + v
        rw [hadd]
        simp only [ZornMatrix.add_a, ZornMatrix.add_b, ZornMatrix.add_x, ZornMatrix.add_y,
          Pi.add_apply, neg_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
        calc _ =
            ((TensorProduct.AlgebraTensorModule.lift complexZornBilinear u).a ⊗ₜ[ℝ] uPlusCD +
              (TensorProduct.AlgebraTensorModule.lift complexZornBilinear u).b ⊗ₜ[ℝ] uMinusCD +
              ∑ i : Fin 3,
                (-(TensorProduct.AlgebraTensorModule.lift complexZornBilinear u).x i) ⊗ₜ[ℝ]
                  ePlusCD i +
              ∑ i : Fin 3,
                (TensorProduct.AlgebraTensorModule.lift complexZornBilinear u).y i ⊗ₜ[ℝ]
                  eMinusCD i) +
            ((TensorProduct.AlgebraTensorModule.lift complexZornBilinear v).a ⊗ₜ[ℝ] uPlusCD +
              (TensorProduct.AlgebraTensorModule.lift complexZornBilinear v).b ⊗ₜ[ℝ] uMinusCD +
              ∑ i : Fin 3,
                (-(TensorProduct.AlgebraTensorModule.lift complexZornBilinear v).x i) ⊗ₜ[ℝ]
                  ePlusCD i +
              ∑ i : Fin 3,
                (TensorProduct.AlgebraTensorModule.lift complexZornBilinear v).y i ⊗ₜ[ℝ]
                  eMinusCD i) := by abel
          _ = u + v := by rw [hu', hv']
  right_inv Z := by
    change TensorProduct.AlgebraTensorModule.lift complexZornBilinear
      (Z.a ⊗ₜ[ℝ] uPlusCD + Z.b ⊗ₜ[ℝ] uMinusCD +
        ∑ i : Fin 3, (-Z.x i) ⊗ₜ[ℝ] ePlusCD i + ∑ i : Fin 3, (Z.y i) ⊗ₜ[ℝ] eMinusCD i) = Z
    simp only [map_add, map_sum]
    have ht : ∀ (c : ℂ) (x : SplitOctCD),
        TensorProduct.AlgebraTensorModule.lift complexZornBilinear (c ⊗ₜ[ℝ] x) =
          c • (⟨((splitOctCDEquivZornMatrix x).a : ℂ),
                ((splitOctCDEquivZornMatrix x).b : ℂ),
                fun i => ((splitOctCDEquivZornMatrix x).x i : ℂ),
                fun i => ((splitOctCDEquivZornMatrix x).y i : ℂ)⟩ : ZornMatrix ℂ) :=
      fun _ _ => rfl
    simp only [ht, splitOctCDEquivZornMatrix_uPlusCD, splitOctCDEquivZornMatrix_uMinusCD,
      splitOctCDEquivZornMatrix_ePlusCD, splitOctCDEquivZornMatrix_eMinusCD]
    apply ZornMatrix.ext
    · simp [ZornMatrix.zornPlus, ZornMatrix.zornMinus, ZornMatrix.chiralUpperBasis,
        ZornMatrix.chiralLowerBasis, Fin.sum_univ_three]
    · simp [ZornMatrix.zornPlus, ZornMatrix.zornMinus, ZornMatrix.chiralUpperBasis,
        ZornMatrix.chiralLowerBasis, Fin.sum_univ_three]
    · funext i; fin_cases i <;>
        simp [ZornMatrix.zornPlus, ZornMatrix.zornMinus, ZornMatrix.chiralUpperBasis,
          ZornMatrix.chiralLowerBasis, Fin.sum_univ_three]
    · funext i; fin_cases i <;>
        simp [ZornMatrix.zornPlus, ZornMatrix.zornMinus, ZornMatrix.chiralUpperBasis,
          ZornMatrix.chiralLowerBasis, Fin.sum_univ_three]

private def zornMatrixCToBraidZorn :
    ZornMatrix ℂ ≃ InfoGeometry.Physics.SplitOctonionBraidSU3.Zorn where
  toFun Z := { a := Z.a, u := Z.x, v := Z.y, b := Z.b }
  invFun W := { a := W.a, b := W.b, x := W.u, y := W.v }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Complexified split-octonion equivalence `(ℂ ⊗[ℝ] SplitOctCD) ≃ SplitOctonionBraidSU3.Zorn`. -/
def complexifiedSplitOctCD_equiv_zorn :
    (ℂ ⊗[ℝ] SplitOctCD) ≃ InfoGeometry.Physics.ThreeColorSL3ZornAction.Zorn :=
  complexifiedSplitOctCD_equiv_zornMatrixC.toEquiv.trans zornMatrixCToBraidZorn

/-- Unconditional proof of `ThreeColorSL3ZornAction.PreservesCrossFundamental` for all
`g ∈ SL(3, ℂ)` via `cofactor3` at `R = ℂ`. -/
theorem sl3C_preservesCrossFundamental (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    InfoGeometry.Physics.ThreeColorSL3ZornAction.PreservesCrossFundamental g := by
  intro u v
  have hcr : InfoGeometry.Physics.SplitOctonionBraidSU3.cross3 u v = cross3R u v := by
    funext i; fin_cases i <;> rfl
  have hcr1 : InfoGeometry.Physics.SplitOctonionBraidSU3.cross3
      (InfoGeometry.Physics.ThreeColorSL3ZornAction.colourFundamentalAction g u)
      (InfoGeometry.Physics.ThreeColorSL3ZornAction.colourFundamentalAction g v) =
      cross3R (g.1 *ᵥ u) (g.1 *ᵥ v) := by
    funext i; fin_cases i <;> rfl
  rw [hcr, hcr1, cross3R_mulVec, cofactor3_sl_eq_inv_transpose g]
  rfl

/-- Unconditional proof of `ThreeColorSL3ZornAction.PreservesDualCross` for all
`g ∈ SL(3, ℂ)` via `cofactor3` at `R = ℂ`. -/
theorem sl3C_preservesDualCross (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    InfoGeometry.Physics.ThreeColorSL3ZornAction.PreservesDualCross g := by
  intro u v
  have hcr : InfoGeometry.Physics.SplitOctonionBraidSU3.cross3 u v = cross3R u v := by
    funext i; fin_cases i <;> rfl
  have hcr2 : InfoGeometry.Physics.SplitOctonionBraidSU3.cross3
      (InfoGeometry.Physics.ThreeColorSL3ZornAction.colourDualAction g u)
      (InfoGeometry.Physics.ThreeColorSL3ZornAction.colourDualAction g v) =
      cross3R (cofactor3 g.1 *ᵥ u) (cofactor3 g.1 *ᵥ v) := by
    rw [cofactor3_sl_eq_inv_transpose g]
    funext i; fin_cases i <;> rfl
  rw [hcr, hcr2, cross3R_cofactor3_mulVec, g.2, one_smul]
  rfl

/-- Unconditional multiplicativity of `ThreeColorSL3ZornAction.zornSL3Action g`
for every `g ∈ SL(3, ℂ)`. -/
theorem zornSL3Action_mul_unconditional (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (X Y : InfoGeometry.Physics.ThreeColorSL3ZornAction.Zorn) :
    InfoGeometry.Physics.ThreeColorSL3ZornAction.zornSL3Action g
        (InfoGeometry.Physics.SplitOctonionBraidSU3.zornMul X Y) =
      InfoGeometry.Physics.SplitOctonionBraidSU3.zornMul
        (InfoGeometry.Physics.ThreeColorSL3ZornAction.zornSL3Action g X)
        (InfoGeometry.Physics.ThreeColorSL3ZornAction.zornSL3Action g Y) :=
  InfoGeometry.Physics.ThreeColorSL3ZornAction.zornSL3Action_mul_of_covariant g
    (sl3C_preservesCrossFundamental g) (sl3C_preservesDualCross g) X Y

/-- Group homomorphism `SU(3) →* SL(3, ℂ)`. -/
def su3ToSL3C :
    CanonicalZornPeirceUnitaryPhase.SU3 →* Matrix.SpecialLinearGroup (Fin 3) ℂ where
  toFun g := ⟨g.1, (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Group homomorphism `SL(3, ℝ) →* SL(3, ℂ)`. -/
def sl3RToSL3C :
    Matrix.SpecialLinearGroup (Fin 3) ℝ →* Matrix.SpecialLinearGroup (Fin 3) ℂ where
  toFun g :=
    ⟨Matrix.map g.1 (algebraMap ℝ ℂ), by
      change ((algebraMap ℝ ℂ).mapMatrix g.1).det = 1
      rw [← RingHom.map_det, g.2, map_one]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp
  map_mul' g h := by
    apply Subtype.ext
    ext i j
    change Matrix.map (g * h).1 (algebraMap ℝ ℂ) i j =
      (Matrix.map g.1 (algebraMap ℝ ℂ) * Matrix.map h.1 (algebraMap ℝ ℂ)) i j
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]

private def sl3CZornLinearEquiv (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    ZornMatrix ℂ ≃ₗ[ℂ] ZornMatrix ℂ where
  toFun Z :=
    { a := Z.a
      b := Z.b
      x := InfoGeometry.Physics.ThreeColorSL3ZornAction.colourFundamentalAction g Z.x
      y := InfoGeometry.Physics.ThreeColorSL3ZornAction.colourDualAction g Z.y }
  invFun Z :=
    { a := Z.a
      b := Z.b
      x := InfoGeometry.Physics.ThreeColorSL3ZornAction.colourFundamentalAction g⁻¹ Z.x
      y := InfoGeometry.Physics.ThreeColorSL3ZornAction.colourDualAction g⁻¹ Z.y }
  left_inv Z := by
    apply ZornMatrix.ext
    · rfl
    · rfl
    · funext i
      change (g⁻¹.1 *ᵥ (g.1 *ᵥ Z.x)) i = Z.x i
      rw [Matrix.mulVec_mulVec]
      have h : g⁻¹.1 * g.1 = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [h, Matrix.one_mulVec]
    · funext i
      change (((g⁻¹)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1ᵀ *ᵥ (g⁻¹.1ᵀ *ᵥ Z.y)) i = Z.y i
      rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul]
      have h : g⁻¹.1 * ((g⁻¹)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1 = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [h, Matrix.transpose_one, Matrix.one_mulVec]
  right_inv Z := by
    apply ZornMatrix.ext
    · rfl
    · rfl
    · funext i
      change (g.1 *ᵥ (g⁻¹.1 *ᵥ Z.x)) i = Z.x i
      rw [Matrix.mulVec_mulVec]
      have h : g.1 * g⁻¹.1 = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [h, Matrix.one_mulVec]
    · funext i
      change (g⁻¹.1ᵀ *ᵥ (((g⁻¹)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1ᵀ *ᵥ Z.y)) i = Z.y i
      rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul]
      have h : ((g⁻¹)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1 * g⁻¹.1 = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [h, Matrix.transpose_one, Matrix.one_mulVec]
  map_add' Z₁ Z₂ := by
    apply ZornMatrix.ext <;>
      simp [InfoGeometry.Physics.ThreeColorSL3ZornAction.colourFundamentalAction,
        InfoGeometry.Physics.ThreeColorSL3ZornAction.colourDualAction, Matrix.mulVec_add]
  map_smul' c Z := by
    apply ZornMatrix.ext
    · simp [ZornMatrix.smul_a]
    · simp [ZornMatrix.smul_b]
    · simp [ZornMatrix.smul_x,
        InfoGeometry.Physics.ThreeColorSL3ZornAction.colourFundamentalAction, Matrix.mulVec_smul]
    · simp [ZornMatrix.smul_y,
        InfoGeometry.Physics.ThreeColorSL3ZornAction.colourDualAction, Matrix.mulVec_smul]

/-- Complexified `SL(3, ℂ)` action on `ℂ ⊗[ℝ] SplitOctCD`. -/
def sl3CComplexStabilizer_action :
    Matrix.SpecialLinearGroup (Fin 3) ℂ →* ((ℂ ⊗[ℝ] SplitOctCD) ≃ₗ[ℂ] (ℂ ⊗[ℝ] SplitOctCD)) where
  toFun g := complexifiedSplitOctCD_equiv_zornMatrixC.trans
    ((sl3CZornLinearEquiv g).trans complexifiedSplitOctCD_equiv_zornMatrixC.symm)
  map_one' := by
    apply LinearEquiv.ext; intro w
    apply complexifiedSplitOctCD_equiv_zornMatrixC.injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.coe_one, id_eq]
    apply ZornMatrix.ext <;> simp [sl3CZornLinearEquiv]
  map_mul' g₁ g₂ := by
    apply LinearEquiv.ext; intro w
    apply complexifiedSplitOctCD_equiv_zornMatrixC.injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.mul_apply]
    apply ZornMatrix.ext
    · rfl
    · rfl
    · simp [sl3CZornLinearEquiv,
        InfoGeometry.Physics.ThreeColorSL3ZornAction.colourFundamentalAction,
        Matrix.mulVec_mulVec]
    · simp [sl3CZornLinearEquiv,
        InfoGeometry.Physics.ThreeColorSL3ZornAction.colourDualAction,
        Matrix.mulVec_mulVec, Matrix.transpose_mul]

/-- `SU(3)` action on `ℂ ⊗[ℝ] SplitOctCD` obtained by restricting `sl3CComplexStabilizer_action`. -/
def su3ComplexStabilizer_action :
    CanonicalZornPeirceUnitaryPhase.SU3 →* ((ℂ ⊗[ℝ] SplitOctCD) ≃ₗ[ℂ] (ℂ ⊗[ℝ] SplitOctCD)) :=
  sl3CComplexStabilizer_action.comp su3ToSL3C

theorem su3ComplexStabilizer_action_eq_zornSL3Action
    (g : CanonicalZornPeirceUnitaryPhase.SU3) (w : ℂ ⊗[ℝ] SplitOctCD) :
    complexifiedSplitOctCD_equiv_zorn (su3ComplexStabilizer_action g w) =
      InfoGeometry.Physics.ThreeColorSL3ZornAction.zornSL3Action (su3ToSL3C g)
        (complexifiedSplitOctCD_equiv_zorn w) := by
  dsimp [complexifiedSplitOctCD_equiv_zorn, su3ComplexStabilizer_action,
    sl3CComplexStabilizer_action]
  rw [complexifiedSplitOctCD_equiv_zornMatrixC.apply_symm_apply]
  rfl

theorem su3ComplexStabilizer_action_offDiagonal
    (g : CanonicalZornPeirceUnitaryPhase.SU3) (w : ℂ ⊗[ℝ] SplitOctCD) :
    let Z := complexifiedSplitOctCD_equiv_zorn w
    let Z' := complexifiedSplitOctCD_equiv_zorn (su3ComplexStabilizer_action g w)
    (Z'.u, Z'.v) = CanonicalZornPeirceUnitaryPhase.su3OffDiagonalAction g (Z.u, Z.v) := by
  rw [su3ComplexStabilizer_action_eq_zornSL3Action]
  have hinv : ((su3ToSL3C g)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1 =
      (g⁻¹ : CanonicalZornPeirceUnitaryPhase.SU3).1 := by
    have hL : (g⁻¹ : CanonicalZornPeirceUnitaryPhase.SU3).1 * (su3ToSL3C g).1 = 1 := by
      change ((g⁻¹ * g : CanonicalZornPeirceUnitaryPhase.SU3) : Matrix (Fin 3) (Fin 3) ℂ) = 1
      rw [inv_mul_cancel]
      rfl
    have hR : (su3ToSL3C g).1 * ((su3ToSL3C g)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1 = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc ((su3ToSL3C g)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1
        = 1 * ((su3ToSL3C g)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1 :=
            (Matrix.one_mul _).symm
      _ = ((g⁻¹ : CanonicalZornPeirceUnitaryPhase.SU3).1 * (su3ToSL3C g).1) *
            ((su3ToSL3C g)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1 := by rw [hL]
      _ = (g⁻¹ : CanonicalZornPeirceUnitaryPhase.SU3).1 *
            ((su3ToSL3C g).1 * ((su3ToSL3C g)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1) :=
            Matrix.mul_assoc _ _ _
      _ = (g⁻¹ : CanonicalZornPeirceUnitaryPhase.SU3).1 := by rw [hR, Matrix.mul_one]
  refine Prod.ext rfl ?_
  change (((su3ToSL3C g)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1ᵀ) *ᵥ _ =
    ((g⁻¹ : CanonicalZornPeirceUnitaryPhase.SU3).1ᵀ) *ᵥ _
  rw [hinv]

theorem su3ComplexStabilizer_action_preserves_mul_and_norm
    (g : CanonicalZornPeirceUnitaryPhase.SU3) (w₁ w₂ : ℂ ⊗[ℝ] SplitOctCD) :
    InfoGeometry.Physics.SplitOctonionBraidSU3.zornMul
        (complexifiedSplitOctCD_equiv_zorn (su3ComplexStabilizer_action g w₁))
        (complexifiedSplitOctCD_equiv_zorn (su3ComplexStabilizer_action g w₂)) =
      InfoGeometry.Physics.ThreeColorSL3ZornAction.zornSL3Action (su3ToSL3C g)
        (InfoGeometry.Physics.SplitOctonionBraidSU3.zornMul
          (complexifiedSplitOctCD_equiv_zorn w₁) (complexifiedSplitOctCD_equiv_zorn w₂)) ∧
    InfoGeometry.Physics.SplitOctonionBraidSU3.zornNorm
        (complexifiedSplitOctCD_equiv_zorn (su3ComplexStabilizer_action g w₁)) =
      InfoGeometry.Physics.SplitOctonionBraidSU3.zornNorm
        (complexifiedSplitOctCD_equiv_zorn w₁) := by
  refine ⟨?_, ?_⟩
  · rw [su3ComplexStabilizer_action_eq_zornSL3Action, su3ComplexStabilizer_action_eq_zornSL3Action,
      zornSL3Action_mul_unconditional]
  · rw [su3ComplexStabilizer_action_eq_zornSL3Action]
    exact InfoGeometry.Physics.ThreeColorSL3ZornAction.zornSL3Action_preserves_norm_of_pairing
      (su3ToSL3C g) _

theorem su3ComplexStabilizer_action_fixes_chiral_singlets
    (g : CanonicalZornPeirceUnitaryPhase.SU3) :
    su3ComplexStabilizer_action g ((1 : ℂ) ⊗ₜ[ℝ] ellCD) = (1 : ℂ) ⊗ₜ[ℝ] ellCD ∧
    su3ComplexStabilizer_action g ((1 : ℂ) ⊗ₜ[ℝ] uPlusCD) = (1 : ℂ) ⊗ₜ[ℝ] uPlusCD ∧
    su3ComplexStabilizer_action g ((1 : ℂ) ⊗ₜ[ℝ] uMinusCD) = (1 : ℂ) ⊗ₜ[ℝ] uMinusCD := by
  have hfix : ∀ α₁ α₂ : ℝ,
      su3ComplexStabilizer_action g ((1 : ℂ) ⊗ₜ[ℝ] chiralZornReconstruct α₁ α₂ 0 0) =
        (1 : ℂ) ⊗ₜ[ℝ] chiralZornReconstruct α₁ α₂ 0 0 := by
    intro α₁ α₂
    apply complexifiedSplitOctCD_equiv_zornMatrixC.injective
    have ht : complexifiedSplitOctCD_equiv_zornMatrixC
        ((1 : ℂ) ⊗ₜ[ℝ] chiralZornReconstruct α₁ α₂ 0 0) =
        ⟨(α₁ : ℂ), (α₂ : ℂ), 0, 0⟩ := by
      have h1 : complexifiedSplitOctCD_equiv_zornMatrixC
          ((1 : ℂ) ⊗ₜ[ℝ] chiralZornReconstruct α₁ α₂ 0 0) =
          (1 : ℂ) • (⟨((splitOctCDEquivZornMatrix (chiralZornReconstruct α₁ α₂ 0 0)).a : ℂ),
            ((splitOctCDEquivZornMatrix (chiralZornReconstruct α₁ α₂ 0 0)).b : ℂ),
            fun i => ((splitOctCDEquivZornMatrix (chiralZornReconstruct α₁ α₂ 0 0)).x i : ℂ),
            fun i => ((splitOctCDEquivZornMatrix (chiralZornReconstruct α₁ α₂ 0 0)).y i : ℂ)⟩ :
            ZornMatrix ℂ) := rfl
      rw [h1, one_smul, splitOctCDEquivZornMatrix_chiralZornReconstruct]
      apply ZornMatrix.ext
      · simp
      · simp
      · funext i; simp
      · funext i; simp
    change complexifiedSplitOctCD_equiv_zornMatrixC
      (complexifiedSplitOctCD_equiv_zornMatrixC.symm
        (sl3CZornLinearEquiv (su3ToSL3C g)
          (complexifiedSplitOctCD_equiv_zornMatrixC
            ((1 : ℂ) ⊗ₜ[ℝ] chiralZornReconstruct α₁ α₂ 0 0)))) = _
    rw [complexifiedSplitOctCD_equiv_zornMatrixC.apply_symm_apply, ht]
    apply ZornMatrix.ext
    · simp [sl3CZornLinearEquiv]
    · simp [sl3CZornLinearEquiv]
    · funext i
      simp [sl3CZornLinearEquiv,
        InfoGeometry.Physics.ThreeColorSL3ZornAction.colourFundamentalAction]
    · funext i
      simp [sl3CZornLinearEquiv,
        InfoGeometry.Physics.ThreeColorSL3ZornAction.colourDualAction]
  have hell : ellCD = chiralZornReconstruct 1 (-1) 0 0 := by
    rw [← uPlusCD_sub_uMinusCD, sub_eq_add_neg]
    unfold chiralZornReconstruct
    simp
  have huP : uPlusCD = chiralZornReconstruct 1 0 0 0 := by
    unfold chiralZornReconstruct; simp
  have huM : uMinusCD = chiralZornReconstruct 0 1 0 0 := by
    unfold chiralZornReconstruct; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hell]; exact hfix 1 (-1)
  · rw [huP]; exact hfix 1 0
  · rw [huM]; exact hfix 0 1

theorem sl3CComplexStabilizer_compat_real
    (g : Matrix.SpecialLinearGroup (Fin 3) ℝ) (x : SplitOctCD) :
    sl3CComplexStabilizer_action (sl3RToSL3C g) ((1 : ℂ) ⊗ₜ[ℝ] x) =
      (1 : ℂ) ⊗ₜ[ℝ] ((sl3ToSplitOctCDAut g).1 x) := by
  obtain ⟨⟨α₁, α₂, a, b⟩, rfl⟩ := chiralZornEquiv.symm.surjective x
  simp only [chiralZornEquiv_symm_apply]
  change _ = (1 : ℂ) ⊗ₜ[ℝ] sl3LinearEquiv g (chiralZornReconstruct α₁ α₂ a b)
  rw [sl3LinearEquiv_reconstruct]
  apply complexifiedSplitOctCD_equiv_zornMatrixC.injective
  simp only [sl3CComplexStabilizer_action, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hL : ∀ α₁' α₂' a' b',
      complexifiedSplitOctCD_equiv_zornMatrixC
        ((1 : ℂ) ⊗ₜ[ℝ] chiralZornReconstruct α₁' α₂' a' b') =
        ⟨(α₁' : ℂ), (α₂' : ℂ), fun i => (-a' i : ℂ), fun i => (b' i : ℂ)⟩ := by
    intro α₁' α₂' a' b'
    have h1 : complexifiedSplitOctCD_equiv_zornMatrixC
        ((1 : ℂ) ⊗ₜ[ℝ] chiralZornReconstruct α₁' α₂' a' b') =
        (1 : ℂ) • (⟨((splitOctCDEquivZornMatrix (chiralZornReconstruct α₁' α₂' a' b')).a : ℂ),
          ((splitOctCDEquivZornMatrix (chiralZornReconstruct α₁' α₂' a' b')).b : ℂ),
          fun i => ((splitOctCDEquivZornMatrix (chiralZornReconstruct α₁' α₂' a' b')).x i : ℂ),
          fun i => ((splitOctCDEquivZornMatrix (chiralZornReconstruct α₁' α₂' a' b')).y i : ℂ)⟩ :
          ZornMatrix ℂ) := rfl
    rw [h1, one_smul, splitOctCDEquivZornMatrix_chiralZornReconstruct]
    apply ZornMatrix.ext
    · simp
    · simp
    · funext i; simp
    · funext i; simp
  rw [hL, hL]
  apply ZornMatrix.ext
  · rfl
  · rfl
  · have hcoe : (sl3RToSL3C g).1 = Matrix.map g.1 (algebraMap ℝ ℂ) := rfl
    funext i
    simp [sl3CZornLinearEquiv, InfoGeometry.Physics.ThreeColorSL3ZornAction.colourFundamentalAction,
      hcoe, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · have hcof : ((sl3RToSL3C g)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1 =
        Matrix.map (g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ).1 (algebraMap ℝ ℂ) := by
      have h1 : (g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ).1 = g.1.adjugate := rfl
      have h2 : ((sl3RToSL3C g)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ).1 =
          ((sl3RToSL3C g).1).adjugate := rfl
      rw [h1, h2]
      exact (RingHom.map_adjugate (algebraMap ℝ ℂ) g.1).symm
    funext i
    simp [sl3CZornLinearEquiv, InfoGeometry.Physics.ThreeColorSL3ZornAction.colourDualAction,
      hcof, sl3DualMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-! ## Section 6: Non-Commutativity Witnesses (Trap T16) -/

theorem mat8_car_noncommutative :
    carAnnihilateMat 0 * carCreateMat 0 ≠ carCreateMat 0 * carAnnihilateMat 0 := by
  intro h
  have hadd := carAnnihilateMat_carCreateMat_anticomm 0 0
  simp only [↓reduceIte, one_smul] at hadd
  rw [← h, ← two_smul ℝ] at hadd
  have hsq : carAnnihilateMat 0 * (2 : ℝ) • (carAnnihilateMat 0 * carCreateMat 0) =
      carAnnihilateMat 0 * 1 := congrArg (carAnnihilateMat 0 * ·) hadd
  rw [Algebra.mul_smul_comm, ← Matrix.mul_assoc, carAnnihilateMat_sq, Matrix.zero_mul, smul_zero,
    Matrix.mul_one] at hsq
  have hzero : carAnnihilateMat 0 = 0 := hsq.symm
  have hent := congrFun (congrFun hzero 0) 1
  norm_num [carAnnihilateMat, leftMulMat, leftMulFin8, leftMulEnd, basisCD_repr_apply,
    ePlusCD_components, qBasis, cdToFin8, fin8ToCD, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr, Pi.single_apply] at hent

theorem cliffordQ33_noncommutative :
    CliffordAlgebra.ι Q33 (Pi.single 0 1) * CliffordAlgebra.ι Q33 (Pi.single 3 1) ≠
      CliffordAlgebra.ι Q33 (Pi.single 3 1) * CliffordAlgebra.ι Q33 (Pi.single 0 1) := by
  intro h
  have hmap := congrArg cliffordQ33ToMat8Hom h
  rw [map_mul, map_mul, cliffordQ33ToMat8Hom_gen, cliffordQ33ToMat8Hom_gen] at hmap
  have hanti := q33GenMat_anticomm (a := 0) (b := 3) (by decide)
  rw [← hmap, ← two_smul ℝ] at hanti
  have hz : q33GenMat 0 * q33GenMat 3 = 0 := (smul_eq_zero.mp hanti).resolve_left (by norm_num)
  have hmul : q33GenMat 0 * (q33GenMat 0 * q33GenMat 3) = 0 := by rw [hz, Matrix.mul_zero]
  rw [← Matrix.mul_assoc, q33GenMat_sq 0] at hmul
  simp [q33Sig] at hmul
  have hzero : q33GenMat 3 = 0 := hmul
  have hent := congrFun (congrFun hzero 0) 1
  norm_num [q33GenMat, majoranaMinusMat_eq_leftMulMat_iCD, leftMulMat, leftMulFin8, leftMulEnd,
    iCD, qBasis, cdToFin8, fin8ToCD, LinearMap.toMatrix_apply, Pi.basisFun_apply,
    Pi.basisFun_repr, Pi.single_apply] at hent

theorem mat3_real_noncommutative :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℝ, A * B ≠ B * A := by
  refine ⟨!![0, 1, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 1, 0; 0, 0, 0], ?_⟩
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_three] at h01

theorem sl3_real_noncommutative :
    ∃ g h : Matrix.SpecialLinearGroup (Fin 3) ℝ, g * h ≠ h * g := by
  let g : Matrix.SpecialLinearGroup (Fin 3) ℝ :=
    ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩
  let h : Matrix.SpecialLinearGroup (Fin 3) ℝ :=
    ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩
  refine ⟨g, h, ?_⟩
  intro heq
  have h00 : (g.1 * h.1) 0 0 = (h.1 * g.1) 0 0 :=
    congrFun (congrFun (congrArg Subtype.val heq) 0) 0
  norm_num [g, h, Matrix.mul_apply, Fin.sum_univ_three] at h00

theorem splitOctCDAut_noncommutative :
    ∃ φ ψ : SplitOctCDAut, φ * ψ ≠ ψ * φ := by
  obtain ⟨g, h, hne⟩ := sl3_real_noncommutative
  refine ⟨sl3ToSplitOctCDAut g, sl3ToSplitOctCDAut h, ?_⟩
  intro heq
  apply hne
  have heq' :
      sl3ToSplitOctCDAut_equiv_ellStabilizer.symm (g * h) =
        sl3ToSplitOctCDAut_equiv_ellStabilizer.symm (h * g) :=
    Subtype.ext (by
      change sl3ToSplitOctCDAut (g * h) = sl3ToSplitOctCDAut (h * g)
      rw [map_mul, map_mul]
      exact heq)
  exact sl3ToSplitOctCDAut_equiv_ellStabilizer.symm.injective heq'

theorem su3_complex_noncommutative :
    ∃ g h : CanonicalZornPeirceUnitaryPhase.SU3, g * h ≠ h * g := by
  let U₁ : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; -1, 0, 0; 0, 0, 1]
  let U₂ : Matrix (Fin 3) (Fin 3) ℂ := !![Complex.I, 0, 0; 0, -Complex.I, 0; 0, 0, 1]
  have hU₁ : U₁ ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [U₁, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [U₁, Matrix.det_fin_three]
  have hU₂ : U₂ ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [U₂, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [U₂, Matrix.det_fin_three]
  refine ⟨⟨U₁, hU₁⟩, ⟨U₂, hU₂⟩, ?_⟩
  intro heq
  have h01 := congrFun (congrFun (congrArg Subtype.val heq) 0) 1
  simp [U₁, U₂] at h01
  have hI : Complex.I = -Complex.I := h01.symm
  have h0 : (2 : ℂ) * Complex.I = 0 := by linear_combination hI
  exact Complex.I_ne_zero ((mul_eq_zero.mp h0).resolve_left (by norm_num))

theorem mat8_real_noncommutative :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A :=
  ⟨carAnnihilateMat 0, carCreateMat 0, mat8_car_noncommutative⟩

theorem mat3_complex_noncommutative :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℂ, A * B ≠ B * A := by
  obtain ⟨g, h, hne⟩ := su3_complex_noncommutative
  exact ⟨g.1, h.1, fun heq => hne (Subtype.ext heq)⟩

theorem mat3_ring_noncommutative {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 3) (Fin 3) R, A * B ≠ B * A := by
  refine ⟨Matrix.of ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]],
    Matrix.of ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ?_⟩
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h01

end InfoGeometry.Lie.SplitOctonionCl33G2Stabilizer

end

