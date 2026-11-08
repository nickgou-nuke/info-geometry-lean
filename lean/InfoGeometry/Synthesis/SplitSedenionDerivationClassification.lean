/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.SplitSedenionDerivationRepresentationSynthesis

/-!
# Full 14-Dimensional Split-Sedenion Derivation Classification Theorem

This module proves that for the 16-dimensional split-sedenion Cayley–Dickson
algebra `SplitSedenion ℝ` (`sedenionMul`), every real derivation `D` (`IsSedenionDerivation D`)
is diagonally lifted from a derivation of the split-octonion algebra `ZornSplitOctonion ℝ`:
$$\forall D \in \operatorname{Der}_{\mathbb{R}}(\mathbb{S}_s), \quad \exists!\, p \in \mathrm{Params} = (\mathrm{Fin}\,14 \to \mathbb{R}) : \quad D = \operatorname{sedenionG2Derivation}(p).$$
Consequently:
1. The off-diagonal derivation blocks vanish identically:
   $(D(a, 0)).2 = 0$ and $(D(0, b)).1 = 0$ for all $a, b \in \mathbb{O}_s$.
2. The two diagonal blocks coincide:
   $(D(0, b)).2 = (D(b, 0)).1$ for all $b \in \mathbb{O}_s$.
3. Every derivation of `sedenionMul` automatically commutes with `sedenionConj`
   (`IsSedenionDerivation D ↔ IsSedenionStarDerivation D`) and annihilates the
   Cayley–Dickson doubling unit `sedenionEll = (0, 1)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 800000

noncomputable section

namespace InfoGeometry.Synthesis.SplitSedenionDerivationClassification

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Synthesis.SplitSedenionDerivationRepresentationSynthesis

/-!
## Section 1: Vector-Matrix Transport of the Four Cayley–Dickson Blocks of a Sedenion Derivation
-/

/-- Conjugation involution on `VZ = ZornVectorMatrix ℝ` matching `zornConj` under `zornVectorMatrixEquiv`. -/
def vzConj (X : VZ) : VZ :=
  ⟨X.b, fun i => -X.v i, fun i => -X.w i, X.a⟩

/-- `zornVectorMatrixEquiv` intertwines `vzConj` and `zornConj`. -/
theorem zornVectorMatrixEquiv_vzConj (X : VZ) :
    zornVectorMatrixEquiv (vzConj X) = zornConj (zornVectorMatrixEquiv X) := by
  rfl

/-- `zornVectorMatrixEquiv` maps `zero : VZ` to `zornZero`. -/
theorem zornVectorMatrixEquiv_zero :
    zornVectorMatrixEquiv (zero : VZ) = zornZero := by
  rfl

/-- `zornVectorMatrixEquiv` maps `ZornVectorMatrix.neg X` to `zornSmul (-1) (zornVectorMatrixEquiv X)`. -/
theorem zornVectorMatrixEquiv_neg (X : VZ) :
    zornVectorMatrixEquiv (ZornVectorMatrix.neg X) =
      zornSmul (-1 : ℝ) (zornVectorMatrixEquiv X) := by
  ext k
  · dsimp [zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion, ZornVectorMatrix.neg, zornSmul]
    ring
  · fin_cases k <;>
      (dsimp [zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion, ZornVectorMatrix.neg, zornSmul]; ring)
  · fin_cases k <;>
      (dsimp [zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion, ZornVectorMatrix.neg, zornSmul]; ring)
  · dsimp [zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion, ZornVectorMatrix.neg, zornSmul]
    ring

/-- Coordinate readout `coordVZ X i` on `VZ = ZornVectorMatrix ℝ`. -/
def coordVZ (X : VZ) (i : Fin 8) : ℝ :=
  if i = 0 then X.a
  else if i = 1 then X.b
  else if i = 2 then X.v 0
  else if i = 3 then X.v 1
  else if i = 4 then X.v 2
  else if i = 5 then X.w 0
  else if i = 6 then X.w 1
  else X.w 2

/-- Any additive, scalar-homogeneous map `f : VZ → VZ` maps `zero` to `zero`. -/
theorem zornVZ_linear_map_zero {f : VZ → VZ}
    (hf_smul : ∀ c : ℝ, ∀ X : VZ, f (ZornVectorMatrix.smul c X) = ZornVectorMatrix.smul c (f X)) :
    f zero = zero := by
  have hzero : ZornVectorMatrix.smul (0 : ℝ) (zero : VZ) = zero := by
    apply ZornVectorMatrix.ext
    · simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · funext i; fin_cases i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · funext i; fin_cases i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  have hzero_f : ZornVectorMatrix.smul (0 : ℝ) (f zero) = zero := by
    apply ZornVectorMatrix.ext
    · simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · funext i; fin_cases i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · funext i; fin_cases i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  calc
    f zero = f (ZornVectorMatrix.smul (0 : ℝ) zero) := by rw [hzero]
    _ = ZornVectorMatrix.smul (0 : ℝ) (f zero) := hf_smul 0 zero
    _ = zero := hzero_f

/-- Any scalar-homogeneous map `f : VZ → VZ` commutes with `ZornVectorMatrix.neg`. -/
theorem zornVZ_linear_map_neg {f : VZ → VZ}
    (hf_smul : ∀ c : ℝ, ∀ X : VZ, f (ZornVectorMatrix.smul c X) = ZornVectorMatrix.smul c (f X))
    (X : VZ) :
    f (ZornVectorMatrix.neg X) = ZornVectorMatrix.neg (f X) := by
  have hneg : ∀ Y : VZ, ZornVectorMatrix.neg Y = ZornVectorMatrix.smul (-1 : ℝ) Y := by
    intro Y
    apply ZornVectorMatrix.ext
    · simp [ZornVectorMatrix.neg, ZornVectorMatrix.smul]
    · funext i; fin_cases i <;> simp [ZornVectorMatrix.neg, ZornVectorMatrix.smul]
    · funext i; fin_cases i <;> simp [ZornVectorMatrix.neg, ZornVectorMatrix.smul]
    · simp [ZornVectorMatrix.neg, ZornVectorMatrix.smul]
  rw [hneg X, hneg (f X)]
  exact hf_smul (-1 : ℝ) X

/-- Basis expansion of an arbitrary `X : VZ` in terms of `E11, E22, U 0..2, V 0..2`. -/
def vzBasisCombination (f : VZ → VZ) (X : VZ) : VZ :=
  ZornVectorMatrix.add (ZornVectorMatrix.smul X.a (f E11))
    (ZornVectorMatrix.add (ZornVectorMatrix.smul X.b (f E22))
      (ZornVectorMatrix.add (ZornVectorMatrix.smul (X.v 0) (f (U 0)))
        (ZornVectorMatrix.add (ZornVectorMatrix.smul (X.v 1) (f (U 1)))
          (ZornVectorMatrix.add (ZornVectorMatrix.smul (X.v 2) (f (U 2)))
            (ZornVectorMatrix.add (ZornVectorMatrix.smul (X.w 0) (f (V 0)))
              (ZornVectorMatrix.add (ZornVectorMatrix.smul (X.w 1) (f (V 1)))
                (ZornVectorMatrix.smul (X.w 2) (f (V 2)))))))))

theorem zornVZ_basisCombination_id (X : VZ) : vzBasisCombination id X = X := by
  apply ZornVectorMatrix.ext
  · simp [vzBasisCombination, ZornVectorMatrix.add, ZornVectorMatrix.smul,
      E11, E22, U, V, ZornVec3.basis]
  · funext i
    fin_cases i <;>
      simp [vzBasisCombination, ZornVectorMatrix.add, ZornVectorMatrix.smul,
        E11, E22, U, V, ZornVec3.basis]
  · funext i
    fin_cases i <;>
      simp [vzBasisCombination, ZornVectorMatrix.add, ZornVectorMatrix.smul,
        E11, E22, U, V, ZornVec3.basis]
  · simp [vzBasisCombination, ZornVectorMatrix.add, ZornVectorMatrix.smul,
      E11, E22, U, V, ZornVec3.basis]

theorem zornVZ_eq_zero_of_basis_eq_zero {f : VZ → VZ}
    (hf_add : ∀ X Y : VZ, f (ZornVectorMatrix.add X Y) = ZornVectorMatrix.add (f X) (f Y))
    (hf_smul : ∀ c : ℝ, ∀ X : VZ, f (ZornVectorMatrix.smul c X) = ZornVectorMatrix.smul c (f X))
    (h0 : f E11 = zero) (h1 : f E22 = zero)
    (h2 : f (U 0) = zero) (h3 : f (U 1) = zero) (h4 : f (U 2) = zero)
    (h5 : f (V 0) = zero) (h6 : f (V 1) = zero) (h7 : f (V 2) = zero)
    (X : VZ) : f X = zero := by
  have hcomb : f X = vzBasisCombination f X := by
    calc
      f X = f (vzBasisCombination id X) := congrArg f (zornVZ_basisCombination_id X).symm
      _ = vzBasisCombination f X := by
        simp only [vzBasisCombination, hf_add, hf_smul, id_eq]
  rw [hcomb]
  simp only [vzBasisCombination, h0, h1, h2, h3, h4, h5, h6, h7]
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · funext i; fin_cases i <;> simp [ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · funext i; fin_cases i <;> simp [ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · simp [ZornVectorMatrix.add, ZornVectorMatrix.smul, ZornVectorMatrix.zero]

/-!
## Section 2: Vanishing of the Lower-Left Off-Diagonal Block $f(a) = (D(a, 0)).2 = 0$
-/

private theorem mul_basis_0_1 : ZornVectorMatrix.mul E11 E22 = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_0_2 : ZornVectorMatrix.mul E11 (U 0) = ((U 0) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_0_3 : ZornVectorMatrix.mul E11 (U 1) = ((U 1) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_0_4 : ZornVectorMatrix.mul E11 (U 2) = ((U 2) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_0_5 : ZornVectorMatrix.mul E11 (V 0) = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_0_6 : ZornVectorMatrix.mul E11 (V 1) = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_0_7 : ZornVectorMatrix.mul E11 (V 2) = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_1_0 : ZornVectorMatrix.mul E22 E11 = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_1_2 : ZornVectorMatrix.mul E22 (U 0) = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_1_3 : ZornVectorMatrix.mul E22 (U 1) = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_1_5 : ZornVectorMatrix.mul E22 (V 0) = ((V 0) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_1_6 : ZornVectorMatrix.mul E22 (V 1) = ((V 1) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_2_3 : ZornVectorMatrix.mul (U 0) (U 1) = ((V 2) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_2_4 : ZornVectorMatrix.mul (U 0) (U 2) = (ZornVectorMatrix.neg (V 1) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_2_5 : ZornVectorMatrix.mul (U 0) (V 0) = (E11 : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_2_6 : ZornVectorMatrix.mul (U 0) (V 1) = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_3_4 : ZornVectorMatrix.mul (U 1) (U 2) = ((V 0) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_3_5 : ZornVectorMatrix.mul (U 1) (V 0) = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_3_6 : ZornVectorMatrix.mul (U 1) (V 1) = (E11 : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_4_5 : ZornVectorMatrix.mul (U 2) (V 0) = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_4_6 : ZornVectorMatrix.mul (U 2) (V 1) = (zero : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_5_6 : ZornVectorMatrix.mul (V 0) (V 1) = (ZornVectorMatrix.neg (U 2) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_5_7 : ZornVectorMatrix.mul (V 0) (V 2) = ((U 1) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem mul_basis_6_7 : ZornVectorMatrix.mul (V 1) (V 2) = (ZornVectorMatrix.neg (U 0) : VZ) := by
  ext k <;> try { funext k }
  all_goals try fin_cases k
  all_goals simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero,
    ZornVectorMatrix.neg, E11, E22, U, V, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

private theorem od1_basis_0_eq_zero (f : VZ → VZ)
    (hf_zero : f zero = zero)
    (hf_neg : ∀ X : VZ, f (ZornVectorMatrix.neg X) = ZornVectorMatrix.neg (f X))
    (hf_od1 : ∀ X Y : VZ,
      f (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (f X) (vzConj Y))
          (ZornVectorMatrix.mul (f Y) X)) :
    f E11 = zero := by
  have h_0_2_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 E11 (U 0))
  have h_0_2_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (U 0))
  have h_0_2_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (U 0))
  have h_0_3_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (U 1))
  have h_0_3_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (U 1))
  have h_0_4_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (U 2))
  have h_0_5_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (V 0))
  have h_0_5_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (V 0))
  have h_0_5_5 := congrArg (fun Z : VZ => coordVZ Z 5) (hf_od1 E11 (V 0))
  have h_0_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (V 1))
  have h_0_6_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (V 1))
  have h_0_7_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (V 2))
  have h_2_3_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 (U 0) (U 1))
  have h_5_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (V 0) (V 1))
  rw [mul_basis_0_2] at h_0_2_2 h_0_2_6 h_0_2_7
  rw [mul_basis_0_3] at h_0_3_3 h_0_3_7
  rw [mul_basis_0_4] at h_0_4_4
  rw [mul_basis_0_5] at h_0_5_3 h_0_5_4 h_0_5_5
  rw [mul_basis_0_6] at h_0_6_4 h_0_6_6
  rw [mul_basis_0_7] at h_0_7_7
  rw [mul_basis_2_3] at h_2_3_7
  rw [mul_basis_5_6] at h_5_6_4
  simp only [hf_zero, hf_neg] at h_0_2_2 h_0_2_6 h_0_2_7 h_0_3_3 h_0_3_7 h_0_4_4 h_0_5_3 h_0_5_4 h_0_5_5 h_0_6_4 h_0_6_6 h_0_7_7 h_2_3_7 h_5_6_4
  simp [coordVZ, vzConj, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h_0_2_2 h_0_2_6 h_0_2_7 h_0_3_3 h_0_3_7 h_0_4_4 h_0_5_3 h_0_5_4 h_0_5_5 h_0_6_4 h_0_6_6 h_0_7_7 h_2_3_7 h_5_6_4
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_0_2_2, h_0_3_3, h_0_4_4, h_0_5_5, h_0_6_6, h_0_7_7, h_2_3_7, h_5_6_4]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_3_7]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_7]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_6]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_6_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_5_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_5_3]
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_0_2_2, h_0_3_3, h_0_4_4, h_0_5_5, h_0_6_6, h_0_7_7, h_2_3_7, h_5_6_4]

private theorem od1_basis_1_eq_zero (f : VZ → VZ)
    (hf_zero : f zero = zero)
    (hf_neg : ∀ X : VZ, f (ZornVectorMatrix.neg X) = ZornVectorMatrix.neg (f X))
    (hf_od1 : ∀ X Y : VZ,
      f (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (f X) (vzConj Y))
          (ZornVectorMatrix.mul (f Y) X)) :
    f E22 = zero := by
  have h_0_1_0 := congrArg (fun Z : VZ => coordVZ Z 0) (hf_od1 E11 E22)
  have h_0_2_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 E11 (U 0))
  have h_0_3_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (U 1))
  have h_0_4_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (U 2))
  have h_0_5_5 := congrArg (fun Z : VZ => coordVZ Z 5) (hf_od1 E11 (V 0))
  have h_0_6_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (V 1))
  have h_0_7_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (V 2))
  have h_1_0_1 := congrArg (fun Z : VZ => coordVZ Z 1) (hf_od1 E22 E11)
  have h_1_2_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E22 (U 0))
  have h_1_2_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E22 (U 0))
  have h_1_3_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E22 (U 1))
  have h_1_5_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E22 (V 0))
  have h_1_5_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E22 (V 0))
  have h_1_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E22 (V 1))
  have h_2_3_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 (U 0) (U 1))
  have h_5_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (V 0) (V 1))
  rw [mul_basis_0_1] at h_0_1_0
  rw [mul_basis_0_2] at h_0_2_2
  rw [mul_basis_0_3] at h_0_3_3
  rw [mul_basis_0_4] at h_0_4_4
  rw [mul_basis_0_5] at h_0_5_5
  rw [mul_basis_0_6] at h_0_6_6
  rw [mul_basis_0_7] at h_0_7_7
  rw [mul_basis_1_0] at h_1_0_1
  rw [mul_basis_1_2] at h_1_2_6 h_1_2_7
  rw [mul_basis_1_3] at h_1_3_7
  rw [mul_basis_1_5] at h_1_5_3 h_1_5_4
  rw [mul_basis_1_6] at h_1_6_4
  rw [mul_basis_2_3] at h_2_3_7
  rw [mul_basis_5_6] at h_5_6_4
  simp only [hf_zero, hf_neg] at h_0_1_0 h_0_2_2 h_0_3_3 h_0_4_4 h_0_5_5 h_0_6_6 h_0_7_7 h_1_0_1 h_1_2_6 h_1_2_7 h_1_3_7 h_1_5_3 h_1_5_4 h_1_6_4 h_2_3_7 h_5_6_4
  simp [coordVZ, vzConj, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h_0_1_0 h_0_2_2 h_0_3_3 h_0_4_4 h_0_5_5 h_0_6_6 h_0_7_7 h_1_0_1 h_1_2_6 h_1_2_7 h_1_3_7 h_1_5_3 h_1_5_4 h_1_6_4 h_2_3_7 h_5_6_4
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_0_1_0, h_0_2_2, h_0_3_3, h_0_4_4, h_0_5_5, h_0_6_6, h_0_7_7, h_2_3_7, h_5_6_4]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_1_3_7]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_1_2_7]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_1_2_6]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_1_6_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_1_5_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_1_5_3]
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_0_2_2, h_0_3_3, h_0_4_4, h_0_5_5, h_0_6_6, h_0_7_7, h_1_0_1, h_2_3_7, h_5_6_4]

private theorem od1_basis_2_eq_zero (f : VZ → VZ)
    (hf_zero : f zero = zero)
    (hf_neg : ∀ X : VZ, f (ZornVectorMatrix.neg X) = ZornVectorMatrix.neg (f X))
    (hf_od1 : ∀ X Y : VZ,
      f (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (f X) (vzConj Y))
          (ZornVectorMatrix.mul (f Y) X)) :
    f (U 0) = zero := by
  have h_0_2_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 E11 (U 0))
  have h_0_2_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (U 0))
  have h_0_2_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (U 0))
  have h_0_2_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (U 0))
  have h_0_2_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (U 0))
  have h_0_3_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (U 1))
  have h_0_4_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (U 2))
  have h_0_5_5 := congrArg (fun Z : VZ => coordVZ Z 5) (hf_od1 E11 (V 0))
  have h_0_6_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (V 1))
  have h_0_7_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (V 2))
  have h_2_3_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 (U 0) (U 1))
  have h_2_4_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 0) (U 2))
  have h_2_5_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 (U 0) (V 0))
  have h_2_5_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 0) (V 0))
  have h_2_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 0) (V 1))
  have h_2_6_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 (U 0) (V 1))
  have h_5_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (V 0) (V 1))
  have h_6_7_1 := congrArg (fun Z : VZ => coordVZ Z 1) (hf_od1 (V 1) (V 2))
  rw [mul_basis_0_2] at h_0_2_2 h_0_2_3 h_0_2_4 h_0_2_6 h_0_2_7
  rw [mul_basis_0_3] at h_0_3_3
  rw [mul_basis_0_4] at h_0_4_4
  rw [mul_basis_0_5] at h_0_5_5
  rw [mul_basis_0_6] at h_0_6_6
  rw [mul_basis_0_7] at h_0_7_7
  rw [mul_basis_2_3] at h_2_3_7
  rw [mul_basis_2_4] at h_2_4_4
  rw [mul_basis_2_5] at h_2_5_3 h_2_5_4
  rw [mul_basis_2_6] at h_2_6_4 h_2_6_6
  rw [mul_basis_5_6] at h_5_6_4
  rw [mul_basis_6_7] at h_6_7_1
  simp only [hf_zero, hf_neg] at h_0_2_2 h_0_2_3 h_0_2_4 h_0_2_6 h_0_2_7 h_0_3_3 h_0_4_4 h_0_5_5 h_0_6_6 h_0_7_7 h_2_3_7 h_2_4_4 h_2_5_3 h_2_5_4 h_2_6_4 h_2_6_6 h_5_6_4 h_6_7_1
  simp [coordVZ, vzConj, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h_0_2_2 h_0_2_3 h_0_2_4 h_0_2_6 h_0_2_7 h_0_3_3 h_0_4_4 h_0_5_5 h_0_6_6 h_0_7_7 h_2_3_7 h_2_4_4 h_2_5_3 h_2_5_4 h_2_6_4 h_2_6_6 h_5_6_4 h_6_7_1
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_2_4_4, h_2_6_6, h_6_7_1]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_2, h_0_3_3, h_0_4_4, h_0_5_5, h_0_6_6, h_0_7_7, h_2_3_7, h_5_6_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_3]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_4]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_2_6_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_6, h_2_5_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_7, h_2_5_3]
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_6_7_1]

private theorem od1_basis_3_eq_zero (f : VZ → VZ)
    (hf_zero : f zero = zero)
    (hf_neg : ∀ X : VZ, f (ZornVectorMatrix.neg X) = ZornVectorMatrix.neg (f X))
    (hf_od1 : ∀ X Y : VZ,
      f (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (f X) (vzConj Y))
          (ZornVectorMatrix.mul (f Y) X)) :
    f (U 1) = zero := by
  have h_0_2_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 E11 (U 0))
  have h_0_2_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (U 0))
  have h_0_3_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 E11 (U 1))
  have h_0_3_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (U 1))
  have h_0_3_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (U 1))
  have h_0_4_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (U 2))
  have h_0_5_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (V 0))
  have h_0_5_5 := congrArg (fun Z : VZ => coordVZ Z 5) (hf_od1 E11 (V 0))
  have h_0_6_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (V 1))
  have h_0_7_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (V 2))
  have h_2_3_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 (U 0) (U 1))
  have h_2_5_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 (U 0) (V 0))
  have h_3_4_0 := congrArg (fun Z : VZ => coordVZ Z 0) (hf_od1 (U 1) (U 2))
  have h_3_4_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 1) (U 2))
  have h_3_5_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 (U 1) (V 0))
  have h_3_5_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 1) (V 0))
  have h_3_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 1) (V 1))
  have h_5_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (V 0) (V 1))
  have h_5_7_1 := congrArg (fun Z : VZ => coordVZ Z 1) (hf_od1 (V 0) (V 2))
  rw [mul_basis_0_2] at h_0_2_2 h_0_2_6
  rw [mul_basis_0_3] at h_0_3_2 h_0_3_3 h_0_3_4
  rw [mul_basis_0_4] at h_0_4_4
  rw [mul_basis_0_5] at h_0_5_4 h_0_5_5
  rw [mul_basis_0_6] at h_0_6_6
  rw [mul_basis_0_7] at h_0_7_7
  rw [mul_basis_2_3] at h_2_3_7
  rw [mul_basis_2_5] at h_2_5_6
  rw [mul_basis_3_4] at h_3_4_0 h_3_4_4
  rw [mul_basis_3_5] at h_3_5_3 h_3_5_4
  rw [mul_basis_3_6] at h_3_6_4
  rw [mul_basis_5_6] at h_5_6_4
  rw [mul_basis_5_7] at h_5_7_1
  simp only [hf_zero, hf_neg] at h_0_2_2 h_0_2_6 h_0_3_2 h_0_3_3 h_0_3_4 h_0_4_4 h_0_5_4 h_0_5_5 h_0_6_6 h_0_7_7 h_2_3_7 h_2_5_6 h_3_4_0 h_3_4_4 h_3_5_3 h_3_5_4 h_3_6_4 h_5_6_4 h_5_7_1
  simp [coordVZ, vzConj, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h_0_2_2 h_0_2_6 h_0_3_2 h_0_3_3 h_0_3_4 h_0_4_4 h_0_5_4 h_0_5_5 h_0_6_6 h_0_7_7 h_2_3_7 h_2_5_6 h_3_4_0 h_3_4_4 h_3_5_3 h_3_5_4 h_3_6_4 h_5_6_4 h_5_7_1
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_0_5_4, h_2_5_6, h_3_4_4]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_3_2]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_2, h_0_3_3, h_0_4_4, h_0_5_5, h_0_6_6, h_0_7_7, h_2_3_7, h_5_6_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_3_4]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_6, h_3_6_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_3_5_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_3_4_0, h_3_5_3]
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_5_7_1]

private theorem od1_basis_4_eq_zero (f : VZ → VZ)
    (hf_zero : f zero = zero)
    (hf_neg : ∀ X : VZ, f (ZornVectorMatrix.neg X) = ZornVectorMatrix.neg (f X))
    (hf_od1 : ∀ X Y : VZ,
      f (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (f X) (vzConj Y))
          (ZornVectorMatrix.mul (f Y) X)) :
    f (U 2) = zero := by
  have h_0_2_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 E11 (U 0))
  have h_0_3_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (U 1))
  have h_0_4_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 E11 (U 2))
  have h_0_4_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (U 2))
  have h_0_4_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (U 2))
  have h_0_5_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (V 0))
  have h_0_5_5 := congrArg (fun Z : VZ => coordVZ Z 5) (hf_od1 E11 (V 0))
  have h_0_6_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (V 1))
  have h_0_7_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (V 2))
  have h_2_3_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 (U 0) (U 1))
  have h_2_4_0 := congrArg (fun Z : VZ => coordVZ Z 0) (hf_od1 (U 0) (U 2))
  have h_2_5_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 (U 0) (V 0))
  have h_3_4_0 := congrArg (fun Z : VZ => coordVZ Z 0) (hf_od1 (U 1) (U 2))
  have h_3_4_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 (U 1) (U 2))
  have h_4_5_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 (U 2) (V 0))
  have h_4_5_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 2) (V 0))
  have h_4_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 2) (V 1))
  have h_5_6_1 := congrArg (fun Z : VZ => coordVZ Z 1) (hf_od1 (V 0) (V 1))
  have h_5_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (V 0) (V 1))
  rw [mul_basis_0_2] at h_0_2_2
  rw [mul_basis_0_3] at h_0_3_3
  rw [mul_basis_0_4] at h_0_4_2 h_0_4_3 h_0_4_4
  rw [mul_basis_0_5] at h_0_5_3 h_0_5_5
  rw [mul_basis_0_6] at h_0_6_6
  rw [mul_basis_0_7] at h_0_7_7
  rw [mul_basis_2_3] at h_2_3_7
  rw [mul_basis_2_4] at h_2_4_0
  rw [mul_basis_2_5] at h_2_5_7
  rw [mul_basis_3_4] at h_3_4_0 h_3_4_3
  rw [mul_basis_4_5] at h_4_5_3 h_4_5_4
  rw [mul_basis_4_6] at h_4_6_4
  rw [mul_basis_5_6] at h_5_6_1 h_5_6_4
  simp only [hf_zero, hf_neg] at h_0_2_2 h_0_3_3 h_0_4_2 h_0_4_3 h_0_4_4 h_0_5_3 h_0_5_5 h_0_6_6 h_0_7_7 h_2_3_7 h_2_4_0 h_2_5_7 h_3_4_0 h_3_4_3 h_4_5_3 h_4_5_4 h_4_6_4 h_5_6_1 h_5_6_4
  simp [coordVZ, vzConj, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h_0_2_2 h_0_3_3 h_0_4_2 h_0_4_3 h_0_4_4 h_0_5_3 h_0_5_5 h_0_6_6 h_0_7_7 h_2_3_7 h_2_4_0 h_2_5_7 h_3_4_0 h_3_4_3 h_4_5_3 h_4_5_4 h_4_6_4 h_5_6_1 h_5_6_4
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_0_5_3, h_2_5_7, h_3_4_3]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_4_2]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_4_3]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_2, h_0_3_3, h_0_4_4, h_0_5_5, h_0_6_6, h_0_7_7, h_2_3_7, h_5_6_4]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_2_4_0, h_4_6_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_3_4_0, h_4_5_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_4_5_3]
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_5_6_1]

private theorem od1_basis_5_eq_zero (f : VZ → VZ)
    (hf_zero : f zero = zero)
    (hf_neg : ∀ X : VZ, f (ZornVectorMatrix.neg X) = ZornVectorMatrix.neg (f X))
    (hf_od1 : ∀ X Y : VZ,
      f (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (f X) (vzConj Y))
          (ZornVectorMatrix.mul (f Y) X)) :
    f (V 0) = zero := by
  have h_0_2_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 E11 (U 0))
  have h_0_3_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (U 1))
  have h_0_4_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (U 2))
  have h_0_5_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (V 0))
  have h_0_5_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (V 0))
  have h_0_5_5 := congrArg (fun Z : VZ => coordVZ Z 5) (hf_od1 E11 (V 0))
  have h_0_5_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (V 0))
  have h_0_5_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (V 0))
  have h_0_6_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (V 1))
  have h_0_7_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (V 2))
  have h_2_3_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 (U 0) (U 1))
  have h_2_5_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 (U 0) (V 0))
  have h_2_5_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 (U 0) (V 0))
  have h_3_4_0 := congrArg (fun Z : VZ => coordVZ Z 0) (hf_od1 (U 1) (U 2))
  have h_3_4_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 (U 1) (U 2))
  have h_4_5_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 2) (V 0))
  have h_5_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (V 0) (V 1))
  have h_5_6_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 (V 0) (V 1))
  rw [mul_basis_0_2] at h_0_2_2
  rw [mul_basis_0_3] at h_0_3_3
  rw [mul_basis_0_4] at h_0_4_4
  rw [mul_basis_0_5] at h_0_5_3 h_0_5_4 h_0_5_5 h_0_5_6 h_0_5_7
  rw [mul_basis_0_6] at h_0_6_6
  rw [mul_basis_0_7] at h_0_7_7
  rw [mul_basis_2_3] at h_2_3_7
  rw [mul_basis_2_5] at h_2_5_6 h_2_5_7
  rw [mul_basis_3_4] at h_3_4_0 h_3_4_2
  rw [mul_basis_4_5] at h_4_5_4
  rw [mul_basis_5_6] at h_5_6_4 h_5_6_6
  simp only [hf_zero, hf_neg] at h_0_2_2 h_0_3_3 h_0_4_4 h_0_5_3 h_0_5_4 h_0_5_5 h_0_5_6 h_0_5_7 h_0_6_6 h_0_7_7 h_2_3_7 h_2_5_6 h_2_5_7 h_3_4_0 h_3_4_2 h_4_5_4 h_5_6_4 h_5_6_6
  simp [coordVZ, vzConj, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h_0_2_2 h_0_3_3 h_0_4_4 h_0_5_3 h_0_5_4 h_0_5_5 h_0_5_6 h_0_5_7 h_0_6_6 h_0_7_7 h_2_3_7 h_2_5_6 h_2_5_7 h_3_4_0 h_3_4_2 h_4_5_4 h_5_6_4 h_5_6_6
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_3_4_0]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_3_4_2]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_5_3, h_2_5_7]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_5_4, h_2_5_6]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_2, h_0_3_3, h_0_4_4, h_0_5_5, h_0_6_6, h_0_7_7, h_2_3_7, h_5_6_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_5_6]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_5_7]
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_3_4_0, h_4_5_4, h_5_6_6]

private theorem od1_basis_6_eq_zero (f : VZ → VZ)
    (hf_zero : f zero = zero)
    (hf_neg : ∀ X : VZ, f (ZornVectorMatrix.neg X) = ZornVectorMatrix.neg (f X))
    (hf_od1 : ∀ X Y : VZ,
      f (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (f X) (vzConj Y))
          (ZornVectorMatrix.mul (f Y) X)) :
    f (V 1) = zero := by
  have h_0_2_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 E11 (U 0))
  have h_0_3_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (U 1))
  have h_0_4_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (U 2))
  have h_0_5_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (V 0))
  have h_0_5_5 := congrArg (fun Z : VZ => coordVZ Z 5) (hf_od1 E11 (V 0))
  have h_0_6_5 := congrArg (fun Z : VZ => coordVZ Z 5) (hf_od1 E11 (V 1))
  have h_0_6_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (V 1))
  have h_0_6_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (V 1))
  have h_0_7_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (V 2))
  have h_2_3_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 (U 0) (U 1))
  have h_2_4_0 := congrArg (fun Z : VZ => coordVZ Z 0) (hf_od1 (U 0) (U 2))
  have h_2_4_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 (U 0) (U 2))
  have h_2_4_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 (U 0) (U 2))
  have h_2_5_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 (U 0) (V 0))
  have h_2_6_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 (U 0) (V 1))
  have h_3_4_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 (U 1) (U 2))
  have h_4_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 2) (V 1))
  have h_5_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (V 0) (V 1))
  have h_5_6_5 := congrArg (fun Z : VZ => coordVZ Z 5) (hf_od1 (V 0) (V 1))
  have h_6_7_1 := congrArg (fun Z : VZ => coordVZ Z 1) (hf_od1 (V 1) (V 2))
  rw [mul_basis_0_2] at h_0_2_2
  rw [mul_basis_0_3] at h_0_3_3
  rw [mul_basis_0_4] at h_0_4_4
  rw [mul_basis_0_5] at h_0_5_3 h_0_5_5
  rw [mul_basis_0_6] at h_0_6_5 h_0_6_6 h_0_6_7
  rw [mul_basis_0_7] at h_0_7_7
  rw [mul_basis_2_3] at h_2_3_7
  rw [mul_basis_2_4] at h_2_4_0 h_2_4_2 h_2_4_3
  rw [mul_basis_2_5] at h_2_5_7
  rw [mul_basis_2_6] at h_2_6_6
  rw [mul_basis_3_4] at h_3_4_3
  rw [mul_basis_4_6] at h_4_6_4
  rw [mul_basis_5_6] at h_5_6_4 h_5_6_5
  rw [mul_basis_6_7] at h_6_7_1
  simp only [hf_zero, hf_neg] at h_0_2_2 h_0_3_3 h_0_4_4 h_0_5_3 h_0_5_5 h_0_6_5 h_0_6_6 h_0_6_7 h_0_7_7 h_2_3_7 h_2_4_0 h_2_4_2 h_2_4_3 h_2_5_7 h_2_6_6 h_3_4_3 h_4_6_4 h_5_6_4 h_5_6_5 h_6_7_1
  simp [coordVZ, vzConj, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h_0_2_2 h_0_3_3 h_0_4_4 h_0_5_3 h_0_5_5 h_0_6_5 h_0_6_6 h_0_6_7 h_0_7_7 h_2_3_7 h_2_4_0 h_2_4_2 h_2_4_3 h_2_5_7 h_2_6_6 h_3_4_3 h_4_6_4 h_5_6_4 h_5_6_5 h_6_7_1
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_2_4_0]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_5_3, h_2_4_2, h_2_5_7, h_3_4_3]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_2_4_3]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_2_6_6, h_6_7_1]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_6_5]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_2, h_0_3_3, h_0_4_4, h_0_5_5, h_0_6_6, h_0_7_7, h_2_3_7, h_5_6_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_6_7]
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_2_4_0, h_4_6_4, h_5_6_5]

private theorem od1_basis_7_eq_zero (f : VZ → VZ)
    (hf_zero : f zero = zero)
    (hf_neg : ∀ X : VZ, f (ZornVectorMatrix.neg X) = ZornVectorMatrix.neg (f X))
    (hf_od1 : ∀ X Y : VZ,
      f (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (f X) (vzConj Y))
          (ZornVectorMatrix.mul (f Y) X)) :
    f (V 2) = zero := by
  have h_0_2_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 E11 (U 0))
  have h_0_2_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (U 0))
  have h_0_3_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 E11 (U 1))
  have h_0_4_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (U 2))
  have h_0_5_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 E11 (V 0))
  have h_0_5_5 := congrArg (fun Z : VZ => coordVZ Z 5) (hf_od1 E11 (V 0))
  have h_0_6_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (V 1))
  have h_0_7_5 := congrArg (fun Z : VZ => coordVZ Z 5) (hf_od1 E11 (V 2))
  have h_0_7_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 E11 (V 2))
  have h_0_7_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 E11 (V 2))
  have h_2_3_0 := congrArg (fun Z : VZ => coordVZ Z 0) (hf_od1 (U 0) (U 1))
  have h_2_3_2 := congrArg (fun Z : VZ => coordVZ Z 2) (hf_od1 (U 0) (U 1))
  have h_2_3_3 := congrArg (fun Z : VZ => coordVZ Z 3) (hf_od1 (U 0) (U 1))
  have h_2_3_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 0) (U 1))
  have h_2_3_7 := congrArg (fun Z : VZ => coordVZ Z 7) (hf_od1 (U 0) (U 1))
  have h_2_4_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 0) (U 2))
  have h_2_5_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 (U 0) (V 0))
  have h_2_6_6 := congrArg (fun Z : VZ => coordVZ Z 6) (hf_od1 (U 0) (V 1))
  have h_3_4_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 1) (U 2))
  have h_3_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (U 1) (V 1))
  have h_5_6_4 := congrArg (fun Z : VZ => coordVZ Z 4) (hf_od1 (V 0) (V 1))
  have h_5_7_5 := congrArg (fun Z : VZ => coordVZ Z 5) (hf_od1 (V 0) (V 2))
  have h_6_7_1 := congrArg (fun Z : VZ => coordVZ Z 1) (hf_od1 (V 1) (V 2))
  rw [mul_basis_0_2] at h_0_2_2 h_0_2_6
  rw [mul_basis_0_3] at h_0_3_3
  rw [mul_basis_0_4] at h_0_4_4
  rw [mul_basis_0_5] at h_0_5_4 h_0_5_5
  rw [mul_basis_0_6] at h_0_6_6
  rw [mul_basis_0_7] at h_0_7_5 h_0_7_6 h_0_7_7
  rw [mul_basis_2_3] at h_2_3_0 h_2_3_2 h_2_3_3 h_2_3_4 h_2_3_7
  rw [mul_basis_2_4] at h_2_4_4
  rw [mul_basis_2_5] at h_2_5_6
  rw [mul_basis_2_6] at h_2_6_6
  rw [mul_basis_3_4] at h_3_4_4
  rw [mul_basis_3_6] at h_3_6_4
  rw [mul_basis_5_6] at h_5_6_4
  rw [mul_basis_5_7] at h_5_7_5
  rw [mul_basis_6_7] at h_6_7_1
  simp only [hf_zero, hf_neg] at h_0_2_2 h_0_2_6 h_0_3_3 h_0_4_4 h_0_5_4 h_0_5_5 h_0_6_6 h_0_7_5 h_0_7_6 h_0_7_7 h_2_3_0 h_2_3_2 h_2_3_3 h_2_3_4 h_2_3_7 h_2_4_4 h_2_5_6 h_2_6_6 h_3_4_4 h_3_6_4 h_5_6_4 h_5_7_5 h_6_7_1
  simp [coordVZ, vzConj, E11, E22, U, V, ZornVectorMatrix.mul,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVectorMatrix.neg,
    ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h_0_2_2 h_0_2_6 h_0_3_3 h_0_4_4 h_0_5_4 h_0_5_5 h_0_6_6 h_0_7_5 h_0_7_6 h_0_7_7 h_2_3_0 h_2_3_2 h_2_3_3 h_2_3_4 h_2_3_7 h_2_4_4 h_2_5_6 h_2_6_6 h_3_4_4 h_3_6_4 h_5_6_4 h_5_7_5 h_6_7_1
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_2_3_0]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_5_4, h_2_3_2, h_2_5_6, h_3_4_4]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_2_3_3, h_2_4_4, h_2_6_6, h_6_7_1]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_2_3_4]
  · funext i
    fin_cases i
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_7_5]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_7_6]
    · simp [ZornVectorMatrix.zero, E11, E22, U, V]
      linarith only [h_0_2_2, h_0_3_3, h_0_4_4, h_0_5_5, h_0_6_6, h_0_7_7, h_2_3_7, h_5_6_4]
  · simp [ZornVectorMatrix.zero, E11, E22, U, V]
    linarith only [h_0_2_6, h_3_6_4, h_5_7_5]

/-- Any linear map `f : VZ → VZ` satisfying the twisted lower-left derivation identity
`f (X * Y) = f X * conj Y + f Y * X` vanishes identically on `VZ`. -/
theorem od1_linear_eq_zero (f : VZ → VZ)
    (hf_add : ∀ X Y : VZ, f (ZornVectorMatrix.add X Y) = ZornVectorMatrix.add (f X) (f Y))
    (hf_smul : ∀ c : ℝ, ∀ X : VZ, f (ZornVectorMatrix.smul c X) = ZornVectorMatrix.smul c (f X))
    (hf_od1 : ∀ X Y : VZ,
      f (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (f X) (vzConj Y))
          (ZornVectorMatrix.mul (f Y) X))
    (X : VZ) : f X = zero := by
  have hf_zero : f zero = zero := zornVZ_linear_map_zero hf_smul
  have hf_neg : ∀ Y : VZ, f (ZornVectorMatrix.neg Y) = ZornVectorMatrix.neg (f Y) :=
    zornVZ_linear_map_neg hf_smul
  exact zornVZ_eq_zero_of_basis_eq_zero hf_add hf_smul
    (od1_basis_0_eq_zero f hf_zero hf_neg hf_od1)
    (od1_basis_1_eq_zero f hf_zero hf_neg hf_od1)
    (od1_basis_2_eq_zero f hf_zero hf_neg hf_od1)
    (od1_basis_3_eq_zero f hf_zero hf_neg hf_od1)
    (od1_basis_4_eq_zero f hf_zero hf_neg hf_od1)
    (od1_basis_5_eq_zero f hf_zero hf_neg hf_od1)
    (od1_basis_6_eq_zero f hf_zero hf_neg hf_od1)
    (od1_basis_7_eq_zero f hf_zero hf_neg hf_od1) X

/-!
## Section 3: Vanishing of the Upper-Right Block $g(b) = (D(0, b)).1 = 0$ and Equality of Diagonal Blocks
-/

/-- If `c : VZ` satisfies `(Y * X) * c = X * (Y * c)` for all `X, Y : VZ`, then `c = zero`. -/
theorem zornVZ_right_antiassociator_eq_zero (c : VZ)
    (hc : ∀ X Y : VZ,
      ZornVectorMatrix.mul (ZornVectorMatrix.mul Y X) c =
        ZornVectorMatrix.mul X (ZornVectorMatrix.mul Y c)) :
    c = zero := by
  have h1 := congrArg (fun Z : VZ => coordVZ Z 0) (hc (U 0) E11)
  have h2 := congrArg (fun Z : VZ => coordVZ Z 2) (hc (U 0) E11)
  have h3 := congrArg (fun Z : VZ => coordVZ Z 0) (hc (U 1) E11)
  have h4 := congrArg (fun Z : VZ => coordVZ Z 0) (hc (U 2) E11)
  have h5 := congrArg (fun Z : VZ => coordVZ Z 1) (hc (V 0) E11)
  have h6 := congrArg (fun Z : VZ => coordVZ Z 5) (hc (V 0) E11)
  have h7 := congrArg (fun Z : VZ => coordVZ Z 1) (hc (V 1) E11)
  have h8 := congrArg (fun Z : VZ => coordVZ Z 1) (hc (V 2) E11)
  simp [coordVZ, E11, U, V, ZornVectorMatrix.mul, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h1 h2 h3 h4 h5 h6 h7 h8
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.zero]; linarith only [h6]
  · funext i; fin_cases i
    · simp [ZornVectorMatrix.zero]; linarith only [h5]
    · simp [ZornVectorMatrix.zero]; linarith only [h7]
    · simp [ZornVectorMatrix.zero]; linarith only [h8]
  · funext i; fin_cases i
    · simp [ZornVectorMatrix.zero]; linarith only [h1]
    · simp [ZornVectorMatrix.zero]; linarith only [h3]
    · simp [ZornVectorMatrix.zero]; linarith only [h4]
  · simp [ZornVectorMatrix.zero]; linarith only [h2]

/-- If `c : VZ` is trace-zero (`c.a + c.b = 0`) and lies in the left nucleus
(`c * (Y * X) = (c * Y) * X` for all `X, Y : VZ`), then `c = zero`. -/
theorem zornVZ_left_nucleus_trace_zero_eq_zero (c : VZ)
    (htr : c.a + c.b = 0)
    (hc : ∀ X Y : VZ,
      ZornVectorMatrix.mul c (ZornVectorMatrix.mul Y X) =
        ZornVectorMatrix.mul (ZornVectorMatrix.mul c Y) X) :
    c = zero := by
  have h1 := congrArg (fun Z : VZ => coordVZ Z 0) (hc (U 1) (U 0))
  have h2 := congrArg (fun Z : VZ => coordVZ Z 2) (hc (U 1) (U 0))
  have h3 := congrArg (fun Z : VZ => coordVZ Z 3) (hc (U 1) (U 0))
  have h4 := congrArg (fun Z : VZ => coordVZ Z 7) (hc (U 1) (U 0))
  have h5 := congrArg (fun Z : VZ => coordVZ Z 0) (hc (U 2) (U 1))
  have h6 := congrArg (fun Z : VZ => coordVZ Z 3) (hc (U 2) (U 1))
  have h7 := congrArg (fun Z : VZ => coordVZ Z 0) (hc (U 2) (U 0))
  simp [coordVZ, U, ZornVectorMatrix.mul, ZornVec3.basis,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at h1 h2 h3 h4 h5 h6 h7
  apply ZornVectorMatrix.ext
  · simp [ZornVectorMatrix.zero]; linarith only [htr, h4]
  · funext i; fin_cases i
    · simp [ZornVectorMatrix.zero]; linarith only [h5]
    · simp [ZornVectorMatrix.zero]; linarith only [h7]
    · simp [ZornVectorMatrix.zero]; linarith only [h1]
  · funext i; fin_cases i
    · simp [ZornVectorMatrix.zero]; linarith only [h3]
    · simp [ZornVectorMatrix.zero]; linarith only [h2]
    · simp [ZornVectorMatrix.zero]; linarith only [h6]
  · simp [ZornVectorMatrix.zero]; linarith only [htr, h4]

/-!
## Section 4: Block Analysis of an Arbitrary Split-Sedenion Derivation
-/

/-- Lower-left block `fVZ D X = zornVectorMatrixEquiv.symm (D (zornVectorMatrixEquiv X, 0)).2`. -/
def fVZ (D : SplitSedenion ℝ → SplitSedenion ℝ) (X : VZ) : VZ :=
  zornVectorMatrixEquiv.symm (D (zornVectorMatrixEquiv X, zornZero)).2

/-- Upper-left block `dVZ D X = zornVectorMatrixEquiv.symm (D (zornVectorMatrixEquiv X, 0)).1`. -/
def dVZ (D : SplitSedenion ℝ → SplitSedenion ℝ) (X : VZ) : VZ :=
  zornVectorMatrixEquiv.symm (D (zornVectorMatrixEquiv X, zornZero)).1

/-- Upper-right block `gVZ D X = zornVectorMatrixEquiv.symm (D (0, zornVectorMatrixEquiv X)).1`. -/
def gVZ (D : SplitSedenion ℝ → SplitSedenion ℝ) (X : VZ) : VZ :=
  zornVectorMatrixEquiv.symm (D (zornZero, zornVectorMatrixEquiv X)).1

/-- Lower-right block `hVZ D X = zornVectorMatrixEquiv.symm (D (0, zornVectorMatrixEquiv X)).2`. -/
def hVZ (D : SplitSedenion ℝ → SplitSedenion ℝ) (X : VZ) : VZ :=
  zornVectorMatrixEquiv.symm (D (zornZero, zornVectorMatrixEquiv X)).2

theorem zornVectorMatrixEquiv_symm_add (x y : ZornSplitOctonion ℝ) :
    zornVectorMatrixEquiv.symm (zornAdd x y) =
      ZornVectorMatrix.add (zornVectorMatrixEquiv.symm x) (zornVectorMatrixEquiv.symm y) := by
  apply zornVectorMatrixEquiv.injective
  rw [zornVectorMatrixEquiv.apply_symm_apply, zornVectorMatrixEquiv_add,
    zornVectorMatrixEquiv.apply_symm_apply, zornVectorMatrixEquiv.apply_symm_apply]

theorem zornVectorMatrixEquiv_symm_smul (c : ℝ) (x : ZornSplitOctonion ℝ) :
    zornVectorMatrixEquiv.symm (zornSmul c x) =
      ZornVectorMatrix.smul c (zornVectorMatrixEquiv.symm x) := by
  apply zornVectorMatrixEquiv.injective
  rw [zornVectorMatrixEquiv.apply_symm_apply, zornVectorMatrixEquiv_smul,
    zornVectorMatrixEquiv.apply_symm_apply]

theorem zornVectorMatrixEquiv_symm_mul (x y : ZornSplitOctonion ℝ) :
    zornVectorMatrixEquiv.symm (zornMul x y) =
      ZornVectorMatrix.mul (zornVectorMatrixEquiv.symm x) (zornVectorMatrixEquiv.symm y) := by
  apply zornVectorMatrixEquiv.injective
  rw [zornVectorMatrixEquiv.apply_symm_apply, zornVectorMatrixEquiv_mul,
    zornVectorMatrixEquiv.apply_symm_apply, zornVectorMatrixEquiv.apply_symm_apply]

theorem zornVectorMatrixEquiv_symm_conj (x : ZornSplitOctonion ℝ) :
    zornVectorMatrixEquiv.symm (zornConj x) = vzConj (zornVectorMatrixEquiv.symm x) := by
  rfl

theorem zornAdd_zornZero_right (x : ZornSplitOctonion ℝ) :
    zornAdd x zornZero = x := by
  ext k
  · dsimp [zornAdd, zornZero]; ring
  · fin_cases k <;> (dsimp [zornAdd, zornZero]; ring)
  · fin_cases k <;> (dsimp [zornAdd, zornZero]; ring)
  · dsimp [zornAdd, zornZero]; ring

theorem zornAdd_zornZero_left (x : ZornSplitOctonion ℝ) :
    zornAdd zornZero x = x := by
  ext k
  · dsimp [zornAdd, zornZero]; ring
  · fin_cases k <;> (dsimp [zornAdd, zornZero]; ring)
  · fin_cases k <;> (dsimp [zornAdd, zornZero]; ring)
  · dsimp [zornAdd, zornZero]; ring

theorem zornSmul_zornZero (c : ℝ) :
    zornSmul c (zornZero : ZornSplitOctonion ℝ) = zornZero := by
  ext k
  · dsimp [zornSmul, zornZero]; ring
  · fin_cases k <;> (dsimp [zornSmul, zornZero]; ring)
  · fin_cases k <;> (dsimp [zornSmul, zornZero]; ring)
  · dsimp [zornSmul, zornZero]; ring

theorem zornMul_zornZero_right (x : ZornSplitOctonion ℝ) :
    zornMul x zornZero = zornZero := by
  ext k
  · dsimp [zornMul, zornZero, vec3Dot]; ring
  · fin_cases k <;> (dsimp [zornMul, zornZero, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornMul, zornZero, vec3Cross]; ring)
  · dsimp [zornMul, zornZero, vec3Dot]; ring

theorem zornMul_zornZero_left (x : ZornSplitOctonion ℝ) :
    zornMul zornZero x = zornZero := by
  ext k
  · dsimp [zornMul, zornZero, vec3Dot]; ring
  · fin_cases k <;> (dsimp [zornMul, zornZero, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornMul, zornZero, vec3Cross]; ring)
  · dsimp [zornMul, zornZero, vec3Dot]; ring

theorem zornConj_zornZero :
    zornConj (zornZero : ZornSplitOctonion ℝ) = zornZero := by
  ext k
  · dsimp [zornConj, zornZero]
  · fin_cases k <;> (dsimp [zornConj, zornZero]; ring)
  · fin_cases k <;> (dsimp [zornConj, zornZero]; ring)
  · dsimp [zornConj, zornZero]

/-- Step 1: For any sedenion derivation `D`, the lower-left block `(D (a, 0)).2` vanishes identically. -/
theorem sedenionDerivation_fst_sheet_snd_eq_zero
    {D : SplitSedenion ℝ → SplitSedenion ℝ} (hD : IsSedenionDerivation D)
    (a : ZornSplitOctonion ℝ) :
    (D (a, zornZero)).2 = zornZero := by
  rcases hD with ⟨hD_add, hD_smul, hD_mul⟩
  have hf_add : ∀ X Y : VZ, fVZ D (ZornVectorMatrix.add X Y) = ZornVectorMatrix.add (fVZ D X) (fVZ D Y) := by
    intro X Y
    dsimp [fVZ]
    rw [zornVectorMatrixEquiv_add]
    have hpair : (zornAdd (zornVectorMatrixEquiv X) (zornVectorMatrixEquiv Y), (zornZero : ZornSplitOctonion ℝ)) =
        sedenionAdd (zornVectorMatrixEquiv X, zornZero) (zornVectorMatrixEquiv Y, zornZero) := by
      apply Prod.ext
      · rfl
      · exact (zornAdd_zornZero_right zornZero).symm
    rw [hpair, hD_add]
    exact zornVectorMatrixEquiv_symm_add _ _
  have hf_smul : ∀ c : ℝ, ∀ X : VZ, fVZ D (ZornVectorMatrix.smul c X) = ZornVectorMatrix.smul c (fVZ D X) := by
    intro c X
    dsimp [fVZ]
    rw [zornVectorMatrixEquiv_smul]
    have hpair : (zornSmul c (zornVectorMatrixEquiv X), (zornZero : ZornSplitOctonion ℝ)) =
        sedenionSmul c (zornVectorMatrixEquiv X, zornZero) := by
      apply Prod.ext
      · rfl
      · exact (zornSmul_zornZero c).symm
    rw [hpair, hD_smul]
    exact zornVectorMatrixEquiv_symm_smul c _
  have hf_od1 : ∀ X Y : VZ,
      fVZ D (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (fVZ D X) (vzConj Y))
          (ZornVectorMatrix.mul (fVZ D Y) X) := by
    intro X Y
    dsimp [fVZ]
    rw [zornVectorMatrixEquiv_mul]
    have hprod : (zornMul (zornVectorMatrixEquiv X) (zornVectorMatrixEquiv Y), (zornZero : ZornSplitOctonion ℝ)) =
        sedenionMul (zornVectorMatrixEquiv X, zornZero) (zornVectorMatrixEquiv Y, zornZero) := by
      apply Prod.ext
      · dsimp [sedenionMul]
        rw [zornConj_zornZero, zornMul_zornZero_left, zornAdd_zornZero_right]
      · dsimp [sedenionMul]
        rw [zornMul_zornZero_left, zornMul_zornZero_left, zornAdd_zornZero_right]
    rw [hprod, hD_mul]
    dsimp [sedenionAdd, sedenionMul]
    simp only [zornConj_zornZero, zornMul_zornZero_left, zornMul_zornZero_right,
      zornAdd_zornZero_left, zornAdd_zornZero_right]
    rw [zornVectorMatrixEquiv_symm_add, zornVectorMatrixEquiv_symm_mul, zornVectorMatrixEquiv_symm_mul,
      zornVectorMatrixEquiv_symm_conj, zornVectorMatrixEquiv.symm_apply_apply, zornVectorMatrixEquiv.symm_apply_apply]
  have hzero := od1_linear_eq_zero (fVZ D) hf_add hf_smul hf_od1 (zornVectorMatrixEquiv.symm a)
  dsimp [fVZ] at hzero
  rw [zornVectorMatrixEquiv.apply_symm_apply] at hzero
  have h := congrArg zornVectorMatrixEquiv hzero
  rw [zornVectorMatrixEquiv.apply_symm_apply] at h
  exact h

/-- Step 2: For any sedenion derivation `D`, the upper-right block `(D (0, b)).1` vanishes identically. -/
theorem sedenionDerivation_snd_sheet_fst_eq_zero
    {D : SplitSedenion ℝ → SplitSedenion ℝ} (hD : IsSedenionDerivation D)
    (b : ZornSplitOctonion ℝ) :
    (D (zornZero, b)).1 = zornZero := by
  have hf_zero := sedenionDerivation_fst_sheet_snd_eq_zero hD
  rcases hD with ⟨_, _, hD_mul⟩
  -- For any a, b: (a, 0) * (0, b) = (0, b * a), so first component of D((a, 0) * (0, b)) gives g(b * a) = a * g(b)
  have hg_rel : ∀ a y : ZornSplitOctonion ℝ,
      (D (zornZero, zornMul y a)).1 = zornMul a (D (zornZero, y)).1 := by
    intro a y
    have hprod : sedenionMul (a, zornZero) (zornZero, y) = (zornZero, zornMul y a) := by
      apply Prod.ext
      · dsimp [sedenionMul]
        rw [zornMul_zornZero_right, zornMul_zornZero_right, zornAdd_zornZero_right]
      · dsimp [sedenionMul]
        rw [zornConj_zornZero, zornMul_zornZero_left, zornAdd_zornZero_right]
    have hleib := congrArg Prod.fst (hD_mul (a, zornZero) (zornZero, y))
    rw [hprod] at hleib
    dsimp [sedenionAdd, sedenionMul] at hleib
    simp only [hf_zero a, zornConj_zornZero, zornMul_zornZero_left, zornMul_zornZero_right,
      zornAdd_zornZero_left, zornAdd_zornZero_right] at hleib
    exact hleib
  have h_one_mul : ∀ a : ZornSplitOctonion ℝ, zornMul zornOne a = a := by
    intro a; ext k
    · dsimp [zornMul, zornOne, vec3Dot]; ring
    · fin_cases k <;> (dsimp [zornMul, zornOne, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornMul, zornOne, vec3Cross]; ring)
    · dsimp [zornMul, zornOne, vec3Dot]; ring
  -- Hence (D (0, a)).1 = a * (D (0, 1)).1
  have hg_one : ∀ a : ZornSplitOctonion ℝ,
      (D (zornZero, a)).1 = zornMul a (D (zornZero, zornOne)).1 := by
    intro a
    have h := hg_rel a zornOne
    rw [h_one_mul a] at h
    exact h
  -- Consequently c = zornVectorMatrixEquiv.symm (D (0, 1)).1 satisfies (Y * X) * c = X * (Y * c)
  let c : VZ := zornVectorMatrixEquiv.symm (D (zornZero, zornOne)).1
  have hc : ∀ X Y : VZ,
      ZornVectorMatrix.mul (ZornVectorMatrix.mul Y X) c =
        ZornVectorMatrix.mul X (ZornVectorMatrix.mul Y c) := by
    intro X Y
    have h := hg_rel (zornVectorMatrixEquiv X) (zornVectorMatrixEquiv Y)
    rw [hg_one (zornMul (zornVectorMatrixEquiv Y) (zornVectorMatrixEquiv X)),
      hg_one (zornVectorMatrixEquiv Y)] at h
    have hsymm := congrArg zornVectorMatrixEquiv.symm h
    rw [zornVectorMatrixEquiv_symm_mul, zornVectorMatrixEquiv_symm_mul,
      zornVectorMatrixEquiv_symm_mul, zornVectorMatrixEquiv_symm_mul,
      zornVectorMatrixEquiv.symm_apply_apply, zornVectorMatrixEquiv.symm_apply_apply] at hsymm
    exact hsymm
  have hc_zero : c = zero := zornVZ_right_antiassociator_eq_zero c hc
  have hd_one : (D (zornZero, zornOne)).1 = zornZero := by
    have h := congrArg zornVectorMatrixEquiv hc_zero
    dsimp [c] at h
    rw [zornVectorMatrixEquiv.apply_symm_apply] at h
    exact h
  rw [hg_one b, hd_one, zornMul_zornZero_right]

/-- Step 3: For any sedenion derivation `D`, the upper-left block `d(a) = (D(a, 0)).1` is a derivation
of `zornMul` on `ZornSplitOctonion ℝ`. -/
theorem sedenionDerivation_fst_sheet_fst_leibniz
    {D : SplitSedenion ℝ → SplitSedenion ℝ} (hD : IsSedenionDerivation D)
    (a b : ZornSplitOctonion ℝ) :
    (D (zornMul a b, zornZero)).1 =
      zornAdd (zornMul (D (a, zornZero)).1 b) (zornMul a (D (b, zornZero)).1) := by
  rcases hD with ⟨_, _, hD_mul⟩
  have hprod : sedenionMul (a, zornZero) (b, zornZero) = (zornMul a b, zornZero) := by
    apply Prod.ext
    · dsimp [sedenionMul]
      rw [zornConj_zornZero, zornMul_zornZero_left, zornAdd_zornZero_right]
    · dsimp [sedenionMul]
      rw [zornMul_zornZero_left, zornMul_zornZero_left, zornAdd_zornZero_right]
  have hleib := congrArg Prod.fst (hD_mul (a, zornZero) (b, zornZero))
  rw [hprod] at hleib
  dsimp [sedenionAdd, sedenionMul] at hleib
  simp only [zornConj_zornZero, zornMul_zornZero_left, zornMul_zornZero_right,
    zornAdd_zornZero_left, zornAdd_zornZero_right] at hleib
  exact hleib

/-- Step 4: For any sedenion derivation `D`, the two diagonal blocks coincide:
`(D (0, b)).2 = (D (b, 0)).1` for all `b : ZornSplitOctonion ℝ`. -/
theorem sedenionDerivation_snd_sheet_snd_eq_fst_sheet_fst
    {D : SplitSedenion ℝ → SplitSedenion ℝ} (hD : IsSedenionDerivation D)
    (b : ZornSplitOctonion ℝ) :
    (D (zornZero, b)).2 = (D (b, zornZero)).1 := by
  have hd_leib := sedenionDerivation_fst_sheet_fst_leibniz hD
  have hf_zero := sedenionDerivation_fst_sheet_snd_eq_zero hD
  have hg_zero := sedenionDerivation_snd_sheet_fst_eq_zero hD
  rcases hD with ⟨_, _, hD_mul⟩
  -- Second component of D((a, 0) * (0, y)) = D(0, y * a) gives h(y * a) = h(y) * a + y * d(a)
  have hh_rel : ∀ a y : ZornSplitOctonion ℝ,
      (D (zornZero, zornMul y a)).2 =
        zornAdd (zornMul (D (zornZero, y)).2 a) (zornMul y (D (a, zornZero)).1) := by
    intro a y
    have hprod : sedenionMul (a, zornZero) (zornZero, y) = (zornZero, zornMul y a) := by
      apply Prod.ext
      · dsimp [sedenionMul]
        rw [zornMul_zornZero_right, zornMul_zornZero_right, zornAdd_zornZero_right]
      · dsimp [sedenionMul]
        rw [zornConj_zornZero, zornMul_zornZero_left, zornAdd_zornZero_right]
    have hleib := congrArg Prod.snd (hD_mul (a, zornZero) (zornZero, y))
    rw [hprod] at hleib
    dsimp [sedenionAdd, sedenionMul] at hleib
    simp only [hf_zero a, hg_zero y, zornConj_zornZero, zornMul_zornZero_left,
      zornMul_zornZero_right, zornAdd_zornZero_left, zornAdd_zornZero_right] at hleib
    rw [hleib]
    ext k <;> (dsimp [zornAdd]; ring)
  -- First component of D((1, 0) * (1, 0)) gives d(1) = 0
  have h_one_mul : ∀ a : ZornSplitOctonion ℝ, zornMul zornOne a = a := by
    intro a; ext k
    · dsimp [zornMul, zornOne, vec3Dot]; ring
    · fin_cases k <;> (dsimp [zornMul, zornOne, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornMul, zornOne, vec3Cross]; ring)
    · dsimp [zornMul, zornOne, vec3Dot]; ring
  have h_mul_one : ∀ a : ZornSplitOctonion ℝ, zornMul a zornOne = a := by
    intro a; ext k
    · dsimp [zornMul, zornOne, vec3Dot]; ring
    · fin_cases k <;> (dsimp [zornMul, zornOne, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornMul, zornOne, vec3Cross]; ring)
    · dsimp [zornMul, zornOne, vec3Dot]; ring
  have hd_one : (D (zornOne, zornZero)).1 = zornZero := by
    have h := hd_leib zornOne zornOne
    rw [h_one_mul zornOne, h_mul_one, h_one_mul] at h
    ext k
    · have hk := congrArg ZornSplitOctonion.a h; dsimp [zornAdd, zornZero] at hk ⊢; linarith
    · fin_cases k
      · have hk := congrArg (fun z => z.u 0) h; dsimp [zornAdd, zornZero] at hk ⊢; linarith
      · have hk := congrArg (fun z => z.u 1) h; dsimp [zornAdd, zornZero] at hk ⊢; linarith
      · have hk := congrArg (fun z => z.u 2) h; dsimp [zornAdd, zornZero] at hk ⊢; linarith
    · fin_cases k
      · have hk := congrArg (fun z => z.v 0) h; dsimp [zornAdd, zornZero] at hk ⊢; linarith
      · have hk := congrArg (fun z => z.v 1) h; dsimp [zornAdd, zornZero] at hk ⊢; linarith
      · have hk := congrArg (fun z => z.v 2) h; dsimp [zornAdd, zornZero] at hk ⊢; linarith
    · have hk := congrArg ZornSplitOctonion.b h; dsimp [zornAdd, zornZero] at hk ⊢; linarith
  -- First component of D((0, 1) * (0, 1)) = D(1, 0) gives h(1) + conj(h(1)) = d(1) = 0
  have hh_one_tr : ((D (zornZero, zornOne)).2).a + ((D (zornZero, zornOne)).2).b = 0 := by
    have hprod11 : sedenionMul (zornZero, zornOne) (zornZero, zornOne) =
        ((zornOne, zornZero) : SplitSedenion ℝ) := by
      apply Prod.ext
      · dsimp [sedenionMul]
        have hconj1 : zornConj (zornOne : ZornSplitOctonion ℝ) = zornOne := by
          ext k
          · dsimp [zornConj, zornOne]
          · fin_cases k <;> (dsimp [zornConj, zornOne]; ring)
          · fin_cases k <;> (dsimp [zornConj, zornOne]; ring)
          · dsimp [zornConj, zornOne]
        rw [zornMul_zornZero_left, hconj1, h_one_mul, zornAdd_zornZero_left]
      · dsimp [sedenionMul]
        rw [zornMul_zornZero_right, zornConj_zornZero, zornMul_zornZero_right, zornAdd_zornZero_right]
    have hleib := congrArg Prod.fst (hD_mul (zornZero, zornOne) (zornZero, zornOne))
    rw [hprod11, hd_one] at hleib
    dsimp [sedenionAdd, sedenionMul] at hleib
    have ha := congrArg ZornSplitOctonion.a hleib
    dsimp [zornZero, zornAdd, zornMul, zornConj, zornOne, vec3Dot] at ha ⊢
    linarith
  -- From hh_rel at y = 1: h(a) = h(1) * a + d(a), so T(a) := h(a) - d(a) = h(1) * a
  have hh_sub_d : ∀ a : ZornSplitOctonion ℝ,
      (D (zornZero, a)).2 = zornAdd (zornMul (D (zornZero, zornOne)).2 a) (D (a, zornZero)).1 := by
    intro a
    have h := hh_rel a zornOne
    rw [h_one_mul a, h_one_mul (D (a, zornZero)).1] at h
    exact h
  -- Substituting hh_sub_d into hh_rel and subtracting hd_leib gives h(1) * (y * a) = (h(1) * y) * a
  let c : VZ := zornVectorMatrixEquiv.symm (D (zornZero, zornOne)).2
  have hc_tr : c.a + c.b = 0 := hh_one_tr
  have hc_nuc : ∀ X Y : VZ,
      ZornVectorMatrix.mul c (ZornVectorMatrix.mul Y X) =
        ZornVectorMatrix.mul (ZornVectorMatrix.mul c Y) X := by
    intro X Y
    let a := zornVectorMatrixEquiv X
    let y := zornVectorMatrixEquiv Y
    have h1 := hh_rel a y
    rw [hh_sub_d (zornMul y a), hh_sub_d y, hd_leib y a] at h1
    have hcancel : zornMul (D (zornZero, zornOne)).2 (zornMul y a) =
        zornMul (zornMul (D (zornZero, zornOne)).2 y) a := by
      have hdist : zornMul (zornAdd (zornMul (D (zornZero, zornOne)).2 y) (D (y, zornZero)).1) a =
          zornAdd (zornMul (zornMul (D (zornZero, zornOne)).2 y) a) (zornMul (D (y, zornZero)).1 a) := by
        ext k
        · dsimp [zornMul, zornAdd, vec3Dot]; ring
        · fin_cases k <;> (dsimp [zornMul, zornAdd, vec3Cross]; ring)
        · fin_cases k <;> (dsimp [zornMul, zornAdd, vec3Cross]; ring)
        · dsimp [zornMul, zornAdd, vec3Dot]; ring
      rw [hdist] at h1
      ext k
      · have hk := congrArg ZornSplitOctonion.a h1; dsimp [zornAdd] at hk ⊢; linarith
      · fin_cases k
        · have hk := congrArg (fun z => z.u 0) h1; dsimp [zornAdd] at hk ⊢; linarith
        · have hk := congrArg (fun z => z.u 1) h1; dsimp [zornAdd] at hk ⊢; linarith
        · have hk := congrArg (fun z => z.u 2) h1; dsimp [zornAdd] at hk ⊢; linarith
      · fin_cases k
        · have hk := congrArg (fun z => z.v 0) h1; dsimp [zornAdd] at hk ⊢; linarith
        · have hk := congrArg (fun z => z.v 1) h1; dsimp [zornAdd] at hk ⊢; linarith
        · have hk := congrArg (fun z => z.v 2) h1; dsimp [zornAdd] at hk ⊢; linarith
      · have hk := congrArg ZornSplitOctonion.b h1; dsimp [zornAdd] at hk ⊢; linarith
    have hsymm := congrArg zornVectorMatrixEquiv.symm hcancel
    rw [zornVectorMatrixEquiv_symm_mul, zornVectorMatrixEquiv_symm_mul,
      zornVectorMatrixEquiv_symm_mul, zornVectorMatrixEquiv_symm_mul,
      zornVectorMatrixEquiv.symm_apply_apply, zornVectorMatrixEquiv.symm_apply_apply] at hsymm
    exact hsymm
  have hc_zero : c = zero := zornVZ_left_nucleus_trace_zero_eq_zero c hc_tr hc_nuc
  have hh_one_zero : (D (zornZero, zornOne)).2 = zornZero := by
    have h := congrArg zornVectorMatrixEquiv hc_zero
    dsimp [c] at h
    rw [zornVectorMatrixEquiv.apply_symm_apply] at h
    exact h
  rw [hh_sub_d b, hh_one_zero, zornMul_zornZero_left, zornAdd_zornZero_left]

/-!
## Section 5: The Main 14-Dimensional Split-Sedenion Derivation Classification Theorems
-/

/-- Every derivation `D` of `sedenionMul` has the exact diagonal form `D(a, b) = (d(a), d(b))`
where `d(a) = (D(a, 0)).1`. -/
theorem sedenionDerivation_eq_cdLift_fst
    {D : SplitSedenion ℝ → SplitSedenion ℝ} (hD : IsSedenionDerivation D)
    (X : SplitSedenion ℝ) :
    D X = cdLift (fun a => (D (a, zornZero)).1) X := by
  have hf_zero := sedenionDerivation_fst_sheet_snd_eq_zero hD
  have hg_zero := sedenionDerivation_snd_sheet_fst_eq_zero hD
  have hh_eq := sedenionDerivation_snd_sheet_snd_eq_fst_sheet_fst hD
  rcases hD with ⟨hD_add, _, _⟩
  have hsplit : X = sedenionAdd (X.1, zornZero) (zornZero, X.2) := by
    apply Prod.ext
    · exact (zornAdd_zornZero_right X.1).symm
    · exact (zornAdd_zornZero_left X.2).symm
  conv_lhs => rw [hsplit]
  rw [hD_add]
  apply Prod.ext
  · dsimp [sedenionAdd, cdLift]
    rw [hg_zero X.2, zornAdd_zornZero_right]
  · dsimp [sedenionAdd, cdLift]
    rw [hf_zero X.1, hh_eq X.2, zornAdd_zornZero_left]

/-- Construct the `VDer` (`ZornVectorMatrix.Derivation (R := ℝ)`) induced by the upper-left
block of a split-sedenion derivation `D`. -/
noncomputable def sedenionToVDer
    (D : SplitSedenion ℝ → SplitSedenion ℝ) (hD : IsSedenionDerivation D) : VDer where
  toFun := dVZ D
  map_add' X Y := by
    rcases hD with ⟨hD_add, _, _⟩
    dsimp [dVZ]
    rw [zornVectorMatrixEquiv_add]
    have hpair : (zornAdd (zornVectorMatrixEquiv X) (zornVectorMatrixEquiv Y), (zornZero : ZornSplitOctonion ℝ)) =
        sedenionAdd (zornVectorMatrixEquiv X, zornZero) (zornVectorMatrixEquiv Y, zornZero) := by
      apply Prod.ext
      · rfl
      · exact (zornAdd_zornZero_right zornZero).symm
    rw [hpair, hD_add]
    exact zornVectorMatrixEquiv_symm_add _ _
  map_smul' c X := by
    rcases hD with ⟨_, hD_smul, _⟩
    dsimp [dVZ]
    rw [zornVectorMatrixEquiv_smul]
    have hpair : (zornSmul c (zornVectorMatrixEquiv X), (zornZero : ZornSplitOctonion ℝ)) =
        sedenionSmul c (zornVectorMatrixEquiv X, zornZero) := by
      apply Prod.ext
      · rfl
      · exact (zornSmul_zornZero c).symm
    rw [hpair, hD_smul]
    exact zornVectorMatrixEquiv_symm_smul c _
  map_mul' X Y := by
    have hd_leib := sedenionDerivation_fst_sheet_fst_leibniz hD
    dsimp [dVZ]
    rw [zornVectorMatrixEquiv_mul, hd_leib, zornVectorMatrixEquiv_symm_add,
      zornVectorMatrixEquiv_symm_mul, zornVectorMatrixEquiv_symm_mul,
      zornVectorMatrixEquiv.symm_apply_apply, zornVectorMatrixEquiv.symm_apply_apply]

/-- The 14-coordinate readout `derivationParameters (sedenionToVDer D hD)` coincides
definitionally with `readSedenionG2Params D`. -/
theorem derivationParameters_sedenionToVDer
    (D : SplitSedenion ℝ → SplitSedenion ℝ) (hD : IsSedenionDerivation D) :
    derivationParameters (sedenionToVDer D hD) = readSedenionG2Params D := by
  rfl

/-- **Full 14-Dimensional Split-Sedenion Derivation Classification Theorem**:
Every derivation `D` of `sedenionMul` (`IsSedenionDerivation D`) equals
`sedenionG2Derivation (readSedenionG2Params D)`. -/
theorem sedenionDerivation_eq_sedenionG2Derivation
    {D : SplitSedenion ℝ → SplitSedenion ℝ} (hD : IsSedenionDerivation D)
    (X : SplitSedenion ℝ) :
    D X = sedenionG2Derivation (readSedenionG2Params D) X := by
  rw [sedenionDerivation_eq_cdLift_fst hD X]
  have hvder : parameterLinearEquiv (derivationParameters (sedenionToVDer D hD)) = sedenionToVDer D hD :=
    parameterLinearEquiv.right_inv (sedenionToVDer D hD)
  rw [derivationParameters_sedenionToVDer D hD] at hvder
  have hact : ∀ a : ZornSplitOctonion ℝ,
      (D (a, zornZero)).1 = zornG2Derivation (readSedenionG2Params D) a := by
    intro a
    have h := congrArg (fun V : VDer => zornVectorMatrixEquiv (V (zornVectorMatrixEquiv.symm a))) hvder.symm
    dsimp [parameterLinearEquiv, parameterDerivation, sedenionToVDer, dVZ, zornG2Derivation] at h ⊢
    rw [zornVectorMatrixEquiv.apply_symm_apply, zornVectorMatrixEquiv.apply_symm_apply] at h
    exact h
  dsimp [sedenionG2Derivation, cdLift]
  rw [hact X.1, hact X.2]

/-- **Existence and Uniqueness of the 14-Dimensional $\mathfrak{g}_{2(2)}$ Parameter Vector**:
Every derivation `D` of `sedenionMul` is represented by a unique `p : Params = (Fin 14 → ℝ)`
such that `D = sedenionG2Derivation p`. -/
theorem sedenionDerivation_existsUnique_g2Params
    {D : SplitSedenion ℝ → SplitSedenion ℝ} (hD : IsSedenionDerivation D) :
    ∃! p : Params, D = sedenionG2Derivation p := by
  refine ⟨readSedenionG2Params D, ?_, ?_⟩
  · funext X
    exact sedenionDerivation_eq_sedenionG2Derivation hD X
  · intro q hq
    have hread := congrArg readSedenionG2Params hq
    rw [readSedenionG2Params_sedenionG2Derivation q] at hread
    exact hread.symm

/-- **Automatic Star-Derivation Theorem**:
Every derivation of `sedenionMul` automatically commutes with `sedenionConj`
(`IsSedenionDerivation D ↔ IsSedenionStarDerivation D`). -/
theorem sedenionDerivation_iff_starDerivation
    (D : SplitSedenion ℝ → SplitSedenion ℝ) :
    IsSedenionDerivation D ↔ IsSedenionStarDerivation D := by
  constructor
  · intro hD
    have h_eq : D = sedenionG2Derivation (readSedenionG2Params D) := by
      funext X
      exact sedenionDerivation_eq_sedenionG2Derivation hD X
    rw [h_eq]
    exact sedenionG2Derivation_isStarDerivation (readSedenionG2Params D)
  · intro hStar
    exact hStar.1

/-- **Automatic Annihilation of the Cayley–Dickson Doubling Unit**:
Every derivation of `sedenionMul` annihilates `sedenionEll = (0, 1)`. -/
theorem sedenionDerivation_sedenionEll_eq_zero
    {D : SplitSedenion ℝ → SplitSedenion ℝ} (hD : IsSedenionDerivation D) :
    D sedenionEll = sedenionZero := by
  rw [sedenionDerivation_eq_sedenionG2Derivation hD sedenionEll]
  exact sedenionG2Derivation_sedenionEll_zero (readSedenionG2Params D)

end InfoGeometry.Synthesis.SplitSedenionDerivationClassification
