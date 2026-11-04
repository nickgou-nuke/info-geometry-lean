/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.HypercomplexTriad
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# The split atom: signs, Peirce blocks, and Clifford involutions

The carrier and Clifford equivalence belong to `Cl11Matrix`.  These aliases
use the convention I = epsilon, J = sigma_z, K = I J = -sigma_x.  In particular
`HypercomplexTriad.I` has the opposite sign.  No operation below is identified
with physical charge conjugation, parity, or antiunitary time reversal.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitAtom

abbrev Mat2 := Cl11Matrix.Mat2
abbrev Cl11 := CliffordAlgebra Cl11Matrix.q11
abbrev I : Mat2 := Cl11Matrix.Eminus
abbrev J : Mat2 := Cl11Matrix.Eplus
abbrev K : Mat2 := -Cl11Matrix.J1
abbrev Pplus : Mat2 := InfoGeometry.Algebra.HypercomplexTriad.Pplus
abbrev Pminus : Mat2 := InfoGeometry.Algebra.HypercomplexTriad.Pminus
abbrev raising : Mat2 := InfoGeometry.Algebra.HypercomplexTriad.N

/-- The nilpotent seed transported from the matrix model into the native
`Cl(1,1)` carrier by the existing algebra equivalence. -/
noncomputable def raisingCl : Cl11 := Cl11Matrix.cl11EquivMat.symm raising

/-- The opposite chiral seed, transported from the matrix transpose of the
raising seed. This makes the chosen dual operation explicit on the carrier. -/
noncomputable def loweringCl : Cl11 :=
  Cl11Matrix.cl11EquivMat.symm (star raising)

/-- The transpose involution transported from the real matrix model to the
Clifford carrier. This is an explicit alternative involution; it is not
silently identified with Mathlib's Clifford conjugation. -/
noncomputable def transposeDual (x : Cl11) : Cl11 :=
  Cl11Matrix.cl11EquivMat.symm (star (Cl11Matrix.cl11EquivMat x))

/-- The transported dual reverses products. -/
theorem transposeDual_mul (x y : Cl11) :
    transposeDual (x * y) = transposeDual y * transposeDual x := by
  apply Cl11Matrix.cl11EquivMat.injective
  simp only [map_mul, transposeDual, AlgEquiv.apply_symm_apply]
  rw [star_mul]

/-- The transported transpose dual is involutive. -/
theorem transposeDual_involutive (x : Cl11) :
    transposeDual (transposeDual x) = x := by
  apply Cl11Matrix.cl11EquivMat.injective
  simp [transposeDual]

/-- On the seed, the transported dual is exactly the selected lowering
operator. -/
theorem transposeDual_raising : transposeDual raisingCl = loweringCl := by
  simp [transposeDual, raisingCl, loweringCl]

/-- The transported matrix transpose fixes the positive Clifford generator. -/
theorem transposeDual_iota_pos :
    transposeDual (CliffordAlgebra.ι Cl11Matrix.q11 (1, 0)) =
      CliffordAlgebra.ι Cl11Matrix.q11 (1, 0) := by
  apply Cl11Matrix.cl11EquivMat.injective
  simp only [transposeDual, Cl11Matrix.cl11EquivMat_iota_pos,
    AlgEquiv.apply_symm_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Cl11Matrix.Eplus, Matrix.star_apply, Matrix.transpose_apply]

/-- The transported transpose is not Mathlib's canonical Clifford
conjugation: it fixes a vector generator, while `CliffordAlgebra.star`
negates every vector generator. -/
theorem transposeDual_ne_cliffordStar :
    ∃ x : Cl11, transposeDual x ≠ star x := by
  refine ⟨CliffordAlgebra.ι Cl11Matrix.q11 (1, 0), ?_⟩
  rw [transposeDual_iota_pos, CliffordAlgebra.star_ι]
  intro h
  have hm := congrArg Cl11Matrix.cl11EquivMat h
  rw [Cl11Matrix.cl11EquivMat_iota_pos] at hm
  have h00 := congrArg (fun A : Mat2 => A 0 0) hm
  norm_num [Cl11Matrix.Eplus] at h00

/-- The split generator transported into the native Clifford carrier. -/
noncomputable def splitGeneratorCl : Cl11 := Cl11Matrix.cl11EquivMat.symm J

@[simp] theorem I_sq : I * I = -(1 : Mat2) := by
  simpa using Cl11Matrix.Eminus_sq

@[simp] theorem J_sq : J * J = (1 : Mat2) := Cl11Matrix.Eplus_sq

@[simp] theorem K_sq : K * K = (1 : Mat2) := by
  simpa only [K, neg_mul_neg] using Cl11Matrix.J1_sq

@[simp] theorem I_mul_J : I * J = K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, J, K, Cl11Matrix.Eminus, Cl11Matrix.Eplus,
      Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem J_mul_I : J * I = -K := by
  simpa only [J, I, K, neg_neg] using Cl11Matrix.Eplus_mul_Eminus

@[simp] theorem J_mul_K : J * K = -I := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, J, K, Cl11Matrix.Eminus, Cl11Matrix.Eplus,
      Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem K_mul_J : K * J = I := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, J, K, Cl11Matrix.Eminus, Cl11Matrix.Eplus,
      Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem K_mul_I : K * I = J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, J, K, Cl11Matrix.Eminus, Cl11Matrix.Eplus,
      Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem I_mul_K : I * K = -J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, J, K, Cl11Matrix.Eminus, Cl11Matrix.Eplus,
      Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two]

theorem elliptic_owner_sign : I = -InfoGeometry.Algebra.HypercomplexTriad.I := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, Cl11Matrix.Eminus, InfoGeometry.Algebra.HypercomplexTriad.I]

theorem raising_eq_half_I_sub_K : raising = (1 / 2 : ℝ) • (I - K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [raising, InfoGeometry.Algebra.HypercomplexTriad.N, I, K,
      Cl11Matrix.Eminus, Cl11Matrix.J1]

/-- The parabolic Clifford seed is the matrix raising operator from the
hypercomplex triad. Its involutive adjoint is the opposite chiral lowering
operator. -/
theorem raising_adjoint :
    star raising = !![(0 : ℝ), 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [raising, InfoGeometry.Algebra.HypercomplexTriad.N,
      Matrix.star_apply, Matrix.transpose_apply]

/-- The split atom's parabolic seed is a regular square-zero element. This is
the concrete `Cl(1,1)` matrix realization of the nilpotent-pair hypotheses
used by the anomaly-first chiral block construction. -/
theorem raising_regular_nilpotent :
    raising * raising = 0 ∧ raising * star raising * raising = raising := by
  constructor
  · simpa [raising] using InfoGeometry.Algebra.HypercomplexTriad.N_sq
  · rw [raising_adjoint]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [raising, InfoGeometry.Algebra.HypercomplexTriad.N,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- On the concrete split Clifford atom, the parity anomaly generated by the
parabolic nilpotent pair equals the hyperbolic split generator, and its square
is the identity gap of this full `M₂(ℝ)` carrier. -/
theorem raising_anomaly_gap_realization :
    (raising * star raising - star raising * raising) = J ∧
      (raising * star raising - star raising * raising) *
        (raising * star raising - star raising * raising) = 1 ∧
      (raising + star raising) * (raising + star raising) = 1 := by
  rw [raising_adjoint]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [raising, J, Cl11Matrix.Eplus,
        InfoGeometry.Algebra.HypercomplexTriad.N,
        Matrix.mul_apply, Fin.sum_univ_two]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [raising, J, Cl11Matrix.Eplus,
      InfoGeometry.Algebra.HypercomplexTriad.N,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Transporting the concrete seed pair through `Cl(1,1) ≃ₐ[ℝ] M₂(ℝ)`
preserves square-zero and von Neumann regularity in the native Clifford
carrier. The dual here is the matrix-transpose dual transported by the
equivalence, not an assumed Clifford conjugation. -/
theorem raisingCl_regular_nilpotent :
    raisingCl * raisingCl = 0 ∧
      raisingCl * loweringCl * raisingCl = raisingCl := by
  apply And.intro
  · apply Cl11Matrix.cl11EquivMat.injective
    simp only [map_mul, map_zero, raisingCl,
      AlgEquiv.apply_symm_apply]
    exact InfoGeometry.Algebra.HypercomplexTriad.N_sq
  · apply Cl11Matrix.cl11EquivMat.injective
    simp only [map_mul, raisingCl, loweringCl,
      AlgEquiv.apply_symm_apply]
    exact raising_regular_nilpotent.2

/-- The anomaly-first block identities hold in the native `Cl(1,1)` carrier:
the commutator of the transported nilpotent pair is the split generator, and
both its square and the symmetric chiral block square are the carrier unit. -/
theorem raisingCl_anomaly_gap_realization :
    (raisingCl * loweringCl - loweringCl * raisingCl) = splitGeneratorCl ∧
      (raisingCl * loweringCl - loweringCl * raisingCl) *
        (raisingCl * loweringCl - loweringCl * raisingCl) = 1 ∧
      (raisingCl + loweringCl) * (raisingCl + loweringCl) = 1 := by
  apply And.intro
  · apply Cl11Matrix.cl11EquivMat.injective
    simp only [map_sub, map_mul, raisingCl, loweringCl, splitGeneratorCl,
      AlgEquiv.apply_symm_apply]
    exact (raising_anomaly_gap_realization).1
  apply And.intro
  · apply Cl11Matrix.cl11EquivMat.injective
    simp only [map_sub, map_mul, map_one, raisingCl, loweringCl,
      AlgEquiv.apply_symm_apply]
    exact (raising_anomaly_gap_realization).2.1
  · apply Cl11Matrix.cl11EquivMat.injective
    simp only [map_add, map_mul, map_one, raisingCl, loweringCl,
      AlgEquiv.apply_symm_apply]
    exact (raising_anomaly_gap_realization).2.2

theorem Pplus_formula : Pplus = (1 / 2 : ℝ) • ((1 : Mat2) + J) := rfl

theorem Pminus_formula : Pminus = (1 / 2 : ℝ) • ((1 : Mat2) - J) := rfl

/-- Full operator Peirce decomposition, including both off-diagonal blocks. -/
theorem peirce_four_blocks (A : Mat2) :
    A = Pplus * A * Pplus + Pplus * A * Pminus +
      Pminus * A * Pplus + Pminus * A * Pminus := by
  have hp : Pplus + Pminus = (1 : Mat2) :=
    InfoGeometry.Algebra.HypercomplexTriad.Pplus_add_Pminus
  calc
    A = (Pplus + Pminus) * A * (Pplus + Pminus) := by rw [hp]; simp
    _ = _ := by noncomm_ring

