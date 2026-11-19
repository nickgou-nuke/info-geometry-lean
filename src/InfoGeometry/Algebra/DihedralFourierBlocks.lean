/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.FiniteGroupFourier
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Irreducible

/-!
# Paired-character dihedral representations and their matrix Fourier blocks

The carrier is the full complex two-by-two matrix algebra. A cyclic character
and its opposite frequency are coupled by the reflection exchanging the two
coordinates. The resulting map is a homomorphism on Mathlib's `DihedralGroup`;
the native group multiplication fixes the order of all reflected products.

Finite Fourier blocks reuse the counting-measure transform and convolution
from `FiniteGroupFourier`. This constructs an individual matrix block, not a
complete irreducible dual or a Peter--Weyl inversion theorem.
-/

noncomputable section

namespace InfoGeometry.Algebra.DihedralFourierBlocks

open scoped Matrix BigOperators
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Algebra.FiniteGroupFourier
open InfoGeometry.Algebra.NoncommutativePlaneWaveKernel

variable {n : ℕ}

/-- The reflection couples the two opposite cyclic-frequency coordinates. -/
def pairedMatrix (χ : AddChar (ZMod n) ℂ) : DihedralGroup n →* Mat2C where
  toFun
    | .r i => !![χ i, 0; 0, χ (-i)]
    | .sr i => !![0, χ (-i); χ i, 0]
  map_one' := by
    change (!![χ 0, 0; 0, χ (-0)] : Mat2C) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' := by
    rintro (i | i) (j | j) <;>
      ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
        Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg,
        AddChar.map_add_eq_mul, mul_comm]

@[simp] theorem pairedMatrix_r (χ : AddChar (ZMod n) ℂ) (i : ZMod n) :
    pairedMatrix χ (.r i) = !![χ i, 0; 0, χ (-i)] := rfl

@[simp] theorem pairedMatrix_sr (χ : AddChar (ZMod n) ℂ) (i : ZMod n) :
    pairedMatrix χ (.sr i) = !![0, χ (-i); χ i, 0] := rfl

@[simp] theorem pairedMatrix_reflection (χ : AddChar (ZMod n) ℂ) :
    pairedMatrix χ (.sr 0) = J_plus + J_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J_plus, J_minus]

/-- The period is inherited from the actual finite cyclic group. -/
theorem rotation_pow_order (χ : AddChar (ZMod n) ℂ) :
    pairedMatrix χ (.r 1) ^ n = 1 := by
  rw [← map_pow, DihedralGroup.r_one_pow_n, map_one]

theorem reflection_sq (χ : AddChar (ZMod n) ℂ) :
    pairedMatrix χ (.sr 0) ^ 2 = 1 := by
  rw [pow_two, ← map_mul, DihedralGroup.sr_mul_self, map_one]

/-- Reflection reverses the rotation parameter before evaluation. -/
theorem reflection_rotation_reflection (χ : AddChar (ZMod n) ℂ) (i : ZMod n) :
    pairedMatrix χ (.sr 0) * pairedMatrix χ (.r i) * pairedMatrix χ (.sr 0) =
      pairedMatrix χ (.r (-i)) := by
  rw [← map_mul, ← map_mul]
  simp

/-- Distinct opposite frequencies are exactly the obstruction to commutation. -/
theorem reflection_rotation_commute_iff (χ : AddChar (ZMod n) ℂ) (i : ZMod n) :
    pairedMatrix χ (.sr 0) * pairedMatrix χ (.r i) =
      pairedMatrix χ (.r i) * pairedMatrix χ (.sr 0) ↔ χ i = χ (-i) := by
  constructor
  · intro h
    have he := congrArg (fun M : Mat2C => M 0 1) h
    simpa [pairedMatrix, Matrix.mul_apply, Fin.sum_univ_two] using he.symm
  · intro h
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [pairedMatrix, Matrix.mul_apply, Fin.sum_univ_two, h]

/-- Standard cyclic frequencies give concrete dihedral matrix representations. -/
def frequencyMatrix [NeZero n] (k : ZMod n) : DihedralGroup n →* Mat2C :=
  pairedMatrix (ZMod.stdAddChar.mulShift k)

theorem frequencyMatrix_noncommuting_iff [NeZero n] (k : ZMod n) :
    frequencyMatrix k (.sr 0) * frequencyMatrix k (.r 1) ≠
      frequencyMatrix k (.r 1) * frequencyMatrix k (.sr 0) ↔ k ≠ -k := by
  simp only [frequencyMatrix, ne_eq, reflection_rotation_commute_iff,
    AddChar.mulShift_apply, mul_one, mul_neg, ZMod.injective_stdAddChar.eq_iff]

/-- An actual noncommuting two-dimensional representation of the order-six group. -/
theorem frequencyMatrix_three_noncommuting :
    frequencyMatrix (1 : ZMod 3) (.sr 0) * frequencyMatrix (1 : ZMod 3) (.r 1) ≠
      frequencyMatrix (1 : ZMod 3) (.r 1) * frequencyMatrix (1 : ZMod 3) (.sr 0) := by
  rw [frequencyMatrix_noncommuting_iff]
  decide

/-- The same matrices as a native representation on complex two-vectors. -/
def pairedRepresentation (χ : AddChar (ZMod n) ℂ) :
    Representation ℂ (DihedralGroup n) (Fin 2 → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp (pairedMatrix χ)

@[simp] theorem pairedRepresentation_apply (χ : AddChar (ZMod n) ℂ)
    (g : DihedralGroup n) (v : Fin 2 → ℂ) :
    pairedRepresentation χ g v = (pairedMatrix χ g).mulVec v := rfl

theorem pairedMatrix_rotation_mulVec (χ : AddChar (ZMod n) ℂ)
    (i : ZMod n) (v : Fin 2 → ℂ) :
    (pairedMatrix χ (.r i)).mulVec v = ![χ i * v 0, χ (-i) * v 1] := by
  ext a
  fin_cases a <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem pairedMatrix_reflection_mulVec (χ : AddChar (ZMod n) ℂ) (v : Fin 2 → ℂ) :
    (pairedMatrix χ (.sr 0)).mulVec v = ![v 1, v 0] := by
  ext a
  fin_cases a <;> simp [pairedMatrix_sr, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- A rotation with distinct eigenvalues and its coordinate-swapping reflection
have no proper nonzero invariant complex subspace. -/
theorem invariant_submodule_eq_bot_or_top (χ : AddChar (ZMod n) ℂ)
    (hχ : χ 1 ≠ χ (-1)) (U : Submodule ℂ (Fin 2 → ℂ))
    (hR : ∀ v ∈ U, (pairedMatrix χ (.r 1)).mulVec v ∈ U)
    (hS : ∀ v ∈ U, (pairedMatrix χ (.sr 0)).mulVec v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hex : ∃ w ∈ U, w 0 ≠ 0 := by
    by_cases hv0 : v 0 = 0
    · refine ⟨(pairedMatrix χ (.sr 0)).mulVec v, hS v hv, ?_⟩
      rw [pairedMatrix_reflection_mulVec]
      change v 1 ≠ 0
      intro hv1
      apply hvne
      ext i
      fin_cases i <;> simp [hv0, hv1]
    · exact ⟨v, hv, hv0⟩
  obtain ⟨w, hw, hw0⟩ := hex
  have hz : ![(χ 1 - χ (-1)) * w 0, 0] ∈ U := by
    have ht := U.sub_mem (hR w hw) (U.smul_mem (χ (-1)) hw)
    rw [pairedMatrix_rotation_mulVec] at ht
    convert ht using 1
    ext i
    fin_cases i
    · simp
      ring
    · simp
  have he0 : (![1, 0] : Fin 2 → ℂ) ∈ U := by
    have ht := U.smul_mem (((χ 1 - χ (-1)) * w 0)⁻¹) hz
    convert ht using 1
    ext i
    fin_cases i
    · change 1 = ((χ 1 - χ (-1)) * w 0)⁻¹ * ((χ 1 - χ (-1)) * w 0)
      exact (inv_mul_cancel₀ (mul_ne_zero (sub_ne_zero.mpr hχ) hw0)).symm
    · simp
  have he1 : (![0, 1] : Fin 2 → ℂ) ∈ U := by
    have ht := hS _ he0
    rw [pairedMatrix_reflection_mulVec] at ht
    exact ht
  apply top_unique
  intro z hz
  have hsplit : z = z 0 • (![1, 0] : Fin 2 → ℂ) + z 1 • ![0, 1] := by
    ext i
    fin_cases i <;> simp
  rw [hsplit]
  exact U.add_mem (U.smul_mem _ he0) (U.smul_mem _ he1)

/-- Native irreducibility with the exact nonexceptional character hypothesis. -/
theorem pairedRepresentation_isIrreducible (χ : AddChar (ZMod n) ℂ)
    (hχ : χ 1 ≠ χ (-1)) : Representation.IsIrreducible (pairedRepresentation χ) where
  exists_pair_ne := ⟨⊥, ⊤, by
    intro h
    have he := congrArg Subrepresentation.toSubmodule h
    exact (bot_ne_top : (⊥ : Submodule ℂ (Fin 2 → ℂ)) ≠ ⊤) he⟩
  eq_bot_or_eq_top U := by
    rcases invariant_submodule_eq_bot_or_top χ hχ U.toSubmodule
      (fun v hv => U.apply_mem_toSubmodule (.r 1) hv)
      (fun v hv => U.apply_mem_toSubmodule (.sr 0) hv) with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

/-- For the standard cyclic character, only a genuinely distinct pair qualifies.
The zero frequency, and the self-opposite frequency when the order is even,
are excluded by the explicit hypothesis. -/
theorem frequencyRepresentation_isIrreducible [NeZero n]
    (k : ZMod n) (hk : k ≠ -k) :
    Representation.IsIrreducible
      (pairedRepresentation (ZMod.stdAddChar.mulShift k)) := by
  apply pairedRepresentation_isIrreducible
  simpa only [ne_eq, AddChar.mulShift_apply, mul_one, mul_neg,
    ZMod.injective_stdAddChar.eq_iff] using hk

/-- Equal opposite characters preserve the proper symmetric line. -/
theorem pairedRepresentation_not_isIrreducible (χ : AddChar (ZMod n) ℂ)
    (hχ : ∀ i, χ i = χ (-i)) :
    ¬ Representation.IsIrreducible (pairedRepresentation χ) := by
  let U : Subrepresentation (pairedRepresentation χ) := {
    toSubmodule := {
      carrier := {v | v 0 = v 1}
      zero_mem' := rfl
      add_mem' := by intro v w hv hw; change v 0 + w 0 = v 1 + w 1; rw [hv, hw]
      smul_mem' := by intro a v hv; change a * v 0 = a * v 1; rw [hv] }
    apply_mem_toSubmodule := by
      rintro (i | i) v hv <;>
        change v 0 = v 1 at hv <;>
        change ((pairedMatrix χ _).mulVec v) 0 = ((pairedMatrix χ _).mulVec v) 1 <;>
        simp [pairedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hχ i, hv] }
  intro h
  rcases h.eq_bot_or_eq_top U with hbot | htop
  · have hv : (![1, 1] : Fin 2 → ℂ) ∈ U := by change (1 : ℂ) = 1; rfl
    rw [hbot] at hv
    have hz : (![1, 1] : Fin 2 → ℂ) = 0 := (Submodule.mem_bot ℂ).mp hv
    have hz0 := congrFun hz 0
    simp at hz0
  · have hv : (![1, 0] : Fin 2 → ℂ) ∈ U := by rw [htop]; trivial
    exact one_ne_zero (show (1 : ℂ) = 0 from hv)

/-- Exact classification of the exceptional frequencies for this family. -/
theorem frequencyRepresentation_isIrreducible_iff [NeZero n] (k : ZMod n) :
    Representation.IsIrreducible
      (pairedRepresentation (ZMod.stdAddChar.mulShift k)) ↔ k ≠ -k := by
  refine ⟨?_, frequencyRepresentation_isIrreducible k⟩
  intro h hk
  apply pairedRepresentation_not_isIrreducible (ZMod.stdAddChar.mulShift k) ?_ h
  intro i
  simp only [AddChar.mulShift_apply]
  congr 1
  rw [mul_neg, ← neg_mul, ← hk]

section Fourier

variable [NeZero n]

/-- The matrix-valued Fourier coefficient for the paired-character representation. -/
def dihedralFourier (χ : AddChar (ZMod n) ℂ) (f : DihedralGroup n → ℂ) : Mat2C :=
  finiteRepresentationTransform (pairedMatrix χ) f

/-- Split counting measure into the native rotation and reflection sectors. -/
theorem sum_dihedral {A : Type*} [AddCommMonoid A] (f : DihedralGroup n → A) :
    ∑ g, f g = (∑ i : ZMod n, f (.r i)) + ∑ i : ZMod n, f (.sr i) := by
  rw [← DihedralGroup.equivSum.symm.sum_comp f, Fintype.sum_sum_type]
  rfl

/-- Both cyclic frequencies and both reflected channels remain in the full block. -/
theorem dihedralFourier_entries (χ : AddChar (ZMod n) ℂ) (f : DihedralGroup n → ℂ) :
    dihedralFourier χ f =
      !![∑ i : ZMod n, f (.r i) * χ i, ∑ i : ZMod n, f (.sr i) * χ (-i);
         ∑ i : ZMod n, f (.sr i) * χ i, ∑ i : ZMod n, f (.r i) * χ (-i)] := by
  rw [dihedralFourier, finiteRepresentationTransform_apply, sum_dihedral]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.sum_apply]

/-- Forward-convention blocks multiply without reversing the convolution factors. -/
theorem dihedralFourier_convolution (χ : AddChar (ZMod n) ℂ)
    (f h : DihedralGroup n → ℂ) :
    dihedralFourier χ (finiteConvolution f h) = dihedralFourier χ f * dihedralFourier χ h :=
  finiteRepresentationTransform_convolution (pairedMatrix χ) f h

end Fourier

/-- Full four-channel reconstruction in the existing spin-half matrix coordinates. -/
theorem matrix_four_channels (M : Mat2C) :
    M = ((M 0 0 + M 1 1) / 2) • (1 : Mat2C) +
      ((M 0 1 - M 1 0) / 2) • (J_plus - J_minus) +
      ((M 0 0 - M 1 1) / 2) • ((2 : ℂ) • J_zero) +
      ((M 0 1 + M 1 0) / 2) • (J_plus + J_minus) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J_plus, J_minus, J_zero, Matrix.smul_apply] <;> ring

end InfoGeometry.Algebra.DihedralFourierBlocks
