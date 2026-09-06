import InfoGeometry.OperatorAlgebra.RealDoubledChiralNambuFrame

/-!
# Hadamard rewrite between the two doubled Krein bases

The null/cross-sheet form and the diagonal `(+,−)` form are the same form in
two bases.  We use the unnormalised Hadamard map here, so the exact identity
has the harmless factor `2`; the normalised map is obtained by scaling by
`1 / Real.sqrt 2` in a concrete Hilbert representation.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinHadamard

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev H₂ := DoubledSpace E

/-- Unnormalised Hadamard change of doubled coordinates. -/
def hadamard (u : H₂ (E := E)) : H₂ (E := E) :=
  to_doubled (WithLp.fst u + WithLp.snd u)
    (WithLp.fst u - WithLp.snd u)

/-- Inverse of the unnormalised Hadamard change. -/
def hadamardInv (u : H₂ (E := E)) : H₂ (E := E) :=
  to_doubled
    ((1 / 2 : ℝ) • (WithLp.fst u + WithLp.snd u))
    ((1 / 2 : ℝ) • (WithLp.fst u - WithLp.snd u))

/-- Normalised Hadamard change, corresponding to `2⁻¹ᐟ² W`. -/
def hadamardNormalized (u : H₂ (E := E)) : H₂ (E := E) :=
  (1 / Real.sqrt 2 : ℝ) • hadamard u

@[simp] theorem hadamard_to_doubled (x ξ : E) :
    hadamard (to_doubled x ξ : H₂ (E := E)) =
      to_doubled (x + ξ) (x - ξ) := by
  rfl

@[simp] theorem hadamardInv_to_doubled (x ξ : E) :
    hadamardInv (to_doubled x ξ : H₂ (E := E)) =
      to_doubled ((1 / 2 : ℝ) • (x + ξ))
        ((1 / 2 : ℝ) • (x - ξ)) := by
  rfl

theorem hadamardInv_hadamard (u : H₂ (E := E)) :
    hadamardInv (hadamard u) = u := by
  have hu : to_doubled (WithLp.fst u) (WithLp.snd u) = u := by
    exact DoubledSpace.ext rfl rfl
  rw [← hu]
  apply DoubledSpace.ext <;>
    simp [hadamard, hadamardInv, sub_eq_add_neg, smul_add, add_assoc,
      add_left_comm, add_comm] <;> module

theorem hadamard_hadamardInv (u : H₂ (E := E)) :
    hadamard (hadamardInv u) = u := by
  have hu : to_doubled (WithLp.fst u) (WithLp.snd u) = u := by
    exact DoubledSpace.ext rfl rfl
  rw [← hu]
  apply DoubledSpace.ext <;>
    simp [hadamard, hadamardInv, sub_eq_add_neg, smul_add, add_assoc,
      add_left_comm, add_comm] <;> module

theorem splitKreinForm_hadamard (u v : H₂ (E := E)) :
    splitKreinForm (hadamard u) (hadamard v) =
      2 * chiralKreinForm u v := by
  have hu : to_doubled (WithLp.fst u) (WithLp.snd u) = u := by
    exact DoubledSpace.ext rfl rfl
  have hv : to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    exact DoubledSpace.ext rfl rfl
  rw [← hu, ← hv]
  simp [hadamard, splitKreinForm, chiralKreinForm, WithLp.prod_inner_apply,
    sub_eq_add_neg, inner_add_left, inner_add_right]
  ring

theorem hadamard_smul (c : ℝ) (u : H₂ (E := E)) :
    hadamard (c • u) = c • hadamard u := by
  apply DoubledSpace.ext <;>
    simp [hadamard, sub_eq_add_neg, smul_add, add_assoc, add_left_comm,
      add_comm]

theorem hadamard_hadamard (u : H₂ (E := E)) :
    hadamard (hadamard u) = (2 : ℝ) • u := by
  have hu : to_doubled (WithLp.fst u) (WithLp.snd u) = u := by
    exact DoubledSpace.ext rfl rfl
  rw [← hu]
  apply DoubledSpace.ext <;>
    simp [hadamard, sub_eq_add_neg, smul_add, add_assoc, add_left_comm,
      add_comm]
  <;> module

theorem hadamardNormalized_involution (u : H₂ (E := E)) :
    hadamardNormalized (hadamardNormalized u) = u := by
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    simpa using (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hs0 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  simp only [hadamardNormalized]
  rw [hadamard_smul, hadamard_hadamard]
  simp only [smul_smul]
  congr 1
  field_simp [hs0, hs]
  simp [hs]

theorem splitKreinForm_smul (a b : ℝ) (u v : H₂ (E := E)) :
    splitKreinForm (a • u) (b • v) = a * b * splitKreinForm u v := by
  simp [splitKreinForm, real_inner_smul_left, real_inner_smul_right,
    mul_assoc]
  ring

theorem splitKreinForm_hadamardNormalized (u v : H₂ (E := E)) :
    splitKreinForm (hadamardNormalized u) (hadamardNormalized v) =
      chiralKreinForm u v := by
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    simpa using (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hs0 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  simp only [hadamardNormalized]
  rw [splitKreinForm_smul, splitKreinForm_hadamard]
  field_simp [hs0, hs]
  rw [hs]


end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinHadamard
