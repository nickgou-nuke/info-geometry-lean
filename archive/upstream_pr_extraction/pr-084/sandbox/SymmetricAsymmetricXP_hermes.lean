import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open Complex

/-! # Symmetric / Asymmetric XP Splitting

This module formalizes the exact canonical decomposition of the first-quantized
operator x̂p̂ into its symmetric (Weyl-ordered dilation) and antisymmetric
(commutator) sectors.

This is an EXACT COPY of `FirstQuantizedChiralConeBridge.lean` (lines 308-359)
under `BoundedCanonicalPair`. -/

section BoundedCanonicalPair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A bounded canonical pair with explicit central commutator [x̂, p̂] = iℏ -/
structure BoundedCanonicalPair where
  xOp : E →L[ℂ] E
  pOp : E →L[ℂ] E
  hbar : ℝ
  commutation :
    xOp.comp pOp - pOp.comp xOp =
      (Complex.I * (hbar : ℂ)) • ContinuousLinearMap.id ℂ E

namespace BoundedCanonicalPair

variable (C : BoundedCanonicalPair (E := E))

/-- Weyl-ordered symmetric dilation operator: Ĥ_sym = ½(x̂p̂ + p̂x̂) -/
noncomputable def symmetric : E →L[ℂ] E :=
  (1 / 2 : ℂ) • (C.xOp.comp C.pOp + C.pOp.comp C.xOp)

/-- Antisymmetric commutator sector: Ĥ_asym = ½(x̂p̂ - p̂x̂) -/
noncomputable def antisymmetric : E →L[ℂ] E :=
  (1 / 2 : ℂ) • (C.xOp.comp C.pOp - C.pOp.comp C.xOp)

/-- Theorem 1: Exact operator decomposition x̂p̂ = Ĥ_sym + Ĥ_asym -/
theorem xp_eq_symmetric_add_antisymmetric :
    C.xOp.comp C.pOp = C.symmetric + C.antisymmetric := by
  dsimp [symmetric, antisymmetric]
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  <;> module

/-- Theorem 2: The antisymmetric sector is the central scalar iℏ/2 -/
theorem antisymmetric_eq_central_scalar :
    C.antisymmetric = ((Complex.I * (C.hbar : ℂ)) / 2) • ContinuousLinearMap.id ℂ E := by
  dsimp [antisymmetric]
  rw [C.commutation]
  <;> module

/-- Theorem 3: The symmetric operator is x̂p̂ shifted by -iℏ/2 -/
theorem symmetric_eq_xp_sub_central :
    C.symmetric = C.xOp.comp C.pOp - ((Complex.I * (C.hbar : ℂ)) / 2) • ContinuousLinearMap.id ℂ E := by
  have hsplit := xp_eq_symmetric_add_antisymmetric
  have hasym := antisymmetric_eq_central_scalar
  rw [hasym] at hsplit
  exact eq_sub_of_add_eq' (by simpa [add_comm] using hsplit.symm)

end BoundedCanonicalPair

end BoundedCanonicalPair