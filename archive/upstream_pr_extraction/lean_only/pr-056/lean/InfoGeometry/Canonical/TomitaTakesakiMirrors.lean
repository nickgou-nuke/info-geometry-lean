import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Clifford.SplitQ44
import InfoGeometry.Clifford.Cl44Witt
import InfoGeometry.Canonical.TopologicalKMSFlow

/-!
# Tomita-Takesaki Mirrors in the Clifford Algebra

This file implements the modular conjugation operator $J$ (the Tomita-Takesaki mirror)
natively in the split `Cl(4,4)` algebra.

We construct $J$ as an orthogonal reflection on the vector space that swaps
the chiral parity/mode sheets (i.e., mapping creation operators to annihilation operators).

Then, we prove the fundamental Tomita-Takesaki theorem for the KMS modular flow:
$$ J \circ \alpha_t \circ J = \alpha_{-t} $$
which states that the modular conjugation acts as CPT time-reversal on the thermodynamic flow.
-/

noncomputable section

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Canonical.TopologicalKMSFlow
open CliffordAlgebra

namespace InfoGeometry.Canonical.TomitaTakesakiMirrors

variable (E μ : Fin 4 → ℝ)

/-- 
The vector space reflection that acts as the Tomita-Takesaki mirror $J$.
It preserves the $e$-modes and reflects the $f$-modes, which exactly swaps
the creation and annihilation operators.
-/
def modularConjugationFun (x : Fin 8 → ℝ) : Fin 8 → ℝ
  | 0 => x 0
  | 1 => x 1
  | 2 => x 2
  | 3 => x 3
  | 4 => - x 4
  | 5 => - x 5
  | 6 => - x 6
  | 7 => - x 7

lemma modularConjugationFun_add (x y : Fin 8 → ℝ) :
    modularConjugationFun (x + y) = modularConjugationFun x + modularConjugationFun y := by
  ext j; fin_cases j <;> simp [modularConjugationFun, Pi.add_apply] <;> ring

lemma modularConjugationFun_smul (c : ℝ) (x : Fin 8 → ℝ) :
    modularConjugationFun (c • x) = c • modularConjugationFun x := by
  ext j; fin_cases j <;> simp [modularConjugationFun, Pi.smul_apply]

/-- The modular conjugation is an isometry of the split quadratic form. -/
theorem modularConjugation_preserves_Q (x : Fin 8 → ℝ) :
    splitQ44 (modularConjugationFun x) = splitQ44 x := by
  simp [splitQ44_apply, modularConjugationFun]

/-- The modular conjugation as a linear equivalence on the vector space. -/
noncomputable def modularConjugationIsometryEquiv : QuadraticMap.IsometryEquiv splitQ44 splitQ44 where
  toFun := modularConjugationFun
  invFun := modularConjugationFun
  map_add' := modularConjugationFun_add
  map_smul' := modularConjugationFun_smul
  left_inv x := by ext j; fin_cases j <;> simp [modularConjugationFun]
  right_inv x := by ext j; fin_cases j <;> simp [modularConjugationFun]
  map_app' x := modularConjugation_preserves_Q x

/-- 
The Tomita-Takesaki mirror $J$ lifted to a full algebra automorphism on `Cl(4,4)`.
-/
noncomputable def modularConjugation : Cl44 ≃ₐ[ℝ] Cl44 :=
  CliffordAlgebra.equivOfIsometry modularConjugationIsometryEquiv

/-- 
The fundamental Tomita-Takesaki time-reversal theorem:
$$ J \circ \alpha_t \circ J^{-1} = \alpha_{-t} $$
proved natively on the vector space generators.
-/
theorem modularConjugation_reverses_flow (t : ℝ) (x : Fin 8 → ℝ) :
    modularConjugationFun (boostFun E μ t (modularConjugationFun x)) = boostFun E μ (-t) x := by
  ext j
  fin_cases j <;> simp [modularConjugationFun, boostFun, Real.cosh_neg, Real.sinh_neg] <;> ring

/--
The lifted algebra formulation of the Tomita-Takesaki time-reversal.
Applying $J$ before and after the modular flow exactly reverses the direction of time.
-/
theorem J_alpha_J_eq_alpha_inv (t : ℝ) :
    (modularConjugation : Cl44 →ₐ[ℝ] Cl44).comp ((modularFlow E μ t : Cl44 →ₐ[ℝ] Cl44).comp (modularConjugation : Cl44 →ₐ[ℝ] Cl44)) =
    (modularFlow E μ (-t) : Cl44 →ₐ[ℝ] Cl44) := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  simp only [AlgHom.comp_apply, AlgHom.toLinearMap_apply, LinearMap.comp_apply]
  change CliffordAlgebra.map modularConjugationIsometryEquiv.toIsometry (
           CliffordAlgebra.map (boostIsometryEquiv E μ t).toIsometry (
             CliffordAlgebra.map modularConjugationIsometryEquiv.toIsometry (ι splitQ44 x)
           )
         ) = CliffordAlgebra.map (boostIsometryEquiv E μ (-t)).toIsometry (ι splitQ44 x)
  rw [CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι]
  exact congrArg (ι splitQ44) (modularConjugation_reverses_flow E μ t x)

end InfoGeometry.Canonical.TomitaTakesakiMirrors
