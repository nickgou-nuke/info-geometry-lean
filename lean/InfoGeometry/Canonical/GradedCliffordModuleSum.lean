/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AtiyahBottShapiroSymbol
import Mathlib.Algebra.Algebra.Prod
import Mathlib.LinearAlgebra.Prod

/-!
# Direct sums of actual graded Clifford modules and ABS symbols

The sum is the product carrier with the componentwise native Clifford action.
Its grading subspaces are linearly equivalent to the products of the original
grading subspaces. Under these equivalences the ABS symbol is the direct sum
of the original symbols. Additivity of grading dimensions is a consequence.
-/

noncomputable section

namespace InfoGeometry.Canonical.GradedCliffordModuleSum

open CliffordAlgebra
open PinOperatorFamilyBridge AtiyahBottShapiroSymbol

variable {M W V : Type*}
variable [AddCommGroup M] [Module ℝ M]
variable [AddCommGroup W] [Module ℝ W] [AddCommGroup V] [Module ℝ V]
variable {Q : QuadraticForm ℝ M}
variable (ρ : GradedCliffordOperatorRepresentation
  (R := ℝ) (M := M) (W := W) (Q := Q))
variable (σ : GradedCliffordOperatorRepresentation
  (R := ℝ) (M := M) (W := V) (Q := Q))

/-- The actual product carrier with componentwise action and grading. -/
def directSum : GradedCliffordOperatorRepresentation
    (R := ℝ) (M := M) (W := W × V) (Q := Q) where
  representation := (LinearMap.prodMapAlgHom ℝ W V).comp
    (ρ.representation.prod σ.representation)
  grading := ρ.grading.prodMap σ.grading
  grading_sq := by
    apply LinearMap.ext
    rintro ⟨w, v⟩
    change (ρ.grading (ρ.grading w), σ.grading (σ.grading v)) = (w, v)
    exact Prod.ext (ρ.grading_grading_apply w) (σ.grading_grading_apply v)
  generator_odd x := by
    apply LinearMap.ext
    rintro ⟨w, v⟩
    change (ρ.grading (ρ.representation (ι Q x) w) +
        ρ.representation (ι Q x) (ρ.grading w),
      σ.grading (σ.representation (ι Q x) v) +
        σ.representation (ι Q x) (σ.grading v)) = (0, 0)
    exact Prod.ext
      (congrArg (fun f : Module.End ℝ W => f w) (ρ.generator_odd x))
      (congrArg (fun f : Module.End ℝ V => f v) (σ.generator_odd x))

@[simp] theorem directSum_representation_apply (a : CliffordAlgebra Q) (p : W × V) :
    (directSum ρ σ).representation a p =
      (ρ.representation a p.1, σ.representation a p.2) := rfl

@[simp] theorem directSum_grading_apply (p : W × V) :
    (directSum ρ σ).grading p = (ρ.grading p.1, σ.grading p.2) := rfl

/-- The even subspace of the actual sum is the product of the even subspaces. -/
def evenDirectSumEquiv : evenSpace (directSum ρ σ) ≃ₗ[ℝ] evenSpace ρ × evenSpace σ where
  toFun p :=
    (⟨p.val.1, (mem_evenSpace_iff ρ _).mpr
      (congrArg Prod.fst ((mem_evenSpace_iff (directSum ρ σ) _).mp p.property))⟩,
     ⟨p.val.2, (mem_evenSpace_iff σ _).mpr
      (congrArg Prod.snd ((mem_evenSpace_iff (directSum ρ σ) _).mp p.property))⟩)
  invFun p := ⟨(p.1, p.2), (mem_evenSpace_iff (directSum ρ σ) _).mpr
    (Prod.ext ((mem_evenSpace_iff ρ _).mp p.1.property)
      ((mem_evenSpace_iff σ _).mp p.2.property))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The odd subspace of the actual sum is the product of the odd subspaces. -/
def oddDirectSumEquiv : oddSpace (directSum ρ σ) ≃ₗ[ℝ] oddSpace ρ × oddSpace σ where
  toFun p :=
    (⟨p.val.1, (mem_oddSpace_iff ρ _).mpr
      (congrArg Prod.fst ((mem_oddSpace_iff (directSum ρ σ) _).mp p.property))⟩,
     ⟨p.val.2, (mem_oddSpace_iff σ _).mpr
      (congrArg Prod.snd ((mem_oddSpace_iff (directSum ρ σ) _).mp p.property))⟩)
  invFun p := ⟨(p.1, p.2), (mem_oddSpace_iff (directSum ρ σ) _).mpr
    (Prod.ext ((mem_oddSpace_iff ρ _).mp p.1.property)
      ((mem_oddSpace_iff σ _).mp p.2.property))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full symbol on the sum is the sum of the two actual symbols. -/
theorem symbol_directSum (v : M) (w : oddSpace (directSum ρ σ)) :
    evenDirectSumEquiv ρ σ (symbol (directSum ρ σ) v w) =
      (symbol ρ v (oddDirectSumEquiv ρ σ w).1,
        symbol σ v (oddDirectSumEquiv ρ σ w).2) := rfl

/-- The inverse symbol has the same direct-sum compatibility. -/
theorem inverseSymbol_directSum (v : M) (w : evenSpace (directSum ρ σ)) :
    oddDirectSumEquiv ρ σ (inverseSymbol (directSum ρ σ) v w) =
      (inverseSymbol ρ v (evenDirectSumEquiv ρ σ w).1,
        inverseSymbol σ v (evenDirectSumEquiv ρ σ w).2) := rfl

/-- Additivity of even dimension is induced by the actual subspace equivalence. -/
theorem finrank_even_directSum [FiniteDimensional ℝ W] [FiniteDimensional ℝ V] :
    Module.finrank ℝ (evenSpace (directSum ρ σ)) =
      Module.finrank ℝ (evenSpace ρ) + Module.finrank ℝ (evenSpace σ) := by
  rw [(evenDirectSumEquiv ρ σ).finrank_eq, Module.finrank_prod]

/-- Additivity of odd dimension is induced by the actual subspace equivalence. -/
theorem finrank_odd_directSum [FiniteDimensional ℝ W] [FiniteDimensional ℝ V] :
    Module.finrank ℝ (oddSpace (directSum ρ σ)) =
      Module.finrank ℝ (oddSpace ρ) + Module.finrank ℝ (oddSpace σ) := by
  rw [(oddDirectSumEquiv ρ σ).finrank_eq, Module.finrank_prod]

end InfoGeometry.Canonical.GradedCliffordModuleSum
