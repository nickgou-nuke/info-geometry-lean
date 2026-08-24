import InfoGeometry.Algebra.JordanInnerDerivations
import InfoGeometry.Algebra.BaezF4H3Zorn

/-!
# Structure operators on the verified split-Albert carrier

This owner records the concrete operator calculation
`S(D,a) = D + L_a` on `H3Zorn ℝ`.  It is deliberately only an
operator-level bridge: it does not identify the resulting carrier with an
exceptional Lie algebra by dimension or naming.
-/

namespace InfoGeometry.Algebra.SplitAlbertStructureOperators

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn

abbrev JordanCarrier := H3Zorn ℝ
abbrev Operator := Module.End ℝ JordanCarrier
/- The derivation carrier is exposed directly from its native owner. -/

noncomputable def structureOperator (D : H3ZornF4Derivations) (a : JordanCarrier) : Operator :=
  (D : Operator) + jordanLmul (R := ℝ) a

theorem structureOperator_lie_formula
    (D E : H3ZornF4Derivations) (a b : JordanCarrier) :
    ⁅structureOperator D a, structureOperator E b⁆ =
      ⁅(D : Operator), (E : Operator)⁆
        + (h3ZornJordanInnerDerivation a b : Operator)
      + jordanLmul (R := ℝ)
            ((D : Operator) b - (E : Operator) a) := by
  apply LinearMap.ext
  intro x
  change
    ((D : Operator) + jordanLmul (R := ℝ) a)
          ((E : Operator) x + b * x) -
      ((E : Operator) + jordanLmul (R := ℝ) b)
          ((D : Operator) x + a * x) =
    ((D : Operator) ((E : Operator) x) -
        (E : Operator) ((D : Operator) x)) +
      (a * (b * x) - b * (a * x)) +
      ((D : Operator) b - (E : Operator) a) * x
  rw [map_add, map_add]
  simp only [LinearMap.add_apply]
  have hD := D.property b x
  have hE := E.property a x
  rw [hD, hE]
  simp only [jordanLmul_apply]
  rw [sub_mul]
  abel_nf

def structureOperatorCarrier : Set Operator :=
  {T | ∃ D : H3ZornF4Derivations, ∃ a : JordanCarrier,
      T = structureOperator D a}

def structureOperatorLieSubalgebra : LieSubalgebra ℝ Operator where
  carrier := structureOperatorCarrier
  zero_mem' := by
    refine ⟨0, 0, ?_⟩
    change (0 : Operator) = (0 : Operator) + jordanLmul (R := ℝ) 0
    rw [zero_add]
    apply LinearMap.ext
    intro x
    change (0 : JordanCarrier) = 0 * x
    rw [zero_mul]
  add_mem' := by
    rintro T U ⟨D, a, rfl⟩ ⟨E, b, rfl⟩
    refine ⟨D + E, a + b, ?_⟩
    apply LinearMap.ext
    intro x
    change
      ((D : Operator) x + a * x) + ((E : Operator) x + b * x) =
        ((D : Operator) x + (E : Operator) x) + (a + b) * x
    rw [add_mul]
    abel
  smul_mem' := by
    intro r T hT
    rcases hT with ⟨D, a, hT⟩
    refine ⟨r • D, r • a, ?_⟩
    rw [hT]
    apply LinearMap.ext
    intro x
    change r • ((D : Operator) x + a * x) =
      (r • (D : Operator)) x + (r • a) * x
    simp only [LinearMap.smul_apply, smul_add]
    have hmul : r • (a * x) = (r • a) * x := by
      simpa only [candidateJordanMul_eq_mul] using
        (candidateJordanMul_smul_left r a x).symm
    rw [hmul]
  lie_mem' := by
    rintro T U ⟨D, a, rfl⟩ ⟨E, b, rfl⟩
    have hab :
        (h3ZornJordanInnerDerivation a b : Operator) ∈ H3ZornF4Derivations :=
      h3ZornJordanInnerDerivation_mem_F4 a b
    let H : H3ZornF4Derivations := ⟨h3ZornJordanInnerDerivation a b, hab⟩
    refine ⟨⁅D, E⁆ + H, (D : Operator) b - (E : Operator) a, ?_⟩
    rw [structureOperator_lie_formula]
    rfl

theorem structureOperator_mem
    (D : H3ZornF4Derivations) (a : JordanCarrier) :
    structureOperator D a ∈ structureOperatorLieSubalgebra := by
  exact ⟨D, a, rfl⟩

theorem structureOperator_lie_mem
    (D E : H3ZornF4Derivations) (a b : JordanCarrier) :
    ⁅structureOperator D a, structureOperator E b⁆ ∈
      structureOperatorLieSubalgebra := by
  exact structureOperatorLieSubalgebra.lie_mem
    (structureOperator_mem D a) (structureOperator_mem E b)

end InfoGeometry.Algebra.SplitAlbertStructureOperators
