import InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
import InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift

/-!
# Tensor-power Artin relations for the standard logarithmic Jordan object

The right-associated slice construction admits a short induction:

* generator zero acts by the checked-R on the first two factors;
* a successor generator is identity on the first factor and the corresponding
  generator on the tail;
* two successors are identity on the first two factors.

These formulas reduce every adjacent Artin relation to the local three-site
Yang--Baxter calculation and every far relation to disjoint tensor support.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations

open CategoryTheory
open scoped TensorProduct

open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
open InfoGeometry.Categorical.LogNilpotentCrossCheckedR
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
open InfoGeometry.Clifford.LogCftMonodromy

/-- Adjacent checked-R slice on the standard logarithmic tensor power. -/
def standardTensorPowerGenerator
    (n : ℕ) (i : Fin (n + 1)) :
    tensorPowerObj standardJordanObject (n + 2) ≃ₗ[ℂ]
      tensorPowerObj standardJordanObject (n + 2) :=
  braidGeneratorLinearEquiv
    standardJordanObject
      (symmetricSwapIso standardJordanObject standardJordanObject) n i

/-- Underlying action of the checked-R isomorphism on a pure tensor. -/
@[simp]
theorem standardPairIso_tmul
    (x y : standardJordanObject) :
      (symmetricSwapIso standardJordanObject standardJordanObject).hom.hom
        (x ⊗ₜ[ℂ] y) = y ⊗ₜ[ℂ] x := by
  change (TensorProduct.comm ℂ standardJordanObject.toLogEndModule.V
      standardJordanObject.toLogEndModule.V)
      (x ⊗ₜ[ℂ] y) = y ⊗ₜ[ℂ] x
  rw [TensorProduct.comm_tmul]

/-- The unique generator on the two-fold tensor power is the checked-R. -/
@[simp]
theorem standardTensorPowerGenerator_base_tmul
    (x y : standardJordanObject) :
    standardTensorPowerGenerator 0 (0 : Fin 1) (x ⊗ₜ[ℂ] y) =
      y ⊗ₜ[ℂ] x := by
  simpa [standardTensorPowerGenerator, braidGeneratorLinearEquiv,
    isoToLinearEquiv_apply] using standardPairIso_tmul x y

/-- Generator zero acts on the first two factors and leaves the remaining tail
untouched. -/
@[simp]
theorem standardTensorPowerGenerator_zero_tmul
    (n : ℕ) (x y : standardJordanObject)
    (t : tensorPowerObj standardJordanObject (n + 1)) :
      standardTensorPowerGenerator (n + 1) (0 : Fin (n + 2))
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] t)) =
      y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] t) := by
  dsimp [standardTensorPowerGenerator, braidGeneratorLinearEquiv,
    isoToLinearEquiv_apply, braidGeneratorIso]
  change (LogNilpotentModule.associatorIso standardJordanObject
      standardJordanObject (tensorPowerObj standardJordanObject (n + 1))).hom.hom
      ((tensorIso
        (standardJordanObject.symmetricSwapIso standardJordanObject)
        (Iso.refl (tensorPowerObj standardJordanObject (n + 1)))).hom.hom
        ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] t)) = _
  rw [tensorIso_hom_tmul, standardPairIso_tmul,
    LogNilpotentModule.associatorHom_tmul]
  simp

/-- A successor generator acts trivially on the first factor and recursively on
its tail. -/
@[simp]
theorem standardTensorPowerGenerator_succ_tmul
    (n : ℕ) (i : Fin (n + 1))
    (x : standardJordanObject)
    (t : tensorPowerObj standardJordanObject (n + 2)) :
    standardTensorPowerGenerator (n + 1) i.succ (x ⊗ₜ[ℂ] t) =
      x ⊗ₜ[ℂ] standardTensorPowerGenerator n i t := by
  simp [standardTensorPowerGenerator, braidGeneratorLinearEquiv,
    isoToLinearEquiv_apply, braidGeneratorIso, tensorIso]

/-- Two successor steps expose two spectator factors. -/
@[simp]
theorem standardTensorPowerGenerator_succ_succ_tmul
    (n : ℕ) (i : Fin (n + 1))
    (x y : standardJordanObject)
    (t : tensorPowerObj standardJordanObject (n + 2)) :
    standardTensorPowerGenerator (n + 2) i.succ.succ
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] t)) =
      x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] standardTensorPowerGenerator n i t) := by
  calc
    standardTensorPowerGenerator (n + 2) i.succ.succ
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] t)) =
        x ⊗ₜ[ℂ]
          standardTensorPowerGenerator (n + 1) i.succ (y ⊗ₜ[ℂ] t) := by
            simpa using standardTensorPowerGenerator_succ_tmul
              (n := n + 1) (i := i.succ) x (y ⊗ₜ[ℂ] t)
    _ = x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] standardTensorPowerGenerator n i t) := by
      rw [standardTensorPowerGenerator_succ_tmul]

/-- Local three-factor Artin relation, proved directly from the finite checked-R
formula. -/
theorem standardTensorPower_artin_three :
    standardTensorPowerGenerator 1 (0 : Fin 2) *
        standardTensorPowerGenerator 1 (1 : Fin 2) *
        standardTensorPowerGenerator 1 (0 : Fin 2) =
      standardTensorPowerGenerator 1 (1 : Fin 2) *
        standardTensorPowerGenerator 1 (0 : Fin 2) *
        standardTensorPowerGenerator 1 (1 : Fin 2) := by
  apply LinearEquiv.ext
  intro t
  have h := congrArg (fun e => e.hom t)
    InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategorical_artin
  simpa [standardTensorPowerGenerator, braidGeneratorLinearEquiv,
    isoToLinearEquiv_apply, braidGeneratorIso,
    standardSymmetricSigmaOne, standardSymmetricSigmaTwo,
    InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategoricalSigmaOne,
    InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategoricalSigmaTwo,
    LogNilpotentModule.hom_comp, Module.End.mul_eq_comp] using h

/-- The first two generator positions satisfy Artin on every longer tensor
power; all further factors are spectators. -/
theorem standardTensorPower_front_artin (n : ℕ) :
    standardTensorPowerGenerator (n + 2) (0 : Fin (n + 3)) *
        standardTensorPowerGenerator (n + 2) (1 : Fin (n + 3)) *
        standardTensorPowerGenerator (n + 2) (0 : Fin (n + 3)) =
      standardTensorPowerGenerator (n + 2) (1 : Fin (n + 3)) *
        standardTensorPowerGenerator (n + 2) (0 : Fin (n + 3)) *
        standardTensorPowerGenerator (n + 2) (1 : Fin (n + 3)) := by
  apply LinearEquiv.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro x tail
    refine TensorProduct.induction_on tail ?_ ?_ ?_
    · simp
    · intro y tail₂
      refine TensorProduct.induction_on tail₂ ?_ ?_ ?_
      · simp
      · intro z rest
        change (standardTensorPowerGenerator (n + 2) 0)
            ((standardTensorPowerGenerator (n + 2) 1)
              ((standardTensorPowerGenerator (n + 2) 0)
                (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest))))) =
          (standardTensorPowerGenerator (n + 2) 1)
            ((standardTensorPowerGenerator (n + 2) 0)
              ((standardTensorPowerGenerator (n + 2) 1)
                (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest)))))
        have h0 : standardTensorPowerGenerator (n + 2) (0 : Fin (n + 3))
              (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest))) =
            y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest)) := by
          simpa [Nat.add_assoc] using
            (standardTensorPowerGenerator_zero_tmul (n := n + 1) x y
              (z ⊗ₜ[ℂ] rest))
        rw [h0]
        have h1 : standardTensorPowerGenerator (n + 2) (1 : Fin (n + 3))
              (y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest))) =
            y ⊗ₜ[ℂ]
              (standardTensorPowerGenerator (n + 1) (0 : Fin (n + 2))
                (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest))) := by
          simpa [Nat.add_assoc] using
            (standardTensorPowerGenerator_succ_tmul (n := n + 1)
              (i := (0 : Fin (n + 2))) y (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest)))
        rw [h1]
        have h2 : standardTensorPowerGenerator (n + 1) (0 : Fin (n + 2))
              (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest)) =
            z ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] rest) := by
          simpa [Nat.add_assoc] using
            (standardTensorPowerGenerator_zero_tmul (n := n) x z rest)
        rw [h2]
        have h1x := standardTensorPowerGenerator_succ_tmul
          (n := n + 1) (i := (0 : Fin (n + 2))) x
            (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest))
        have h1y := standardTensorPowerGenerator_succ_tmul
          (n := n + 1) (i := (0 : Fin (n + 2))) y
            (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest))
        have h1x' :
            (standardTensorPowerGenerator (n + 2) 1)
                (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest))) =
              x ⊗ₜ[ℂ] (standardTensorPowerGenerator (n + 1) 0)
                (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest)) := by
          simpa [Nat.add_assoc] using h1x
        have h1y' :
            (standardTensorPowerGenerator (n + 2) 1)
                (y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest))) =
              y ⊗ₜ[ℂ] (standardTensorPowerGenerator (n + 1) 0)
                (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] rest)) := by
          simpa [Nat.add_assoc] using h1y
        have h2y := standardTensorPowerGenerator_zero_tmul
          (n := n) y z rest
        have h0' := standardTensorPowerGenerator_zero_tmul
          (n := n + 1) x z (y ⊗ₜ[ℂ] rest)
        have h1z := standardTensorPowerGenerator_succ_tmul
          (n := n + 1) (i := (0 : Fin (n + 2))) z
            (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] rest))
        have h1z' :
            (standardTensorPowerGenerator (n + 2) 1)
                (z ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] rest))) =
              z ⊗ₜ[ℂ] (standardTensorPowerGenerator (n + 1) 0)
                (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] rest)) := by
          simpa [Nat.add_assoc] using h1z
        have h0xy := standardTensorPowerGenerator_zero_tmul
          (n := n) x y rest
        have h0yz := standardTensorPowerGenerator_zero_tmul
          (n := n + 1) y z (x ⊗ₜ[ℂ] rest)
        rw [h1x', h2y, h0', h1z', h0xy, h0yz]
      · intro a b ha hb
        simpa only [TensorProduct.tmul_add, map_add] using
          congrArg₂ (· + ·) ha hb
    · intro a b ha hb
      simpa only [TensorProduct.tmul_add, map_add] using
        congrArg₂ (· + ·) ha hb
  · intro a b ha hb
    simpa only [map_add] using congrArg₂ (· + ·) ha hb

/-- Generator zero commutes with every generator supported at least two slots to
its right. -/
theorem standardTensorPower_front_far
    (n : ℕ) (j : Fin (n + 1)) :
    standardTensorPowerGenerator (n + 2) (0 : Fin (n + 3)) *
        standardTensorPowerGenerator (n + 2) j.succ.succ =
      standardTensorPowerGenerator (n + 2) j.succ.succ *
        standardTensorPowerGenerator (n + 2) (0 : Fin (n + 3)) := by
  apply LinearEquiv.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro x tail
    refine TensorProduct.induction_on tail ?_ ?_ ?_
    · simp
    · intro y rest
      change (standardTensorPowerGenerator (n + 2) 0)
          ((standardTensorPowerGenerator (n + 2) j.succ.succ)
            (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] rest))) =
        (standardTensorPowerGenerator (n + 2) j.succ.succ)
          ((standardTensorPowerGenerator (n + 2) 0)
            (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] rest)))
      simp only [standardTensorPowerGenerator_zero_tmul (n := n + 1),
        standardTensorPowerGenerator_succ_succ_tmul (n := n)]
    · intro a b ha hb
      simpa only [TensorProduct.tmul_add, map_add] using
        congrArg₂ (fun x₁ x₂ => x₁ + x₂) ha hb
  · intro a b ha hb
    simpa only [map_add] using congrArg₂ (fun x₁ x₂ => x₁ + x₂) ha hb

/-- Every adjacent pair of slice generators satisfies the Artin relation. -/
theorem standardTensorPower_artin
    (n : ℕ) (i : Fin (n + 1)) :
    standardTensorPowerGenerator (n + 1) i.castSucc *
        standardTensorPowerGenerator (n + 1) i.succ *
        standardTensorPowerGenerator (n + 1) i.castSucc =
      standardTensorPowerGenerator (n + 1) i.succ *
        standardTensorPowerGenerator (n + 1) i.castSucc *
        standardTensorPowerGenerator (n + 1) i.succ := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact standardTensorPower_artin_three
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [Nat.succ_eq_add_one] using standardTensorPower_front_artin n
      · apply LinearEquiv.ext
        intro t
        refine TensorProduct.induction_on t ?_ ?_ ?_
        · simp
        · intro x tail
          have htail := ih j
          have hpoint := congrArg (fun e => e tail) htail
          simpa [LinearEquiv.mul_apply,
            standardTensorPowerGenerator_succ_tmul] using
            congrArg (fun y => x ⊗ₜ[ℂ] y) hpoint
        · intro a b ha hb
          simpa only [TensorProduct.tmul_add, map_add] using
            congrArg₂ (fun x₁ x₂ => x₁ + x₂) ha hb

/-- Every pair of generators separated by at least one untouched strand
commutes.  This statement matches the repository's finite braid relation
encoding: positions `i` and `j+2`, with `i ≤ j`. -/
theorem standardTensorPower_far
    (n : ℕ) (i j : Fin (n + 1)) (hij : i ≤ j) :
    standardTensorPowerGenerator (n + 2) i.castSucc.castSucc *
        standardTensorPowerGenerator (n + 2) j.succ.succ =
      standardTensorPowerGenerator (n + 2) j.succ.succ *
        standardTensorPowerGenerator (n + 2) i.castSucc.castSucc := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      have hj : j = 0 := Fin.eq_zero j
      subst i
      subst j
      exact standardTensorPower_front_far 0 (0 : Fin 1)
  | succ n ih =>
      induction i using Fin.cases with
      | zero =>
          exact standardTensorPower_front_far (n + 1) j
      | succ i' =>
          induction j using Fin.cases with
          | zero =>
              exact (by simp at hij)
          | succ j' =>
              have hij' : i' ≤ j' := Fin.succ_le_succ_iff.mp hij
              apply LinearEquiv.ext
              intro t
              refine TensorProduct.induction_on t ?_ ?_ ?_
              · simp
              · intro x tail
                have htail := ih i' j' hij'
                have hpoint := congrArg (fun e => e tail) htail
                simpa [LinearEquiv.mul_apply,
                  standardTensorPowerGenerator_succ_tmul] using
                  congrArg (fun y => x ⊗ₜ[ℂ] y) hpoint
              · intro a b ha hb
                simpa only [TensorProduct.tmul_add, map_add] using
                  congrArg₂ (fun x₁ x₂ => x₁ + x₂) ha hb

end InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations
