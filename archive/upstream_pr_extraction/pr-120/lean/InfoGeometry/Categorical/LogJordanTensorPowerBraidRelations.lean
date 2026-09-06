import InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
import InfoGeometry.Categorical.LogJordanCheckedRBraidBridge

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
    standardJordanObject standardHadjiivanovCheckedRLogIso n i

/-- Underlying action of the checked-R isomorphism on a pure tensor. -/
@[simp]
theorem standardPairIso_tmul
    (x y : standardJordanObject) :
    standardHadjiivanovCheckedRLogIso.hom.hom (x ⊗ₜ[ℂ] y) =
      y ⊗ₜ[ℂ] x + logShearBase •
        (standardJordanObject.N y ⊗ₜ[ℂ] standardJordanObject.N x) := by
  simp [standardHadjiivanovCheckedRLogIso, logCheckedRLogIso,
    checkedRIso, checkedRHom, standardHadjiivanovCheckedRDatum,
    logCheckedRDatum, logCheckedR_tmul]

/-- The unique generator on the two-fold tensor power is the checked-R. -/
@[simp]
theorem standardTensorPowerGenerator_base_tmul
    (x y : standardJordanObject) :
    standardTensorPowerGenerator 0 (0 : Fin 1) (x ⊗ₜ[ℂ] y) =
      y ⊗ₜ[ℂ] x + logShearBase •
        (standardJordanObject.N y ⊗ₜ[ℂ] standardJordanObject.N x) := by
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
      y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] t) +
        logShearBase •
          (standardJordanObject.N y ⊗ₜ[ℂ]
            (standardJordanObject.N x ⊗ₜ[ℂ] t)) := by
  simp [standardTensorPowerGenerator, braidGeneratorLinearEquiv,
    isoToLinearEquiv_apply, braidGeneratorIso, tensorIso,
    standardPairIso_tmul]

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
  simp [standardTensorPowerGenerator_succ_tmul]

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
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro x tail
    refine TensorProduct.induction_on tail ?_ ?_ ?_
    · simp
    · intro y z
      simp [LinearEquiv.mul_apply, standardTensorPowerGenerator_zero_tmul,
        standardTensorPowerGenerator_succ_tmul,
        standardTensorPowerGenerator_base_tmul,
        standardJordanObject_N_e0, standardJordanObject_N_e1,
        standardJordanObject_sq_zero, pow_two, Module.End.mul_eq_comp]
      have hx := congrArg (fun T : Module.End ℂ standardJordanObject => T x)
        standardJordanObject_sq_zero
      have hy := congrArg (fun T : Module.End ℂ standardJordanObject => T y)
        standardJordanObject_sq_zero
      have hz := congrArg (fun T : Module.End ℂ standardJordanObject => T z)
        standardJordanObject_sq_zero
      simp [pow_two, Module.End.mul_eq_comp, LinearMap.comp_apply] at hx hy hz
      simp [hx, hy, hz]
      module
    · intro a b ha hb
      simp [map_add, ha, hb]
  · intro a b ha hb
    simp [map_add, ha, hb]

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
        have hx := congrArg (fun T : Module.End ℂ standardJordanObject => T x)
          standardJordanObject_sq_zero
        have hy := congrArg (fun T : Module.End ℂ standardJordanObject => T y)
          standardJordanObject_sq_zero
        have hz := congrArg (fun T : Module.End ℂ standardJordanObject => T z)
          standardJordanObject_sq_zero
        simp [pow_two, Module.End.mul_eq_comp, LinearMap.comp_apply] at hx hy hz
        simp [LinearEquiv.mul_apply, standardTensorPowerGenerator_zero_tmul,
          standardTensorPowerGenerator_succ_tmul,
          standardTensorPowerGenerator_base_tmul, hx, hy, hz]
        module
      · intro a b ha hb
        simp [map_add, ha, hb]
    · intro a b ha hb
      simp [map_add, ha, hb]
  · intro a b ha hb
    simp [map_add, ha, hb]

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
      simp [LinearEquiv.mul_apply, standardTensorPowerGenerator_zero_tmul,
        standardTensorPowerGenerator_succ_succ_tmul]
      module
    · intro a b ha hb
      simp [map_add, ha, hb]
  · intro a b ha hb
    simp [map_add, ha, hb]

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
      have hi : i = 0 := Subsingleton.elim _ _
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
          simp [map_add, ha, hb]

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
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i
      subst j
      exact standardTensorPower_front_far 0 (0 : Fin 1)
  | succ n ih =>
      refine Fin.cases ?_ (fun i' => ?_) i
      · exact standardTensorPower_front_far (n + 1) j
      · refine Fin.cases ?_ (fun j' => ?_) j
        · have hfalse : ¬ ((Fin.succ i' : Fin (n + 2)) ≤ (0 : Fin (n + 2))) := by
            simp
          exact False.elim (hfalse hij)
        · have hij' : i' ≤ j' := by
            exact Fin.succ_le_succ_iff.mp hij
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
            simp [map_add, ha, hb]

end InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations
