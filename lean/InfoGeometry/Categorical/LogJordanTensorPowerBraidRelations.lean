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
  change (symmetricSwapIso standardJordanObject standardJordanObject).hom.hom
    (x ⊗ₜ[ℂ] y) = y ⊗ₜ[ℂ] x
  exact standardPairIso_tmul x y

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
  have hswap :
      (tensorIso (standardJordanObject.symmetricSwapIso standardJordanObject)
        (Iso.refl (tensorPowerObj standardJordanObject (n + 1)))).hom.hom
        ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] t) = (y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] t := by
    let hxy : (standardJordanObject.tensorObj standardJordanObject).toLogEndModule.V :=
      x ⊗ₜ[ℂ] y
    have h := tensorIso_hom_tmul
      (standardJordanObject.symmetricSwapIso standardJordanObject)
      (Iso.refl (tensorPowerObj standardJordanObject (n + 1))) hxy t
    rw [standardPairIso_tmul] at h
    simp only [Iso.refl_hom, LogNilpotentModule.hom_id,
      LinearMap.id_apply] at h
    convert h using 1; rfl
  rw [hswap]
  exact LogNilpotentModule.associatorHom_tmul
    standardJordanObject standardJordanObject
    (tensorPowerObj standardJordanObject (n + 1)) y x t

/-- A successor generator acts trivially on the first factor and recursively on
its tail. -/
@[simp]
theorem standardTensorPowerGenerator_succ_tmul
    (n : ℕ) (i : Fin (n + 1))
    (x : standardJordanObject)
    (t : tensorPowerObj standardJordanObject (n + 2)) :
    standardTensorPowerGenerator (n + 1) i.succ (x ⊗ₜ[ℂ] t) =
      x ⊗ₜ[ℂ] standardTensorPowerGenerator n i t := by
  change (LogNilpotentModule.tensorHom (𝟙 standardJordanObject)
      (braidGeneratorIso standardJordanObject
        (standardJordanObject.symmetricSwapIso standardJordanObject) n i).hom).hom
      (x ⊗ₜ[ℂ] t) = x ⊗ₜ[ℂ]
        (standardTensorPowerGenerator n i t)
  exact LogNilpotentModule.tensorHom_tmul (𝟙 standardJordanObject)
    (braidGeneratorIso standardJordanObject
      (standardJordanObject.symmetricSwapIso standardJordanObject) n i).hom x t

/-- Two successor steps expose two spectator factors. -/
@[simp]
theorem standardTensorPowerGenerator_succ_succ_tmul
    (n : ℕ) (i : Fin (n + 1))
    (x y : standardJordanObject)
    (t : tensorPowerObj standardJordanObject (n + 2)) :
    standardTensorPowerGenerator (n + 2) i.succ.succ
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] t)) =
      x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] standardTensorPowerGenerator n i t) := by
  rw [standardTensorPowerGenerator_succ_tmul
    (n := n + 1) (i := i.succ) x (y ⊗ₜ[ℂ] t)]
  exact congrArg (fun z => x ⊗ₜ[ℂ] z)
    (standardTensorPowerGenerator_succ_tmul (n := n) (i := i) y t)

/-- Generator zero exchanges the first two bundled tensor factors. -/
theorem standardTensorPowerGenerator_zero_leftTmul
    (n : ℕ) (x y : standardJordanObject)
    (t : tensorPowerObj standardJordanObject (n + 1)) :
    standardTensorPowerGenerator (n + 1) (0 : Fin (n + 2))
        (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x
          (tensorPowerObj_succ_succ_leftTmul standardJordanObject n y t)) =
      tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y
        (tensorPowerObj_succ_succ_leftTmul standardJordanObject n x t) := by
  change standardTensorPowerGenerator (n + 1) (0 : Fin (n + 2))
      (x ⊗ₜ[ℂ] (tensorPowerObj_succ_succ_leftTmul standardJordanObject n y t)) =
    y ⊗ₜ[ℂ] (tensorPowerObj_succ_succ_leftTmul standardJordanObject n x t)
  rw [tensorPowerObj_succ_succ_leftTmul_tmul,
    tensorPowerObj_succ_succ_leftTmul_tmul]
  exact standardTensorPowerGenerator_zero_tmul n x y t

/-- A successor generator acts on a bundled tensor tail by the corresponding
tail generator, leaving the first factor fixed. -/
theorem standardTensorPowerGenerator_succ_leftTmul
    (n : ℕ) (i : Fin (n + 2))
    (x : standardJordanObject)
    (t : tensorPowerObj standardJordanObject (n + 3)) :
    standardTensorPowerGenerator (n + 2) i.succ
        (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x t) =
      tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x
        (standardTensorPowerGenerator (n + 1) i t) := by
  change standardTensorPowerGenerator (n + 2) i.succ (x ⊗ₜ[ℂ] t) =
    x ⊗ₜ[ℂ] standardTensorPowerGenerator (n + 1) i t
  exact standardTensorPowerGenerator_succ_tmul (n + 1) i x t

/-- Two successor steps act on the bundled tail after two fixed factors. -/
theorem standardTensorPowerGenerator_succ_succ_leftTmul
    (n : ℕ) (i : Fin (n + 1))
    (x y : standardJordanObject)
    (t : tensorPowerObj standardJordanObject (n + 2)) :
    standardTensorPowerGenerator (n + 2) i.succ.succ
        (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x
          (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y t)) =
      tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x
        (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y
          (standardTensorPowerGenerator n i t)) := by
  change standardTensorPowerGenerator (n + 2) i.succ.succ
      (x ⊗ₜ[ℂ] (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y t)) =
    x ⊗ₜ[ℂ] (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y
      (standardTensorPowerGenerator n i t))
  rw [tensorPowerObj_succ_succ_leftTmul_tmul,
    tensorPowerObj_succ_succ_leftTmul_tmul]
  exact standardTensorPowerGenerator_succ_succ_tmul n i x y t

/-- Local three-factor Artin relation, proved directly from the finite checked-R
formula. -/
theorem standardTensorPowerGenerator_three_zero_apply
    (t : tensorPowerObj standardJordanObject 3) :
    standardTensorPowerGenerator 1 (0 : Fin 2) t =
      _root_.InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategoricalSigmaOne.hom t := by
  rfl

theorem standardTensorPowerGenerator_three_one_apply
    (t : tensorPowerObj standardJordanObject 3) :
    standardTensorPowerGenerator 1 (1 : Fin 2) t =
      _root_.InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategoricalSigmaTwo.hom t := by
  rfl

theorem standardTensorPowerGenerator_three_zero_linearMap :
    (standardTensorPowerGenerator 1 (0 : Fin 2)).toLinearMap =
      _root_.InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategoricalSigmaOne.hom := by
  ext t
  exact standardTensorPowerGenerator_three_zero_apply t

theorem standardTensorPowerGenerator_three_one_linearMap :
    (standardTensorPowerGenerator 1 (1 : Fin 2)).toLinearMap =
      _root_.InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategoricalSigmaTwo.hom := by
  ext t
  exact standardTensorPowerGenerator_three_one_apply t

theorem standardTensorPower_artin_three :
    standardTensorPowerGenerator 1 (0 : Fin 2) *
        standardTensorPowerGenerator 1 (1 : Fin 2) *
        standardTensorPowerGenerator 1 (0 : Fin 2) =
      standardTensorPowerGenerator 1 (1 : Fin 2) *
        standardTensorPowerGenerator 1 (0 : Fin 2) *
        standardTensorPowerGenerator 1 (1 : Fin 2) := by
  apply LinearEquiv.ext
  intro t
  change (standardTensorPowerGenerator 1 0)
      ((standardTensorPowerGenerator 1 1)
        ((standardTensorPowerGenerator 1 0) t)) =
    (standardTensorPowerGenerator 1 1)
      ((standardTensorPowerGenerator 1 0)
        ((standardTensorPowerGenerator 1 1) t))
  rw [standardTensorPowerGenerator_three_zero_apply,
    standardTensorPowerGenerator_three_one_apply,
    standardTensorPowerGenerator_three_zero_apply,
    standardTensorPowerGenerator_three_one_apply,
    standardTensorPowerGenerator_three_zero_apply,
    standardTensorPowerGenerator_three_one_apply]
  have h := congrArg (fun e => e.hom t)
    _root_.InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategorical_artin
  change (((_root_.InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategoricalSigmaOne.hom.comp
      _root_.InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategoricalSigmaTwo.hom).comp
      _root_.InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategoricalSigmaOne.hom) t) =
    (((_root_.InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategoricalSigmaTwo.hom.comp
      _root_.InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategoricalSigmaOne.hom).comp
      _root_.InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift.standardCategoricalSigmaTwo.hom) t)
  exact h

/-- The first two generator positions satisfy Artin on every longer tensor
power; all further factors are spectators. -/
theorem standardTensorPower_front_artin (n : ℕ) :
    standardTensorPowerGenerator (n + 1 + 1) (0 : Fin (n + 1 + 1 + 1)) *
        standardTensorPowerGenerator (n + 1 + 1) (1 : Fin (n + 1 + 1 + 1)) *
        standardTensorPowerGenerator (n + 1 + 1) (0 : Fin (n + 1 + 1 + 1)) =
      standardTensorPowerGenerator (n + 1 + 1) (1 : Fin (n + 1 + 1 + 1)) *
        standardTensorPowerGenerator (n + 1 + 1) (0 : Fin (n + 1 + 1 + 1)) *
        standardTensorPowerGenerator (n + 1 + 1) (1 : Fin (n + 1 + 1 + 1)) := by
  apply LinearEquiv.ext
  intro t
  refine tensorPowerObj_succ_succ_induction standardJordanObject (n + 2)
    (P := fun u =>
      (standardTensorPowerGenerator (n + 2) 0 *
          standardTensorPowerGenerator (n + 2) 1 *
          standardTensorPowerGenerator (n + 2) 0) u =
        (standardTensorPowerGenerator (n + 2) 1 *
          standardTensorPowerGenerator (n + 2) 0 *
          standardTensorPowerGenerator (n + 2) 1) u) ?_ ?_ t
  · intro x tail
    refine tensorPowerObj_succ_succ_induction standardJordanObject (n + 1)
      (P := fun u =>
        (standardTensorPowerGenerator (n + 2) 0 *
            standardTensorPowerGenerator (n + 2) 1 *
            standardTensorPowerGenerator (n + 2) 0)
            (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x u) =
          (standardTensorPowerGenerator (n + 2) 1 *
            standardTensorPowerGenerator (n + 2) 0 *
            standardTensorPowerGenerator (n + 2) 1)
            (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x u)) ?_ ?_ tail
    · intro y rest
      refine tensorPowerObj_succ_succ_induction standardJordanObject n
        (P := fun u =>
          (standardTensorPowerGenerator (n + 2) 0 *
              standardTensorPowerGenerator (n + 2) 1 *
              standardTensorPowerGenerator (n + 2) 0)
              (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x
                (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y u)) =
            (standardTensorPowerGenerator (n + 2) 1 *
              standardTensorPowerGenerator (n + 2) 0 *
              standardTensorPowerGenerator (n + 2) 1)
              (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x
                (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y u))) ?_ ?_ rest
      · intro z w
        change standardTensorPowerGenerator (n + 2) 0
            (standardTensorPowerGenerator (n + 2) 1
              (standardTensorPowerGenerator (n + 2) 0
                (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x
                  (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject n z w))))) =
          standardTensorPowerGenerator (n + 2) 1
            (standardTensorPowerGenerator (n + 2) 0
              (standardTensorPowerGenerator (n + 2) 1
                (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x
                  (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject n z w)))))
        rw [standardTensorPowerGenerator_zero_leftTmul (n + 1) x y
          (tensorPowerObj_succ_succ_leftTmul standardJordanObject n z w)]
        have h1 : (1 : Fin (n + 3)) = (0 : Fin (n + 2)).succ := by
          apply Fin.ext
          rfl
        rw [h1]
        rw [standardTensorPowerGenerator_succ_leftTmul n (0 : Fin (n + 2)) y
          (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x
            (tensorPowerObj_succ_succ_leftTmul standardJordanObject n z w))]
        rw [standardTensorPowerGenerator_zero_leftTmul n x z w]
        rw [standardTensorPowerGenerator_zero_leftTmul (n + 1) y z
          (tensorPowerObj_succ_succ_leftTmul standardJordanObject n x w)]
        rw [standardTensorPowerGenerator_succ_leftTmul n (0 : Fin (n + 2)) x
          (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y
            (tensorPowerObj_succ_succ_leftTmul standardJordanObject n z w))]
        rw [standardTensorPowerGenerator_zero_leftTmul n y z w]
        rw [standardTensorPowerGenerator_zero_leftTmul (n + 1) x z
          (tensorPowerObj_succ_succ_leftTmul standardJordanObject n y w)]
        rw [standardTensorPowerGenerator_succ_leftTmul n (0 : Fin (n + 2)) z
          (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x
            (tensorPowerObj_succ_succ_leftTmul standardJordanObject n y w))]
        rw [standardTensorPowerGenerator_zero_leftTmul n x y w]
      · intro a b ha hb
        simp only [LinearEquiv.mul_apply, map_add, ha, hb]
    · intro a b ha hb
      simp only [LinearEquiv.mul_apply, map_add, ha, hb]
  · intro a b ha hb
    simp only [LinearEquiv.mul_apply, map_add, ha, hb]

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
  refine tensorPowerObj_succ_succ_induction standardJordanObject (n + 2)
    (P := fun u =>
      (standardTensorPowerGenerator (n + 2) 0 *
          standardTensorPowerGenerator (n + 2) j.succ.succ) u =
        (standardTensorPowerGenerator (n + 2) j.succ.succ *
          standardTensorPowerGenerator (n + 2) 0) u) ?_ ?_ t
  · intro x tail
    refine tensorPowerObj_succ_succ_induction standardJordanObject (n + 1)
      (P := fun u =>
        (standardTensorPowerGenerator (n + 2) 0 *
            standardTensorPowerGenerator (n + 2) j.succ.succ)
            (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x u) =
          (standardTensorPowerGenerator (n + 2) j.succ.succ *
            standardTensorPowerGenerator (n + 2) 0)
            (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x u)) ?_ ?_ tail
    · intro y rest
      change standardTensorPowerGenerator (n + 2) 0
          (standardTensorPowerGenerator (n + 2) j.succ.succ
            (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x
              (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y rest))) =
        standardTensorPowerGenerator (n + 2) j.succ.succ
          (standardTensorPowerGenerator (n + 2) 0
            (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x
              (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y rest)))
      rw [standardTensorPowerGenerator_succ_succ_leftTmul n j x y rest]
      rw [standardTensorPowerGenerator_zero_leftTmul (n + 1) x y
        (standardTensorPowerGenerator n j rest)]
      rw [standardTensorPowerGenerator_zero_leftTmul (n + 1) x y rest]
      rw [standardTensorPowerGenerator_succ_succ_leftTmul n j y x rest]
    · intro a b ha hb
      simp only [LinearEquiv.mul_apply, map_add, ha, hb]
  · intro a b ha hb
    simp only [LinearEquiv.mul_apply, map_add, ha, hb]

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
        refine tensorPowerObj_succ_succ_induction standardJordanObject (n + 2)
          (P := fun u =>
            (standardTensorPowerGenerator (n + 2) j.castSucc.succ *
                standardTensorPowerGenerator (n + 2) j.succ.succ *
                standardTensorPowerGenerator (n + 2) j.castSucc.succ) u =
              (standardTensorPowerGenerator (n + 2) j.succ.succ *
                standardTensorPowerGenerator (n + 2) j.castSucc.succ *
                standardTensorPowerGenerator (n + 2) j.succ.succ) u) ?_ ?_ t
        · intro x tail
          have hpoint := congrArg (fun e => e tail) (ih j)
          change standardTensorPowerGenerator (n + 2) j.castSucc.succ
              (standardTensorPowerGenerator (n + 2) j.succ.succ
                (standardTensorPowerGenerator (n + 2) j.castSucc.succ
                  (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x tail))) =
            standardTensorPowerGenerator (n + 2) j.succ.succ
              (standardTensorPowerGenerator (n + 2) j.castSucc.succ
                (standardTensorPowerGenerator (n + 2) j.succ.succ
                  (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x tail)))
          rw [standardTensorPowerGenerator_succ_leftTmul n j.castSucc x tail]
          rw [standardTensorPowerGenerator_succ_leftTmul n j.succ x
            (standardTensorPowerGenerator (n + 1) j.castSucc tail)]
          rw [standardTensorPowerGenerator_succ_leftTmul n j.castSucc x
            (standardTensorPowerGenerator (n + 1) j.succ
              (standardTensorPowerGenerator (n + 1) j.castSucc tail))]
          rw [standardTensorPowerGenerator_succ_leftTmul n j.succ x tail]
          rw [standardTensorPowerGenerator_succ_leftTmul n j.castSucc x
            (standardTensorPowerGenerator (n + 1) j.succ tail)]
          rw [standardTensorPowerGenerator_succ_leftTmul n j.succ x
            (standardTensorPowerGenerator (n + 1) j.castSucc
              (standardTensorPowerGenerator (n + 1) j.succ tail))]
          exact congrArg (tensorPowerObj_succ_succ_leftTmul
            standardJordanObject (n + 2) x) hpoint
        · intro a b ha hb
          simp only [LinearEquiv.mul_apply, map_add, ha, hb]

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
              refine tensorPowerObj_succ_succ_induction standardJordanObject (n + 3)
                (P := fun u =>
                  (standardTensorPowerGenerator (n + 3)
                      i'.castSucc.castSucc.succ *
                    standardTensorPowerGenerator (n + 3) j'.succ.succ.succ) u =
                  (standardTensorPowerGenerator (n + 3)
                      j'.succ.succ.succ *
                    standardTensorPowerGenerator (n + 3)
                      i'.castSucc.castSucc.succ) u) ?_ ?_ t
              · intro x tail
                have hpoint := congrArg (fun e => e tail) (ih i' j' hij')
                change standardTensorPowerGenerator (n + 3)
                      i'.castSucc.castSucc.succ
                    (standardTensorPowerGenerator (n + 3) j'.succ.succ.succ
                      (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 3) x tail)) =
                  standardTensorPowerGenerator (n + 3) j'.succ.succ.succ
                    (standardTensorPowerGenerator (n + 3)
                      i'.castSucc.castSucc.succ
                      (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 3) x tail))
                calc
                  _ = tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 3) x
                        (standardTensorPowerGenerator (n + 2)
                          i'.castSucc.castSucc
                          (standardTensorPowerGenerator (n + 2) j'.succ.succ tail)) := by
                        rw [standardTensorPowerGenerator_succ_leftTmul (n + 1)
                          j'.succ.succ x tail]
                        rw [standardTensorPowerGenerator_succ_leftTmul (n + 1)
                          i'.castSucc.castSucc x
                          (standardTensorPowerGenerator (n + 2) j'.succ.succ tail)]
                  _ = tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 3) x
                        (standardTensorPowerGenerator (n + 2) j'.succ.succ
                          (standardTensorPowerGenerator (n + 2)
                            i'.castSucc.castSucc tail)) := by
                        exact congrArg
                          (tensorPowerObj_succ_succ_leftTmul
                            standardJordanObject (n + 3) x) hpoint
                  _ = standardTensorPowerGenerator (n + 3) j'.succ.succ.succ
                        (standardTensorPowerGenerator (n + 3)
                          i'.castSucc.castSucc.succ
                          (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 3) x tail)) := by
                        rw [standardTensorPowerGenerator_succ_leftTmul (n + 1)
                          i'.castSucc.castSucc x tail]
                        rw [standardTensorPowerGenerator_succ_leftTmul (n + 1)
                          j'.succ.succ x
                          (standardTensorPowerGenerator (n + 2)
                            i'.castSucc.castSucc tail)]
              · intro a b ha hb
                simp only [LinearEquiv.mul_apply, map_add, ha, hb]

end InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations
