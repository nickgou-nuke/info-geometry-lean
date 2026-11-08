/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Faithfulness and the universal star map of the real matrix tower

The carrier, bonding maps, star operation and ring universal map in this file
are those of `Cl11TensorTowerLimit` and `DirectLimitSuperClosureLemmas`.
The first branch proves reflection through the actual injective matrix-stage
maps. The second proves that star preservation and injectivity of the existing
universal map are detected on the finite stages. Its native `StarAlgHom`
packaging uses the existing real algebra action on the same colimit.
Faithful inclusions of the full matrix stages also prove that this real
algebraic limit is not finite dimensional.

The Gram identities below are algebraic factorization identities. No order,
norm, completion or spectral lower bound is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.RealStarColimitUniversal

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-- Faithfulness comes from the actual maps `A ↦ A ⊗ I₂`. -/
theorem ofStage_injective (n : ℕ) : Function.Injective (ofStage n) := by
  apply directLimitOf_injective stageBond
  intro k
  change Function.Injective (matStageEmbed k)
  exact matStageEmbed_injective k

/-- A finite matrix vanishes in the algebraic colimit exactly when it vanishes
at its source stage. -/
@[simp] theorem ofStage_eq_zero_iff (n : ℕ) (x : Stage n) :
    ofStage n x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply ofStage_injective n
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- The faithful stage maps reflect commutation, without any ambient
commutativity assumption. -/
theorem ofStage_commute_iff (n : ℕ) (x y : Stage n) :
    Commute (ofStage n x) (ofStage n y) ↔ Commute x y := by
  change ofStage n x * ofStage n y = ofStage n y * ofStage n x ↔
    x * y = y * x
  rw [← (ofStage n).map_mul, ← (ofStage n).map_mul]
  exact ⟨fun h => ofStage_injective n h, fun h => congrArg (ofStage n) h⟩

/-- The native commutator cannot become zero after faithful stage inclusion. -/
theorem ofStage_bracket_ne_zero_iff (n : ℕ) (x y : Stage n) :
    ⁅ofStage n x, ofStage n y⁆ ≠ 0 ↔ ⁅x, y⁆ ≠ 0 := by
  have hmap : ofStage n ⁅x, y⁆ = ⁅ofStage n x, ofStage n y⁆ := by
    simp only [Ring.lie_def, map_sub, map_mul]
  rw [← hmap]
  exact not_congr (ofStage_eq_zero_iff n ⁅x, y⁆)

/-- The existing star on the colimit and faithfulness reflect self-adjointness. -/
theorem ofStage_isSelfAdjoint_iff (n : ℕ) (x : Stage n) :
    IsSelfAdjoint (ofStage n x) ↔ IsSelfAdjoint x := by
  change star (ofStage n x) = ofStage n x ↔ star x = x
  rw [← ofStage_star]
  exact ⟨fun h => ofStage_injective n h, fun h => congrArg (ofStage n) h⟩

/-- The actual algebraic colimit of the full real matrix stages is not a
finite-dimensional real vector space. -/
theorem limit_not_finite : ¬ Module.Finite ℝ Limit := by
  intro hfinite
  let : Module.Finite ℝ Limit := hfinite
  let d : ℕ := Module.finrank ℝ Limit
  let inclusion : Stage d →ₗ[ℝ] Limit :=
    { toFun := ofStage d
      map_add' := fun x y => (ofStage d).map_add x y
      map_smul' := by
        intro r x
        change ofStage d (r • x) = r • ofStage d x
        simp only [Algebra.smul_def, map_mul]
        change ofStage d (algebraMap ℝ (Stage d) r) * ofStage d x =
          realAlgebraMap r * ofStage d x
        rw [← realAlgebraMap_stage d r] }
  have hinclusion : Function.Injective inclusion := ofStage_injective d
  have hbound := LinearMap.finrank_le_finrank_of_injective hinclusion
  have hdim : Module.finrank ℝ (Stage d) = (2 ^ d) ^ 2 := by
    change Module.finrank ℝ
      (Matrix (InfoGeometry.Clifford.TowerMatrix.Idx d)
        (InfoGeometry.Clifford.TowerMatrix.Idx d) ℝ) = (2 ^ d) ^ 2
    simp only [Module.finrank_matrix, Module.finrank_self, mul_one,
      InfoGeometry.Clifford.TowerMatrix.idx_card_pow_two, pow_two]
  have hle : (2 ^ d) ^ 2 ≤ d := by
    simpa only [hdim] using hbound
  have hlt : d < (2 ^ d) ^ 2 := by
    calc
      d < 2 ^ d := Nat.lt_two_pow_self
      _ ≤ (2 ^ d) ^ 2 := by
        simpa only [pow_two] using Nat.le_mul_self (2 ^ d)
  exact hlt.not_ge hle

section RingUniversalMap

variable {B : Type} [Ring B]

/-- The universal ring map is faithful exactly when every cone leg is
faithful. The reverse implication compares representatives at a common stage. -/
theorem directLimitLift_injective_iff
    (f : ∀ n : ℕ, Stage n →+* B)
    (hcone : CompatibleCone stageBond f) :
    Function.Injective (directLimitLift stageBond f hcone) ↔
      ∀ n : ℕ, Function.Injective (f n) := by
  constructor
  · intro h n x y hxy
    apply ofStage_injective n
    apply h
    change f n x = f n y
    exact hxy
  · intro h x y
    induction x, y using DirectLimit.induction₂ with
    | _ n x y =>
        intro hxy
        change f n x = f n y at hxy
        change ofStage n x = ofStage n y
        exact congrArg (ofStage n) (h n hxy)

variable [StarRing B]

/-- A compatible family of star-preserving ring maps descends to a
star-preserving map on the existing colimit. -/
theorem directLimitLift_star
    (f : ∀ n : ℕ, Stage n →+* B)
    (hcone : CompatibleCone stageBond f)
    (hstar : ∀ n (x : Stage n), f n (star x) = star (f n x))
    (x : Limit) :
    directLimitLift stageBond f hcone (star x) =
      star (directLimitLift stageBond f hcone x) := by
  induction x using DirectLimit.induction with
  | _ n x =>
      change f n (star x) = star (f n x)
      exact hstar n x

/-- Star preservation of the universal map is precisely stagewise star
preservation; compatibility alone does not supply it. -/
theorem directLimitLift_star_iff
    (f : ∀ n : ℕ, Stage n →+* B)
    (hcone : CompatibleCone stageBond f) :
    (∀ x : Limit, directLimitLift stageBond f hcone (star x) =
      star (directLimitLift stageBond f hcone x)) ↔
      ∀ n (x : Stage n), f n (star x) = star (f n x) := by
  constructor
  · intro h n x
    calc
      f n (star x) = directLimitLift stageBond f hcone (ofStage n (star x)) := rfl
      _ = directLimitLift stageBond f hcone (star (ofStage n x)) := by
        rw [ofStage_star]
      _ = star (directLimitLift stageBond f hcone (ofStage n x)) := h _
      _ = star (f n x) := rfl
  · intro h x
    exact directLimitLift_star f hcone h x

/-- Ordered products with adjoints descend through the actual universal map. -/
theorem directLimitLift_gram
    (f : ∀ n : ℕ, Stage n →+* B)
    (hcone : CompatibleCone stageBond f)
    (hstar : ∀ n (x : Stage n), f n (star x) = star (f n x))
    (x : Limit) :
    directLimitLift stageBond f hcone (x * star x + star x * x) =
      directLimitLift stageBond f hcone x * star (directLimitLift stageBond f hcone x) +
        star (directLimitLift stageBond f hcone x) * directLimitLift stageBond f hcone x := by
  simp only [map_add, map_mul, directLimitLift_star f hcone hstar]

/-- Mixed native commutators with adjoints descend with their multiplication
order intact. -/
theorem directLimitLift_star_bracket
    (f : ∀ n : ℕ, Stage n →+* B)
    (hcone : CompatibleCone stageBond f)
    (hstar : ∀ n (x : Stage n), f n (star x) = star (f n x))
    (x y : Limit) :
    directLimitLift stageBond f hcone ⁅x, star y⁆ =
      ⁅directLimitLift stageBond f hcone x, star (directLimitLift stageBond f hcone y)⁆ := by
  simp only [Ring.lie_def, map_sub, map_mul, directLimitLift_star f hcone hstar]

end RingUniversalMap

section RealStarUniversalMap

variable {B : Type} [Ring B] [StarRing B] [Algebra ℝ B]

/-- The existing universal ring map, with its proven star preservation and
the existing real algebra action, as a native real star algebra homomorphism. -/
noncomputable def liftStarAlgHom
    (f : ∀ n : ℕ, Stage n →⋆ₐ[ℝ] B)
    (hcone : CompatibleCone stageBond (fun n => (f n).toAlgHom.toRingHom)) :
    Limit →⋆ₐ[ℝ] B where
  toAlgHom :=
    { toRingHom := directLimitLift stageBond (fun n => (f n).toAlgHom.toRingHom) hcone
      commutes' := by
        intro r
        change f 0 (algebraMap ℝ (Stage 0) r) = algebraMap ℝ B r
        exact (f 0).toAlgHom.commutes r }
  map_star' := directLimitLift_star (fun n => (f n).toAlgHom.toRingHom) hcone
    (fun n x => map_star (f n) x)

/-- The native star algebra lift retains the original universal computation
rule on every finite stage. -/
@[simp] theorem liftStarAlgHom_ofStage
    (f : ∀ n : ℕ, Stage n →⋆ₐ[ℝ] B)
    (hcone : CompatibleCone stageBond (fun n => (f n).toAlgHom.toRingHom))
    (n : ℕ) (x : Stage n) :
    liftStarAlgHom f hcone (ofStage n x) = f n x := rfl

/-- Uniqueness in the native real star algebra language follows from the
existing ring-colimit universal property. -/
theorem liftStarAlgHom_unique
    (f : ∀ n : ℕ, Stage n →⋆ₐ[ℝ] B)
    (hcone : CompatibleCone stageBond (fun n => (f n).toAlgHom.toRingHom))
    (F : Limit →⋆ₐ[ℝ] B)
    (hF : ∀ n (x : Stage n), F (ofStage n x) = f n x) :
    F = liftStarAlgHom f hcone := by
  have hring : F.toAlgHom.toRingHom =
      directLimitLift stageBond (fun n => (f n).toAlgHom.toRingHom) hcone := by
    apply directLimitLift_unique stageBond (fun n => (f n).toAlgHom.toRingHom) hcone
    intro n
    ext x
    exact hF n x
  apply StarAlgHom.ext
  intro x
  exact congrArg (fun φ : Limit →+* B => φ x) hring

/-- Faithfulness of the native universal star algebra map is detected on its
finite-stage legs. -/
theorem liftStarAlgHom_injective_iff
    (f : ∀ n : ℕ, Stage n →⋆ₐ[ℝ] B)
    (hcone : CompatibleCone stageBond (fun n => (f n).toAlgHom.toRingHom)) :
    Function.Injective (liftStarAlgHom f hcone) ↔
      ∀ n : ℕ, Function.Injective (f n) := by
  exact directLimitLift_injective_iff (fun n => (f n).toAlgHom.toRingHom) hcone

end RealStarUniversalMap

end InfoGeometry.Canonical.RealStarColimitUniversal
