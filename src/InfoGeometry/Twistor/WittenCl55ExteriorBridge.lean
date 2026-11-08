/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.WittenExteriorHelicity
import InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal

/-!
# Four exterior modes inside the calibrated five-mode Cl(5,5) spinor

The injection selects modes `0,1,2,3` by `Fin.castSucc` and leaves mode `4`
empty. It is an actual split injection on vector spaces and exterior algebras,
available over both real and complex scalars.  The Cl(5,5) comparison below
uses the existing real representation: native `annihilation55` is wedge,
native `creation55` is contraction, and their ordered number sum is `5-Nψ`.

Thus the real four-mode helicity transports as `(N55-3)/2`.  This comparison
does not identify the Clifford adjoint five-grading with the five exterior
degrees of Witten's complex supermultiplet, or assert a complexification
equivalence for the real Clifford algebra.
-/

noncomputable section

namespace InfoGeometry.Twistor.WittenCl55ExteriorBridge

open InfoGeometry.Twistor.WittenExteriorHelicity
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open scoped BigOperators

section FourIntoFive

variable {R : Type*} [CommRing R]

/-- Select the first four modes; the fifth coordinate is literally zero. -/
def firstFourEmbedding : (Fin 4 → R) →ₗ[R] (Fin 5 → R) where
  toFun v := Fin.lastCases 0 v
  map_add' v w := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · change Fin.lastCases (motive := fun _ : Fin 5 => R) (0 : R) (v + w) (Fin.last 4) =
        Fin.lastCases (motive := fun _ : Fin 5 => R) (0 : R) v (Fin.last 4) +
          Fin.lastCases (motive := fun _ : Fin 5 => R) (0 : R) w (Fin.last 4)
      simp only [Fin.lastCases_last, add_zero]
    · intro j
      change Fin.lastCases (motive := fun _ : Fin 5 => R) (0 : R) (v + w) j.castSucc =
        Fin.lastCases (motive := fun _ : Fin 5 => R) (0 : R) v j.castSucc +
          Fin.lastCases (motive := fun _ : Fin 5 => R) (0 : R) w j.castSucc
      simp only [Fin.lastCases_castSucc, Pi.add_apply]
  map_smul' c v := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · change Fin.lastCases (motive := fun _ : Fin 5 => R) (0 : R) (c • v) (Fin.last 4) =
        c • Fin.lastCases (motive := fun _ : Fin 5 => R) (0 : R) v (Fin.last 4)
      simp only [Fin.lastCases_last, smul_zero]
    · intro j
      change Fin.lastCases (motive := fun _ : Fin 5 => R) (0 : R) (c • v) j.castSucc =
        c • Fin.lastCases (motive := fun _ : Fin 5 => R) (0 : R) v j.castSucc
      simp only [Fin.lastCases_castSucc, Pi.smul_apply]

@[simp] theorem firstFourEmbedding_castSucc (v : Fin 4 → R) (i : Fin 4) :
    firstFourEmbedding v i.castSucc = v i := by
  change Fin.lastCases (motive := fun _ : Fin 5 => R) (0 : R) v i.castSucc = v i
  exact Fin.lastCases_castSucc i

@[simp] theorem firstFourEmbedding_last (v : Fin 4 → R) :
    firstFourEmbedding v (Fin.last 4) = 0 := by
  change Fin.lastCases (motive := fun _ : Fin 5 => R) (0 : R) v (Fin.last 4) = 0
  exact Fin.lastCases_last

def firstFourProjection : (Fin 5 → R) →ₗ[R] (Fin 4 → R) where
  toFun v i := v i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem firstFourProjection_embedding :
    (firstFourProjection (R := R)).comp firstFourEmbedding = LinearMap.id := by
  ext v i
  simp [firstFourProjection]

theorem firstFourEmbedding_injective :
    Function.Injective (firstFourEmbedding (R := R)) := by
  intro v w h
  have h' := congrArg firstFourProjection h
  simpa only [← LinearMap.comp_apply, firstFourProjection_embedding,
    LinearMap.id_apply] using h'

/-- The exterior map is induced by the native exterior-algebra functor. -/
def firstFourExterior :
    ExteriorAlgebra R (Fin 4 → R) →ₐ[R] ExteriorAlgebra R (Fin 5 → R) :=
  ExteriorAlgebra.map firstFourEmbedding

theorem firstFourExterior_injective :
    Function.Injective (firstFourExterior (R := R)) :=
  ExteriorAlgebra.map_injective
    ⟨firstFourProjection, firstFourProjection_embedding⟩

@[simp] theorem firstFourExterior_generator (v : Fin 4 → R) :
    firstFourExterior (ExteriorAlgebra.ι R v) =
      ExteriorAlgebra.ι R (firstFourEmbedding v) :=
  ExteriorAlgebra.map_apply_ι _ _

theorem firstFourEmbedding_coordinateVector (i : Fin 4) :
    firstFourEmbedding (coordinateVector (R := R) i) =
      coordinateVector i.castSucc := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · change firstFourEmbedding (coordinateVector (R := R) i) (Fin.last 4) =
      coordinateVector i.castSucc (Fin.last 4)
    rw [firstFourEmbedding_last]
    simp only [coordinateVector, Pi.single_apply,
      (Fin.castSucc_ne_last i).symm, if_false]
  · intro k
    simp [coordinateVector, Pi.single_apply, eq_comm]

/-- The actual Euler operator commutes with this exterior inclusion. -/
theorem firstFourExterior_euler (ψ : ExteriorAlgebra R (Fin 4 → R)) :
    exteriorEuler R 5 (firstFourExterior ψ) =
      firstFourExterior (exteriorEuler R 4 ψ) := by
  induction ψ using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp [Algebra.algebraMap_eq_smul_one]
  | add ψ χ hψ hχ =>
      simp only [map_add, hψ, hχ]
  | ι_mul ψ v hψ =>
      change exteriorEuler R 5 (firstFourExterior (ExteriorAlgebra.ι R v * ψ)) =
        firstFourExterior (exteriorEuler R 4 (ExteriorAlgebra.ι R v * ψ))
      simp only [map_mul, firstFourExterior_generator,
        exteriorEuler_generator_mul, map_add, hψ]

end FourIntoFive

/-- The finite modes reuse the calibrated native wedge operators exactly. -/
theorem coordinateWedge_eq_native (i : Fin 5) :
    coordinateWedge (R := ℝ) i = wedge (basisVector i) := rfl

theorem coordinateDerivative_eq_native (i : Fin 5) :
    coordinateDerivative (R := ℝ) i = contract (dualBasisVector i) := rfl

/-- The native number operator contracts after wedge multiplication. -/
theorem numberSpinor_eq_oppositeEulerOrder :
    numberSpinor = ∑ i : Fin 5,
      coordinateDerivative (R := ℝ) i * coordinateWedge i := by
  simp [numberSpinor, cl55SpinorRep, numberOperator55,
    creation55_spinor, annihilation55_spinor,
    coordinateDerivative_eq_native, coordinateWedge_eq_native]

/-- CAR derives the complementary degree operator on the entire real spinor. -/
theorem numberSpinor_add_exteriorEuler :
    numberSpinor + exteriorEuler ℝ 5 = (5 : ℝ) • (1 : SpinorEnd) := by
  rw [numberSpinor_eq_oppositeEulerOrder, exteriorEuler, ← Finset.sum_add_distrib]
  calc
    (∑ i : Fin 5,
        (coordinateDerivative (R := ℝ) i * coordinateWedge i +
          coordinateWedge i * coordinateDerivative i)) =
        ∑ _i : Fin 5, (1 : SpinorEnd) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [coordinateDerivative_eq_native, coordinateWedge_eq_native,
        contract_wedge_add_wedge_contract]
      simp
    _ = (5 : ℝ) • (1 : SpinorEnd) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      exact (Nat.cast_smul_eq_nsmul ℝ 5 (1 : SpinorEnd)).symm

theorem numberSpinor_apply_complement (ψ : Spinor) :
    numberSpinor ψ = (5 : ℝ) • ψ - exteriorEuler ℝ 5 ψ := by
  have h := congrArg (fun T : SpinorEnd => T ψ) numberSpinor_add_exteriorEuler
  exact eq_sub_of_add_eq (by
    simpa only [LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] using h)

/-- A four-mode real homogeneous form has the native eigenvalue `5-r`.
The scalar subtraction is in `ℝ`, so no hidden natural-number truncation occurs. -/
theorem numberSpinor_firstFour_homogeneous
    (r : ℕ) (ψ : ⋀[ℝ]^r (Fin 4 → ℝ)) :
    numberSpinor (firstFourExterior (ψ : ExteriorAlgebra ℝ (Fin 4 → ℝ))) =
      (5 - (r : ℝ)) • firstFourExterior (ψ : ExteriorAlgebra ℝ (Fin 4 → ℝ)) := by
  rw [numberSpinor_apply_complement, firstFourExterior_euler,
    exteriorEuler_homogeneous, map_smul, sub_smul]

/-- The real specialization of the same four-mode Euler/helicity expression. -/
def realFermionicHelicity : Module.End ℝ (ExteriorAlgebra ℝ (Fin 4 → ℝ)) :=
  1 - (1 / 2 : ℝ) • exteriorEuler ℝ 4

/-- Exact normalization relating the four-mode helicity and native Cl(5,5) number. -/
theorem firstFourExterior_realHelicity (ψ : ExteriorAlgebra ℝ (Fin 4 → ℝ)) :
    firstFourExterior (realFermionicHelicity ψ) =
      (1 / 2 : ℝ) • numberSpinor (firstFourExterior ψ) -
        (3 / 2 : ℝ) • firstFourExterior ψ := by
  simp only [realFermionicHelicity, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul]
  rw [numberSpinor_apply_complement, firstFourExterior_euler]
  module

end InfoGeometry.Twistor.WittenCl55ExteriorBridge
