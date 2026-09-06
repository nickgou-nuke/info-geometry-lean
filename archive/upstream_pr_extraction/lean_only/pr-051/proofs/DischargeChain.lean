import proofs.TwistorParafermionBoundary
import proofs.PrimonBosonFermionDuality
import proofs.PrimonCoarseGraining
import proofs.CantorBoundaryCuntzFamily

/-!
# Discharge Chain: direct finite primon and Cuntz identities

Zero sorries.
-/

noncomputable section

namespace DischargeChain

open TwistorParafermionBoundary
open PrimonBosonFermionDuality
open PrimonCoarseGraining
open CantorBoundaryCuntzFamily

/-! ## Finite primon identities -/

theorem boson_mobius_finite_product (p : ℕ) (β : ℝ) (K : ℕ) :
    singlePrimeBosonPartition p β K * singlePrimeMobiusPartition p β =
    1 - (primeBoltzmannWeight p β) ^ (K + 1) := by
  dsimp [singlePrimeMobiusPartition, singlePrimeBosonPartition, bosonOccupationWeight]
  set a := primeBoltzmannWeight p β
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    simp [pow_succ]
    ring

theorem fermion_mobius_product_identity (p : ℕ) (β : ℝ) :
    singlePrimeFermionPartition p β * singlePrimeMobiusPartition p β =
    1 - (primeBoltzmannWeight p β) ^ 2 := by
  rw [singlePrimeFermionPartition_eq, singlePrimeMobiusPartition]
  set x := primeBoltzmannWeight p β
  calc
    (1 + x) * (1 - x) = 1 - x ^ 2 := by ring
    _ = 1 - (primeBoltzmannWeight p β) ^ 2 := rfl

theorem mobius_partition_at_zero (p : ℕ) :
    singlePrimeMobiusPartition p 0 = 0 := by
  simp [singlePrimeMobiusPartition, primeBoltzmannWeight]

theorem boson_partition_succ (p : ℕ) (β : ℝ) (K : ℕ) :
    singlePrimeBosonPartition p β (K + 1) =
    singlePrimeBosonPartition p β K + (primeBoltzmannWeight p β) ^ (K + 1) := by
  simp [singlePrimeBosonPartition, bosonOccupationWeight, Finset.sum_range_succ]

theorem boson_partition_at_zero (p : ℕ) (β : ℝ) :
    singlePrimeBosonPartition p β 0 = 1 :=
  by simp [singlePrimeBosonPartition, bosonOccupationWeight]

theorem boson_mobius_with_truncation_error (p : ℕ) (β : ℝ) (K : ℕ) :
    singlePrimeBosonPartition p β K * singlePrimeMobiusPartition p β =
    1 - truncationError p β K := by
  rw [truncationError]
  exact boson_mobius_finite_product p β K

/-! ## Concrete Cuntz identities -/

theorem c4_shift_orthogonality (i j : Fin 4) :
    cuntzT i * cuntzS j =
      if i = j then (1 : C4Functions →ₗ[ℂ] C4Functions) else 0 := by
  ext f b
  dsimp [cuntzT, cuntzS]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

theorem c4_shift_partition :
    (∑ i : Fin 4, cuntzS i * cuntzT i) = (1 : C4Functions →ₗ[ℂ] C4Functions) := by
  apply LinearMap.ext
  intro f
  apply funext
  intro b
  dsimp [cuntzS, cuntzT]
  calc
    (∑ i : Fin 4, (if headN b = i then f (prependN i (tailN b)) else 0))
        = f (prependN (headN b) (tailN b)) := by
      simp [Finset.mem_univ]
    _ = f b := by
      rw [prependN_headN_tailN]

end DischargeChain

end noncomputable section
