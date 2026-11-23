/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KK.QuasilatticeIndexInvariance
import InfoGeometry.Canonical.FormalPrimeRootSystem

/-!
# Quasilattice Boolean Index Bridge

Connects the operatorial KK Fredholm index `quasilatticeAnalyticalIndex` (from
`InfoGeometry.KK.QuasilatticeIndexInvariance`) to the finite Boolean `A₁^P`
alternating Weyl sum `weylAlternatingSum` (from `FormalPrimeRootSystem`).

When the positive and negative chiral kernel defect slices decompose as direct
sectors indexed by the even- and odd-cardinality Boolean Weyl elements of `B(P)`,
the Bogoliubov-invariant quasilattice analytical index equals the signed
alternating dimension sum over `BooleanWeylGroup L`, whose multiplicative
evaluation specializes to `∏_{p ∈ L.primes} (1 - x p)`.
-/

noncomputable section

namespace InfoGeometry.KK.QuasilatticeBooleanIndexBridge

open scoped BigOperators
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Krein

private def booleanWeylGroupEquivPowerset (L : FormalPrimeRootLattice) :
    BooleanWeylGroup L ≃ { S : Finset ℕ // S ∈ L.primes.powerset } where
  toFun w := ⟨w.support, Finset.mem_powerset.mpr w.support_subset⟩
  invFun S := ⟨S.1, Finset.mem_powerset.mp S.2⟩
  left_inv w := by
    rcases w with ⟨_, _⟩
    rfl
  right_inv S := by
    rcases S with ⟨_, _⟩
    rfl

/-- Finite enumeration of `BooleanWeylGroup L` via `L.primes.powerset`. -/
noncomputable instance instFintypeBooleanWeylGroup (L : FormalPrimeRootLattice) :
    Fintype (BooleanWeylGroup L) :=
  Fintype.ofEquiv { S : Finset ℕ // S ∈ L.primes.powerset }
    (booleanWeylGroupEquivPowerset L).symm

/-- Real-valued inclusion–exclusion index over `BooleanWeylGroup L`. -/
def booleanAlternatingIndex
    (L : FormalPrimeRootLattice) (d : BooleanWeylGroup L → ℝ) : ℝ :=
  ∑ w : BooleanWeylGroup L, weylSign w * d w

/-- On multiplicative weights `d w = ∏ p ∈ w.support, x p`, `booleanAlternatingIndex`
coincides with `weylAlternatingSum L x`. -/
theorem booleanAlternatingIndex_multiplicative_eq_weylAlternatingSum
    (L : FormalPrimeRootLattice) (x : ℕ → ℝ) :
    booleanAlternatingIndex L (fun w => ∏ p ∈ w.support, x p) =
      weylAlternatingSum L x := by
  unfold booleanAlternatingIndex
  calc
    (∑ w : BooleanWeylGroup L, weylSign w * ∏ p ∈ w.support, x p)
        = ∑ S : { S : Finset ℕ // S ∈ L.primes.powerset },
            (-1 : ℝ) ^ S.1.card * ∏ p ∈ S.1, x p := by
          refine Fintype.sum_equiv (booleanWeylGroupEquivPowerset L) _ _ ?_
          intro w
          rfl
    _ = ∑ S ∈ L.primes.powerset, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p := by
          simpa using
            (Finset.sum_coe_sort L.primes.powerset
              (fun S => (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p))
    _ = weylAlternatingSum L x := rfl

/-- Product formula for multiplicative Boolean inclusion–exclusion indices:
`∑_{w} ε(w) ∏_{p ∈ w.support} x p = ∏_{p ∈ L.primes} (1 - x p)`. -/
theorem booleanAlternatingIndex_multiplicative_eq_prod_one_sub
    (L : FormalPrimeRootLattice) (x : ℕ → ℝ) :
    booleanAlternatingIndex L (fun w => ∏ p ∈ w.support, x p) =
      ∏ p ∈ L.primes, (1 - x p) := by
  rw [booleanAlternatingIndex_multiplicative_eq_weylAlternatingSum,
    weylAlternatingSum_eq_prod_one_sub]

section DimensionGrading

open Classical in
/-- Total dimension of the even-parity Boolean Weyl sectors. -/
def booleanEvenSectorDimSum
    (L : FormalPrimeRootLattice) (d : BooleanWeylGroup L → ℕ) : ℕ :=
  ∑ w ∈ (Finset.univ : Finset (BooleanWeylGroup L)).filter (fun w => Even w.support.card), d w

open Classical in
/-- Total dimension of the odd-parity Boolean Weyl sectors. -/
def booleanOddSectorDimSum
    (L : FormalPrimeRootLattice) (d : BooleanWeylGroup L → ℕ) : ℕ :=
  ∑ w ∈ (Finset.univ : Finset (BooleanWeylGroup L)).filter (fun w => ¬ Even w.support.card), d w

/-- Signed integer alternating dimension sum over `BooleanWeylGroup L`. -/
def booleanDimensionAlternatingSum
    (L : FormalPrimeRootLattice) (d : BooleanWeylGroup L → ℕ) : ℤ :=
  ∑ w : BooleanWeylGroup L, (-1 : ℤ) ^ w.support.card * (d w : ℤ)

open Classical in
/-- Splitting the alternating dimension sum into even minus odd sector dimensions. -/
theorem booleanDimensionAlternatingSum_eq_even_sub_odd
    (L : FormalPrimeRootLattice) (d : BooleanWeylGroup L → ℕ) :
    booleanDimensionAlternatingSum L d =
      (booleanEvenSectorDimSum L d : ℤ) - (booleanOddSectorDimSum L d : ℤ) := by
  unfold booleanDimensionAlternatingSum booleanEvenSectorDimSum booleanOddSectorDimSum
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (BooleanWeylGroup L)) (fun w => Even w.support.card)]
  have hEven :
      (∑ w ∈ (Finset.univ : Finset (BooleanWeylGroup L)).filter (fun w => Even w.support.card),
          (-1 : ℤ) ^ w.support.card * (d w : ℤ)) =
        ((∑ w ∈ (Finset.univ : Finset (BooleanWeylGroup L)).filter
            (fun w => Even w.support.card), d w : ℕ) : ℤ) := by
    push_cast
    refine Finset.sum_congr rfl ?_
    intro w hw
    have hEw : Even w.support.card := (Finset.mem_filter.mp hw).2
    rw [hEw.neg_one_pow, one_mul]
  have hOdd :
      (∑ w ∈ (Finset.univ : Finset (BooleanWeylGroup L)).filter (fun w => ¬ Even w.support.card),
          (-1 : ℤ) ^ w.support.card * (d w : ℤ)) =
        -((∑ w ∈ (Finset.univ : Finset (BooleanWeylGroup L)).filter
            (fun w => ¬ Even w.support.card), d w : ℕ) : ℤ) := by
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro w hw
    have hOw : Odd w.support.card := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hw).2
    rw [hOw.neg_one_pow]
    ring
  rw [hEven, hOdd, sub_eq_add_neg]

/-- Casting the integer Boolean alternating dimension sum to `ℝ` yields
`booleanAlternatingIndex` applied to the sector dimensions. -/
theorem cast_booleanDimensionAlternatingSum_eq_booleanAlternatingIndex
    (L : FormalPrimeRootLattice) (d : BooleanWeylGroup L → ℕ) :
    ((booleanDimensionAlternatingSum L d : ℤ) : ℝ) =
      booleanAlternatingIndex L (fun w => (d w : ℝ)) := by
  unfold booleanDimensionAlternatingSum booleanAlternatingIndex weylSign
  push_cast
  rfl

/-- Given a decomposition of the baseline chiral kernel defect dimensions into even
and odd Boolean Weyl sectors over `L`, the Bogoliubov-transported quasilattice
analytical index equals `booleanDimensionAlternatingSum L d` for every parameter `t`. -/
theorem quasilatticeAnalyticalIndex_eq_booleanDimensionAlternatingSum
    {A B E : Type}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B (DoubledSpace E))
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := DoubledSpace E) V.connectionGenerator)
    (L : FormalPrimeRootLattice)
    (d : BooleanWeylGroup L → ℕ)
    (hPlusDim : Module.finrank ℝ X.chiralKernelSlicePlus = booleanEvenSectorDimSum L d)
    (hMinusDim : Module.finrank ℝ X.chiralKernelSliceMinus = booleanOddSectorDimSum L d)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) =
      booleanDimensionAlternatingSum L d := by
  rw [quasilatticeAnalyticalIndex_eq_initial (E := E) V X hX hEven t]
  rcases hX with ⟨_, _⟩
  change ((Module.finrank ℝ X.chiralKernelSlicePlus : ℤ) -
      (Module.finrank ℝ X.chiralKernelSliceMinus : ℤ)) =
    booleanDimensionAlternatingSum L d
  rw [hPlusDim, hMinusDim, booleanDimensionAlternatingSum_eq_even_sub_odd]

/-- Real cast of `quasilatticeAnalyticalIndex` under a Boolean sector grading,
connecting the KK Fredholm index directly to `booleanAlternatingIndex`. -/
theorem quasilatticeAnalyticalIndex_cast_eq_booleanAlternatingIndex
    {A B E : Type}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B (DoubledSpace E))
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := DoubledSpace E) V.connectionGenerator)
    (L : FormalPrimeRootLattice)
    (d : BooleanWeylGroup L → ℕ)
    (hPlusDim : Module.finrank ℝ X.chiralKernelSlicePlus = booleanEvenSectorDimSum L d)
    (hMinusDim : Module.finrank ℝ X.chiralKernelSliceMinus = booleanOddSectorDimSum L d)
    (t : ℝ) :
    ((quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) : ℤ) : ℝ) =
      booleanAlternatingIndex L (fun w => (d w : ℝ)) := by
  rw [quasilatticeAnalyticalIndex_eq_booleanDimensionAlternatingSum
      (E := E) V X hX hEven L d hPlusDim hMinusDim t,
    cast_booleanDimensionAlternatingSum_eq_booleanAlternatingIndex]

end DimensionGrading

end InfoGeometry.KK.QuasilatticeBooleanIndexBridge
