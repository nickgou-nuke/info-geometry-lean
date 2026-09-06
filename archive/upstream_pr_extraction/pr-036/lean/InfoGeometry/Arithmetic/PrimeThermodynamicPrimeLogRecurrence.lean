import InfoGeometry.Arithmetic.PrimeEnergyNative
import InfoGeometry.Arithmetic.PrimeThermodynamicLogRecurrence

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeThermodynamicPrimeLogRecurrence

open InfoGeometry.Arithmetic.PrimeEnergyNative
open InfoGeometry.Arithmetic.PrimeThermodynamicLogRecurrence

def primeModeWeight (β : ℝ) (p : Nat.Primes) : ℝ :=
  Real.exp (-β * Real.log (p : ℝ))

theorem primeModeWeight_pos (β : ℝ) (p : Nat.Primes) :
    0 < primeModeWeight β p := by
  unfold primeModeWeight
  exact Real.exp_pos _

theorem primeModeWeight_ne_zero (β : ℝ) (p : Nat.Primes) :
    primeModeWeight β p ≠ 0 :=
  (primeModeWeight_pos β p).ne'

def primeStageProduct (β : ℝ) (S : Finset Nat.Primes) : ℝ :=
  stageProduct S (primeModeWeight β)

theorem primeStageProduct_insert
    (β : ℝ) (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∉ S) :
    primeStageProduct β (insert p S) =
      primeModeWeight β p * primeStageProduct β S := by
  exact stageProduct_insert S p (primeModeWeight β) hp

theorem primeStageProduct_pos
    (β : ℝ) (S : Finset Nat.Primes) :
    0 < primeStageProduct β S := by
  exact stageProduct_pos S (primeModeWeight β)
    (fun p _hp => primeModeWeight_pos β p)

theorem primeStageProduct_ne_zero
    (β : ℝ) (S : Finset Nat.Primes) :
    primeStageProduct β S ≠ 0 :=
  (primeStageProduct_pos β S).ne'

theorem primeStageProduct_union
    (β : ℝ) (S T : Finset Nat.Primes) (hST : Disjoint S T) :
    primeStageProduct β (S ∪ T) =
      primeStageProduct β S * primeStageProduct β T := by
  exact stageProduct_union S T (primeModeWeight β) hST

theorem primeStageLog_union
    (β : ℝ) (S T : Finset Nat.Primes) (hST : Disjoint S T) :
    Real.log (primeStageProduct β (S ∪ T)) =
      Real.log (primeStageProduct β S) +
        Real.log (primeStageProduct β T) := by
  exact stageLogProduct_union S T (primeModeWeight β) hST
    (fun p _hp => primeModeWeight_pos β p)
    (fun p _hp => primeModeWeight_pos β p)

theorem primeStageLog_insert
    (β : ℝ) (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∉ S) :
    Real.log (primeStageProduct β (insert p S)) =
      Real.log (primeStageProduct β S) +
        stageLogIncrement (primeModeWeight β p) := by
  apply stageLogProduct_insert S p (primeModeWeight β) hp
  · exact primeModeWeight_ne_zero β p
  · exact primeStageProduct_ne_zero β S

end InfoGeometry.Arithmetic.PrimeThermodynamicPrimeLogRecurrence
