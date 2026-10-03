import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.GU.Window6FiberEdgeCouplingDet
import Omega.GU.Window6GreenKernelPstarValuationOne
import Omega.GU.Window6KirchhoffGreenPadicLiftStability

namespace Omega.GU

/-- The audited determinant of the local window-`6` edge-coupling matrix. -/
def window6LocalDeterminantAudited : Nat :=
  2 * 3 * 5 * 23

/-- The audited determinant controlling the coarse Green-kernel denominator. -/
def window6CoarseGreenDeterminantAudited : Nat :=
  2 ^ 3 * 3 ^ 3 * window6KirchhoffGreenPadicPrime

/-- Odd prime support of a natural number via its factorization. -/
def window6OddPrimeSupport (n : Nat) : Finset Nat :=
  n.factorization.support.filter fun p => p % 2 = 1

/-- Odd primes appearing in the local determinant audit. -/
def Window6LocalOddPrimeSupport : Finset Nat :=
  window6OddPrimeSupport window6LocalDeterminantAudited

/-- Odd primes appearing in the coarse Green-kernel audit. -/
def Window6CoarseGreenOddPrimeSupport : Finset Nat :=
  window6OddPrimeSupport window6CoarseGreenDeterminantAudited

/-- The distinguished prime `571` appears to first order in the coarse Green denominator. -/
def Window6CoarseGreenPrime571Order : Nat :=
  window6CoarseGreenDeterminantAudited.factorization window6KirchhoffGreenPadicPrime

private theorem window6CoarseGreenPrime571Order_eq_one :
    Window6CoarseGreenPrime571Order = 1 := by
  unfold Window6CoarseGreenPrime571Order window6CoarseGreenDeterminantAudited
  have h571 :
      (2 ^ 3 * 3 ^ 3 * window6KirchhoffGreenPadicPrime).factorization
          window6KirchhoffGreenPadicPrime = 1 := by
    refine paper_window6_green_kernel_pstar_valuation_one
      (D := 2 ^ 3 * 3 ^ 3 * window6KirchhoffGreenPadicPrime)
      (pstar := window6KirchhoffGreenPadicPrime) ?_ ?_ ?_
    · unfold window6KirchhoffGreenPadicPrime
      norm_num
    · unfold window6KirchhoffGreenPadicPrime
      norm_num
    · unfold window6KirchhoffGreenPadicPrime
      norm_num
  simpa [window6KirchhoffGreenPadicPrime] using h571

private theorem window6LocalDeterminant_primeFactors :
    window6LocalDeterminantAudited.primeFactors = {2, 3, 5, 23} := by
  unfold window6LocalDeterminantAudited
  calc
    (2 * 3 * 5 * 23 : Nat).primeFactors =
        (2 * (3 * (5 * 23)) : Nat).primeFactors := by norm_num
    _ = (2 : Nat).primeFactors ∪ (3 * (5 * 23) : Nat).primeFactors :=
      Nat.primeFactors_mul (by norm_num) (by norm_num)
    _ = ({2} : Finset Nat) ∪
        ((3 : Nat).primeFactors ∪ (5 * 23 : Nat).primeFactors) := by
      rw [Nat.Prime.primeFactors (by norm_num : Nat.Prime 2),
        Nat.primeFactors_mul (by norm_num) (by norm_num)]
    _ = ({2} : Finset Nat) ∪
        (({3} : Finset Nat) ∪ ((5 : Nat).primeFactors ∪ (23 : Nat).primeFactors)) := by
      rw [Nat.Prime.primeFactors (by norm_num : Nat.Prime 3),
        Nat.primeFactors_mul (by norm_num) (by norm_num)]
    _ = {2, 3, 5, 23} := by
      rw [Nat.Prime.primeFactors (by norm_num : Nat.Prime 5),
        Nat.Prime.primeFactors (by norm_num : Nat.Prime 23)]
      ext p
      simp only [Finset.mem_union, Finset.mem_singleton]
      simp

private theorem window6CoarseGreenDeterminant_primeFactors :
    window6CoarseGreenDeterminantAudited.primeFactors = {2, 3, 571} := by
  unfold window6CoarseGreenDeterminantAudited window6KirchhoffGreenPadicPrime
  calc
    (2 ^ 3 * 3 ^ 3 * 571 : Nat).primeFactors =
        (2 ^ 3 * (3 ^ 3 * 571) : Nat).primeFactors := by norm_num
    _ = (2 ^ 3 : Nat).primeFactors ∪ (3 ^ 3 * 571 : Nat).primeFactors :=
      Nat.primeFactors_mul (by norm_num) (by norm_num)
    _ = ({2} : Finset Nat) ∪ ((3 ^ 3 : Nat).primeFactors ∪ (571 : Nat).primeFactors) := by
      rw [Nat.primeFactors_pow 2 (by norm_num),
        Nat.Prime.primeFactors (by norm_num : Nat.Prime 2),
        Nat.primeFactors_mul (by norm_num) (by norm_num)]
    _ = ({2} : Finset Nat) ∪ (({3} : Finset Nat) ∪ ({571} : Finset Nat)) := by
      rw [Nat.primeFactors_pow 3 (by norm_num),
        Nat.Prime.primeFactors (by norm_num : Nat.Prime 3),
        Nat.Prime.primeFactors (by norm_num : Nat.Prime 571)]
    _ = {2, 3, 571} := by
      ext p
      simp only [Finset.mem_union, Finset.mem_singleton]
      simp

private theorem window6LocalOddPrimeSupport_eq :
    Window6LocalOddPrimeSupport = {3, 5, 23} := by
  change (Nat.primeFactors 690).filter (fun p => p % 2 = 1) = _
  have hfactor : (690 : Nat).primeFactors = {2, 3, 5, 23} := by
    simpa [window6LocalDeterminantAudited] using window6LocalDeterminant_primeFactors
  rw [hfactor]
  ext p
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp | hp | hp | hp, hodd⟩
    · subst p
      norm_num at hodd
    · exact Or.inl hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr hp)
  · rintro (hp | hp | hp)
    · subst p
      exact ⟨Or.inr (Or.inl rfl), by norm_num⟩
    · subst p
      exact ⟨Or.inr (Or.inr (Or.inl rfl)), by norm_num⟩
    · subst p
      exact ⟨Or.inr (Or.inr (Or.inr rfl)), by norm_num⟩

private theorem window6CoarseGreenOddPrimeSupport_eq :
    Window6CoarseGreenOddPrimeSupport = {3, 571} := by
  change (Nat.primeFactors 123336).filter (fun p => p % 2 = 1) = _
  have hfactor : (123336 : Nat).primeFactors = {2, 3, 571} := by
    simpa [window6CoarseGreenDeterminantAudited,
      window6KirchhoffGreenPadicPrime] using window6CoarseGreenDeterminant_primeFactors
  rw [hfactor]
  ext p
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp | hp | hp, hodd⟩
    · subst p
      norm_num at hodd
    · exact Or.inl hp
    · exact Or.inr hp
  · rintro (hp | hp)
    · subst p
      exact ⟨Or.inr (Or.inl rfl), by norm_num⟩
    · subst p
      exact ⟨Or.inr (Or.inr rfl), by norm_num⟩

/-- Package the audited determinant factors on the local side, and combine them with the
distinguished `571`-adic Green-kernel obstruction to separate the odd-prime supports.
    thm:window6-local-determinant-vs-coarse-green-odd-primes -/
theorem paper_window6_local_determinant_vs_coarse_green_odd_primes :
    Window6LocalOddPrimeSupport = ({3, 5, 23} : Finset Nat) ∧
      Window6CoarseGreenOddPrimeSupport = ({3, 571} : Finset Nat) ∧
      Window6CoarseGreenPrime571Order = 1 := by
  have hdet := paper_terminal_window6_fiber_edge_coupling_det
  let _ := hdet
  refine ⟨?_, ?_, window6CoarseGreenPrime571Order_eq_one⟩
  · exact window6LocalOddPrimeSupport_eq
  · exact window6CoarseGreenOddPrimeSupport_eq

end Omega.GU
