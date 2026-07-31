import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedMaxNoncontractibleFiberNoExponentialPenalty
import Omega.POM.DerivedFiberIndependencePolynomialMinusOneTrichotomy
import Omega.POM.FiberParityHomotopyEquivalence

namespace Omega.DerivedConsequences

/-- Odd parity forces the spherical branch and compresses the `t = -1` specialization to a pure
sign, while the noncontractible branch keeps the same exponential growth rate as the optimal one.
-/
def derived_optimal_spherical_fiber_sign_compression_statement : Prop :=
  (∀ (badModThreeComponent allComponentsAvoidBadModThree
        joinDecomposition contractibleCase sphereCase : Prop)
      (_hJoinDecomposition : joinDecomposition)
      (_badModThreeComponentForcesContraction :
        badModThreeComponent → joinDecomposition → contractibleCase)
      (_allGoodComponentsGiveSphere :
        allComponentsAvoidBadModThree → joinDecomposition → sphereCase)
      (L : List ℕ) (tau : ℕ) (E : Omega.POM.POMFiberStokesEulerBoundaryObservabilityData)
      (_hBad : (∃ ℓ ∈ L, ℓ % 3 = 1) → badModThreeComponent)
      (_hGood : (∀ ℓ ∈ L, ℓ % 3 ≠ 1) → allComponentsAvoidBadModThree)
      (_hContractibleEuler : contractibleCase → E.reducedEulerCharacteristic = 0)
      (_hSphereEuler : sphereCase → E.reducedEulerCharacteristic = (-1 : ℤ) ^ (tau - 1))
      (_hTauPos : sphereCase → 1 ≤ tau),
      (((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod % 2 = 1) →
        sphereCase ∧ E.zAtMinusOne = (-1 : ℤ) ^ tau)) ∧
    (∃ c C : ℚ,
      0 < c ∧
      c ≤ C ∧
      (∀ k : ℕ,
        9 ≤ k →
          c ≤ (Omega.Conclusion.noncontractibleFiberCount (2 * k) : ℚ) /
                Omega.Conclusion.noncontractibleMainFiberCount (2 * k) ∧
            (Omega.Conclusion.noncontractibleFiberCount (2 * k) : ℚ) /
                Omega.Conclusion.noncontractibleMainFiberCount (2 * k) ≤ C) ∧
      (∀ k : ℕ,
        8 ≤ k →
          c ≤ (Omega.Conclusion.noncontractibleFiberCount (2 * k + 1) : ℚ) /
                Omega.Conclusion.noncontractibleMainFiberCount (2 * k + 1) ∧
            (Omega.Conclusion.noncontractibleFiberCount (2 * k + 1) : ℚ) /
                Omega.Conclusion.noncontractibleMainFiberCount (2 * k + 1) ≤ C)) ∧
    Real.log (Real.sqrt Real.goldenRatio) = (1 / 2 : ℝ) * Real.log Real.goldenRatio

/-- Paper label: `cor:derived-optimal-spherical-fiber-sign-compression`. -/
theorem paper_derived_optimal_spherical_fiber_sign_compression :
    derived_optimal_spherical_fiber_sign_compression_statement := by
  rcases paper_derived_max_noncontractible_fiber_no_exponential_penalty with
    ⟨c, C, hc, hcC, heven, hodd, hlog⟩
  refine ⟨?_, ?_, hlog⟩
  · intro badModThreeComponent allComponentsAvoidBadModThree joinDecomposition contractibleCase
      sphereCase hJoinDecomposition badModThreeComponentForcesContraction allGoodComponentsGiveSphere
      L tau E hBad hGood hContractibleEuler hSphereEuler hTauPos hodd
    have hsphere :
        sphereCase :=
      (Omega.POM.paper_pom_fiber_parity_homotopy_equivalence hJoinDecomposition
        badModThreeComponentForcesContraction allGoodComponentsGiveSphere L hBad hGood).2 hodd
    have hsign :
        E.zAtMinusOne = (-1 : ℤ) ^ tau :=
      (Omega.POM.paper_derived_fiber_independence_polynomial_minus_one_trichotomy
        hJoinDecomposition badModThreeComponentForcesContraction allGoodComponentsGiveSphere
        L tau E hBad hGood hContractibleEuler hSphereEuler hTauPos).2 hodd
    exact ⟨hsphere, hsign⟩
  · exact ⟨c, C, hc, hcC, heven, hodd⟩

end Omega.DerivedConsequences
