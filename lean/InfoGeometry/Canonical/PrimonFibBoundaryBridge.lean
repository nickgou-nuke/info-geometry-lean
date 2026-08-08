import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeSuperalgebra
import InfoGeometry.Arithmetic.MobiusPrimonParity
import InfoGeometry.Arithmetic.PrimonSupergradedGasAlgebra
import InfoGeometry.Krein.DoubledSpace
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# PrimonFibBoundaryBridge

Finite owner surface for the proposed primon/Fibonacci boundary lane.

The proposed informal map is:
1. Prime-indexed states with energies E_p = log(p)
2. Partition function Z(s) = ∏_p (1 - p^{-s})⁻¹ = ζ(s)
3. V₄ quotient fragments primon sectors into Fib(n)-graded sub-slices
4. Möbius function µ(n) = V₄ charge parity of boundary state n
5. Boson/fermion statistics = V₄ eigenspace assignment (ψ⁺ = boson, ψ⁻ = fermion)

This file intentionally does not expose theorem surfaces for those analytic or
representation-theoretic claims.  Finite prime supertrace facts are owned by
the arithmetic Witten-index and Majorana character files; categorical
Fibonacci facts are owned by `InfoGeometry.Categorical.FibonacciBraiding`.

SymPy property: `tools/sympy/primon_fib_boundary_bridge.py`
-/

namespace InfoGeometry.Canonical.PrimonFibBoundaryBridge

/--
The concrete primon-gas Euler product agrees with `riemannZeta` on its
half-plane of convergence, using the arithmetic owner theorem.
-/
theorem partition_function_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    InfoGeometry.Arithmetic.PrimeSuperalgebra.infiniteComplexBosonicEulerProduct s =
      riemannZeta s :=
  InfoGeometry.Arithmetic.PrimeSuperalgebra.infiniteComplexBosonicEulerProduct_eq_riemannZeta hs

/-- The number of boundary states at tower depth n is Fib(n).
    These are the V₄-invariant graded sub-slice dimensions. -/
def boundary_state_count (n : ℕ) : ℕ := Nat.fib n

/--
The finite square-free state owner identifies the Möbius readout with the
fermion-parity charge.
-/
theorem mobiusReadout_eq_fermionParity
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (S : InfoGeometry.Arithmetic.MobiusPrimonParity.SquareFreePrimonState P) :
    S.mobiusReadout = S.fermionParity :=
  InfoGeometry.Arithmetic.MobiusPrimonParity.SquareFreePrimonState.mobiusReadout_eq_fermionParity S

/--
Closure debt: build the boson/fermion eigenspace splitting as an actual
graded representation theorem.
-/
/- The existing finite supergraded owner supplies the CAR/supercharge spine.
   It is deliberately not renamed as a V₄ eigenspace theorem: that stronger
   representation-theoretic statement remains a separate owner obligation. -/
theorem graded_statistics_finite_owner
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair (E := E)
        (InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARAnnihilation
          (E := E))
        (InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARCreation
          (E := E)) ∧
      InfoGeometry.Canonical.SuperchargeCARCCRBridge.CARBracket (E := E)
          (InfoGeometry.Canonical.SuperchargeCARCCRBridge.paritySuperchargeOp
            (E := E))
          (InfoGeometry.Canonical.SuperchargeCARCCRBridge.modularSuperchargeOp
            (E := E)) = 0 ∧
        InfoGeometry.Canonical.SuperchargeCARCCRBridge.CCRBracket (E := E)
            (InfoGeometry.Canonical.SuperchargeCARCCRBridge.paritySuperchargeOp
              (E := E))
            (InfoGeometry.Canonical.SuperchargeCARCCRBridge.modularSuperchargeOp
              (E := E)) =
          (2 : ℝ) •
            InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp
              (E := E) ∧
          (InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp
            (E := E)).comp
              (InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp
                (E := E)) =
            -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) := by
  exact InfoGeometry.Arithmetic.PrimonSupergradedGasAlgebra.primonSupergradedFockSpine

end InfoGeometry.Canonical.PrimonFibBoundaryBridge
