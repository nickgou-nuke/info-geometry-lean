import InfoGeometry.Categorical.CelikZ3FibonacciCuntzBoundaryBridge
import InfoGeometry.Physics.SplitOctonionCuntzSUSYBridge

/-!
# Chiral Cuntz braided supercharge bridge

This is a transport layer between two existing owners:

* `CelikZ3FibonacciCuntzBoundaryBridge`, which owns the finite `Z₃` /
  Fibonacci / Yang--Baxter / Cantor--Cuntz socket;
* `SplitOctonionCuntzSUSYBridge`, which owns the Cuntz-valued chiral block
  factorisation.

The three reflection-like notions remain distinct: the chiral sheet flip,
the Yang--Baxter matrix pair, and the Cuntz shifts.  No physical braid,
scattering, parafermion, or central-extension identification is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.ChiralCuntzBraidedSuperchargeBridge

open InfoGeometry.Categorical.CelikZ3FibonacciCuntzBoundaryBridge
open InfoGeometry.Physics.SplitOctonionCuntzSUSYBridge

variable {A : Type*} [Mul A]

/-- The finite chiral supercharge packet transported alongside the existing
`Z₃`/Fibonacci/Cuntz boundary packet. -/
theorem chiral_cuntz_braided_supercharge_packet
    (n : ℕ) (c : Fin n → ℂ)
    (R12 R23 : A)
    (sourceR sourceB : Matrix (Fin 2) (Fin 2) ℝ)
    (hYB : HasSalihCelikZ3CartanYBE R12 R23)
    (hMatch : MatchesFiniteZ3FibonacciMatrices sourceR sourceB)
    (a b : Bool) :
    cuntzWeylQPlus n c * cuntzWeylQPlus n c = 0 ∧
      cuntzWeylQMinus n c * cuntzWeylQMinus n c = 0 ∧
      cuntzWeylDirac n c * cuntzWeylDirac n c = cuntzWeylHamiltonian n c ∧
      (R12 * R23 * R12 = R23 * R12 * R23) ∧
      (sourceR * sourceB * sourceR = sourceB * sourceR * sourceB) ∧
      (wordParityZ2 (oddStep a) = 1 ∧
        wordParityZ2 (oddStep b) = 1 ∧
          wordParityZ2 (oddStep a ++ oddStep b) = 0) := by
  refine ⟨cuntzWeylQPlus_sq n c, cuntzWeylQMinus_sq n c,
    cuntzWeylDirac_sq n c, hYB,
    matched_source_satisfies_fibonacci_z3_artin sourceR sourceB hMatch,
    cantor_cuntz_odd_odd_boundary_even a b⟩

end InfoGeometry.Physics.ChiralCuntzBraidedSuperchargeBridge
