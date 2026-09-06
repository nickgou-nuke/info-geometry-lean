import InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge

namespace InfoGeometry.Canonical

namespace CuntzBogoliubovDeGennesFormalism

/-! Algebraic BdG data for a star-algebra element.

This file deliberately contains only the bridge identity.  It does not
identify the cyclic supercharge with a nilpotent exterior differential, and
it does not assert positivity or non-vanishing of the gap.
-/

variable {A : Type*} [Ring A] [StarRing A]

open ToeplitzCuntzThreeVacuumBridge

/-- The sum and difference combinations of a star-algebra element. -/
def diracPlus (Q : A) : A := Q + star Q

def diracMinus (Q : A) : A := Q - star Q

/-- The algebraic pairing term used as the BdG gap. -/
def bdgGap (Q : A) : A := Q * Q

/-- The symmetric kinetic term associated with a star-algebra element. -/
def bdgKinetic (Q : A) : A := star Q * Q + Q * star Q

/--
The anticommutator of the two Dirac combinations is the star-odd part of
the quadratic gap.  This is purely an associative ring identity.
-/
theorem dirac_anticommutator_eq_gap_defect (Q : A) :
    diracPlus Q * diracMinus Q + diracMinus Q * diracPlus Q =
      2 * (bdgGap Q - star (bdgGap Q)) := by
  dsimp [diracPlus, diracMinus, bdgGap]
  rw [star_mul]
  noncomm_ring

/-- The quadratic gap is the square of the native cyclic supercharge. -/
theorem cyclicSupercharge_bdgGap_eq_square
    (g : ToeplitzCuntzThreeGenerators A) :
    bdgGap (ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge g) =
      g.V1 * star g.V3 + g.V2 * star g.V1 + g.V3 * star g.V2 := by
  exact ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge_sq g

/--
The generic gap-defect identity specialized to the repository's native
three-channel cyclic supercharge.
-/
theorem cyclicSupercharge_dirac_anticommutator_eq_gap_defect
    (g : ToeplitzCuntzThreeGenerators A) :
    diracPlus (ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge g) *
          diracMinus (ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge g) +
        diracMinus (ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge g) *
          diracPlus (ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge g) =
      2 *
        (bdgGap (ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge g) -
          star (bdgGap (ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge g))) := by
  exact dirac_anticommutator_eq_gap_defect
    (ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge g)

/-- The native cyclic owner identifies the adjoint of Q with its square. -/
theorem cyclicSupercharge_bdgGap_eq_star
    (g : ToeplitzCuntzThreeGenerators A) :
    star (ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge g) =
      bdgGap (ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge g) := by
  exact ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge_star_eq_sq g

end CuntzBogoliubovDeGennesFormalism

end InfoGeometry.Canonical
