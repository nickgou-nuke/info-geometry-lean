/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.PrimeSUSYVacuum

/-!
# Prime SUSY vacuum finite capstone

The upstream packet assembly depended on an obsolete analytic witness carrier.
This canonical capstone retains its valid finite content: cancellation of the
fermion-parity/Witten-index sum over a nonempty prime register.
-/

namespace InfoGeometry.Canonical.PrimeSUSYVacuumCapstone

open InfoGeometry.Canonical.PrimeSUSYVacuum

theorem finite_prime_susy_vacuum_synthesis
    (P : InfoGeometry.Arithmetic.PrimeSuperalgebraReadback.FermionicPrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndexSum P = 0 ∧
      (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 :=
  finiteSUSYVacuum_wittenIndexCancellation P hP

end InfoGeometry.Canonical.PrimeSUSYVacuumCapstone
