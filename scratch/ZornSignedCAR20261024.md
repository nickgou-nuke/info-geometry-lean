# U, -V signed operator CAR

Uncompiled scratch candidate; parent integration, independent AA and locked QA pending.
No builds/tests/CAS executed. Native ZornVectorMatrix and L_map are reused directly.

Prior-owner check: SplitOctonionCARBdGRegularLift.leftRegular_anticommutator and
leftRegular_sq_zero_of_sq_zero specialize to Canonical.ZornMatrix ℝ.
ZornLeftCAR and FirstQuantizedLeftRegular are also real-specialized. The new
two generic L_map lemmas assume only left alternativity on a nonunital
nonassociative R-algebra. Polarization divides by nothing.

Five Zorn consequences cover the explicit U_i, -V_i convention over any CommRing:
both squares zero, both same-sector anticommutators zero, mixed anticommutator
(if i=j then -1 else 0) times the identity. Nilpotency reuses native element
square-zero proofs. CAR reuses CattoGurseySplitBasis.car_relations through the
explicit swap/sign dictionary; Catto itself uses V_i, -U_i.

Two real obstruction lemmas show -(L_U0 * L_(-V1)) sends U1 to U0 and differs
from the zero off-diagonal odd anticommutator. No new E01 definition or carrier
is introduced. This rejects the proposed identification with that ordered
operator; it does not classify all Lie superalgebra representations.

No parity lemmas: parent owns grading, including the convention-sensitive
parity-product sign. No star/adjoint claim or ordered-product homomorphism.

Audit all nine theorem heads in this file. Generic lemmas should integrate
with the existing generic alternative-action owner; signed consequences with
the native Zorn operator consumer. No forwarding wrapper module is needed.
