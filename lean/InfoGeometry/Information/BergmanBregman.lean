import InfoGeometry.Canonical.SouriauOperatorBregmanModular
import InfoGeometry.Canonical.SouriauModularBregmanOperator

/-!
# Bregman information compatibility surface

The former file exposed a one-dimensional real `bregmanDiv` wrapper.  That
surface was not consumed by any downstream theorem and is not an owner for the
noncommutative information geometry used by this repository.  The maintained
owners are the operator-valued Souriau/Bregman modules imported above.

No scalar localization or surrogate commutative theorem is introduced here.
-/
