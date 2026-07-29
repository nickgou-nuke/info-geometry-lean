import Mathlib.Tactic
import Omega.Core.WalshStokesSingleton

namespace Automath.Generated

set_option linter.unusedVariables false

/-- Faithful Automath Omega: Walsh-Stokes singleton identity on the Cantor group -/
theorem omega_walsh_stokes {n : Nat} (i : Fin n) (f : Omega.Word n → ℤ) :
    Finset.sum (Finset.univ.filter fun w : Omega.Word n => w i = false)
        (Omega.Core.deltaBit i f) =
      ∑ w : Omega.Word n, (if w i = false then 1 else -1) * f w := by
  exact Omega.Core.walshStokes_singleton i f

end Automath.Generated
