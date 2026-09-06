import Lean
import Aesop

/-!
# Dvořák Tactics

Custom tactics borrowed from Martin Dvořák's "Pursuit of Truth and Beauty in Lean 4".
These tactics prioritize structural preservation and automation of validity conditions.
-/

namespace InfoGeometry.Meta

/--
`aeply t` is a custom tactic based on `aesop`.
It introduces hypotheses, applies the given term `t`, and then uses `aesop` to 
discharge any remaining side goals (such as validity or measurability conditions).
-/
macro "aeply" t:term : tactic => `(tactic| try intro <;> apply $t <;> first | aesop | assumption)

end InfoGeometry.Meta
