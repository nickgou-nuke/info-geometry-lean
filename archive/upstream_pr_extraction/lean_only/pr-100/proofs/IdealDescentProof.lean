import proofs.BraidIdealDescent
import proofs.YangBaxterQuotientDescent
import proofs.JonesBraidB3
import proofs.YangBaxterQSwap

/-!
# Ideal Descent Proof — capstone

Single import verifying the full descent chain compiles:

- `BraidIdealDescent` — τ-maps, left/right τ-ideal submodule preservation
- `YangBaxterQuotientDescent` — generic quotient YBE descent
- `JonesBraidB3` — concrete B₃ Artin relation
- `YangBaxterQSwap` — concrete YBE for all q ∈ ℂ

Next target: construct concrete `IsLeftTauIdeal` for the chiral TL
relation submodule with the q-cross map, finishing the instantiation.
-/

noncomputable section

namespace IdealDescentProof

#check YangBaxterQuotientDescent.yang_baxter_descends
#check JonesBraidB3.artin_braid_relation
#check YangBaxterQSwap.yang_baxter_relation

end IdealDescentProof
