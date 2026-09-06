import proofs.ChiralCausalCone
import proofs.ChiralTensorRecoupling
import proofs.TLChain
import proofs.JonesBraidB3
import proofs.YangBaxterQSwap
import proofs.B3PresentedGroup
import proofs.SpectralYangBaxter
import proofs.FibAnyonThm4
import proofs.HexagonCocycle
import proofs.BraidNegativeIdentityMonodromy
import proofs.ArtinMonodromyPin55

/-!
# Baxter Anchor Manifest — unified YBE/braid spine

Single import point verifying that ALL Baxter/YBE anchor modules compile.

| Module                         | Theorem                        |
|--------------------------------|--------------------------------|
| `ChiralCausalCone`             | chiral CAR algebra             |
| `ChiralTensorRecoupling`       | TL generator e²=2e             |
| `TLChain`                      | TL₃(2) skein relations         |
| `JonesBraidB3`                 | `artin_braid_relation`         |
| `YangBaxterQSwap`              | `yang_baxter_relation` (∀ q∈ℂ) |
| `B3PresentedGroup`             | s₀²=-I, s₁²=-I, GL₈ units      |
| `SpectralYangBaxter`           | spectral field YBE             |
| `FibAnyonThm4`                 | Fibonacci braid                |
| `HexagonCocycle`               | categorical hexagon→YBE        |
| `BraidNegativeIdentityMonodromy`| spinor monodromy              |
| `ArtinMonodromyPin55`          | Pin(5,5) monodromy             |

`lake build BaxterAnchorManifest` compiles all 11 modules as a single target.
-/

namespace BaxterAnchorManifest

#check JonesBraidB3.artin_braid_relation
#check YangBaxterQSwap.yang_baxter_relation
#check B3PresentedGroup.braid_square_eq_neg_one

end BaxterAnchorManifest
