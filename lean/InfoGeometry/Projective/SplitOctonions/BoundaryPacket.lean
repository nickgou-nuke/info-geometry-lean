import InfoGeometry.Canonical.AlbertCayleyDickson
import InfoGeometry.Canonical.SplitAlbert
import InfoGeometry.Projective.SplitOctonions.Albert
import InfoGeometry.Projective.SplitOctonions.Polar
import InfoGeometry.Projective.SplitOctonions.ZornConcrete
import InfoGeometry.Projective.SplitOctonions.ZornInstance

/-!
# Split octonion / Albert / Zorn boundary packet

This file packages the split-octonion and split-Albert owner surfaces that the
repository actually proves:

* Albert-Cayley-Dickson split doubling has canonical zero divisors;
* the split Albert carrier has real finrank `27`;
* the concrete Zorn projective datum and its polar incidence are available;
* the canonical positive/negative diagonal rays and light-rays are explicit.

No twistor identification is claimed here.
No Zorn-to-`2 × 2` matrix equivalence is claimed here.
No `twistor space = split octonions` theorem is encoded here.
-/

namespace InfoGeometry.Projective.SplitOctonions.BoundaryPacket

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.SplitAlbert
open InfoGeometry.Projective.SplitOctonions
open ZornProjectiveDatum
open ZornProjectiveDatum.PolarDatum
open ZornCell
end InfoGeometry.Projective.SplitOctonions.BoundaryPacket
