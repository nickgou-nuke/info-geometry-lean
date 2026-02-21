import InfoGeometry.Axioms
import InfoGeometry.Assumptions
import InfoGeometry.Analytic.LogSumExp
import InfoGeometry.Degree
import InfoGeometry.EntropicInference
import InfoGeometry.Information.MultiLogPotential
import InfoGeometry.Library
import InfoGeometry.Projective.LogSum
import InfoGeometry.Research
import InfoGeometry.Thermo.Gibbs
import InfoGeometry.TransformationGroups

/-!
# InfoGeometry.New

Legacy scratchpad compatibility module.

The previous experimental draft content has been retired; unresolved claims are
now surfaced explicitly through `InfoGeometry.Assumptions` / `InfoGeometry.Axioms`.
Constructive material remains in the canonical `InfoGeometry` / `InfoGeometry.Library`
surface.

Additional noncanonical compatibility modules are imported here so legacy users can
transition away from `InfoGeometry.New` incrementally.

Research APIs extracted from old `New.lean` are now exposed domain-by-domain in:

- `InfoGeometry.Research.IB`
- `InfoGeometry.Research.ManifoldHomology`
- `InfoGeometry.Research.Determinant`
- `InfoGeometry.Research.DualConnections`
- `InfoGeometry.Research.LLN`
-/

namespace InfoGeometry.New

/- Namespace intentionally left light-weight; users should import
`InfoGeometry.Assumptions` or `InfoGeometry.Axioms` directly. -/

end InfoGeometry.New
