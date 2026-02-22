import InfoGeometry.Canonical.Krein
import InfoGeometry.Krein.Metric
import InfoGeometry.Krein.Automorphisms
import InfoGeometry.Krein.CartanDecomposition
import InfoGeometry.Krein.Modular
import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Krein.Thermal

/-!
# InfoGeometry.Krein

Compatibility umbrella for legacy imports.
This file re-exports a few commonly-used definitions under the old
namespace so that legacy code continues to compile even if the
canonical modules are reorganized.

Prefer `import InfoGeometry` (or `InfoGeometry.Canonical.Krein`)
for new development.
-/

namespace InfoGeometry.Krein

-- simple alias for the indefinite Hessian pairing

@[simp]
def hessianIndefiniteFormCompat {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (v w : DoubledSpace E) : ℝ :=
  InfoGeometry.Krein.Metric.hessianIndefiniteForm (E := E) v w

-- compatibility synonym for the isometry structure

abbrev KreinIsometryCompat :=
  InfoGeometry.Krein.Metric.KreinIsometry

end InfoGeometry.Krein
