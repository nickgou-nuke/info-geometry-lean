import InfoGeometry.Quantum.MertensPartialTrace
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.MertensPartialTraceCapstone

open InfoGeometry.Quantum.MertensPartialTrace

/-- Canonical projection of the evaluated Mertens partial-sum owner. -/
theorem capstone_mertens_partial_trace_synthesis :
    mertensSum 1 = 1 := by
  exact mertens_at_one

end InfoGeometry.Canonical.MertensPartialTraceCapstone
