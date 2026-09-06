import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Algebra.AnyonFiniteSpinBraid

/-- GAP finite quotient orders for the D-type Coxeter witnesses. -/
def gapD4Order : ℕ := 192

def gapD5Order : ℕ := 1920

namespace CoxeterDQuotientCertificate

/-- The GAP property records `|W(D₄)| = 192`. -/
theorem D4_order_readout : gapD4Order = 192 :=
  rfl

/-- The GAP property records `|W(D₅)| = 1920`. -/
theorem D5_order_readout : gapD5Order = 1920 :=
  rfl

end CoxeterDQuotientCertificate

end InfoGeometry.Algebra.AnyonFiniteSpinBraid

end noncomputable section
