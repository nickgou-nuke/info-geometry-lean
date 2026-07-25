import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Algebra.AnyonFiniteSpinBraid

/-- GAP finite quotient certificate for the D-type Coxeter witnesses. -/
structure CoxeterDQuotientCertificate where
  D4_order : ℕ
  D5_order : ℕ
  D4_order_eq : D4_order = 192
  D5_order_eq : D5_order = 1920

namespace CoxeterDQuotientCertificate

/-- Certificate values emitted by `tools/gap/anyon_braid_closure.g`. -/
def gapWitness : CoxeterDQuotientCertificate where
  D4_order := 192
  D5_order := 1920
  D4_order_eq := rfl
  D5_order_eq := rfl

/-- The GAP witness records `|W(D₄)| = 192`. -/
theorem D4_order_readout : gapWitness.D4_order = 192 :=
  gapWitness.D4_order_eq

/-- The GAP witness records `|W(D₅)| = 1920`. -/
theorem D5_order_readout : gapWitness.D5_order = 1920 :=
  gapWitness.D5_order_eq

end CoxeterDQuotientCertificate

end InfoGeometry.Algebra.AnyonFiniteSpinBraid

end noncomputable section
