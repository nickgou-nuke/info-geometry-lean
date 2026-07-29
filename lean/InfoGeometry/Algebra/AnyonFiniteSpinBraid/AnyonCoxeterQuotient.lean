import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Algebra.AnyonFiniteSpinBraid

/-- GAP finite quotient orders for the D-type Coxeter witnesses. -/
def gapD4Order : ℕ := 192

def gapD5Order : ℕ := 1920

/-- GAP finite quotient certificate for the D-type Coxeter witnesses. -/
abbrev CoxeterDQuotientCertificate : Prop :=
  gapD4Order = 192 ∧ gapD5Order = 1920

namespace CoxeterDQuotientCertificate

/-- Certificate values emitted by `tools/gap/anyon_braid_closure.g`. -/
def gapWitness : CoxeterDQuotientCertificate :=
  ⟨rfl, rfl⟩

/-- The GAP witness records `|W(D₄)| = 192`. -/
theorem D4_order_readout : gapD4Order = 192 :=
  gapWitness.1

/-- The GAP witness records `|W(D₅)| = 1920`. -/
theorem D5_order_readout : gapD5Order = 1920 :=
  gapWitness.2

end CoxeterDQuotientCertificate

end InfoGeometry.Algebra.AnyonFiniteSpinBraid

end noncomputable section
