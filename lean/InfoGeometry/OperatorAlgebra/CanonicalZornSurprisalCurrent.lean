import InfoGeometry.OperatorAlgebra.CanonicalZornDerivationDifferentialForms

/-!
# Canonical split-octonion operator surprisal current

For the faithful action of canonical Zorn derivations on the associative
operator algebra `End_R(O_s)`, the differential of an operator zero-form `K`
is the one-form `J_K(D) = [D, K]`.

This file records that current as an exact Chevalley--Eilenberg one-form and
therefore proves its closedness from `d² = 0`.  No global flux integral or
spectral interpretation of zeta zeros is asserted.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CanonicalZornSurprisalCurrent

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornOperatorDerivationLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ
abbrev ZornDer := canonicalZornDerivations
abbrev Lane := canonicalZornOperatorDerivationLane
abbrev OperatorOneForm := OneForm Lane

def surprisalCurrent (K : EndCZ) : OperatorOneForm :=
  exteriorDerivativeZero Lane K

@[simp] theorem surprisalCurrent_apply
    (K : EndCZ) (D : ZornDer) :
    surprisalCurrent K D = D.1 * K - K * D.1 := by
  exact InfoGeometry.OperatorAlgebra.CanonicalZornDerivationDifferentialForms.exteriorDerivativeZero_apply K D

theorem surprisalCurrent_isExact (K : EndCZ) :
    IsExactOneForm Lane (surprisalCurrent K) := by
  exact ⟨K, rfl⟩

theorem surprisalCurrent_isClosed (K : EndCZ) :
    IsClosedOneForm Lane (surprisalCurrent K) := by
  unfold IsClosedOneForm surprisalCurrent
  exact InfoGeometry.OperatorAlgebra.CanonicalZornDerivationDifferentialForms.exteriorDerivativeOne_exteriorDerivativeZero K

theorem exteriorDerivative_surprisalCurrent_eq_zero (K : EndCZ) :
    exteriorDerivativeOne Lane (surprisalCurrent K) = 0 :=
  surprisalCurrent_isClosed K

theorem surprisalCurrent_eq_zero_iff_commutes
    (K : EndCZ) (D : ZornDer) :
    surprisalCurrent K D = 0 ↔ D.1 * K = K * D.1 := by
  rw [surprisalCurrent_apply]
  exact sub_eq_zero

theorem surprisalCurrent_eq_zero_of_commutes
    (K : EndCZ) (D : ZornDer)
    (hKD : D.1 * K = K * D.1) :
    surprisalCurrent K D = 0 :=
  (surprisalCurrent_eq_zero_iff_commutes K D).2 hKD

theorem commutes_of_surprisalCurrent_eq_zero
    (K : EndCZ) (D : ZornDer)
    (hJ : surprisalCurrent K D = 0) :
    D.1 * K = K * D.1 :=
  (surprisalCurrent_eq_zero_iff_commutes K D).1 hJ

end InfoGeometry.OperatorAlgebra.CanonicalZornSurprisalCurrent
