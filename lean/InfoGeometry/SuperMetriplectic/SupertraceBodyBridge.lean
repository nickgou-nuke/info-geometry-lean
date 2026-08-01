import InfoGeometry.SuperMetriplectic.BlackHoleEntropy
import InfoGeometry.Algebraic.SplitSuperGeometry

/-!
# Supertrace Body-Positivity Bridge

Scalar/body-level bridge for the supertrace question.

Replacing an ordinary trace by a supertrace does not preserve ordinary
positive-definiteness on the full supergraded space.  At this level we record
the precise conservative shadow:

* the supertrace readout is signed between even and odd sectors;
* the observable second-law statement is carried by a separate body/Fisher
  quadratic form;
* positivity of the supertrace itself requires an additional domination or
  restriction hypothesis.

No concrete `Cl(4,4)` matrix representation, Zorn multiplication table, or
Grassmann algebra is constructed here.
-/

namespace InfoGeometry.SuperMetriplectic

/--
Scalar shadow of the ordinary-trace/supertrace comparison for a Fisher/Onsager
quadratic form.

`evenQuadratic` and `oddQuadratic` are body readouts of the diagonal chiral
blocks.  `nilpotentCancellation` is a scalar placeholder for the part that
disappears, cancels, or is separately projected when passing to the observable
body.  The supertrace readout is signed; hence its nonnegativity is not assumed.
-/
structure SupertraceFisherShadow where
  evenQuadratic : ℝ
  oddQuadratic : ℝ
  nilpotentCancellation : ℝ
  ordinaryTraceQuadratic : ℝ
  supertraceQuadratic : ℝ
  bodyFisherQuadratic : ℝ
  ordinaryTraceQuadratic_eq :
    ordinaryTraceQuadratic =
      evenQuadratic + oddQuadratic + nilpotentCancellation
  supertraceQuadratic_eq :
    supertraceQuadratic =
      evenQuadratic - oddQuadratic + nilpotentCancellation
  bodyFisherQuadratic_eq :
    bodyFisherQuadratic =
      evenQuadratic + oddQuadratic
  bodyFisherQuadratic_nonnegative :
    0 ≤ bodyFisherQuadratic

namespace SupertraceFisherShadow

/-- The ordinary trace keeps the even and odd body contributions with the same sign. -/
theorem ordinaryTrace_eq (S : SupertraceFisherShadow) :
    S.ordinaryTraceQuadratic =
      S.evenQuadratic + S.oddQuadratic + S.nilpotentCancellation :=
  S.ordinaryTraceQuadratic_eq

/-- The supertrace flips the sign of the odd body contribution. -/
theorem supertrace_eq (S : SupertraceFisherShadow) :
    S.supertraceQuadratic =
      S.evenQuadratic - S.oddQuadratic + S.nilpotentCancellation :=
  S.supertraceQuadratic_eq

/-- Observable Fisher positivity is a body statement, not a raw supertrace statement. -/
theorem body_second (S : SupertraceFisherShadow) :
    0 ≤ S.bodyFisherQuadratic :=
  S.bodyFisherQuadratic_nonnegative

/--
The signed supertrace differs from the ordinary trace by twice the odd
quadratic contribution.
-/
theorem supertrace_eq_ordinary_minus_two_odd
    (S : SupertraceFisherShadow) :
    S.supertraceQuadratic =
      S.ordinaryTraceQuadratic - 2 * S.oddQuadratic := by
  rw [S.supertrace_eq, S.ordinaryTrace_eq]
  ring

/--
If the nilpotent/cancellation readout vanishes, the supertrace is the body
Fisher quadratic minus twice the odd contribution.
-/
theorem supertrace_eq_body_minus_two_odd_of_nilpotent_zero
    (S : SupertraceFisherShadow)
    (hN : S.nilpotentCancellation = 0) :
    S.supertraceQuadratic =
      S.bodyFisherQuadratic - 2 * S.oddQuadratic := by
  rw [S.supertrace_eq, S.bodyFisherQuadratic_eq, hN]
  ring

/--
Extra domination condition under which the signed supertrace readout is
nonnegative.  This is deliberately a hypothesis: it is not a consequence of
body Fisher positivity alone.
-/
theorem supertrace_nonnegative_of_odd_dominated
    (S : SupertraceFisherShadow)
    (hN : S.nilpotentCancellation = 0)
    (hdom : 2 * S.oddQuadratic ≤ S.bodyFisherQuadratic) :
    0 ≤ S.supertraceQuadratic := by
  rw [S.supertrace_eq_body_minus_two_odd_of_nilpotent_zero hN]
  exact sub_nonneg.mpr hdom

end SupertraceFisherShadow

/--
Finite scalar body data for a Zorn even/odd entropy split.

This is deliberately a readout packet: it does not assert a concrete Zorn
matrix model or identify the three scalars with an operator trace.  The only
structural law recorded here is the displayed body bookkeeping identity.
-/
structure ZornEvenOddEntropySplit where
  evenBodyEntropy : ℝ
  oddBodyEntropy : ℝ
  cancellationReadout : ℝ
  totalBodyEntropy : ℝ
  totalBodyEntropy_eq :
    totalBodyEntropy = evenBodyEntropy + oddBodyEntropy - cancellationReadout

/--
Bridge from a Zorn even/odd entropy split to the supertrace Fisher shadow.

The field `zornTotal_eq_bodyFisher` states that the Zorn body total is the same
observable Fisher quadratic.  This keeps the `STr` signed readout separate from
the physically ordered body quantity.
-/
structure ZornSupertraceFisherBridge where
  zorn : ZornEvenOddEntropySplit
  fisher : SupertraceFisherShadow
  zornTotal_eq_bodyFisher :
    zorn.totalBodyEntropy = fisher.bodyFisherQuadratic

namespace ZornSupertraceFisherBridge

/-- The Zorn total body entropy inherits the observable Fisher nonnegativity. -/
theorem zorn_total_nonnegative
    (B : ZornSupertraceFisherBridge) :
    0 ≤ B.zorn.totalBodyEntropy := by
  rw [B.zornTotal_eq_bodyFisher]
  exact B.fisher.body_second

/--
The bridge exposes both facts needed for the supertrace interpretation:
the body quantity is nonnegative, while the raw supertrace remains the signed
even-minus-odd readout.
-/
theorem body_positive_and_supertrace_signed
    (B : ZornSupertraceFisherBridge) :
    0 ≤ B.zorn.totalBodyEntropy
      ∧ B.fisher.supertraceQuadratic =
        B.fisher.evenQuadratic
          - B.fisher.oddQuadratic
          + B.fisher.nilpotentCancellation := by
  exact ⟨B.zorn_total_nonnegative, B.fisher.supertrace_eq⟩

end ZornSupertraceFisherBridge

/-
Operator-level translation of the signed supertrace language onto the split
Clifford parity core.

This is the new primitive surface: parity involution, parity-weighted trace,
and supervolume readout on the split Clifford carrier.
-/
namespace SplitParitySupertraceTranslation

open InfoGeometry.Algebraic.SplitSignature

/-- The operator-level parity/supertrace shadow on `Cl(n,n)`. -/
abbrev SplitParitySupertraceShadow (n : ℕ) := SplitCliffordEnd n

namespace SplitParitySupertraceShadow

/-- The canonical parity involution on the split-Clifford carrier. -/
noncomputable def parity {n : ℕ} (_ : SplitParitySupertraceShadow n) : SplitCliffordEnd n :=
  parityOp n

/-- The supertrace readout is the canonical parity-weighted Clifford trace. -/
noncomputable def supertraceReadout
    {n : ℕ} (_ : SplitParitySupertraceShadow n) : SplitCliffordEnd n → ℝ :=
  cliffordSupertrace n

/-- The super-Berezinian readout is the canonical Clifford Berezinian. -/
noncomputable def superBerezinianReadout
    {n : ℕ} (_ : SplitParitySupertraceShadow n) : SplitCliffordEnd n → ℝ :=
  superBerezinian n

/-- The supervolume potential is the canonical effective-action readout. -/
noncomputable def supervolumePotential
    {n : ℕ} (_ : SplitParitySupertraceShadow n) : SplitCliffordEnd n → ℝ :=
  superEffectiveAction n

end SplitParitySupertraceShadow

@[simp]
theorem parity_comp_self (n : ℕ) (x : Cl_nn n) :
    (parityOp n) ((parityOp n) x) = x :=
  InfoGeometry.Algebraic.SplitSuperGeometry.parityOp_comp_self n x

@[simp]
theorem supervolumePotential_eq_neg_log_superBerezinian
    (n : ℕ) (x : SplitCliffordEnd n) :
    (superEffectiveAction n) x = - Real.log ((superBerezinian n) x) :=
  InfoGeometry.Algebraic.SplitSuperGeometry.superEffectiveAction_eq_neg_log_superBerezinian n x

end SplitParitySupertraceTranslation

end InfoGeometry.SuperMetriplectic
