    Nat.Coprime b q →
      AsymptoticEquivalentAtTop
        (fun N => (residuePrimeCount N q a : ℝ))
        (fun N => (residuePrimeCount N q b : ℝ))

/--
RH-style square-root error law for prime counting.

This is intentionally a supplied analytic bound, not a theorem proved here.
-/
def RHPrimeCountingErrorLaw : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 2 ≤ N →
      |(primeCounting N : ℝ) - pntCountingScale N| ≤
        C * Real.sqrt (N : ℝ) * Real.log (N : ℝ)

/-- Bundle of the standard named asymptotic laws. -/
structure PrimeDistributionAsymptoticPacket where
  pnt_counting : PrimeNumberTheoremCountingLaw
  chebyshev_psi : ChebyshevPsiAsymptoticLaw
  chebyshev_theta : ChebyshevThetaAsymptoticLaw