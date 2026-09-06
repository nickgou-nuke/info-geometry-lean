import InfoGeometry.Canonical.EmergentKillingField

/-!
# Finite conjugation invariance of the concrete trace form

This owner records the finite-time algebraic step separately from modular
exponentials.  The only hypotheses are explicit two-sided inverse laws.
-/

namespace InfoGeometry.Canonical.EmergentKillingField

open Matrix

theorem traceForm_conjugation_invariant
    (U Uinv A B : M2R)
    (hleft : Uinv * U = 1) :
    traceForm (U * A * Uinv) (U * B * Uinv) = traceForm A B := by
  unfold traceForm
  calc
    tr ((U * A * Uinv) * (U * B * Uinv)) =
        tr (U * (A * B) * Uinv) := by
      calc
        tr ((U * A * Uinv) * (U * B * Uinv)) =
            tr (U * A * (Uinv * U) * B * Uinv) := by
              simp only [mul_assoc]
        _ = tr (U * (A * B) * Uinv) := by rw [hleft]; simp [mul_assoc]
    _ = tr ((A * B) * Uinv * U) := by
      simpa [mul_assoc] using tr_mul_comm U ((A * B) * Uinv)
    _ = tr ((A * B) * (Uinv * U)) := by simp only [mul_assoc]
    _ = tr (A * B) := by rw [hleft]; simp

end InfoGeometry.Canonical.EmergentKillingField
