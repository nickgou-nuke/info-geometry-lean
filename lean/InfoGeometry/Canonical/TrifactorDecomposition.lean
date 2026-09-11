import InfoGeometry.Canonical.TriFacetGeometry
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Trifactor Decomposition

Canonical sector naming for a tripotent operator `T` satisfying `T ^ 3 = T`.

The proof authority is `InfoGeometry.Canonical.TriFacetGeometry`; this file
relabels its three facets as the projective/modular sectors:

* `P_plus`:  `+1` conformal-flow sector (`det = 1`);
* `P_minus`: `-1` mirror/Tomita sector (`det = -1`);
* `P_zero`:  `0` null-boundary sector (`det = 0`).

The algebra is intentionally finite and polynomial: no spectral theorem,
external certificate, or analytic branch cut is used.
-/

namespace InfoGeometry.Canonical.TrifactorDecomposition

open TriFacetGeometry

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The null boundary projector, corresponding to the `0` sector. -/
def P_zero (T : R) : R := P_par T

/-- The positive conformal-flow projector, corresponding to the `+1` sector. -/
def P_plus (T : R) : R := P_hyp T

/-- The negative mirror projector, corresponding to the `-1` sector. -/
def P_minus (T : R) : R := P_ell T

omit [Invertible (2 : R)] in
/-- The null boundary projector is idempotent under `T ^ 3 = T`. -/
theorem P_zero_idempotent (T : R) (hT : T ^ 3 = T) :
    P_zero T * P_zero T = P_zero T := by
  unfold P_zero
  exact P_par_idem T hT

/-- The positive conformal-flow projector is idempotent under `T ^ 3 = T`. -/
theorem P_plus_idempotent (T : R) (hT : T ^ 3 = T) :
    P_plus T * P_plus T = P_plus T := by
  unfold P_plus
  exact P_hyp_idem T hT

/-- The negative mirror projector is idempotent under `T ^ 3 = T`. -/
theorem P_minus_idempotent (T : R) (hT : T ^ 3 = T) :
    P_minus T * P_minus T = P_minus T := by
  unfold P_minus
  exact P_ell_idem T hT

/-- The positive and negative sectors are orthogonal. -/
theorem P_plus_P_minus_orthogonal (T : R) (hT : T ^ 3 = T) :
    P_plus T * P_minus T = 0 := by
  unfold P_plus P_minus
  exact P_hyp_ell_orth T hT

/-- The null and positive sectors are orthogonal. -/
theorem P_zero_P_plus_orthogonal (T : R) (hT : T ^ 3 = T) :
    P_zero T * P_plus T = 0 := by
  unfold P_zero P_plus
  rw [mul_comm]
  exact P_hyp_par_orth T hT

/-- The null and negative sectors are orthogonal. -/
theorem P_zero_P_minus_orthogonal (T : R) (hT : T ^ 3 = T) :
    P_zero T * P_minus T = 0 := by
  unfold P_zero P_minus
  rw [mul_comm]
  exact P_ell_par_orth T hT

/-- The three sectors form a partition of unity. -/
theorem partition_of_unity (T : R) :
    P_zero T + P_plus T + P_minus T = 1 := by
  unfold P_zero P_plus P_minus
  calc
    P_par T + P_hyp T + P_ell T = P_hyp T + P_ell T + P_par T := by ring
    _ = 1 := P_sum T

omit [Invertible (2 : R)] in
/-- `T` annihilates the null boundary sector. -/
theorem T_on_P_zero (T : R) (hT : T ^ 3 = T) :
    T * P_zero T = 0 := by
  unfold P_zero P_par
  calc
    T * (1 - T ^ 2) = T - T ^ 3 := by ring
    _ = T - T := by rw [hT]
    _ = 0 := by ring

/-- `T` acts by `+1` on the positive conformal-flow sector. -/
theorem T_on_P_plus (T : R) (hT : T ^ 3 = T) :
    T * P_plus T = P_plus T := by
  unfold P_plus P_hyp
  calc
    T * (⅟(2 : R) * (T ^ 2 + T)) = ⅟(2 : R) * (T ^ 3 + T ^ 2) := by ring
    _ = ⅟(2 : R) * (T + T ^ 2) := by rw [hT]
    _ = ⅟(2 : R) * (T ^ 2 + T) := by ring

/-- `T` acts by `-1` on the negative mirror sector. -/
theorem T_on_P_minus (T : R) (hT : T ^ 3 = T) :
    T * P_minus T = -P_minus T := by
  unfold P_minus P_ell
  calc
    T * (⅟(2 : R) * (T ^ 2 - T)) = ⅟(2 : R) * (T ^ 3 - T ^ 2) := by ring
    _ = ⅟(2 : R) * (T - T ^ 2) := by rw [hT]
    _ = -(⅟(2 : R) * (T ^ 2 - T)) := by ring

/-- The tripotent operator is reconstructed as `P_plus - P_minus`. -/
theorem spectral_resolution (T : R) :
    P_plus T - P_minus T = T := by
  unfold P_plus P_minus P_hyp P_ell
  calc
    ⅟(2 : R) * (T ^ 2 + T) - ⅟(2 : R) * (T ^ 2 - T) =
        (⅟(2 : R) * (2 : R)) * T := by ring
    _ = 1 * T := by rw [invOf_mul_self (2 : R)]
    _ = T := by ring

/--
Bundled trifactor readout: tripotence `T ^ 3 = T` gives three idempotent,
orthogonal sectors, a partition of unity, and the expected spectral action.
-/
theorem trifactor_capstone (T : R) (hT : T ^ 3 = T) :
    (P_zero T * P_zero T = P_zero T ∧
      P_plus T * P_plus T = P_plus T ∧
      P_minus T * P_minus T = P_minus T) ∧
    (P_plus T * P_minus T = 0 ∧
      P_zero T * P_plus T = 0 ∧
      P_zero T * P_minus T = 0) ∧
    P_zero T + P_plus T + P_minus T = 1 ∧
    (T * P_zero T = 0 ∧
      T * P_plus T = P_plus T ∧
      T * P_minus T = -P_minus T) ∧
    P_plus T - P_minus T = T := by
  exact ⟨
    ⟨P_zero_idempotent T hT, P_plus_idempotent T hT, P_minus_idempotent T hT⟩,
    ⟨P_plus_P_minus_orthogonal T hT, P_zero_P_plus_orthogonal T hT,
      P_zero_P_minus_orthogonal T hT⟩,
    partition_of_unity T,
    ⟨T_on_P_zero T hT, T_on_P_plus T hT, T_on_P_minus T hT⟩,
    spectral_resolution T⟩

end InfoGeometry.Canonical.TrifactorDecomposition
